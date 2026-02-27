#include "jsonpath_api.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <string_view>
#include <thread>
#include <utility>
#include <vector>

namespace {

template <typename T>
std::shared_ptr<List::list<T>> list_from_vector(const std::vector<T> &xs) {
  auto out = List::list<T>::ctor::nil_();
  for (auto it = xs.rbegin(); it != xs.rend(); ++it) {
    out = List::list<T>::ctor::cons_(*it, out);
  }
  return out;
}

template <typename T>
std::vector<T> vector_from_list(const std::shared_ptr<List::list<T>> &xs) {
  std::vector<T> out;
  auto cur = xs;
  while (true) {
    bool done = false;
    std::visit(
        Overloaded{
            [&](const typename List::list<T>::nil) { done = true; },
            [&](const typename List::list<T>::cons c) {
              out.push_back(c._a0);
              cur = c._a1;
            }},
        cur->v());
    if (done) {
      break;
    }
  }
  return out;
}

std::shared_ptr<Ascii::ascii> to_coq_ascii(unsigned char c) {
  return Ascii::ascii::ctor::Ascii_((c & 1U) != 0U, (c & 2U) != 0U,
                                    (c & 4U) != 0U, (c & 8U) != 0U,
                                    (c & 16U) != 0U, (c & 32U) != 0U,
                                    (c & 64U) != 0U, (c & 128U) != 0U);
}

unsigned char from_coq_ascii(const std::shared_ptr<Ascii::ascii> &a) {
  return std::visit(
      Overloaded{[](const Ascii::ascii::Ascii bits) -> unsigned char {
        unsigned char out = 0U;
        if (bits._a0) {
          out |= 1U;
        }
        if (bits._a1) {
          out |= 2U;
        }
        if (bits._a2) {
          out |= 4U;
        }
        if (bits._a3) {
          out |= 8U;
        }
        if (bits._a4) {
          out |= 16U;
        }
        if (bits._a5) {
          out |= 32U;
        }
        if (bits._a6) {
          out |= 64U;
        }
        if (bits._a7) {
          out |= 128U;
        }
        return out;
      }},
      a->v());
}

std::shared_ptr<String::string> to_coq_string(std::string_view s) {
  auto out = String::string::ctor::EmptyString_();
  for (auto it = s.rbegin(); it != s.rend(); ++it) {
    const auto a = to_coq_ascii(static_cast<unsigned char>(*it));
    out = String::string::ctor::String_(a, out);
  }
  return out;
}

std::string from_coq_string(const std::shared_ptr<String::string> &s) {
  std::string out;
  auto cur = s;
  while (true) {
    bool done = false;
    std::visit(
        Overloaded{
            [&](const String::string::EmptyString) { done = true; },
            [&](const String::string::String x) {
              out.push_back(static_cast<char>(from_coq_ascii(x._a0)));
              cur = x._a1;
            }},
        cur->v());
    if (done) {
      break;
    }
  }
  return out;
}

std::shared_ptr<Positive::positive> positive_from_uint64(std::uint64_t n) {
  if (n <= 1U) {
    return Positive::positive::ctor::xH_();
  }
  const auto tail = positive_from_uint64(n >> 1U);
  if ((n & 1U) == 0U) {
    return Positive::positive::ctor::xO_(tail);
  }
  return Positive::positive::ctor::xI_(tail);
}

std::shared_ptr<Z::z> z_from_int64(std::int64_t n) {
  if (n == 0) {
    return Z::z::ctor::Z0_();
  }
  if (n > 0) {
    return Z::z::ctor::Zpos_(
        positive_from_uint64(static_cast<std::uint64_t>(n)));
  }
  const auto abs_u = static_cast<std::uint64_t>(-(n + 1)) + 1U;
  return Z::z::ctor::Zneg_(positive_from_uint64(abs_u));
}

std::uint64_t positive_to_u64(const std::shared_ptr<Positive::positive> &p) {
  return std::visit(
      Overloaded{
          [](const Positive::positive::xH) -> std::uint64_t { return 1U; },
          [](const Positive::positive::xO x) -> std::uint64_t {
            return positive_to_u64(x._a0) << 1U;
          },
          [](const Positive::positive::xI x) -> std::uint64_t {
            return (positive_to_u64(x._a0) << 1U) | 1U;
          }},
      p->v());
}

std::int64_t z_to_i64(const std::shared_ptr<Z::z> &z) {
  return std::visit(
      Overloaded{
          [](const Z::z::Z0) -> std::int64_t { return 0; },
          [](const Z::z::Zpos x) -> std::int64_t {
            return static_cast<std::int64_t>(positive_to_u64(x._a0));
          },
          [](const Z::z::Zneg x) -> std::int64_t {
            return -static_cast<std::int64_t>(positive_to_u64(x._a0));
          }},
      z->v());
}

std::string escape_json_string(const std::string &s) {
  std::string out;
  out.reserve(s.size() + 8U);
  for (unsigned char ch : s) {
    switch (ch) {
    case '\"':
      out += "\\\"";
      break;
    case '\\':
      out += "\\\\";
      break;
    case '\n':
      out += "\\n";
      break;
    case '\r':
      out += "\\r";
      break;
    case '\t':
      out += "\\t";
      break;
    default:
      out.push_back(static_cast<char>(ch));
      break;
    }
  }
  return out;
}

std::string q_to_string(const std::shared_ptr<Q> &q) {
  const std::int64_t num = z_to_i64(q->Qnum);
  const std::uint64_t den = positive_to_u64(q->Qden);
  if (den == 1U) {
    return std::to_string(num);
  }
  return std::to_string(num) + "/" + std::to_string(den);
}

std::string render_json(const std::shared_ptr<JSON::value> &v) {
  return std::visit(
      Overloaded{
          [](const JSON::value::JNull) -> std::string { return "null"; },
          [](const JSON::value::JBool x) -> std::string {
            return x._a0 ? "true" : "false";
          },
          [](const JSON::value::JNum x) -> std::string {
            return q_to_string(x._a0);
          },
          [](const JSON::value::JStr x) -> std::string {
            return "\"" + escape_json_string(from_coq_string(x._a0)) + "\"";
          },
          [](const JSON::value::JArr x) -> std::string {
            const auto elems = vector_from_list(x._a0);
            std::string out = "[";
            for (std::size_t i = 0; i < elems.size(); ++i) {
              if (i != 0U) {
                out += ", ";
              }
              out += render_json(elems[i]);
            }
            out += "]";
            return out;
          },
          [](const JSON::value::JObject x) -> std::string {
            const auto fields = vector_from_list(x._a0);
            std::string out = "{";
            for (std::size_t i = 0; i < fields.size(); ++i) {
              if (i != 0U) {
                out += ", ";
              }
              out += "\"" + escape_json_string(from_coq_string(fields[i].first)) +
                     "\": " + render_json(fields[i].second);
            }
            out += "}";
            return out;
          }},
      v->v());
}

std::string exec_error_to_string(API::exec_error e) {
  switch (e) {
  case API::exec_error::E_NotWF:
    return "not_wf";
  case API::exec_error::E_NotChildOnly:
    return "not_child_only";
  case API::exec_error::E_NotLinear:
    return "not_linear";
  case API::exec_error::E_NotFound:
    return "not_found";
  case API::exec_error::E_Multiple:
    return "multiple_results";
  }
  return "unknown_error";
}

std::shared_ptr<JSON::value> jnull() { return JSON::value::ctor::JNull_(); }
std::shared_ptr<JSON::value> jbool(bool b) {
  return JSON::value::ctor::JBool_(b);
}
std::shared_ptr<JSON::value> jnum(std::int64_t n) {
  return JSON::value::ctor::JNum_(std::make_shared<Q>(Q{z_from_int64(n), positive_from_uint64(1U)}));
}
std::shared_ptr<JSON::value> jstr(std::string_view s) {
  return JSON::value::ctor::JStr_(to_coq_string(s));
}
std::shared_ptr<JSON::value>
jarr(const std::vector<std::shared_ptr<JSON::value>> &xs) {
  return JSON::value::ctor::JArr_(list_from_vector(xs));
}
std::shared_ptr<JSON::value> jobj(const std::vector<std::pair<std::string, std::shared_ptr<JSON::value>>> &fields) {
  std::vector<std::pair<std::shared_ptr<String::string>, std::shared_ptr<JSON::value>>> out;
  out.reserve(fields.size());
  for (const auto &f : fields) {
    out.emplace_back(to_coq_string(f.first), f.second);
  }
  return JSON::value::ctor::JObject_(list_from_vector(out));
}

std::shared_ptr<JSONPath::selector> sel_name(std::string_view name) {
  return JSONPath::selector::ctor::SelName_(to_coq_string(name));
}
std::shared_ptr<JSONPath::selector> sel_index(std::int64_t idx) {
  return JSONPath::selector::ctor::SelIndex_(z_from_int64(idx));
}
std::shared_ptr<JSONPath::selector> sel_wild() {
  return JSONPath::selector::ctor::SelWildcard_();
}

std::shared_ptr<JSONPath::segment>
seg_child(const std::vector<std::shared_ptr<JSONPath::selector>> &sels) {
  return JSONPath::segment::ctor::Child_(list_from_vector(sels));
}

std::shared_ptr<JSONPath::query>
query(const std::vector<std::shared_ptr<JSONPath::segment>> &segs) {
  return JSONPath::query::ctor::Query_(list_from_vector(segs));
}

std::shared_ptr<JSON::value> build_demo_json() {
  auto book0 = jobj({{"title", jstr("Sword")}, {"price", jnum(10)}, {"in_stock", jbool(true)}});
  auto book1 = jobj({{"title", jstr("Shield")}, {"price", jnum(15)}, {"in_stock", jbool(false)}});
  auto book2 = jobj({{"title", jstr("Potion")}, {"price", jnum(3)}, {"in_stock", jbool(true)}});

  auto store = jobj({{"book", jarr({book0, book1, book2})},
                     {"bicycle", jobj({{"color", jstr("red")}, {"price", jnum(19)}})}});

  return jobj({{"store", store},
               {"tags", jarr({jstr("rpg"), jstr("gear"), jstr("sale")})},
               {"active", jbool(true)},
               {"note", jnull()}});
}

struct DemoCase {
  std::string label;
  std::shared_ptr<JSONPath::query> q;
};

std::vector<DemoCase> build_demo_cases() {
  return {
      {"$.store.book[0].title",
       query({seg_child({sel_name("store")}), seg_child({sel_name("book")}),
              seg_child({sel_index(0)}), seg_child({sel_name("title")})})},
      {"$.store.book[*].price",
       query({seg_child({sel_name("store")}), seg_child({sel_name("book")}),
              seg_child({sel_wild()}), seg_child({sel_name("price")})})},
      {"$.tags[*]",
       query({seg_child({sel_name("tags")}), seg_child({sel_wild()})})},
      {"$.store.bicycle.color",
       query({seg_child({sel_name("store")}), seg_child({sel_name("bicycle")}),
              seg_child({sel_name("color")})})},
      {"$.store.book[9]",
       query({seg_child({sel_name("store")}), seg_child({sel_name("book")}),
              seg_child({sel_index(9)})})},
  };
}

std::vector<std::string> run_demo_transcript() {
  std::vector<std::string> lines;
  lines.push_back("JSONPath Verified -> Crane C++ Demo (Evaluator Subset)");
  lines.push_back("Source: extracted API.eval_checked + API.values_of");
  lines.push_back("");

  const auto doc = build_demo_json();
  lines.push_back("Input JSON:");
  lines.push_back(render_json(doc));
  lines.push_back("");

  const auto cases = build_demo_cases();
  for (const auto &c : cases) {
    lines.push_back("Query: " + c.label);
    auto r = API::eval_checked(c.q, doc);
    std::visit(
        Overloaded{
            [&](const API::result<std::shared_ptr<List::list<JSON::node>>,
                                  API::exec_error>::Ok ok) {
              const auto vals = API::values_of(ok._a0);
              const auto vec = vector_from_list(vals);
              lines.push_back("Status: ok  matches=" + std::to_string(vec.size()));
              if (vec.empty()) {
                lines.push_back("  value: <none>");
              } else {
                for (const auto &v : vec) {
                  lines.push_back("  value: " + render_json(v));
                }
              }
            },
            [&](const API::result<std::shared_ptr<List::list<JSON::node>>,
                                  API::exec_error>::Error err) {
              lines.push_back("Status: error  code=" +
                              exec_error_to_string(err._a0));
            }},
        r->v());
    lines.push_back("");
  }

  lines.push_back("Notes:");
  lines.push_back("- This demo constructs JSONPath/JSON AST directly in C++.");
  lines.push_back("- Parser extraction is not required for this executable demo.");
  lines.push_back("- The viewport below auto-scrolls through this transcript.");
  return lines;
}

std::string fit_line(const std::string &in, int width) {
  if (width <= 0) {
    return "";
  }
  if (static_cast<int>(in.size()) <= width) {
    return in;
  }
  if (width <= 3) {
    return std::string(static_cast<std::size_t>(width), '.');
  }
  return in.substr(0, static_cast<std::size_t>(width - 3)) + "...";
}

struct TerminalGuard {
  TerminalGuard() {
    const char *enter = "\x1b[?1049h\x1b[2J\x1b[H\x1b[?25l";
    std::fwrite(enter, 1, std::strlen(enter), stdout);
    std::fflush(stdout);
  }
  ~TerminalGuard() {
    const char *leave = "\x1b[?25h\x1b[?1049l";
    std::fwrite(leave, 1, std::strlen(leave), stdout);
    std::fflush(stdout);
  }
};

int env_int(const char *name, int fallback) {
  const char *v = std::getenv(name);
  if (!v || *v == '\0') {
    return fallback;
  }
  const int x = std::atoi(v);
  if (x <= 0) {
    return fallback;
  }
  return x;
}

} // namespace

int main(int argc, char **argv) {
  int width = env_int("COLUMNS", 110);
  int height = env_int("LINES", 32);
  int fps = 18;
  int loops = 3;

  for (int i = 1; i + 1 < argc; i += 2) {
    const std::string flag = argv[i];
    const int value = std::atoi(argv[i + 1]);
    if (flag == "--width" && value > 10) {
      width = value;
    } else if (flag == "--height" && value > 8) {
      height = value;
    } else if (flag == "--fps" && value > 0) {
      fps = value;
    } else if (flag == "--loops" && value > 0) {
      loops = value;
    }
  }

  const auto lines = run_demo_transcript();
  if (lines.empty()) {
    return 1;
  }

  const int body_rows = std::max(4, height - 2);
  const int total_positions =
      static_cast<int>(lines.size()) + body_rows * std::max(1, loops);
  const auto frame_sleep =
      std::chrono::milliseconds(std::max(5, 1000 / std::max(1, fps)));

  TerminalGuard term;

  for (int frame = 0; frame < total_positions; ++frame) {
    const int top = frame % std::max(1, static_cast<int>(lines.size()));
    std::string out;
    out.reserve(static_cast<std::size_t>(width * height));
    out += "\x1b[H";

    for (int row = 0; row < body_rows; ++row) {
      const int idx = top + row;
      std::string line;
      if (idx < static_cast<int>(lines.size())) {
        line = lines[static_cast<std::size_t>(idx)];
      }
      line = fit_line(line, width);
      out += line;
      out += "\x1b[K\r\n";
    }

    const std::string status =
        "jsonpath_scroller_demo | frame " + std::to_string(frame + 1) + "/" +
        std::to_string(total_positions) + " | viewport top " +
        std::to_string(top + 1);
    out += fit_line(status, width);
    out += "\x1b[K";

    std::fwrite(out.data(), 1, out.size(), stdout);
    std::fflush(stdout);
    std::this_thread::sleep_for(frame_sleep);
  }

  return 0;
}
