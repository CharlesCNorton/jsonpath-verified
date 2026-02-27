#include "jsonpath_bridge.h"

#include <cctype>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <optional>
#include <sstream>
#include <string_view>
#include <utility>

namespace {

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

template <typename T>
std::shared_ptr<List::list<T>> vector_to_list(const std::vector<T> &xs) {
  auto out = List::list<T>::ctor::nil_();
  for (auto it = xs.rbegin(); it != xs.rend(); ++it) {
    out = List::list<T>::ctor::cons_(*it, out);
  }
  return out;
}

template <typename T>
std::vector<T> list_to_vector(const std::shared_ptr<List::list<T>> &xs) {
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

std::shared_ptr<Positive::positive> positive_from_uint64(std::uint64_t n) {
  if (n == 0U) {
    return Positive::positive::ctor::xH_();
  }
  if (n == 1U) {
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
    return Z::z::ctor::Zpos_(positive_from_uint64(static_cast<std::uint64_t>(n)));
  }
  const auto abs_u = static_cast<std::uint64_t>(-(n + 1)) + 1U;
  return Z::z::ctor::Zneg_(positive_from_uint64(abs_u));
}

std::shared_ptr<Z::z> z_from_digits(const std::string &digits) {
  auto acc = Z::z::ctor::Z0_();
  const auto z10 = z_from_int64(10);
  for (char ch : digits) {
    const int d = ch - '0';
    acc = Z::add(Z::mul(acc, z10), z_from_int64(d));
  }
  return acc;
}

std::shared_ptr<Z::z> z_pow10(int n) {
  auto out = z_from_int64(1);
  const auto z10 = z_from_int64(10);
  for (int i = 0; i < n; ++i) {
    out = Z::mul(out, z10);
  }
  return out;
}

std::shared_ptr<Positive::positive> positive_pow10(int n) {
  auto out = Positive::positive::ctor::xH_();
  const auto p10 = positive_from_uint64(10);
  for (int i = 0; i < n; ++i) {
    out = Pos::mul(out, p10);
  }
  return out;
}

bool z_is_zero(const std::shared_ptr<Z::z> &z) {
  return Z::eqb(z, Z::z::ctor::Z0_());
}

std::optional<std::shared_ptr<Z::z>>
z_from_integer_lexeme(const std::string &lexeme, std::string &err) {
  if (lexeme.empty()) {
    err = "empty integer";
    return std::nullopt;
  }
  std::size_t i = 0;
  bool neg = false;
  if (lexeme[i] == '-') {
    neg = true;
    ++i;
  }
  if (i >= lexeme.size()) {
    err = "missing digits";
    return std::nullopt;
  }
  if (!std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
    err = "invalid integer";
    return std::nullopt;
  }
  for (std::size_t j = i; j < lexeme.size(); ++j) {
    if (!std::isdigit(static_cast<unsigned char>(lexeme[j]))) {
      err = "invalid integer";
      return std::nullopt;
    }
  }

  std::string digits = lexeme.substr(i);
  const auto first_non_zero = digits.find_first_not_of('0');
  if (first_non_zero == std::string::npos) {
    return Z::z::ctor::Z0_();
  }
  digits.erase(0, first_non_zero);
  auto z = z_from_digits(digits);
  if (neg) {
    z = Z::opp(z);
  }
  return z;
}

std::optional<std::shared_ptr<Q>>
q_from_number_lexeme(const std::string &lexeme, std::string &err) {
  if (lexeme.empty()) {
    err = "empty number";
    return std::nullopt;
  }
  std::size_t i = 0;
  bool neg = false;
  if (lexeme[i] == '-') {
    neg = true;
    ++i;
  }
  if (i >= lexeme.size()) {
    err = "missing number digits";
    return std::nullopt;
  }

  std::string int_digits;
  if (lexeme[i] == '0') {
    int_digits = "0";
    ++i;
    if (i < lexeme.size() &&
        std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
      err = "leading zeros are not allowed";
      return std::nullopt;
    }
  } else if (std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
    while (i < lexeme.size() &&
           std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
      int_digits.push_back(lexeme[i++]);
    }
  } else {
    err = "invalid integer part";
    return std::nullopt;
  }

  std::string frac_digits;
  if (i < lexeme.size() && lexeme[i] == '.') {
    ++i;
    if (i >= lexeme.size() ||
        !std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
      err = "fractional part requires digits";
      return std::nullopt;
    }
    while (i < lexeme.size() &&
           std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
      frac_digits.push_back(lexeme[i++]);
    }
  }

  int exp10 = 0;
  if (i < lexeme.size() && (lexeme[i] == 'e' || lexeme[i] == 'E')) {
    ++i;
    bool exp_neg = false;
    if (i < lexeme.size() && (lexeme[i] == '+' || lexeme[i] == '-')) {
      exp_neg = (lexeme[i] == '-');
      ++i;
    }
    if (i >= lexeme.size() ||
        !std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
      err = "exponent requires digits";
      return std::nullopt;
    }
    while (i < lexeme.size() &&
           std::isdigit(static_cast<unsigned char>(lexeme[i]))) {
      const int d = lexeme[i++] - '0';
      if (exp10 > 10000) {
        err = "exponent too large";
        return std::nullopt;
      }
      exp10 = exp10 * 10 + d;
    }
    if (exp_neg) {
      exp10 = -exp10;
    }
  }

  if (i != lexeme.size()) {
    err = "invalid trailing number characters";
    return std::nullopt;
  }

  std::string mantissa_digits = int_digits + frac_digits;
  const auto first_non_zero = mantissa_digits.find_first_not_of('0');
  std::shared_ptr<Z::z> numerator = Z::z::ctor::Z0_();
  if (first_non_zero != std::string::npos) {
    mantissa_digits.erase(0, first_non_zero);
    numerator = z_from_digits(mantissa_digits);
  }

  const int scale = exp10 - static_cast<int>(frac_digits.size());
  std::shared_ptr<Positive::positive> denominator = Positive::positive::ctor::xH_();
  if (scale >= 0) {
    numerator = Z::mul(numerator, z_pow10(scale));
  } else {
    denominator = positive_pow10(-scale);
  }

  if (neg && !z_is_zero(numerator)) {
    numerator = Z::opp(numerator);
  }

  return std::make_shared<Q>(Q{numerator, denominator});
}

std::string json_escape(const std::string &s) {
  std::ostringstream out;
  for (unsigned char ch : s) {
    switch (ch) {
    case '\"':
      out << "\\\"";
      break;
    case '\\':
      out << "\\\\";
      break;
    case '\b':
      out << "\\b";
      break;
    case '\f':
      out << "\\f";
      break;
    case '\n':
      out << "\\n";
      break;
    case '\r':
      out << "\\r";
      break;
    case '\t':
      out << "\\t";
      break;
    default:
      if (ch < 0x20) {
        out << "\\u" << std::hex << std::setw(4) << std::setfill('0')
            << static_cast<int>(ch) << std::dec;
      } else {
        out << static_cast<char>(ch);
      }
      break;
    }
  }
  return out.str();
}

long double positive_to_ld(const std::shared_ptr<Positive::positive> &p) {
  return std::visit(
      Overloaded{
          [](const Positive::positive::xH) -> long double { return 1.0L; },
          [&](const Positive::positive::xO x) -> long double {
            return 2.0L * positive_to_ld(x._a0);
          },
          [&](const Positive::positive::xI x) -> long double {
            return (2.0L * positive_to_ld(x._a0)) + 1.0L;
          }},
      p->v());
}

long double z_to_ld(const std::shared_ptr<Z::z> &z) {
  return std::visit(
      Overloaded{
          [](const Z::z::Z0) -> long double { return 0.0L; },
          [&](const Z::z::Zpos x) -> long double { return positive_to_ld(x._a0); },
          [&](const Z::z::Zneg x) -> long double {
            return -positive_to_ld(x._a0);
          }},
      z->v());
}

std::string q_to_string(const std::shared_ptr<Q> &q) {
  long double denom = positive_to_ld(q->Qden);
  if (denom == 0.0L) {
    return "0";
  }
  long double value = z_to_ld(q->Qnum) / denom;
  if (!std::isfinite(value)) {
    return "0";
  }
  std::ostringstream out;
  out << std::setprecision(17) << static_cast<double>(value);
  std::string s = out.str();
  if (s.find('.') != std::string::npos) {
    while (!s.empty() && s.back() == '0') {
      s.pop_back();
    }
    if (!s.empty() && s.back() == '.') {
      s.pop_back();
    }
  }
  if (s.empty()) {
    return "0";
  }
  return s;
}

class JsonParser {
public:
  explicit JsonParser(const std::string &input) : input_(input) {}

  jpv::JsonParseResult parse() {
    skip_ws();
    auto v = parse_value();
    if (!v) {
      return {.value = nullptr, .error = error_};
    }
    skip_ws();
    if (pos_ != input_.size()) {
      fail("unexpected trailing characters");
      return {.value = nullptr, .error = error_};
    }
    return {.value = v, .error = ""};
  }

private:
  const std::string &input_;
  std::size_t pos_ = 0;
  std::string error_;

  void fail(const std::string &msg) {
    if (error_.empty()) {
      std::ostringstream out;
      out << msg << " at byte " << pos_;
      error_ = out.str();
    }
  }

  bool has_error() const { return !error_.empty(); }

  bool eof() const { return pos_ >= input_.size(); }

  char peek() const { return eof() ? '\0' : input_[pos_]; }

  char take() {
    if (eof()) {
      return '\0';
    }
    return input_[pos_++];
  }

  void skip_ws() {
    while (!eof()) {
      unsigned char ch = static_cast<unsigned char>(peek());
      if (!std::isspace(ch)) {
        break;
      }
      ++pos_;
    }
  }

  bool consume(char c) {
    if (!eof() && peek() == c) {
      ++pos_;
      return true;
    }
    return false;
  }

  std::optional<std::string> parse_string_literal() {
    if (!consume('\"')) {
      fail("expected string");
      return std::nullopt;
    }
    std::string out;
    while (!eof()) {
      char ch = take();
      if (ch == '\"') {
        return out;
      }
      if (ch == '\\') {
        if (eof()) {
          fail("unterminated escape");
          return std::nullopt;
        }
        char esc = take();
        switch (esc) {
        case '\"':
          out.push_back('\"');
          break;
        case '\\':
          out.push_back('\\');
          break;
        case '/':
          out.push_back('/');
          break;
        case 'b':
          out.push_back('\b');
          break;
        case 'f':
          out.push_back('\f');
          break;
        case 'n':
          out.push_back('\n');
          break;
        case 'r':
          out.push_back('\r');
          break;
        case 't':
          out.push_back('\t');
          break;
        case 'u': {
          if (pos_ + 4 > input_.size()) {
            fail("truncated unicode escape");
            return std::nullopt;
          }
          unsigned value = 0;
          for (int i = 0; i < 4; ++i) {
            char h = take();
            value <<= 4U;
            if (h >= '0' && h <= '9') {
              value |= static_cast<unsigned>(h - '0');
            } else if (h >= 'a' && h <= 'f') {
              value |= static_cast<unsigned>(10 + h - 'a');
            } else if (h >= 'A' && h <= 'F') {
              value |= static_cast<unsigned>(10 + h - 'A');
            } else {
              fail("invalid unicode escape");
              return std::nullopt;
            }
          }
          if (value > 0xFFU) {
            fail("non-ASCII unicode escapes are not supported by ASCII JSON "
                 "runtime");
            return std::nullopt;
          }
          out.push_back(static_cast<char>(value));
          break;
        }
        default:
          fail("invalid escape character");
          return std::nullopt;
        }
      } else {
        if (static_cast<unsigned char>(ch) < 0x20U) {
          fail("control character in string");
          return std::nullopt;
        }
        out.push_back(ch);
      }
    }
    fail("unterminated string");
    return std::nullopt;
  }

  std::optional<std::string> parse_number_lexeme() {
    const std::size_t start = pos_;
    consume('-');

    if (consume('0')) {
      if (!eof() && std::isdigit(static_cast<unsigned char>(peek()))) {
        fail("leading zeros are not allowed");
        return std::nullopt;
      }
    } else {
      if (eof() || !std::isdigit(static_cast<unsigned char>(peek()))) {
        fail("invalid number");
        return std::nullopt;
      }
      while (!eof() && std::isdigit(static_cast<unsigned char>(peek()))) {
        ++pos_;
      }
    }

    if (consume('.')) {
      if (eof() || !std::isdigit(static_cast<unsigned char>(peek()))) {
        fail("invalid fractional number");
        return std::nullopt;
      }
      while (!eof() && std::isdigit(static_cast<unsigned char>(peek()))) {
        ++pos_;
      }
    }

    if (!eof() && (peek() == 'e' || peek() == 'E')) {
      ++pos_;
      if (!eof() && (peek() == '+' || peek() == '-')) {
        ++pos_;
      }
      if (eof() || !std::isdigit(static_cast<unsigned char>(peek()))) {
        fail("invalid exponent");
        return std::nullopt;
      }
      while (!eof() && std::isdigit(static_cast<unsigned char>(peek()))) {
        ++pos_;
      }
    }

    return input_.substr(start, pos_ - start);
  }

  std::shared_ptr<JSON::value> parse_array() {
    if (!consume('[')) {
      fail("expected '['");
      return nullptr;
    }
    skip_ws();
    std::vector<std::shared_ptr<JSON::value>> elems;
    if (consume(']')) {
      return JSON::value::ctor::JArr_(
          vector_to_list<std::shared_ptr<JSON::value>>(elems));
    }
    while (true) {
      skip_ws();
      auto elem = parse_value();
      if (!elem) {
        return nullptr;
      }
      elems.push_back(elem);
      skip_ws();
      if (consume(']')) {
        break;
      }
      if (!consume(',')) {
        fail("expected ',' or ']'");
        return nullptr;
      }
    }
    return JSON::value::ctor::JArr_(
        vector_to_list<std::shared_ptr<JSON::value>>(elems));
  }

  std::shared_ptr<JSON::value> parse_object() {
    if (!consume('{')) {
      fail("expected '{'");
      return nullptr;
    }
    skip_ws();
    std::vector<
        std::pair<std::shared_ptr<String::string>, std::shared_ptr<JSON::value>>>
        fields;
    if (consume('}')) {
      return JSON::value::ctor::JObject_(vector_to_list(fields));
    }
    while (true) {
      skip_ws();
      auto key = parse_string_literal();
      if (!key) {
        return nullptr;
      }
      skip_ws();
      if (!consume(':')) {
        fail("expected ':'");
        return nullptr;
      }
      skip_ws();
      auto val = parse_value();
      if (!val) {
        return nullptr;
      }
      fields.emplace_back(jpv::to_coq_string(*key), val);
      skip_ws();
      if (consume('}')) {
        break;
      }
      if (!consume(',')) {
        fail("expected ',' or '}'");
        return nullptr;
      }
    }
    return JSON::value::ctor::JObject_(vector_to_list(fields));
  }

  std::shared_ptr<JSON::value> parse_value() {
    skip_ws();
    if (has_error()) {
      return nullptr;
    }
    if (eof()) {
      fail("unexpected end of input");
      return nullptr;
    }
    const char ch = peek();
    if (ch == 'n') {
      if (input_.substr(pos_, 4) == "null") {
        pos_ += 4;
        return JSON::value::ctor::JNull_();
      }
      fail("invalid token");
      return nullptr;
    }
    if (ch == 't') {
      if (input_.substr(pos_, 4) == "true") {
        pos_ += 4;
        return JSON::value::ctor::JBool_(true);
      }
      fail("invalid token");
      return nullptr;
    }
    if (ch == 'f') {
      if (input_.substr(pos_, 5) == "false") {
        pos_ += 5;
        return JSON::value::ctor::JBool_(false);
      }
      fail("invalid token");
      return nullptr;
    }
    if (ch == '\"') {
      auto s = parse_string_literal();
      if (!s) {
        return nullptr;
      }
      return JSON::value::ctor::JStr_(jpv::to_coq_string(*s));
    }
    if (ch == '[') {
      return parse_array();
    }
    if (ch == '{') {
      return parse_object();
    }
    if (ch == '-' || std::isdigit(static_cast<unsigned char>(ch))) {
      auto lexeme = parse_number_lexeme();
      if (!lexeme) {
        return nullptr;
      }
      std::string parse_err;
      auto q = q_from_number_lexeme(*lexeme, parse_err);
      if (!q) {
        fail(parse_err);
        return nullptr;
      }
      return JSON::value::ctor::JNum_(*q);
    }
    fail("unexpected character");
    return nullptr;
  }
};

enum class SelKind { Name, Index, Wildcard };

struct SelectorData {
  SelKind kind = SelKind::Wildcard;
  std::string name;
  std::string index_lexeme;
};

struct SegmentData {
  bool desc = false;
  SelectorData selector;
};

class QueryParser {
public:
  explicit QueryParser(const std::string &input) : input_(input) {}

  jpv::QueryParseResult parse() {
    if (!consume('$')) {
      fail("query must start with '$'");
      return {.query = nullptr, .error = error_};
    }

    std::vector<SegmentData> segments;
    while (!eof()) {
      if (consume('.')) {
        bool desc = consume('.');
        if (desc) {
          fail("descendant operator '..' is currently unsupported in this CLI");
          break;
        }
        if (eof()) {
          fail("trailing '.'");
          break;
        }
        if (peek() == '[') {
          auto sel = parse_bracket_selector();
          if (!sel) {
            break;
          }
          segments.push_back(SegmentData{desc, *sel});
          continue;
        }
        if (consume('*')) {
          segments.push_back(
              SegmentData{desc, SelectorData{SelKind::Wildcard, "", ""}});
          continue;
        }
        auto name = parse_identifier();
        if (!name) {
          fail("expected identifier after '.'");
          break;
        }
        segments.push_back(
            SegmentData{desc, SelectorData{SelKind::Name, *name, ""}});
        continue;
      }

      if (peek() == '[') {
        auto sel = parse_bracket_selector();
        if (!sel) {
          break;
        }
        segments.push_back(SegmentData{false, *sel});
        continue;
      }

      fail("unexpected character in query");
      break;
    }

    if (!error_.empty()) {
      return {.query = nullptr, .error = error_};
    }

    std::vector<std::shared_ptr<JSONPath::segment>> coq_segments;
    for (const auto &seg : segments) {
      std::shared_ptr<JSONPath::selector> coq_sel;
      if (seg.selector.kind == SelKind::Wildcard) {
        coq_sel = JSONPath::selector::ctor::SelWildcard_();
      } else if (seg.selector.kind == SelKind::Name) {
        coq_sel =
            JSONPath::selector::ctor::SelName_(jpv::to_coq_string(seg.selector.name));
      } else {
        std::string z_err;
        auto z = z_from_integer_lexeme(seg.selector.index_lexeme, z_err);
        if (!z) {
          std::ostringstream out;
          out << "invalid index '" << seg.selector.index_lexeme
              << "': " << z_err;
          return {.query = nullptr, .error = out.str()};
        }
        coq_sel = JSONPath::selector::ctor::SelIndex_(*z);
      }

      std::vector<std::shared_ptr<JSONPath::selector>> one_sel{coq_sel};
      auto sels = vector_to_list(one_sel);
      if (seg.desc) {
        coq_segments.push_back(JSONPath::segment::ctor::Desc_(sels));
      } else {
        coq_segments.push_back(JSONPath::segment::ctor::Child_(sels));
      }
    }

    auto query = JSONPath::query::ctor::Query_(vector_to_list(coq_segments));
    return {.query = query, .error = ""};
  }

private:
  const std::string &input_;
  std::size_t pos_ = 0;
  std::string error_;

  bool eof() const { return pos_ >= input_.size(); }

  char peek() const { return eof() ? '\0' : input_[pos_]; }

  bool consume(char c) {
    if (!eof() && input_[pos_] == c) {
      ++pos_;
      return true;
    }
    return false;
  }

  void fail(const std::string &msg) {
    if (error_.empty()) {
      std::ostringstream out;
      out << msg << " at byte " << pos_;
      error_ = out.str();
    }
  }

  std::optional<std::string> parse_identifier() {
    if (eof()) {
      return std::nullopt;
    }
    auto is_ident_start = [](unsigned char c) {
      return std::isalpha(c) || c == '_';
    };
    auto is_ident_continue = [](unsigned char c) {
      return std::isalnum(c) || c == '_';
    };
    if (!is_ident_start(static_cast<unsigned char>(peek()))) {
      return std::nullopt;
    }
    std::size_t start = pos_;
    ++pos_;
    while (!eof() && is_ident_continue(static_cast<unsigned char>(peek()))) {
      ++pos_;
    }
    return input_.substr(start, pos_ - start);
  }

  std::optional<std::string> parse_quoted_name() {
    if (eof() || (peek() != '\'' && peek() != '\"')) {
      return std::nullopt;
    }
    const char quote = input_[pos_++];
    std::string out;
    while (!eof()) {
      const char ch = input_[pos_++];
      if (ch == quote) {
        return out;
      }
      if (ch == '\\') {
        if (eof()) {
          fail("unterminated string escape");
          return std::nullopt;
        }
        const char esc = input_[pos_++];
        switch (esc) {
        case '\\':
          out.push_back('\\');
          break;
        case '\'':
          out.push_back('\'');
          break;
        case '\"':
          out.push_back('\"');
          break;
        case 'n':
          out.push_back('\n');
          break;
        case 'r':
          out.push_back('\r');
          break;
        case 't':
          out.push_back('\t');
          break;
        default:
          out.push_back(esc);
          break;
        }
      } else {
        out.push_back(ch);
      }
    }
    fail("unterminated quoted selector");
    return std::nullopt;
  }

  std::optional<SelectorData> parse_bracket_selector() {
    if (!consume('[')) {
      fail("expected '['");
      return std::nullopt;
    }

    if (consume('*')) {
      if (!consume(']')) {
        fail("expected ']'");
        return std::nullopt;
      }
      return SelectorData{SelKind::Wildcard, "", ""};
    }

    if (!eof() && (peek() == '\'' || peek() == '\"')) {
      auto name = parse_quoted_name();
      if (!name) {
        return std::nullopt;
      }
      if (!consume(']')) {
        fail("expected ']'");
        return std::nullopt;
      }
      return SelectorData{SelKind::Name, *name, ""};
    }

    std::size_t start = pos_;
    if (!eof() && peek() == '-') {
      ++pos_;
    }
    if (eof() || !std::isdigit(static_cast<unsigned char>(peek()))) {
      fail("expected index, quoted name, or '*'");
      return std::nullopt;
    }
    while (!eof() && std::isdigit(static_cast<unsigned char>(peek()))) {
      ++pos_;
    }
    std::string index_lexeme = input_.substr(start, pos_ - start);
    if (!consume(']')) {
      fail("expected ']'");
      return std::nullopt;
    }
    return SelectorData{SelKind::Index, "", index_lexeme};
  }
};

std::string render_json_value(const std::shared_ptr<JSON::value> &v) {
  return std::visit(
      Overloaded{
          [](const JSON::value::JNull) -> std::string { return "null"; },
          [](const JSON::value::JBool b) -> std::string {
            return b._a0 ? "true" : "false";
          },
          [](const JSON::value::JNum n) -> std::string { return q_to_string(n._a0); },
          [](const JSON::value::JStr s) -> std::string {
            return std::string("\"") + json_escape(jpv::from_coq_string(s._a0)) +
                   "\"";
          },
          [](const JSON::value::JArr a) -> std::string {
            std::ostringstream out;
            out << "[";
            const auto elems = list_to_vector(a._a0);
            for (std::size_t i = 0; i < elems.size(); ++i) {
              if (i != 0U) {
                out << ",";
              }
              out << render_json_value(elems[i]);
            }
            out << "]";
            return out.str();
          },
          [](const JSON::value::JObject o) -> std::string {
            std::ostringstream out;
            out << "{";
            const auto fields = list_to_vector(o._a0);
            for (std::size_t i = 0; i < fields.size(); ++i) {
              if (i != 0U) {
                out << ",";
              }
              out << "\"" << json_escape(jpv::from_coq_string(fields[i].first))
                  << "\":" << render_json_value(fields[i].second);
            }
            out << "}";
            return out.str();
          }},
      v->v());
}

} // namespace

namespace jpv {

std::shared_ptr<String::string> to_coq_string(const std::string &s) {
  auto out = String::string::ctor::EmptyString_();
  for (auto it = s.rbegin(); it != s.rend(); ++it) {
    out = String::string::ctor::String_(
        to_coq_ascii(static_cast<unsigned char>(*it)), out);
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

QueryParseResult parse_query_text(const std::string &input) {
  QueryParser parser(input);
  return parser.parse();
}

JsonParseResult parse_json_text(const std::string &input) {
  JsonParser parser(input);
  return parser.parse();
}

std::vector<std::shared_ptr<JSON::value>> values_list_to_vector(
    const std::shared_ptr<List::list<std::shared_ptr<JSON::value>>> &xs) {
  return list_to_vector(xs);
}

std::string render_json(const std::shared_ptr<JSON::value> &v) {
  return render_json_value(v);
}

std::string exec_error_code(API::exec_error e) {
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

} // namespace jpv
