#include "jsonpath_bridge.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

namespace {

struct CliOptions {
  std::string query;
  std::string json_text;
};

void print_usage() {
  std::cerr
      << "Usage:\n"
      << "  jsonpath_cli --query <JSONPath> --json <JSON text>\n"
      << "  jsonpath_cli --query <JSONPath> --json-file <path>\n\n"
      << "Notes:\n"
      << "  - Query parser adapter currently supports common child/name/index/"
         "wildcard forms.\n"
      << "  - Result is printed as a JSON array of matched values.\n";
}

bool parse_args(int argc, char **argv, CliOptions &opts, std::string &err) {
  bool saw_query = false;
  bool saw_json = false;
  bool saw_json_file = false;

  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--help" || arg == "-h") {
      err.clear();
      return false;
    }
    if (arg == "--query") {
      if (i + 1 >= argc) {
        err = "missing value for --query";
        return false;
      }
      opts.query = argv[++i];
      saw_query = true;
      continue;
    }
    if (arg == "--json") {
      if (i + 1 >= argc) {
        err = "missing value for --json";
        return false;
      }
      opts.json_text = argv[++i];
      saw_json = true;
      continue;
    }
    if (arg == "--json-file") {
      if (i + 1 >= argc) {
        err = "missing value for --json-file";
        return false;
      }
      const std::string path = argv[++i];
      std::ifstream in(path, std::ios::binary);
      if (!in) {
        err = "unable to open JSON file: " + path;
        return false;
      }
      std::ostringstream buf;
      buf << in.rdbuf();
      opts.json_text = buf.str();
      saw_json_file = true;
      continue;
    }
    err = "unknown argument: " + arg;
    return false;
  }

  if (!saw_query) {
    err = "missing --query";
    return false;
  }
  if (saw_json == saw_json_file) {
    err = "provide exactly one of --json or --json-file";
    return false;
  }
  return true;
}

} // namespace

int main(int argc, char **argv) {
  CliOptions opts;
  std::string arg_err;
  if (!parse_args(argc, argv, opts, arg_err)) {
    print_usage();
    if (!arg_err.empty()) {
      std::cerr << "error: " << arg_err << "\n";
      return 2;
    }
    return 0;
  }

  const auto q = jpv::parse_query_text(opts.query);
  if (!q.query) {
    std::cerr << "query parse error: " << q.error << "\n";
    return 3;
  }

  const auto j = jpv::parse_json_text(opts.json_text);
  if (!j.value) {
    std::cerr << "json parse error: " << j.error << "\n";
    return 4;
  }

  auto result = API::eval_checked(q.query, j.value);
  std::shared_ptr<List::list<JSON::node>> nodes;
  std::string eval_error;
  bool ok = false;
  std::visit(
      Overloaded{
          [&](const API::result<std::shared_ptr<List::list<JSON::node>>,
                                API::exec_error>::Ok x) {
            nodes = x._a0;
            ok = true;
          },
          [&](const API::result<std::shared_ptr<List::list<JSON::node>>,
                                API::exec_error>::Error x) {
            eval_error = jpv::exec_error_code(x._a0);
            ok = false;
          }},
      result->v());

  if (!ok) {
    std::cerr << "evaluation error: " << eval_error << "\n";
    return 5;
  }

  const auto values = API::values_of(nodes);
  const auto vec = jpv::values_list_to_vector(values);

  std::cout << "[";
  for (std::size_t i = 0; i < vec.size(); ++i) {
    if (i != 0U) {
      std::cout << ",";
    }
    std::cout << jpv::render_json(vec[i]);
  }
  std::cout << "]\n";
  return 0;
}
