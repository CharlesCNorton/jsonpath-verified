#pragma once

#include <memory>
#include <string>
#include <vector>

#include "jsonpath_api.h"

namespace jpv {

struct QueryParseResult {
  std::shared_ptr<JSONPath::query> query;
  std::string error;
};

struct JsonParseResult {
  std::shared_ptr<JSON::value> value;
  std::string error;
};

std::shared_ptr<String::string> to_coq_string(const std::string &s);
std::string from_coq_string(const std::shared_ptr<String::string> &s);

QueryParseResult parse_query_text(const std::string &input);
JsonParseResult parse_json_text(const std::string &input);

std::vector<std::shared_ptr<JSON::value>> values_list_to_vector(
    const std::shared_ptr<List::list<std::shared_ptr<JSON::value>>> &xs);

std::string render_json(const std::shared_ptr<JSON::value> &v);
std::string exec_error_code(API::exec_error e);

} // namespace jpv
