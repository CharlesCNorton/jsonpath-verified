Require Import JPV_Core JPV_Formalization JPV_Extensions JPV_API_Extraction.
Require Crane.Extraction.
Require Crane.Mapping.Std.

Crane Extraction "cpp/gen/jsonpath_api"
  API.parse_query_string
  API.parse_query_string_opt
  API.parse_query_error_kind_opt
  API.parse_query_error_pos_opt
  API.parse_query_error_code_opt
  API.show_parse_error_kind
  API.eval_checked
  API.eval_nf_checked
  API.eval_one_linear
  API.values_of
  API.paths_of.
