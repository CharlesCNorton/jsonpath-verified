Require Import JPV_Core JPV_Formalization JPV_Extensions JPV_API_Extraction.
Require Crane.Extraction.
Require Crane.Mapping.Std.

Crane Extraction "demo/crane-cli/gen/jsonpath_api"
  API.eval_checked
  API.values_of.
