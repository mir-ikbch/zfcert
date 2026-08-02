val plan :
  (string * Syntax.formula) list ->
  Syntax.formula ->
  (Zfcert_kernel.certificate_step list, string) result
