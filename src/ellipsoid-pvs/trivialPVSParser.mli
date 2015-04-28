type token =
  | COMMENT of (string)
  | DEF of (string)
  | IMPORTING of (string)
  | HEADER
  | FOOTER
  | EOF

val theory :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> TrivialPVS.theory
