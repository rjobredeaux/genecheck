{
  open TrivialPVSParser
  exception UnexpectedToken

}


let newline = ('\010' | '\013' | "\013\010")
let notnewline = [^ '\010' '\013']
let blank = [' ' '\009' '\012']

rule token = parse
  | blank { token lexbuf }
  | newline { token lexbuf }
  | "WP" blank* ":" blank* "THEORY" newline blank* "BEGIN" { HEADER }
  | "IMPORTING" blank* 
      ( (['_' 'A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '@' '_' '0'-'9']* ) as id ) 
      blank* newline 
      { IMPORTING id}
  | (("% " "Why3" (notnewline | newline blank blank notnewline)+) as s) { DEF s }
  | ("% " ([^'W'][^ '\n']+) as s) newline { COMMENT s}
  | "END WP" { FOOTER } 
  | eof { EOF }
  | _ { raise UnexpectedToken }
{

}
