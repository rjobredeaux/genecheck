%{
  open TrivialPVS

%}


%token <string> COMMENT
%token <string> DEF
%token <string> IMPORTING
%token HEADER FOOTER EOF

%start theory
%type <TrivialPVS.theory> theory

%%

theory:
HEADER preamble comments defs FOOTER EOF { let defs, thm = $4 in $2, defs, thm }

preamble: 
IMPORTING { [$1] }
| IMPORTING preamble { $1::$2}  

comments:
COMMENT {[$1]}
| COMMENT comments {$1::$2}

defs:
DEF { [], $1 }
| DEF defs { let defs, thm = $2 in $1::defs, thm }
