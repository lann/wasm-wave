# WAVE EBNF

A WAVE value is defined by the `value` rule below. Many applications will allow
whitespace around the value, equivalent to the `value-ws` rule.

```ebnf
value ::= bool
        | int
        | float
        | char
        | string
        | case
        | tuple
        | list
        | flags
        | record

bool ::= 'true'
       | 'false'

int ::= uint
      | '-' uint
uint ::= '0'
       | [1-9] [0-9]*

float ::= float_finite
        | 'nan'
        | 'inf'
        | '-inf'
float_finite ::= int float_decimal? float_exponent?
float_decimal ::= '.' [0-9]+
float_exponent ::= [eE] [+-]? uint

char ::= ['] char-inner [']
char-char ::= common-char | '"'
string ::= '"' string-inner* '"'
string-char ::= common-char | [']
common-char ::= <UTF-8-encoded Unicode Scalar Value except ['"\]>
              | '\' escape
escape ::= ['"tnr\] | escape-unicode
// escape-unicode must identify a valid Unicode scalar value
escape-unicode ::= 'u{' hex-digit+ '}'
hex-digit ::= [0-9a-fA-F]

case ::= label case-payload?
case-payload ::= '(' value-ws ')'

tuple ::= '(' values-seq ','? ')'

list ::= '[' values-seq ','? ']'

flags ::= '{' flags-seq ','? '}'
flags-seq ::= ws label ws
            | flags-seq ',' label

record ::= '{' record-fields ','? '}'
record-fields ::= ws record-field ws
                | record-fields ',' record-field
record-field ::= label ws ':' ws value

values-seq ::= value-ws
             | values ',' values-ws
value-ws ::= ws value ws
ws ::= <Unicode WS>*


label ::= word
       | label '-' word
word ::= [a-z][a-z0-9]*
       | [A-Z][A-Z0-9]*
```

* "`Unicode scalar value`" and "`UTF-8`" are as defined by Unicode
* "`Unicode WS`" is any Unicode character with property `White_Space=yes`
