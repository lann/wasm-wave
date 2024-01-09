# WAVE EBNF

A WAVE value is defined by the `value` rule below. Many applications may allow
whitespace around the value, equivalent to the `value-ws` rule.

> Note that Bool, Variant, Enum, Option and Result values are combined under
> the `variant-case` rule because these cannot be distinguished without type
> information.

```ebnf
value ::= number
        | char
        | string
        | variant-case
        | tuple
        | list
        | flags
        | record

value-ws ::= ws value ws
ws ::= <Unicode whitespace>*

number ::= number_finite
         | 'nan'
         | 'inf'
         | '-inf'
number_finite ::= integer number-fraction? number-exponent?
integer ::= unsigned-integer
          | '-' unsigned-integer
unsigned-integer ::= '0'
                   | [1-9] [0-9]*
number-fraction ::= '.' [0-9]+
number-exponent ::= [eE] [+-]? unsigned-integer

char ::= ['] char-char [']
char-char ::= common-char | '"'

string ::= '"' string-char* '"'
string-char ::= common-char | [']

common-char ::= <any Unicode Scalar Value except ['"\]>
              | '\' escape
escape ::= ['"tnr\] | escape-unicode
escape-unicode ::= 'u{' [0-9a-fA-F]+ '}'

variant-case ::= label variant-case-payload?
variant-case-payload ::= '(' value-ws ')'

tuple ::= '(' values-seq ','? ')'

list ::= '[' ws ']'
       | '[' values-seq ','? ']'

values-seq ::= value-ws
             | values ',' values-ws

flags ::= '{' ws '}'
        | '{' flags-seq ','? '}'
flags-seq ::= ws label ws
            | flags-seq ',' label

record ::= '{' record-fields ','? '}'
record-fields ::= ws record-field ws
                | record-fields ',' record-field
record-field ::= label ws ':' ws value

label ::= '%'? inner-label
inner-label ::= word
              | inner-label '-' word
word ::= [a-z][a-z0-9]*
       | [A-Z][A-Z0-9]*
```

* "`Unicode scalar value`" is defined by Unicode
* "`Unicode whitespace`" is any Unicode character with property `White_Space=yes`
* `escape-unicode` must identify a valid Unicode scalar value.
