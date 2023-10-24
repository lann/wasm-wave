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

char ::= ['] char-inner [']
char-char ::= common-char | '"'
string ::= '"' string-inner* '"'
string-char ::= common-char | [']
common-char ::= <any Unicode Scalar Value except ['"\]>
              | '\' escape
escape ::= ['"tnr\] | escape-unicode
escape-unicode ::= 'u{' [0-9a-fA-F]+ '}'

variant-case ::= label case-payload?
variant-case-payload ::= '(' value-ws ')'

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

* "`Unicode scalar value`" is defined by Unicode
* "`Unicode WS`" is any Unicode character with property `White_Space=yes`
* `escape-unicode` must identify a valid Unicode scalar value.
