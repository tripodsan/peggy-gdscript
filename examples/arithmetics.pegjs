// Simple Arithmetics Grammar
// ==========================
//
// Accepts expressions like "2 * (3 + 4)" and computes their value.
{{
# ---- globals
const TEST = 42
}}
Expression
  = head:Term tail:(_ ("+" / "-") _ Term)* {
      return tail.reduce(func (result, element):
        if element[1] == "+": return result + element[3]
        if element[1] == "-": return result - element[3]
      , head);
    }

Term
  = head:Factor tail:(_ ("*" / "/") _ Factor)* {
      return tail.reduce(func (result, element):
        if element[1] == "*": return result * element[3]
        if element[1] == "/": return result / element[3]
      , head);
    }

Factor
  = "(" _ @Expression _ ")"
  / Integer

Integer "integer"
  = _ [0-9]+ { return text().to_int() }

_ "whitespace"
  = [ \t\n\r]*
