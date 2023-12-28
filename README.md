
# project

This repository contains an interpreter for a subset of OCaml.

## Extensions:
### Binop operations to allow further operations

1.1 Division - using the ”/” symbol, we can now divide two Nums (and made
sure that division by zero raises an error).
1.2 Modulo - using the ”%” symbol, we can now find the modulo of two Nums
(and made sure that modulo when the second Num is zero raises an error).
1.3 GreaterThan - using the ”>” symbol, we can now check if the first Num is
greater than the second Num.

### Lexical scoped evaluator

2.1 The lexical scoped evaluator differs from the dynamic scoped evaluator be-
cause it evaluates the variables and retain their values in the environment in
which they were originally defined. As a result, I needed to use closures in order
to keep the environment in which the variables are defined.
2.2 Both Dynamic and Lexical scope evaluators differ from the substitution eval-
uator because they do lazy evaluation, meaning that they substitute only when
the value of the variable is needed. In the substitution evaluator we substitute
every time we encounter a variable.
2.3 The pros of Lexical evaluation are that early binding meaning we can trace
it more easily, which makes it easier to read. However, a con is that variable
lookup might be inefficient when we have many nested functions.
2.4 The pros of Dynamic evaluation are that late binding results in more flex-
ibility. Waiting until runtime allows to change local variables without passing
them as parameters. Also, it is easier to write. However, the cons of Dynamic
evaluation is that it is harder to trace.
2.5 As a result, the lexical evaluator evaluates some expressions differently than
the dynamic evaluator. We can see in the unit test file, named evaltest, that I
tested at the end of the file the same expression but expected different results
when I used evald and evals.
