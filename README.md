# Abstract Interpretation

An implementation of [abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation),
a static analysis method which can be used to prove certain properties of a
program by performing an interpretation of the program over an abstract domain.

### Example

The following is an example of abstract interpretation of a program over the
sign domain, which shows that division-by-0 will not occur.

```
x := input()
{ "x" -> ST }
if x > 0 then
    { "x" -> SP }
    x := x * -2
    { "x" -> SN }
else
    { "x" -> SNZ }
    if x < 0 then
        { "x" -> SN }
        x := x * -5
        { "x" -> SP }
    else
        { "x" -> SZ }
        x := x + 1
        { "x" -> SP }
    end
    { "x" -> SP }
end
{ "x" -> SNP }
y := 1 / x
{ "y" -> SNP ; "x" -> SNP }
```

### Features

First, we need the following:
- [x] AST
- [x] concrete interpreter
- [ ] type-checking

Some abstract domains it would be useful to support:
- [x] sign
- [ ] parity
- [ ] intervals

Other desirable features:
- [ ] statically-checked inline annotations
- [ ] lexer and parser
