# Abstract Interpretation

An implementation of [abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation),
a static analysis method which can be used to prove certain properties of a
program by interpreting the program over an abstract domain. Abstract
interpretation computes an over-approximation of the states any concrete
execution of the program may reach.

### Example

Given the following program, we are interested in showing that a division-by-0
will not occur:

```
x := input();
if x > 0 then
    x := x * -2;
else
    if x < 0 then
        x := x * -5;
    else
        x := x + 1;
    end
end
invariant !(x = 0);
y := 1 / x;
```

Below is the abstract interpretation of the program over the sign domain:

```
x := input();
{ "x" -> ST }
if x > 0 then
    { "x" -> SP }
    x := x * -2;
    { "x" -> SN }
else
    { "x" -> SNZ }
    if x < 0 then
        { "x" -> SN }
        x := x * -5;
        { "x" -> SP }
    else
        { "x" -> SZ }
        x := x + 1;
        { "x" -> SP }
    end
    { "x" -> SP }
end
{ "x" -> SNP }
invariant !(x = 0);
{ "x" -> SNP }
y := 1 / x;
{ "y" -> SNP ; "x" -> SNP }
```

The invariant above passes, proving that x is nonzero before the division
is performed.

Note that this domain is not always completely precise. Consider the following
program, equivalent to the program above:

```
x := input();
if x > 0 then
    a := x * 3;
    x := x - a;
else
    if x < 0 then
        b := x * 6;
        x := x - b;
    else
        x := 1;
    end
end
invariant !(x = 0);
y := 1 / x;
```

The analysis fails to prove the invariant with this program:

```
x := input();
{ "x" -> ST }
if x > 0 then
    { "x" -> SP }
    a := x * 3;
    { "a" -> SP ; "x" -> SP }
    x := x - a;
    { "x" -> ST ; "a" -> SP }
else
    { "x" -> SNZ }
    if x < 0 then
        { "x" -> SN }
        b := x * 6;
        { "b" -> SN ; "x" -> SN }
        x := x - b;
        { "x" -> ST ; "b" -> SN }
    else
        { "x" -> SZ }
        x := 1;
        { "x" -> SP }
    end
    { "x" -> ST }
end
{ "x" -> ST }

invariant !(x = 0);
ERROR: unsatisfied invariant:
requires: "x" -> SNP
found:    "x" -> ST

y := 1 / x;
{ "y" -> SB ; "x" -> ST }
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
- [X] statically-checked invariant annotations
- [ ] lexer and parser

### Development

To build an executable with [GHC](https://www.haskell.org/ghc/):

```sh
$ ghc main.hs
$ ./main
```

To load the program up in [GHCi](https://wiki.haskell.org/GHC/GHCi):

```sh
$ ghci main.hs
```

To run the abstract interpretation examples and concrete interpreter,
respectively:

```sh
ghci> abstractMain
ghci> concreteMain
```
