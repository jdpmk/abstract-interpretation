# Abstract Interpretation

An implementation of [abstract interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation),
a static analysis method which can be used to prove certain properties of a
program by interpreting the program over an abstract domain. Abstract
interpretation computes an over-approximation of the states any concrete
execution of the program may reach.

### Theory

More formally, given:
- lattices $C$, $\subseteq_C$ and $A$, $\subseteq_A$, representing the
  concrete and abstract domain, respectively
- abstraction function $\alpha : C \to A$, and concretization function
  $\gamma : A \to C$, where $\alpha, \gamma$ are monotonic

we have a [Galois connection](https://en.wikipedia.org/wiki/Galois_connection),
if

$\forall a \in A, c \in C. \alpha(c) \subseteq_A a \iff c \subseteq_C \gamma(a)$

which means $\alpha(c)$ is the most precise approximation of concrete value
$c \in C$ and $\gamma(a)$ is the least precise concrete element which can be
correctly approximated by abstract value $a \in A$.

See [this diagram](https://github.com/jdpmk/abstract-interpretation/blob/master/resources/galois.gif)
for a visualization.

References:
- [Introduction to Abstract Interpretation, Bruno Blanchet](https://bblanche.gitlabpages.inria.fr/absint.pdf)
- [Abstract Interpretation, Susan B. Horwitz](https://pages.cs.wisc.edu/~horwitz/CS704-NOTES/10.ABSTRACT-INTERPRETATION.html)

### Example

Given the following program, we are interested in showing that a division-by-0
will not occur. This is encoded by the invariant, which is statically checked
before runtime.

```
x := input();
if x > 0 then
    x := x * -4;
else
    if x < 0 then
        x := x * -8;
    else
        x := x + 1;
    end
end
invariant !(x = 0);
y := 1 / x;
```

We can use the sign abstract domain (see [sign.hs](https://github.com/jdpmk/abstract-interpretation/blob/master/sign.hs))
to prove this. This domain is the powerset of the signs, $\mathcal{P}(\\{ -, 0, + \\})$:
- `-/0/+` (`ST`, or "Top", $\top$, representing any integer)
- `0/+`   (`SZP`)
- `-/+`   (`SNP`)
- `-/0`   (`SNZ`)
- `+`     (`SP`)
- `0`     (`SZ`)
- `-`     (`SN`)
- `?`     (`SB`, or "Bottom", $\bot$, representing an error state)

See [this diagram](https://github.com/jdpmk/abstract-interpretation/blob/master/resources/sign.png)
for a visualization.

By showing this domain is a partial order and lattice, and implementing
functions for interpreting expressions and statements of the language, we can
execute this program over this domain:

```
x := input();
{ "x" -> ST }
if x > 0 then
    { "x" -> SP }
    x := x * -4;
    { "x" -> SN }
else
    { "x" -> SNZ }
    if x < 0 then
        { "x" -> SN }
        x := x * -8;
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

Note that this domain cannot always be 100% precise. Consider the following
program, equivalent to the program above:

```
x := input();
if x > 0 then
    a := x * 5;
    x := x - a;
else
    if x < 0 then
        b := x * 9;
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
    a := x * 5;
    { "a" -> SP ; "x" -> SP }
    x := x - a;
    { "x" -> ST ; "a" -> SP }
else
    { "x" -> SNZ }
    if x < 0 then
        { "x" -> SN }
        b := x * 9;
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
