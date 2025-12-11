# Taxi-Driver

This code accompanies the PEPM '26 paper "Hole Refinements for Polymorphic Type-and-Example Driven Synthesis".

Tested with `ghc` version `9.10.1`.

## Instructions

To run the test suite or benchmarks, simply run `cabal test` and `cabal bench` respectively.

The easiest way to synthesize programs using your own tactics and inspecting the results is using GHCi.
Run `cabal repl taxi-driver` to open GHCi.
Run `:load Interactive` to bring all relevant functions as well as the benchmarks in scope.
Now you can try out synthesis using the `synthesize` function and `pretty`-print the results.

Example usage:
```
>>> pretty $ synthesize def { tactic = auto } "unzip"
\xs. (map (\x0. x0.0) xs, map (\x3. x3.1) xs)
(0.25 secs, 365,605,128 bytes)
```
