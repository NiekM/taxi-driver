# Taxi-Driver

This package accompanies the PEPM '26 paper 
["Hole Refinements for Polymorphic Type-and-Example Driven Synthesis"](https://doi.org/10.1145/3779209.3779535).

It implements two components: Taxi and Driver:
- Taxi can analyze specifications (types and examples) to figure out if they are feasible. In addition, Taxi can recognize when a specification is total, i.e. it covers all possible cases.
- Driver is a tactics-based synthesizer that propagates constraints in a top-down fashion, and uses Taxi to prune the search space and shortcut the search whenever the specification is total.
