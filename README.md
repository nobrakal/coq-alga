# coq-alga

This repository contains some theory about [algebraic graphs](https://github.com/snowleopard/alga-paper) and prove a few theorems about homomorphisms in Coq.

The files in the `src/` directory are organized as follow:

* `Graph.v` is containing basic definitions, axioms and tools to use them with Coq.
* `Homomorphism.v` is giving a definition and prove some theorems about structural homomorphism.
* `ReducedHomo.v` is giving a definition and prove some theorems about a kind of homomorphism, preserving a graph equality relation.
* `SmartHomo.v`  is giving a definition and prove some theorems about a kind of reduced homomorphism.

A more precise analysis of these results is given at <https://blog.nyarlathotep.one/2018/12/algebraic-graphs-homomorphisms/>.
