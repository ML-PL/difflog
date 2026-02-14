# Difflog: Differentiable Datalog for Rule Synthesis

This repository contains the implementation of the Difflog differentiable Datalog system. This includes an evaluator for Difflog programs and a system to learn classical Datalog programs from input-output data.

This forms the code and benchmark data for our IJCAI 2019 paper titled "Synthesizing Datalog Programs Using Numerical Relaxation."

## Original Scala Implementation

### How to compile, build, and run Difflog (Scala)

1. Install sbt. We recommend a version >= 1.1.1.

2. Run the command `sbt compile`.

3. To use Difflog to synthesize Datalog programs, invoke `sbt` and issue the following commands at the ensuing prompt:

   ```
   sbt> run alps src/test/resources/ALPS/data/path.d src/test/resources/ALPS/templates/path.tp HybridAnnealingLearner NaiveEvaluator L2Scorer 0.01 1000
   ```

   The system will momentarily print logging information and the final synthesized program and associated metrics.

3. In general, the synthesis command is of the form:

   ```
   run alps data.d templates.tp learnerName evaluatorName scorerName targetLoss numIters
   ```

   For the learner, evaluator, scorer, target loss and number of iterations, we recommend the values
   `HybridAnnealingLearner`, `NaiveEvaluator`, `L2Scorer`, `0.01` and `1000` respectively.

   Several data.d and templates.tp files can be found in the `src/test/resources/ALPS` directory. The user is encouraged to create new benchmarks patterned on these files.

---

## OCaml Reimplementation (`ocaml_src/`)

### Motivation

The original Scala implementation served us well, but for a potential reimplementation we considered alternatives. OCaml was chosen as the sweet spot between Scala, Rust, and OCaml for this particular problem domain:

- **Algebraic data types and pattern matching** map directly to the core abstractions (lineage trees, parameter types, trie instances) without the boilerplate of sealed traits + case classes
- **Module system with functors** cleanly replaces Scala's F-bounded polymorphism (`Value[T <: Value[T]]`) for parameterizing over semirings
- **Immutable-by-default** with efficient persistent data structures via `Map.Make`/`Set.Make` (balanced BSTs, O(log n) operations)
- **Predictable performance** without JVM warm-up, GC pauses, or boxing overhead on numeric types
- **Minimal dependencies** — the entire implementation uses only the OCaml standard library

### Architecture

The OCaml source is organized into 11 modules with a clear dependency DAG:

```
base.ml           Core types: domain, constant, variable, parameter,
                  relation, literal, lineage, rule. Comparison functions,
                  Map/Set module instantiations, normalization.

lineage.ml        Lineage operations: multiplication (And with Empty
                  normalization), flattening (to_list), token set/multiset
                  extraction. TokenSet and TokenMap modules.

value.ml          SEMIRING module type (zero, one, plus, times, leq, gt,
                  nonzero). FValue: Viterbi semiring — plus = max,
                  times = product, carries lineage provenance.
                  eval_lineage: evaluate lineage tree under weight assignment.

token_vec.ml      Token weight vector: Map from token names to float weights
                  in [0,1]. Arithmetic (add, sub, scale), norms, clipping,
                  conversion to FValue position function.

instance.ml       Trie-based instance storage: 'v instance = Base of 'v
                  | Ind of domain * domain list * ('v instance ConstantMap.t).
                  Config = instance RelationMap.t. Assignment type for
                  variable bindings during rule evaluation.

evaluator.ml      Fixed-point Datalog evaluators:
                  - NaiveEvaluator: re-scans all rules each epoch
                  - SeminaiveEvaluator: delta tracking, only processes
                    newly derived facts

scorer.ml         Loss functions and gradient computation:
                  - Gradient formula: dv(t)/dw_i = freq(w_i in lineage) * v(t) / w_i
                  - L2 (squared Euclidean), L1 (Manhattan), XEntropy scorers
                  - Total loss and gradient aggregation over output relations

learner.ml        Learning algorithms:
                  - State: {pos, c_out, grad, loss}
                  - NewtonRootLearner: gradient descent with
                    delta = grad.unit * loss / |grad|, clip to [0,1]
                  - HybridAnnealingLearner: alternates gradient descent
                    (29/30 steps) with MCMC simulated annealing (1/30 steps)
                  - Helper functions: forbidden token detection, solution
                    point simplification, reinterpret (weight sharpening)

problem.ml        Problem specification: input/invented/output relations,
                  discrete EDB/IDB, token weights, candidate rules.
                  Immutable functional updates. EDB/IDB to FValue config
                  conversion.

alps_parser.ml    ALPS format parser: reads .d (data) and .tp (template)
                  files. Domain declarations, relation signatures, tuple
                  listings, meta-variable instantiation for rule generation.

main.ml           CLI entry point: dispatches to alps (learn) or eval mode.
                  Reads files, selects evaluator/learner/scorer, runs
                  learning, prints weighted rules.
```

### Dependency Graph

```
base  ←── lineage  ←── value  ←── token_vec
  ↑                       ↑           ↑
  └───── instance ────────┘           │
              ↑                       │
         evaluator ←──── scorer ──────┘
              ↑              ↑
          learner ───────────┘
              ↑
          problem ←── alps_parser ←── main
```

### Building

Prerequisites: OCaml >= 4.14.0 and dune >= 3.0.

```bash
# Install OCaml (if needed)
# Via opam:
opam install ocaml.4.14.0
eval $(opam env)

# Build
cd ocaml_src
dune build

# Run
dune exec difflog -- alps ../src/test/resources/ALPS/data/path.d \
                          ../src/test/resources/ALPS/templates/path.tp \
                          HybridAnnealingLearner SeminaiveEvaluator L2Scorer 0.01 1000
```

### Usage

```
difflog alps <data.d> <templates.tp> <learner> <evaluator> <scorer> <tgtLoss> <maxIters>
```

Available options:

| Component | Options |
|-----------|---------|
| Learner   | `NewtonRootLearner`, `HybridAnnealingLearner` |
| Evaluator | `NaiveEvaluator`, `SeminaiveEvaluator` |
| Scorer    | `L2Scorer`, `L1Scorer`, `XEntropyScorer` |

### Key Design Decisions (Scala → OCaml)

| Scala Pattern | OCaml Equivalent |
|---------------|-----------------|
| `sealed trait` + `case class` | Algebraic data types (`type t = A \| B of ...`) |
| `Value[T <: Value[T]]` (F-bounded) | `SEMIRING` module type + functors |
| `implicit Semiring[T]` | Explicit `~zero`, `~plus`, `~gt` parameters |
| `Map[K, V]` (Scala collections) | `Map.Make(Ord)` (OCaml stdlib) |
| `Set[T]` (Scala collections) | `Set.Make(Ord)` (OCaml stdlib) |
| Mutable `var` in loops | `ref` cells for imperative loops |
| `case class` copy | Functional record update `{ p with field = ... }` |
| `for`-comprehension | `List.concat_map`, `List.filter_map` |
| Package hierarchy | Flat module files with `open` |

### Known Issues / TODO

The current OCaml code was written as a faithful port but has not yet been compiled or tested. Known items to address:

1. **Cross-module type consistency**: The files were partially written in parallel, so some module path references (e.g., `Lineage.ConstantMap` vs `Base.ConstantMap`) may need harmonization. The canonical locations are: types and Ord/Map/Set modules in `base.ml`, token-specific modules in `lineage.ml`.

2. **FValue module sealing**: In `value.ml`, `FValue` is sealed as `: SEMIRING`, which hides the record fields `v` and `l` and the `make` constructor. Other modules access these fields directly. Fix: either remove the `: SEMIRING` annotation or use a more permissive signature that exposes the internal type.

3. **Evaluator module references**: `evaluator.ml` defines its own `VariableSet` and references `Instance.VarMap`, `Instance.assignment`, etc. These need to be aligned with the actual types in `instance.ml` and `base.ml`.

4. **TrieEvaluator**: Not yet ported (the Scala version uses `RuleTrie` for shared-prefix evaluation). The naive and semi-naive evaluators cover the core functionality.

5. **Stochastic learner / derivation graphs**: The `alps-2` mode from the Scala version (stochastic sampling of derivation graphs) is not yet implemented.

6. **Testing**: No test suite yet. The first validation step should be running the `path` benchmark and comparing output with the Scala version.

### Benchmarks

The ALPS benchmarks from the original Scala project can be used directly:

```
src/test/resources/ALPS/data/       — .d data files
src/test/resources/ALPS/templates/  — .tp template files
```

Available benchmarks include: `path`, `ancestor`, `evenodd`, `scc`, `buildwall`, and others.
