# Order closure, order adherence and Fatou norms

[![Lean CI](https://github.com/pedrotradacete/OrderClosures/actions/workflows/lean.yml/badge.svg)](https://github.com/pedrotradacete/OrderClosures/actions/workflows/lean.yml)

This repository contains the Lean 4 formalization accompanying the paper
*Order closure, order adherence and Fatou norms* by A. Avilés, M. A. Taylor,
and P. Tradacete. A copy of the manuscript is available as
[`paper.pdf`](paper.pdf), and [`FORMALIZATION.md`](FORMALIZATION.md) gives a
detailed correspondence between the paper and the Lean development.

The formalization is built on
[Mathlib](https://github.com/leanprover-community/mathlib4) and
[BanLat](https://github.com/davidmunozlahoz/banlat), a Lean library for vector
and Banach lattices. The exact dependency revisions are recorded in
[`lake-manifest.json`](lake-manifest.json).

## Main results

The repository formalizes:

- the Gao--Leung characterization of order-continuous Banach lattice norms;
- counterexamples concerning order and unbounded-order adherence, including
  solid sets requiring arbitrarily many adherence iterations; and
- a weakly Fatou Banach lattice norm that is not equivalent to any Fatou
  lattice norm.

All declarations in the project have checked proofs; the Lean sources contain
no `sorry` or `admit` placeholders.

## Building

Install [elan](https://github.com/leanprover/elan), clone this repository, and
run from its root:

```bash
lake exe cache get
lake build
```

The first command downloads available precompiled Mathlib artifacts. If the
cache downloader is unavailable on a platform, `lake build` builds the
dependencies from source.

## Formalization layout

- [`OrderClosures/OrderAdherence.lean`](OrderClosures/OrderAdherence.lean):
  shared definitions and general lemmas about order adherence, solidity, and
  the norm properties used throughout the project.
- [`OrderClosures/GaoLeungCharacterization.lean`](OrderClosures/GaoLeungCharacterization.lean):
  formalization of Gao--Leung Theorem 2.7, characterizing order-continuous
  Banach lattice norms through order and unbounded-order adherence of
  sublattices.
- [`OrderClosures/Solovay.lean`](OrderClosures/Solovay.lean): Solovay's
  complete Boolean-algebra construction, its realization by a Stone space,
  and the analytic ingredients used to obtain the Gao--Leung counterexample.
- [`OrderClosures/GaoLeungProblem.lean`](OrderClosures/GaoLeungProblem.lean):
  umbrella module for the Gao--Leung development. Its paper-ordered
  implementation is split into `Counterexample`, `CNFOrder`, `OrdinalSpace`,
  `StageFormula`, and `Iterations` under `OrderClosures/GaoLeungProblem/`.
- [`OrderClosures/WeaklyFatou.lean`](OrderClosures/WeaklyFatou.lean):
  umbrella module for the weakly Fatou construction. Its paper-ordered
  implementation is split into `Reductions`, `FiniteTree`, `TreeNorm`,
  `Bands`, `Moderated`, and `FinalSpace` under
  `OrderClosures/WeaklyFatou/`.
- [`OrderClosures.lean`](OrderClosures.lean): the root import for the complete
  development.

## Citation

If you use this formalization, please cite both the accompanying paper and the
software. Machine-readable citation metadata is provided in
[`CITATION.cff`](CITATION.cff); the DOI and arXiv identifier will be added when
they become available.

## License

The Lean source code and project configuration are licensed under the
[Apache License 2.0](LICENSE). The included [`paper.pdf`](paper.pdf) is not
covered by this software license and retains its authors' copyright.
