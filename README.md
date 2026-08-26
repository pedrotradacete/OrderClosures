# OrderClosures

Lean formalization of *Order closure, order adherence and weakly Fatou norms* by
A. Avilés, M. A. Taylor, and P. Tradacete. The mathematical source is in
[`paper.tex`](paper.tex), with bibliography in [`refs.bib`](refs.bib).

The project is built on [Mathlib](https://github.com/leanprover-community/mathlib4) and
[BanLat](https://github.com/davidmunozlahoz/banlat), a Lean library for vector and
Banach lattices. BanLat is pinned to commit
`b00e59836016aa1099b8011add6b07385e66428e`, which uses Lean and Mathlib `v4.30.0`.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
lake build
```

If the optional cache downloader is unavailable on a platform, running `lake build`
directly builds the dependencies from source.

## Formalization layout

- `OrderClosures/OrderAdherence.lean`: shared order-adherence definitions and lemmas.
- `OrderClosures/GaoLeungProblem.lean`: compatibility umbrella for the
  Gao--Leung development. Its paper-ordered implementation is split into
  `Counterexample`, `CNFOrder`, `OrdinalSpace`, `StageFormula`, and
  `Iterations` under `OrderClosures/GaoLeungProblem/`.
- `OrderClosures/WeaklyFatou.lean`: compatibility umbrella for the weakly
  Fatou construction. Its paper-ordered implementation is split into
  `Reductions`, `FiniteTree`, `TreeNorm`, `Bands`, `Moderated`, and
  `FinalSpace` under `OrderClosures/WeaklyFatou/`.
- `OrderClosures.lean`: the root import for the complete development.

The project contains checked proofs of the formalized results and follows the
presentation order of the paper.
