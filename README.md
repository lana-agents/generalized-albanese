# generalized-albanese

Generalized Albanese varieties for normal-crossings complements.

## Status

**Partial: the punctured-curve case, at the level of points, characters and fundamental
groups.** Everything below is sorry- and axiom-free (`lake build --wfail`); the scope decision,
with what is formalised, what is an interface and what is out of reach, is in
[`Blueprint.md`](Blueprint.md).

* `GeneralizedAlbanese/Boundary/Divisor.lean`: boundary divisors, the character lattice
  `Div⁰_D` of the boundary torus, `Hom(Div⁰_D, M) ≅ (D → M) ⧸ M`, `Div⁰_D` free of rank `#D - 1`.
* `GeneralizedAlbanese/Boundary/Torus.lean`: split tori `Hom(X, A^×)` represented by `R[X]`,
  the boundary torus and `1 → A^× → (A^×)^D → T_Y(A) → 1`.
* `GeneralizedAlbanese/Pi1/SurfaceGroup.lean`, `Pi1/SurfaceAbelianization.lean`: the surface
  group `Π_{g,n}` of a punctured curve; `Π_{g,n}^ab ≅ ℤ^{2g} × ℤ^n/ℤ` is torsion-free and sits in
  `0 → ℤ^n/ℤ → Π_{g,n}^ab → Π_{g,0}^ab → 0`; for characters,
  `0 → Hom(Π_{g,0}, M) → Hom(Π_{g,n}, M) → {f | ∑ f = 0} → 0`, and with `M = ℤ` the quotient is
  `Div⁰_D`.
* `GeneralizedAlbanese/Pi1/Profinite.lean`: the same sequence for continuous characters with
  finite values of any `CuspidalPresentation` (an explicit interface standing for
  `π₁ᵉᵗ(Y_k̄) ≅ Π̂_{g,n}`), and the profinite completions as an instance.
* `GeneralizedAlbanese/Curve/GeneralizedJacobian.lean`: the generalized Jacobian of a punctured
  curve on `k`-points, `0 → T_Y(k) → J_D(k) → J(k) → 0`, and `J(k) ≅ Pic⁰(Z)` under the moving
  lemma, relative to an explicit divisor-theory interface (`CurveDivisorData`,
  `BoundaryEvaluation`; only a degenerate consistency instance is given).

Not formalised: the Albanese / generalized Jacobian as algebraic groups and their universal
property, the higher-dimensional normal-crossings case, and the comparison theorem
`π₁ᵉᵗ(Y_k̄) ≅ Π̂_{g,n}` itself (see `Blueprint.md`).

No lana-agents repository depends on this one: `iut` and its pinned lana-agents
dependencies do not `require` it.

## Goals

Formalise generalized Albanese varieties for complements of normal-crossings divisors.

For a smooth projective variety `Z` and a normal-crossings divisor `D`, with `Y = Z ∖ D`, construct the semi-abelian Albanese extension

```
0 → T_Y → Alb(Y) → Alb(Z) → 0
```

identify the character group of `T_Y` with the subgroup of boundary divisors algebraically equivalent to zero, prove the universal property and base-change/functoriality, and establish the comparison with the maximal torsion-free abelian quotient of the geometric étale fundamental group.

This corresponds to the standard theory reviewed in *Topics in Absolute Anabelian Geometry I*, Appendix, especially Proposition A.8.

## Established sources

* Serre, *Morphismes universels et variété d'Albanese*.
* FGA.
* Bosch–Lütkebohmert–Raynaud, *Néron Models*.
* Barbieri-Viale–Srinivas; Szamuely–Spiess.

## Related repositories

Intended as an input to the anabelian machinery of `iut`; not used by it.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`), its only direct dependency.
Library sources live under `GeneralizedAlbanese/`, and every file must be imported from
the root module `GeneralizedAlbanese.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib GeneralizedAlbanese --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#16](https://taxis.lana.merten.dev/issues/16)

License: Apache 2.0 (see LICENSE).
