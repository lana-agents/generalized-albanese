# generalized-albanese

Generalized Albanese varieties for normal-crossings complements.

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

An independently established input to the anabelian machinery used by `iut`.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
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
