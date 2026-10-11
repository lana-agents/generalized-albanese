# Blueprint: generalized Albanese varieties of normal-crossings complements

Target ([AbsTopI], Appendix, Prop. A.8; Serre, *Morphismes universels*): for `Z` smooth
projective over an algebraically closed field `k`, `D ⊆ Z` a normal-crossings divisor with
components `D₁, …, D_r`, and `Y = Z ∖ D`,

1. the generalized Albanese is a semi-abelian variety `0 → T_Y → Alb(Y) → Alb(Z) → 0`;
2. the character group of the torus `T_Y` is the group of boundary divisors `∑ nᵢ Dᵢ` that are
   algebraically equivalent to zero;
3. `Y → Alb(Y)` is universal for morphisms to semi-abelian varieties, functorial, and compatible
   with base change;
4. the Tate module of `Alb(Y)` is the maximal torsion-free abelian quotient of the geometric
   étale fundamental group `π₁(Y)` (in characteristic zero; prime-to-`p` otherwise).

The downstream use in the IUT strand ([AbsTopIII], Belyi cuspidalisation) needs the case of a
**punctured curve** `Y = Z ∖ {x₁, …, x_n}`, where (1)–(4) read:

* `Alb(Y) = J_D`, Rosenlicht's generalized Jacobian with modulus `D = x₁ + … + x_n`;
* `T_Y` has character group `Div⁰_D` (degree-zero boundary divisors), so
  `T_Y(k) = (k^×)^n / k^×`, of dimension `n - 1`;
* `π₁(Y)^ab ≅ Ẑ^{2g} × Ẑ(1)^n / Ẑ(1)` with `0 → Hom(Div⁰_D, Ẑ(1)) → π₁(Y)^ab → π₁(Z)^ab → 0`,
  the first map sending the generator of the inertia group at `xⱼ` to the class of `eⱼ`.

## What Mathlib (v4.32) and the lana-agents repositories provide

* Mathlib: group objects in schemes and `AlgebraicGeometry.Group.Abelian` (a proper geometrically
  integral group scheme over a field is commutative); `Module.Pic` of a ring; algebraic cycles and
  orders of vanishing on integral schemes; elliptic curves with their group law (Weierstrass
  model). **No** abelian varieties as a theory, no Picard or Albanese schemes, no Jacobians, no
  algebraic tori beyond group algebras, no étale fundamental group of schemes.
  Group theory: `PresentedGroup`, `Abelianization`, and the profinite completion with its
  universal property (`ProfiniteGrp.ProfiniteCompletion`).
* `pi1` (the iut pin): `π₁ᵉᵗ` of a connected scheme as a Galois category, and a Galois-theoretic
  `π₁` of curves (`GaloisPi1`: `Gal(Ω/L) ⧸ ⟨⟨inertia⟩⟩`) with tame inertia. No abelianisation,
  no comparison with surface groups.
* `oka`: GAGA and the Riemann existence theorem (finite étale covers of `X` vs. of `X^an`).
  The topological input (presentation of `π₁` of a punctured surface) is not formalised anywhere.
* `elliptic-curves` (a dependency, pinned at `8e2b208`, same Mathlib commit): divisors, the
  degree-zero theorem, the places of the projective curve (`placeOf`, DVRs, residue fields equal
  to `k` over `k = k̄`) and the class of a divisor in `Cl(k[E])`, compatible with Mathlib's
  `Point.toClass`. `belyi`, `genl`: curves, maps to `ℙ¹`; no Jacobians.

## Scope decision

Constructing `Alb(Y)` as a scheme (or even `Pic⁰`/`Alb` of `Z`) and proving its universal
property among semi-abelian varieties is far out of reach: it needs Picard schemes,
representability, abelian varieties and their duality, none of which exist. We therefore
formalise the **punctured-curve case**, split into a fully proved algebraic/group-theoretic core
and two documented interfaces.

### Formalised (sorry- and axiom-free)

| Statement | Lean | File |
|---|---|---|
| character lattice `ker((D →₀ ℤ) → NS)`; curve case `Div⁰_D = ker deg` | `characterLattice`, `boundaryChar` | `Boundary/Divisor.lean` |
| `Hom(Div⁰_D, M) ≅ (D → M) ⧸ M` for every abelian `M` | `charDualEquiv`, `ker_charDual`, `charDual_surjective` | `Boundary/Divisor.lean` |
| `Div⁰_D ≅ ℤ^{D ∖ d₀}`, free of rank `#D - 1` | `boundaryCharEquiv`, `finrank_boundaryChar` | `Boundary/Divisor.lean` |
| functoriality in the boundary (push-forward), naturality of the duality | `pushforwardChar`, `charDual_comp` | `Boundary/Divisor.lean` |
| split torus `T_X(A) = Hom(X, A^×)`, represented by `R[X]`; `Spec R[X]` | `SplitTorus`, `algHomEquiv`, `scheme`, `schemeHomEquiv` | `Boundary/Torus.lean` |
| functoriality in coefficients (base change) and in characters | `SplitTorus.map`, `SplitTorus.dualMap` | `Boundary/Torus.lean` |
| boundary torus: `1 → A^× → (A^×)^D → T_Y(A) → 1` | `boundaryTorusProj_surjective`, `ker_boundaryTorusProj` | `Boundary/Torus.lean` |
| surface group `Π_{g,n}`, inertia generators, filling in cusps | `SurfaceGroup`, `cusp`, `fill`, `fill_surjective` | `Pi1/SurfaceGroup.lean` |
| `0 → Hom(Π_{g,0},M) → Hom(Π_{g,n},M) → {f ∣ ∑ f = 0} → 0` | `inflate_injective`, `sum_residue`, `exists_residue_eq`, `ker_residue`, `characterQuotientEquiv` | `Pi1/SurfaceGroup.lean` |
| `Hom(Π_{g,n},ℤ) / Hom(Π_{g,0},ℤ) ≅ Div⁰_D` (characters of `T_Y`) | `integralCharacterQuotientEquiv` | `Pi1/SurfaceGroup.lean` |
| `Π_{g,n}^ab ≅ ℤ^g × ℤ^g × ℤ^n/ℤ`, torsion-free | `abEquiv`, `isMulTorsionFree_abelianization` | `Pi1/SurfaceAbelianization.lean` |
| `0 → ℤ^n/ℤ → Π_{g,n}^ab → Π_{g,0}^ab → 0` (`[eⱼ] ↦ [cⱼ]`) | `cuspMap_injective`, `range_cuspMap`, `abFill_surjective` | `Pi1/SurfaceAbelianization.lean` |
| finite-coefficient (étale `H¹`) sequence for any cuspidal presentation | `CuspidalPresentation.inflate_injective`, `.sum_residue`, `.exists_residue_eq`, `.residue_eq_zero_iff` | `Pi1/Profinite.lean` |
| the profinite completions `Π̂_{g,n} → Π̂_{g,0}` are a cuspidal presentation | `CuspidalPresentation.completion` | `Pi1/Profinite.lean` |
| generalized Jacobian on points: `0 → T_Y(k) → J_D(k) → J(k) → 0` | `torusToGenJac_injective`, `genJacToJac_eq_zero_iff`, `genJacToJac_surjective` | `Curve/GeneralizedJacobian.lean` |
| `J(k) ≅ Pic⁰(Z)` under the moving lemma | `jacEquivPic` | `Curve/GeneralizedJacobian.lean` |
| `ℙ¹` (function field `RatFunc k`, `k` algebraically closed) satisfies the divisor interface, for any finite set of cusps, `∞` allowed (value at `∞` = ratio of leading coefficients; approximation = Lagrange interpolation corrected at `∞`) | `ProjectiveLine.curveData`, `ProjectiveLine.valInfty`, `ProjectiveLine.exists_valAt_eq`, `ProjectiveLine.boundaryEvaluation` | `Curve/ProjectiveLine.lean` |
| `J(k) = 0` for `ℙ¹`, hence `T_Y(k) ≅ J_D(k)` for `Y = ℙ¹ ∖ D` | `ProjectiveLine.jac_eq_zero`, `ProjectiveLine.torusEquivGenJac` | `Curve/ProjectiveLine.lean` |
| an elliptic curve `E/k`, `k = k̄`, satisfies the divisor interface (closed points = places of `k(E)`, all of degree one) | `EllipticCurve.curveData`, `EllipticCurve.degProjPt_eq_one` | `Curve/EllipticCurve.lean` |
| values at finitely many cusps of `E` (origin allowed) and the approximation theorem (CRT in `k[E]` + pole order at `O`) | `EllipticCurve.valAt`, `EllipticCurve.exists_valAt_eq`, `EllipticCurve.boundaryEvaluation` | `Curve/EllipticCurve.lean` |
| `J(k) ≅ E(k)` for `Y = E ∖ D` (via `Cl(k[E])` and Mathlib's `Point.toClass`), Abel–Jacobi `[Q] - [R] ↦ Q - R`; `Pic⁰(E) ≅ E(k)` | `EllipticCurve.jacToClass_injective`, `EllipticCurve.range_jacToClass`, `EllipticCurve.jacEquivPoint`, `EllipticCurve.jacEquivPoint_mk`, `EllipticCurve.picEquivPoint` | `Curve/EllipticCurve.lean` |
| `0 → T_Y(k) → J_D(k) → E(k) → 0` for `Y = E ∖ D` | `EllipticCurve.torusToGenJac_injective`, `EllipticCurve.genJacToPoint_eq_zero_iff`, `EllipticCurve.genJacToPoint_surjective` | `Curve/EllipticCurve.lean` |
| `T_X(A)[n] ≅ Hom(X, μ_n(A))`; Galois acts on `T_X[n]`, `T_X[p^n]` via the cyclotomic character (Tate twist: `T_Y[n] ≅ Hom(Div⁰_D, ℤ/n(1))`, `T_p(T_Y) ≅ Hom(Div⁰_D, ℤ_p(1))`) | `SplitTorus.torsionEquiv`, `SplitTorus.map_eq_pow_modularCyclotomicCharacter`, `SplitTorus.map_eq_pow_cyclotomicCharacter`, `boundaryTorus.torsionEquiv` | `Boundary/TateTwist.lean` |

Since `ℤ^n/ℤ = Hom(Div⁰_D, ℤ)` (`charDualEquiv`), the abelianisation sequence is the discrete
(topological) form of `0 → T(T_Y) → T(Alb Y) → T(Alb Z) → 0`, and the finite-coefficient
sequence is its Pontryagin dual over `ℤ/m`, i.e. item (4) for punctured curves once the
interface below is instantiated.

### Stated as interfaces (explicit structure fields; no axioms)

* **`CuspidalPresentation g n GY GZ`** (`Pi1/Profinite.lean`): `GY → GZ` with maps from
  `Π_{g,n} → Π_{g,0}`, compatible with `fill`, with dense image, along which characters with
  finite values extend continuously. For `GY = π₁ᵉᵗ(Y_k̄)`, `GZ = π₁ᵉᵗ(Z_k̄)` in characteristic
  zero this is the comparison `π₁ᵉᵗ ≅ Π̂_{g,n}` (Riemann existence [oka], GAGA, the presentation
  of the topological fundamental group of a punctured surface — the latter is not formalised
  anywhere). The interface is shown satisfiable by the profinite completions.
* **`CurveDivisorData`, `BoundaryEvaluation`** (`Curve/GeneralizedJacobian.lean`): the divisor
  map `K^× → Div(Z)` (kernel = constants, degree zero) and values at the cusps with the
  approximation theorem. Instantiated for `ℙ¹` with finitely many affine cusps
  (`Curve/ProjectiveLine.lean`: divisors via root multiplicities, degree zero over an
  algebraically closed field, approximation by Lagrange interpolation; `∞` may be a cusp) and
  for elliptic curves with any finite set of cusps (`Curve/EllipticCurve.lean`, divisor theory
  and places from `elliptic-curves`, approximation by the Chinese remainder theorem in the
  Dedekind domain `k[E]` with a denominator of large pole order at `O`). For a general curve
  the interface would follow from the theory of places of a function field of one variable
  (strong approximation, finiteness of `div f`, degree of principal divisors), which Mathlib
  does not have beyond `ℙ¹` and Weierstrass curves.

### Out of reach (not formalised), and why

* `Alb(Y)`, `J_D`, `Pic⁰`, `Alb(Z)` as algebraic groups / schemes; Rosenlicht's theorem that
  `J_D` is a semi-abelian variety; the universal property of `Y → Alb(Y)` among morphisms to
  semi-abelian varieties: needs Picard schemes, representability theorems, abelian varieties —
  absent from Mathlib.
* The general normal-crossings case in higher dimension (`NS(Z)`, algebraic equivalence): needs
  Néron–Severi groups and intersection theory. Only the algebraic definition
  `characterLattice cl` for an abstract class map `cl` is provided.
* The comparison `π₁ᵉᵗ(Y_k̄) ≅ Π̂_{g,n}` itself (and its positive-characteristic prime-to-`p`
  analogue via specialisation): needs the topology of punctured surfaces, and the link between
  `pi1`'s `GaloisPi1` and the analytic side. Recorded as `CuspidalPresentation`.
* Tate twists on the fundamental-group side: the torus side is done (`Boundary/TateTwist.lean`:
  Galois acts on `T_Y[n]` and `T_p(T_Y)` through the cyclotomic character). The corresponding
  statement for `π₁` — the inertia subgroup at a cusp is canonically `Ẑ(1)`, and `G_k` acts on
  `π₁(Y_k̄)^ab ⊇ Hom(Div⁰_D, Ẑ(1))` through the cyclotomic character — needs the arithmetic
  fundamental group `1 → π₁(Y_k̄) → π₁(Y) → G_k → 1` with its outer action, and the
  identification of tame inertia of the completed local fields at the cusps with
  `lim μ_n` (Kummer theory of `k̄((t))`); `pi1` has tame inertia groups but neither the
  homotopy exact sequence nor this identification.
* Positive genus beyond elliptic curves: needs the divisor theory of an arbitrary function field
  of one variable (see the interface paragraph above); `J(k) ≅ Pic⁰(Z)` then needs the moving
  lemma (`CurveDivisorData.MovingLemma`), which for `E` is avoided by the class-group argument.

## Milestones

1. M1 boundary divisors and duality — done.
2. M2 split and boundary tori — done.
3. M3 surface groups: residue sequence, abelianisation, torsion-freeness — done.
4. M4 profinite / étale interface and its instantiation by completions — done.
5. M5 generalized Jacobian of a punctured curve on points — done (interface-based).
6. M6 the instance `ℙ¹ ∖ D`: `J_D(k) ≅ T_Y(k)` — done, cusp at `∞` included.
7. M7 the instance `E ∖ D` for an elliptic curve: `0 → T_Y(k) → J_D(k) → E(k) → 0` — done.
8. M8 Tate twist on the torus side — done.
9. Future: connect
   `CuspidalPresentation` to `pi1`'s `GaloisPi1.pi1` of a punctured curve; profinite
   abelianisation `Π̂_{g,n}^ab ≅ Ẑ^{2g+n-1}` directly.
