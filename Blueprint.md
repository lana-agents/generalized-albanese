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
* `elliptic-curves`: divisors, degree-zero theorem and class group on the function field of a
  Weierstrass curve. `belyi`, `genl`: curves, maps to `ℙ¹`; no Jacobians.

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
| `ℙ¹` (function field `RatFunc k`, `k` algebraically closed) satisfies the divisor interface, for any finite set of affine cusps | `ProjectiveLine.curveData`, `ProjectiveLine.boundaryEvaluation` | `Curve/ProjectiveLine.lean` |
| `J(k) = 0` for `ℙ¹`, hence `T_Y(k) ≅ J_D(k)` for `Y = ℙ¹ ∖ D` | `ProjectiveLine.jac_eq_zero`, `ProjectiveLine.torusEquivGenJac` | `Curve/ProjectiveLine.lean` |

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
  algebraically closed field, approximation by Lagrange interpolation). Instantiating it for
  curves of positive genus (e.g. Weierstrass curves via the divisor theory of `elliptic-curves`)
  is future work.

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
* Tate twists: the discrete statements ignore the Galois action; the `Ẑ(1)` twist of the inertia
  generators is part of the arithmetic interface, not of the geometric statements here.

## Milestones

1. M1 boundary divisors and duality — done.
2. M2 split and boundary tori — done.
3. M3 surface groups: residue sequence, abelianisation, torsion-freeness — done.
4. M4 profinite / étale interface and its instantiation by completions — done.
5. M5 generalized Jacobian of a punctured curve on points — done (interface-based).
6. M6 the instance `ℙ¹ ∖ D`: `J_D(k) ≅ T_Y(k)` — done.
7. Future: instantiate `CurveDivisorData` for Weierstrass curves (cusp at infinity included); connect
   `CuspidalPresentation` to `pi1`'s `GaloisPi1.pi1` of a punctured curve; profinite
   abelianisation `Π̂_{g,n}^ab ≅ Ẑ^{2g+n-1}` directly.
