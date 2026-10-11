/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Boundary.Torus
import Mathlib

/-!
# The generalized Jacobian of a punctured curve, on points

Let `Z` be a smooth projective connected curve over an algebraically closed field `k`, with
function field `K` and set of closed points `P`, and let `D ⊆ P` be a finite set of cusps,
`Y = Z ∖ D`. The generalized Albanese of `Y` is Rosenlicht's generalized Jacobian `J_D` of
`Z` for the (reduced) modulus `D`. On `k`-points:

* `J(k) = Pic⁰(Z)` is the group of degree-zero divisors modulo principal divisors;
* `J_D(k)` is the group of degree-zero divisors supported on `Y` modulo divisors of functions
  `f ≡ 1` at every cusp;
* `0 → T_Y(k) → J_D(k) → J(k) → 0` is exact, where `T_Y(k) = (k^×)^D / k^×` is the boundary
  torus, with character group `Div⁰_D`.

The divisor theory of the curve is taken as an explicit interface (`CurveDivisorData`,
`BoundaryEvaluation`): the divisor map `div : K^× → Div(Z)`, the facts that functions without
zeros and poles are constant and that principal divisors have degree zero (properness), the
values of functions at the cusps, and the approximation theorem (every tuple of values at the
cusps is attained by a function regular and invertible there). From these we prove the exact
sequence (`genJacToJac_surjective`, `ker_genJacToJac`, `torusToGenJac_injective`) and, under
the moving lemma, the identification of `J(k)` with `Pic⁰(Z)` (`jacEquivPic`).

Rosenlicht's theorem that `J_D` is a (semi-abelian) algebraic group and the universal property
of `Y → J_D` among morphisms to commutative algebraic groups are out of reach in Mathlib
(no algebraic groups beyond the group-object API, no Picard schemes) and are not formalised.
-/

noncomputable section

namespace GeneralizedAlbanese

section

variable {P : Type*} {D : Type*} (ι : D → P)

/-- Divisors of degree zero supported on `Y = Z ∖ D`. -/
def div0Y : AddSubgroup (P →₀ ℤ) where
  carrier := {x | boundaryDegree P x = 0 ∧ ∀ d, x (ι d) = 0}
  add_mem' hx hy := ⟨by simp [hx.1, hy.1], fun d => by simp [hx.2 d, hy.2 d]⟩
  zero_mem' := ⟨by simp, fun _ => rfl⟩
  neg_mem' hx := ⟨by simp [hx.1], fun d => by simp [hx.2 d]⟩

end

/-- **Interface: the divisor theory of a smooth projective connected curve** over `k`, with
function field `K` and closed points `P`. -/
structure CurveDivisorData (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (P : Type*) where
  /-- The divisor of a rational function. -/
  div : Additive Kˣ →+ (P →₀ ℤ)
  /-- Functions without zeros or poles are constant (`Z` is proper and connected). -/
  div_eq_zero_iff (f : Kˣ) :
    div (.ofMul f) = 0 ↔ f ∈ (Units.map (algebraMap k K).toMonoidHom).range
  /-- Principal divisors have degree zero. -/
  degree_div (f : Kˣ) : boundaryDegree P (div (.ofMul f)) = 0

namespace CurveDivisorData

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K] {P : Type*}
  (C : CurveDivisorData k K P) {D : Type*} (ι : D → P)

/-- The functions that are regular and invertible at every cusp. -/
def unitsAt : Subgroup Kˣ where
  carrier := {f | ∀ d, C.div (.ofMul f) (ι d) = 0}
  mul_mem' {f f'} hf hf' d := by
    rw [ofMul_mul, map_add, Finsupp.add_apply, hf d, hf' d, add_zero]
  one_mem' d := by simp
  inv_mem' {f} hf d := by simp [ofMul_inv, hf d]

/-- The divisor of a function invertible at the cusps, as a degree-zero divisor on `Y`. -/
def divY : Additive (C.unitsAt ι) →+ div0Y ι where
  toFun f := ⟨C.div (.ofMul (f.toMul : Kˣ)), C.degree_div _, f.toMul.2⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp [← map_add]

@[simp]
lemma coe_divY (f : Additive (C.unitsAt ι)) :
    (C.divY ι f : P →₀ ℤ) = C.div (.ofMul (f.toMul : Kˣ)) := rfl

/-- **`J(k)`**: degree-zero divisors on `Y` modulo divisors of functions invertible at the
cusps. Under the moving lemma this is `Pic⁰(Z)` (`jacEquivPic`). -/
abbrev Jac := div0Y ι ⧸ (C.divY ι).range

/-- Principal divisors, as degree-zero divisors. -/
def divDeg0 : Additive Kˣ →+ boundaryChar P where
  toFun f := ⟨C.div f, C.degree_div f.toMul⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp

/-- **`Pic⁰(Z)`**: degree-zero divisors modulo principal divisors. -/
abbrev Pic0 := boundaryChar P ⧸ C.divDeg0.range

lemma div0Y_le : div0Y ι ≤ boundaryChar P := fun _ hx => mem_boundaryChar.mpr hx.1

/-- The comparison `J(k) → Pic⁰(Z)` induced by the inclusion of divisors supported on `Y`. -/
def jacToPic : C.Jac ι →+ C.Pic0 :=
  QuotientAddGroup.map _ _ (AddSubgroup.inclusion (div0Y_le ι)) (by
    rintro _ ⟨f, rfl⟩
    exact ⟨.ofMul (f.toMul : Kˣ), rfl⟩)

/-- The moving lemma: every divisor is linearly equivalent to one supported on `Y`. -/
def MovingLemma : Prop := ∀ x : P →₀ ℤ, ∃ f : Kˣ, ∀ d, (x + C.div (.ofMul f)) (ι d) = 0

theorem jacToPic_injective : Function.Injective (C.jacToPic ι) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨f, hf⟩ := (QuotientAddGroup.eq_zero_iff _).mp hx
  have hfY : f.toMul ∈ C.unitsAt ι := fun d => by
    have := congrArg (fun z : boundaryChar P => (z : P →₀ ℤ) (ι d)) hf
    exact this.trans (y.2.2 d)
  refine (QuotientAddGroup.eq_zero_iff _).mpr ⟨.ofMul ⟨f.toMul, hfY⟩, Subtype.ext ?_⟩
  exact (congrArg Subtype.val hf :)

theorem jacToPic_surjective (hmov : C.MovingLemma ι) : Function.Surjective (C.jacToPic ι) := by
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨f, hf⟩ := hmov x
  have hxY : (x : P →₀ ℤ) + C.div (.ofMul f) ∈ div0Y ι :=
    ⟨by rw [map_add, mem_boundaryChar.mp x.2, C.degree_div, add_zero], hf⟩
  refine ⟨QuotientAddGroup.mk ⟨_, hxY⟩, ?_⟩
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk x
  rw [QuotientAddGroup.eq]
  refine ⟨-.ofMul f, Subtype.ext ?_⟩
  simp [divDeg0]

/-- **`J(k) ≅ Pic⁰(Z)`** under the moving lemma. -/
def jacEquivPic (hmov : C.MovingLemma ι) : C.Jac ι ≃+ C.Pic0 :=
  AddEquiv.ofBijective (C.jacToPic ι) ⟨C.jacToPic_injective ι, C.jacToPic_surjective ι hmov⟩

end CurveDivisorData

/-- **Interface: values at the cusps.** The value `f(d) ∈ k^×` of a function invertible at the
cusps (the residue fields at closed points are `k`), multiplicative, equal to `c` on constants,
and surjective onto `(k^×)^D` (the approximation theorem / Chinese remainder theorem). -/
structure BoundaryEvaluation {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
    {P : Type*} (C : CurveDivisorData k K P) {D : Type*} (ι : D → P) where
  /-- The values at the cusps. -/
  ev : C.unitsAt ι →* (D → kˣ)
  /-- Constants take their own value. -/
  ev_const (c : kˣ) (hc : Units.map (algebraMap k K).toMonoidHom c ∈ C.unitsAt ι) :
    ev ⟨_, hc⟩ = fun _ => c
  /-- Approximation: every tuple of values is attained. -/
  ev_surjective : Function.Surjective ev

namespace BoundaryEvaluation

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K] {P : Type*}
  {C : CurveDivisorData k K P} {D : Type*} {ι : D → P} (E : BoundaryEvaluation C ι)

/-- The functions `≡ 1` at every cusp. -/
def units1 : Subgroup (C.unitsAt ι) := E.ev.ker

/-- **`J_D(k)`, the points of the generalized Jacobian** for the modulus `D`: degree-zero
divisors on `Y` modulo divisors of functions `≡ 1` at the cusps. -/
abbrev GenJac := div0Y ι ⧸ ((C.divY ι).comp
  (E.units1.subtype.toAdditive : Additive E.units1 →+ Additive (C.unitsAt ι))).range

lemma mem_units1 {u : C.unitsAt ι} : u ∈ E.units1 ↔ E.ev u = 1 := MonoidHom.mem_ker

/-- The class in `J_D(k)` of the divisor of a function invertible at the cusps. -/
def unitsToGenJac : C.unitsAt ι →* Multiplicative E.GenJac where
  toFun f := .ofAdd (QuotientAddGroup.mk (C.divY ι (.ofMul f)))
  map_one' := by simp
  map_mul' f f' := by simp [ofMul_mul]

lemma unitsToGenJac_eq_one_iff (f : C.unitsAt ι) :
    E.unitsToGenJac f = 1 ↔ ∃ u ∈ E.units1, C.div (.ofMul (u : Kˣ)) = C.div (.ofMul (f : Kˣ)) := by
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 ↔ _
  rw [Multiplicative.ofAdd.injective.eq_iff, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.toMul, u.toMul.2, congrArg Subtype.val hu⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨.ofMul ⟨u, hu⟩, Subtype.ext h⟩

lemma ker_ev_le : E.ev.ker ≤ E.unitsToGenJac.ker := fun u hu =>
  MonoidHom.mem_ker.mpr ((E.unitsToGenJac_eq_one_iff u).mpr ⟨u, hu, rfl⟩)

/-- The map `(k^×)^D → J_D(k)`: a tuple of values at the cusps goes to the class of the divisor
of any function invertible at the cusps with these values. -/
def valsToGenJac : (D → kˣ) →* Multiplicative E.GenJac :=
  E.ev.liftOfSurjective E.ev_surjective ⟨E.unitsToGenJac, E.ker_ev_le⟩

@[simp]
lemma valsToGenJac_ev (f : C.unitsAt ι) : E.valsToGenJac (E.ev f) = E.unitsToGenJac f :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

lemma const_mem_unitsAt (c : kˣ) : Units.map (algebraMap k K).toMonoidHom c ∈ C.unitsAt ι :=
  fun d => by rw [(C.div_eq_zero_iff _).mpr ⟨c, rfl⟩]; rfl

/-- The kernel of `(k^×)^D → J_D(k)` is the diagonal `k^×`. -/
theorem valsToGenJac_eq_one_iff (t : D → kˣ) :
    E.valsToGenJac t = 1 ↔ ∃ c : kˣ, t = fun _ => c := by
  obtain ⟨f, rfl⟩ := E.ev_surjective t
  rw [valsToGenJac_ev, unitsToGenJac_eq_one_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    have h0 : C.div (.ofMul ((f : Kˣ) * (u : Kˣ)⁻¹)) = 0 := by
      rw [ofMul_mul, ofMul_inv, map_add, map_neg, h, add_neg_cancel]
    obtain ⟨c, hc⟩ := (C.div_eq_zero_iff _).mp h0
    refine ⟨c, ?_⟩
    have hf : f = ⟨_, const_mem_unitsAt c⟩ * u := by
      ext1
      change (f : Kˣ) = Units.map (algebraMap k K).toMonoidHom c * u
      rw [hc, inv_mul_cancel_right]
    rw [hf, map_mul, E.ev_const, E.mem_units1.mp hu, mul_one]
  · rintro ⟨c, hc⟩
    refine ⟨f * (⟨_, const_mem_unitsAt c⟩)⁻¹, ?_, ?_⟩
    · rw [mem_units1, map_mul, map_inv, hc, E.ev_const, mul_inv_cancel]
    · have h0 : C.div (.ofMul (Units.map (algebraMap k K).toMonoidHom c)) = 0 :=
        (C.div_eq_zero_iff _).mpr ⟨c, rfl⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ofMul_mul, ofMul_inv, map_add, map_neg]
      rw [h0, neg_zero, add_zero]

lemma ker_boundaryTorusProj_le :
    (boundaryTorusProj D k).ker ≤ E.valsToGenJac.ker := by
  rw [ker_boundaryTorusProj]
  rintro _ ⟨c, rfl⟩
  exact MonoidHom.mem_ker.mpr ((E.valsToGenJac_eq_one_iff _).mpr ⟨c, rfl⟩)

/-- **The boundary torus inside the generalized Jacobian**: `T_Y(k) → J_D(k)`. -/
def torusToGenJac : boundaryTorus D k →* Multiplicative E.GenJac :=
  (boundaryTorusProj D k).liftOfSurjective (boundaryTorusProj_surjective D k)
    ⟨E.valsToGenJac, E.ker_boundaryTorusProj_le⟩

@[simp]
lemma torusToGenJac_proj (t : D → kˣ) :
    E.torusToGenJac (boundaryTorusProj D k t) = E.valsToGenJac t :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- **`T_Y(k) → J_D(k)` is injective.** -/
theorem torusToGenJac_injective : Function.Injective E.torusToGenJac := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  obtain ⟨t, rfl⟩ := boundaryTorusProj_surjective D k τ
  rw [torusToGenJac_proj, valsToGenJac_eq_one_iff] at hτ
  obtain ⟨c, rfl⟩ := hτ
  rw [← MonoidHom.mem_ker, ker_boundaryTorusProj]
  exact ⟨c, rfl⟩

lemma range_le : ((C.divY ι).comp
    (E.units1.subtype.toAdditive : Additive E.units1 →+ Additive (C.unitsAt ι))).range ≤
    (C.divY ι).range := by
  rintro _ ⟨u, rfl⟩
  exact ⟨_, rfl⟩

/-- **`J_D(k) → J(k)`**: forget the trivialisation at the cusps. -/
def genJacToJac : E.GenJac →+ C.Jac ι :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id _) E.range_le

@[simp]
lemma genJacToJac_mk (x : div0Y ι) :
    E.genJacToJac (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := rfl

/-- **`J_D(k) → J(k)` is surjective.** -/
theorem genJacToJac_surjective : Function.Surjective E.genJacToJac := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨QuotientAddGroup.mk x, rfl⟩

/-- **Exactness at `J_D(k)`**: the kernel of `J_D(k) → J(k)` is the image of the boundary torus
`T_Y(k)`. -/
theorem genJacToJac_eq_zero_iff (x : E.GenJac) :
    E.genJacToJac x = 0 ↔ ∃ τ : boundaryTorus D k, (E.torusToGenJac τ).toAdd = x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [genJacToJac_mk, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨boundaryTorusProj D k (E.ev f.toMul), ?_⟩
    rw [torusToGenJac_proj, valsToGenJac_ev]
    rfl
  · rintro ⟨τ, hτ⟩
    obtain ⟨t, rfl⟩ := boundaryTorusProj_surjective D k τ
    obtain ⟨f, rfl⟩ := E.ev_surjective t
    rw [torusToGenJac_proj, valsToGenJac_ev] at hτ
    obtain ⟨u, hu⟩ := QuotientAddGroup.eq.mp hτ
    refine ⟨.ofMul f + .ofMul (u.toMul : C.unitsAt ι), ?_⟩
    rw [map_add]
    change _ + (C.divY ι).comp (E.units1.subtype.toAdditive) u = y
    rw [hu, add_neg_cancel_left]

end BoundaryEvaluation

/-! ### Consistency check

The interface is consistent: the degenerate datum with `K = k`, no points and no cusps satisfies
it. This is only a sanity check of the hypotheses, not an instance of geometric interest; a
genuine instance (e.g. `ℙ¹`, or a Weierstrass curve via the divisor theory of the
`elliptic-curves` repository) is future work, see `Blueprint.md`. -/

/-- The degenerate divisor datum: `K = k`, no closed points. -/
def CurveDivisorData.trivial (k : Type*) [Field k] : CurveDivisorData k k PEmpty where
  div := 0
  div_eq_zero_iff f := by
    simp only [AddMonoidHom.zero_apply, true_iff]
    exact ⟨f, Units.ext rfl⟩
  degree_div _ := by simp

/-- The degenerate boundary evaluation with no cusps. -/
def BoundaryEvaluation.trivial (k : Type*) [Field k] :
    BoundaryEvaluation (CurveDivisorData.trivial k) (PEmpty.elim : PEmpty → PEmpty) where
  ev := 1
  ev_const _ _ := funext fun d => d.elim
  ev_surjective _ := ⟨1, funext fun d => d.elim⟩

end GeneralizedAlbanese

end
