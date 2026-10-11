/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Curve.GeneralizedJacobian
import Mathlib

/-!
# The projective line as an instance of the divisor-theory interface

For an algebraically closed field `k`, the projective line `ℙ¹_k` has function field
`RatFunc k` and closed points `Option k` (`none` is the point at infinity). We construct
its divisor map (`div f = ∑ₐ ord_a(f) [a] - deg(f) [∞]`), show that it satisfies the interface
`CurveDivisorData` (functions without zeros and poles are constant, principal divisors have
degree zero), and that the values at finitely many affine cusps satisfy `BoundaryEvaluation`
(the approximation theorem is Lagrange interpolation).

This shows that the interface of `GeneralizedAlbanese.Curve.GeneralizedJacobian` is satisfied
by a genuine curve, for every finite set of affine cusps. Moreover `J(k) = 0` for `ℙ¹`
(`jac_eq_zero`), so the exact sequence `0 → T_Y(k) → J_D(k) → J(k) → 0` gives
`T_Y(k) ≅ J_D(k)` (`torusEquivGenJac`): the generalized Albanese of `ℙ¹ ∖ D` is the boundary
torus, of dimension `#D - 1`.
-/

noncomputable section

open Polynomial

namespace GeneralizedAlbanese

namespace ProjectiveLine

variable {k : Type*} [Field k]

/-- The order of vanishing of a rational function at `a ∈ k`. -/
def ord (a : k) (f : RatFunc k) : ℤ :=
  (rootMultiplicity a f.num : ℤ) - rootMultiplicity a f.denom

/-- The order can be computed from any representation `f = p / q`. -/
lemma ord_eq_of_eq_div (a : k) {f : RatFunc k} {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hf : f = algebraMap _ _ p / algebraMap _ _ q) :
    ord a f = (rootMultiplicity a p : ℤ) - rootMultiplicity a q := by
  have hf0 : f ≠ 0 := by
    rw [hf]; exact div_ne_zero (by simpa using hp) (by simpa using hq)
  -- `num f * q = p * denom f`
  have key : f.num * q = p * f.denom := by
    rw [RatFunc.num_mul_eq_mul_denom_iff hq]
    exact hf
  have h1 := congrArg (rootMultiplicity a) key
  rw [rootMultiplicity_mul (mul_ne_zero (RatFunc.num_ne_zero hf0) hq),
    rootMultiplicity_mul (mul_ne_zero hp (RatFunc.denom_ne_zero f))] at h1
  unfold ord
  omega

lemma eq_num_div_denom (f : RatFunc k) :
    f = algebraMap _ _ f.num / algebraMap _ _ f.denom := (RatFunc.num_div_denom f).symm

lemma ord_mul (a : k) {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord a (f * g) = ord a f + ord a g := by
  have hNf := RatFunc.num_ne_zero hf
  have hNg := RatFunc.num_ne_zero hg
  have hDf := RatFunc.denom_ne_zero f
  have hDg := RatFunc.denom_ne_zero g
  rw [ord_eq_of_eq_div a (mul_ne_zero hNf hNg) (mul_ne_zero hDf hDg), rootMultiplicity_mul
    (mul_ne_zero hNf hNg), rootMultiplicity_mul (mul_ne_zero hDf hDg)]
  · unfold ord; push_cast; ring
  · conv_lhs => rw [eq_num_div_denom f, eq_num_div_denom g]
    rw [map_mul, map_mul, div_mul_div_comm]

lemma ord_algebraMap (a : k) {p : k[X]} (hp : p ≠ 0) :
    ord a (algebraMap _ _ p) = rootMultiplicity a p := by
  rw [ord_eq_of_eq_div a hp one_ne_zero (by simp)]
  simp

lemma ord_eq_zero_of_not_isRoot (a : k) (f : RatFunc k) (h : ¬ (f.num * f.denom).IsRoot a) :
    ord a f = 0 := by
  rw [IsRoot, eval_mul, mul_eq_zero, not_or] at h
  simp [ord, rootMultiplicity_eq_zero h.1, rootMultiplicity_eq_zero h.2]

/-- The order at the point at infinity: `-deg f`. -/
def ordInfty (f : RatFunc k) : ℤ := -f.intDegree

/-- The order function on the closed points `Option k` of `ℙ¹` (`none = ∞`). -/
def ordFun (f : RatFunc k) : Option k → ℤ
  | none => ordInfty f
  | some a => ord a f

variable [DecidableEq k]

/-- The finite set of points where a nonzero rational function may have a zero or pole. -/
def suppSet (f : RatFunc k) : Finset (Option k) :=
  insert none ((f.num * f.denom).roots.toFinset.map ⟨some, Option.some_injective k⟩)

lemma ordFun_eq_zero_of_notMem {f : RatFunc k} (hf : f ≠ 0) {x : Option k}
    (hx : x ∉ suppSet f) : ordFun f x = 0 := by
  cases x with
  | none => simp [suppSet] at hx
  | some a =>
    refine ord_eq_zero_of_not_isRoot a f fun h => hx ?_
    refine Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ ?_)
    rw [Multiset.mem_toFinset, mem_roots (mul_ne_zero (RatFunc.num_ne_zero hf)
      (RatFunc.denom_ne_zero f))]
    exact h

/-- **The divisor** of a nonzero rational function on `ℙ¹`. -/
def divisor (f : RatFunc k) (hf : f ≠ 0) : Option k →₀ ℤ :=
  Finsupp.onFinset (suppSet f) (ordFun f) fun x hx => by
    by_contra h
    exact hx (ordFun_eq_zero_of_notMem hf h)

@[simp]
lemma divisor_apply (f : RatFunc k) (hf : f ≠ 0) (x : Option k) :
    divisor f hf x = ordFun f x := rfl

lemma divisor_mul {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisor (f * g) (mul_ne_zero hf hg) = divisor f hf + divisor g hg := by
  ext x
  cases x with
  | none =>
    simp only [divisor_apply, ordFun, ordInfty, Finsupp.add_apply, RatFunc.intDegree_mul hf hg]
    ring
  | some a => simp [ordFun, ord_mul a hf hg]

/-- The divisor map `K^× → Div(ℙ¹)`. -/
def divHom : Additive (RatFunc k)ˣ →+ (Option k →₀ ℤ) where
  toFun f := divisor (f.toMul : RatFunc k) f.toMul.ne_zero
  map_zero' := by
    ext x
    cases x with
    | none => simp [ordFun, ordInfty]
    | some a => simp [ordFun, ord]
  map_add' f g := divisor_mul _ _

lemma sum_rootMultiplicity_of_subset {p : k[X]} {R : Finset k} (hR : p.roots.toFinset ⊆ R) :
    ∑ a ∈ R, rootMultiplicity a p = Multiset.card p.roots := by
  rw [← Multiset.toFinset_sum_count_eq, ← Finset.sum_subset hR]
  · exact Finset.sum_congr rfl fun a _ => (count_roots p).symm
  · intro a _ ha
    rw [← count_roots]
    exact Multiset.count_eq_zero.mpr (fun h => ha (Multiset.mem_toFinset.mpr h))

variable [IsAlgClosed k]

/-- **Principal divisors on `ℙ¹` have degree zero.** -/
theorem degree_divisor {f : RatFunc k} (hf : f ≠ 0) : boundaryDegree _ (divisor f hf) = 0 := by
  have hN := RatFunc.num_ne_zero hf
  have hD := RatFunc.denom_ne_zero f
  set R := (f.num * f.denom).roots.toFinset
  have hRN : f.num.roots.toFinset ⊆ R := by
    intro a ha
    simp only [R, Multiset.mem_toFinset, roots_mul (mul_ne_zero hN hD), Multiset.mem_add] at ha ⊢
    exact Or.inl ha
  have hRD : f.denom.roots.toFinset ⊆ R := by
    intro a ha
    simp only [R, Multiset.mem_toFinset, roots_mul (mul_ne_zero hN hD), Multiset.mem_add] at ha ⊢
    exact Or.inr ha
  rw [boundaryDegree_apply, divisor, Finsupp.onFinset_sum _ (fun _ => rfl), suppSet,
    Finset.sum_insert (by simp), Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, ordFun, ord, ordInfty, RatFunc.intDegree,
    Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum, sum_rootMultiplicity_of_subset hRN,
    sum_rootMultiplicity_of_subset hRD, IsAlgClosed.card_roots_eq_natDegree,
    IsAlgClosed.card_roots_eq_natDegree]
  ring

omit [IsAlgClosed k] in
lemma divisor_C {c : k} (hc : RatFunc.C c ≠ 0) : divisor (RatFunc.C c) hc = 0 := by
  ext x
  cases x with
  | none => simp [ordFun, ordInfty, RatFunc.intDegree_C]
  | some a => simp [ordFun, ord, RatFunc.num_C, RatFunc.denom_C, rootMultiplicity_C]

/-- **Rational functions without zeros or poles on `ℙ¹` are constant.** -/
theorem eq_C_of_divisor_eq_zero {f : RatFunc k} (hf : f ≠ 0) (h : divisor f hf = 0) :
    ∃ c : k, f = RatFunc.C c := by
  have hN := RatFunc.num_ne_zero hf
  -- the numerator has no roots
  have hroot : ∀ a, ¬ f.num.IsRoot a := by
    intro a ha
    have h0 : ord a f = 0 := by simpa [ordFun] using DFunLike.congr_fun h (some a)
    have hpos : 0 < rootMultiplicity a f.num := (rootMultiplicity_pos hN).mpr ha
    have hposD : 0 < rootMultiplicity a f.denom := by unfold ord at h0; omega
    have hDa : f.denom.IsRoot a := (rootMultiplicity_pos (RatFunc.denom_ne_zero f)).mp hposD
    obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom f
    have := congrArg (eval a) huv
    rw [eval_add, eval_mul, eval_mul, ha.eq_zero, hDa.eq_zero, eval_one] at this
    simp at this
  have hdegN : f.num.degree = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f.num hne
    exact hroot a ha
  have hinf : f.intDegree = 0 := by
    have := DFunLike.congr_fun h none
    simpa [ordFun, ordInfty] using this
  have hdegD : f.denom.natDegree = 0 := by
    have hn : f.num.natDegree = 0 := natDegree_eq_of_degree_eq_some hdegN
    unfold RatFunc.intDegree at hinf
    omega
  have hD1 : f.denom = 1 := eq_one_of_monic_natDegree_zero (RatFunc.monic_denom f) hdegD
  refine ⟨f.num.coeff 0, ?_⟩
  conv_lhs => rw [eq_num_div_denom f, hD1, eq_C_of_degree_eq_zero hdegN]
  simp [RatFunc.algebraMap_C]

/-- **`ℙ¹` satisfies the divisor-theory interface.** -/
def curveData : CurveDivisorData k (RatFunc k) (Option k) where
  div := divHom
  div_eq_zero_iff f := by
    constructor
    · intro h
      obtain ⟨c, hc⟩ := eq_C_of_divisor_eq_zero f.ne_zero h
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp only [map_zero] at hc
        exact f.ne_zero hc
      exact ⟨Units.mk0 c hc0, Units.ext (by simp [RatFunc.algebraMap_eq_C, hc])⟩
    · rintro ⟨c, rfl⟩
      have e : ((Units.map (algebraMap k (RatFunc k)).toMonoidHom c : (RatFunc k)ˣ) :
          RatFunc k) = RatFunc.C (c : k) := by simp [RatFunc.algebraMap_eq_C]
      ext x
      change ordFun ((Units.map (algebraMap k (RatFunc k)).toMonoidHom c : (RatFunc k)ˣ) :
          RatFunc k) x = 0
      rw [e]
      exact DFunLike.congr_fun (divisor_C (by simp)) x
  degree_div f := degree_divisor f.ne_zero

/-! ### Values at affine cusps -/

omit [IsAlgClosed k] [DecidableEq k] in
lemma eval_ne_zero_of_ord_eq_zero {a : k} {f : RatFunc k} (hf : f ≠ 0) (h : ord a f = 0) :
    f.num.eval a ≠ 0 ∧ f.denom.eval a ≠ 0 := by
  have hN := RatFunc.num_ne_zero hf
  have hD := RatFunc.denom_ne_zero f
  have hcop : ¬ (f.num.IsRoot a ∧ f.denom.IsRoot a) := by
    rintro ⟨h1, h2⟩
    obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom f
    have := congrArg (eval a) huv
    rw [eval_add, eval_mul, eval_mul, h1.eq_zero, h2.eq_zero, eval_one] at this
    simp at this
  unfold ord at h
  constructor
  · intro hN0
    have h1 := (rootMultiplicity_pos hN).mpr hN0
    exact hcop ⟨hN0, (rootMultiplicity_pos hD).mp (by omega)⟩
  · intro hD0
    have h1 := (rootMultiplicity_pos hD).mpr hD0
    exact hcop ⟨(rootMultiplicity_pos hN).mp (by omega), hD0⟩

/-- The value at `a` of a rational function regular and invertible at `a`. -/
def val (a : k) (f : RatFunc k) : k := f.num.eval a / f.denom.eval a

omit [IsAlgClosed k] [DecidableEq k] in
lemma val_mul {a : k} {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0) (hfa : ord a f = 0)
    (hga : ord a g = 0) : val a (f * g) = val a f * val a g := by
  have hfga : ord a (f * g) = 0 := by rw [ord_mul a hf hg, hfa, hga, add_zero]
  obtain ⟨-, hDfg⟩ := eval_ne_zero_of_ord_eq_zero (mul_ne_zero hf hg) hfga
  obtain ⟨-, hDf⟩ := eval_ne_zero_of_ord_eq_zero hf hfa
  obtain ⟨-, hDg⟩ := eval_ne_zero_of_ord_eq_zero hg hga
  have key := congrArg (eval a) (RatFunc.num_denom_mul f g)
  simp only [eval_mul] at key
  unfold val
  rw [div_mul_div_comm, div_eq_div_iff hDfg (mul_ne_zero hDf hDg)]
  linear_combination key

omit [IsAlgClosed k] [DecidableEq k] in
lemma val_ne_zero {a : k} {f : RatFunc k} (hf : f ≠ 0) (h : ord a f = 0) : val a f ≠ 0 :=
  div_ne_zero (eval_ne_zero_of_ord_eq_zero hf h).1 (eval_ne_zero_of_ord_eq_zero hf h).2

omit [IsAlgClosed k] [DecidableEq k] in
lemma val_algebraMap (a : k) (p : k[X]) : val a (algebraMap _ _ p) = p.eval a := by
  simp [val, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]

variable {D : Type*} (e : D → k)

/-- The affine cusps `e d ∈ k ⊆ ℙ¹(k)`. -/
def cusps : D → Option k := fun d => some (e d)

lemma ord_eq_zero_of_mem {f : (RatFunc k)ˣ} (hf : f ∈ (curveData (k := k)).unitsAt (cusps e))
    (d : D) : ord (e d) (f : RatFunc k) = 0 := hf d

/-- The values at the cusps. -/
def ev : (curveData (k := k)).unitsAt (cusps e) →* (D → kˣ) where
  toFun f d := Units.mk0 (val (e d) ((f : (RatFunc k)ˣ) : RatFunc k))
    (val_ne_zero (f : (RatFunc k)ˣ).ne_zero (ord_eq_zero_of_mem e f.2 d))
  map_one' := by
    ext d
    simp [val]
  map_mul' f g := by
    ext d
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0, Pi.mul_apply]
    exact val_mul (f : (RatFunc k)ˣ).ne_zero (g : (RatFunc k)ˣ).ne_zero
      (ord_eq_zero_of_mem e f.2 d) (ord_eq_zero_of_mem e g.2 d)

variable [Fintype D]

/-- **The values at finitely many affine cusps satisfy the interface**: the approximation
theorem is Lagrange interpolation. -/
def boundaryEvaluation (he : Function.Injective e) :
    BoundaryEvaluation (curveData (k := k)) (cusps e) where
  ev := ev e
  ev_const c hc := by
    ext d
    simp [ev, val, RatFunc.algebraMap_eq_C, RatFunc.num_C, RatFunc.denom_C]
  ev_surjective t := by
    classical
    let p : k[X] := Lagrange.interpolate Finset.univ e (fun d => (t d : k))
    have hp : ∀ d, p.eval (e d) = t d := fun d =>
      Lagrange.eval_interpolate_at_node _ he.injOn (Finset.mem_univ d)
    rcases isEmpty_or_nonempty D with hD | ⟨⟨d₀⟩⟩
    · exact ⟨1, funext fun d => (IsEmpty.false d).elim⟩
    have hp0 : p ≠ 0 := by
      intro h
      have := hp d₀
      rw [h, eval_zero] at this
      exact (t d₀).ne_zero this.symm
    have hf0 : (algebraMap k[X] (RatFunc k) p) ≠ 0 := by simpa using hp0
    let f : (RatFunc k)ˣ := Units.mk0 _ hf0
    have hfmem : f ∈ (curveData (k := k)).unitsAt (cusps e) := by
      intro d
      change ord (e d) (algebraMap k[X] (RatFunc k) p) = 0
      rw [ord_algebraMap _ hp0, rootMultiplicity_eq_zero]
      · rfl
      · rw [IsRoot, hp d]; exact (t d).ne_zero
    refine ⟨⟨f, hfmem⟩, funext fun d => Units.ext ?_⟩
    simp [ev, f, val_algebraMap, hp d]

/-! ### `J(k) = 0` for `ℙ¹`, hence `J_D(k) ≅ T_Y(k)` -/

omit [IsAlgClosed k] [DecidableEq k] in
lemma X_sub_C_ne_zero' (a : k) : algebraMap k[X] (RatFunc k) (X - C a) ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

/-- The linear function `X - a` as a unit of `k(X)`. -/
def lin (a : k) : (RatFunc k)ˣ := Units.mk0 _ (X_sub_C_ne_zero' a)

omit [IsAlgClosed k] in
lemma divHom_lin (a : k) :
    divHom (.ofMul (lin a)) = Finsupp.single (some a) 1 - Finsupp.single none 1 := by
  ext x
  change ordFun (algebraMap k[X] (RatFunc k) (X - C a)) x = _
  cases x with
  | none =>
    simp only [ordFun, ordInfty, RatFunc.intDegree_polynomial, natDegree_X_sub_C]
    simp
  | some b =>
    simp only [ordFun, ord_algebraMap b (X_sub_C_ne_zero a), rootMultiplicity_X_sub_C,
      Finsupp.sub_apply, Finsupp.single_apply, Option.some.injEq, reduceCtorEq, if_false,
      sub_zero]
    split_ifs <;> simp_all [eq_comm]

/-- `x ↦ x - deg(x) [∞]`, written as the divisor of `∏ₐ (X - a)^{x(a)}`. -/
def linComb : (Option k →₀ ℤ) →+ Additive (RatFunc k)ˣ :=
  Finsupp.liftAddHom fun
    | none => 0
    | some a => zmultiplesHom _ (.ofMul (lin a))

omit [IsAlgClosed k] in
lemma divHom_linComb (x : Option k →₀ ℤ) :
    divHom (linComb x) = x - Finsupp.single none (boundaryDegree _ x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, Finsupp.single_add]
    abel
  | single p n =>
    cases p with
    | none => simp [linComb]
    | some a =>
      simp only [linComb, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, map_zsmul,
        divHom_lin, boundaryDegree_single, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]

omit [Fintype D] in
/-- **`J(k) = 0` for `ℙ¹`**: every degree-zero divisor supported away from the cusps is the
divisor of a function invertible at the cusps. -/
theorem jac_eq_zero (z : (curveData (k := k)).Jac (cusps e)) : z = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [QuotientAddGroup.eq_zero_iff]
  have hdiv : divHom (linComb (x : Option k →₀ ℤ)) = x := by
    rw [divHom_linComb, x.2.1, Finsupp.single_zero, sub_zero]
  have hmem : (linComb (x : Option k →₀ ℤ)).toMul ∈ (curveData (k := k)).unitsAt (cusps e) :=
    fun d => by
      change divHom (linComb (x : Option k →₀ ℤ)) _ = 0
      rw [hdiv]
      exact x.2.2 d
  exact ⟨.ofMul ⟨_, hmem⟩, Subtype.ext hdiv⟩

variable (he : Function.Injective e)

/-- **The generalized Jacobian of `ℙ¹ ∖ D` is the boundary torus**: `T_Y(k) ≅ J_D(k)` for
finitely many affine cusps. -/
def torusEquivGenJac :
    boundaryTorus D k ≃* Multiplicative (boundaryEvaluation e he).GenJac :=
  MulEquiv.ofBijective (boundaryEvaluation e he).torusToGenJac
    ⟨(boundaryEvaluation e he).torusToGenJac_injective, fun x => by
      obtain ⟨τ, hτ⟩ := ((boundaryEvaluation e he).genJacToJac_eq_zero_iff x.toAdd).mp
        (jac_eq_zero e _)
      exact ⟨τ, hτ⟩⟩

end ProjectiveLine

end GeneralizedAlbanese

end
