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
degree zero), and that the values at finitely many cusps — affine ones and possibly `∞` —
satisfy `BoundaryEvaluation`. The value at `∞` of a function of degree zero is the ratio of the
leading coefficients (`valInfty`); the approximation theorem (`exists_valAt_eq`) is Lagrange
interpolation, corrected by `t_∞ ∏ (X - a_d)` and divided by `(X - b)^{#affine cusps}`.

This shows that the interface of `GeneralizedAlbanese.Curve.GeneralizedJacobian` is satisfied
by a genuine curve, for every finite set of cusps. Moreover `J(k) = 0` for `ℙ¹`
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

/-! ### Values at infinity -/

/-- The value at `∞` of a rational function regular and invertible at `∞`: the leading
coefficient of the numerator (the denominator is monic). For `f = p / q` with
`deg p = deg q` this is `lc(p) / lc(q)`. -/
def valInfty (f : RatFunc k) : k := f.num.leadingCoeff

omit [IsAlgClosed k] [DecidableEq k] in
lemma valInfty_mul (f g : RatFunc k) : valInfty (f * g) = valInfty f * valInfty g := by
  have key := congrArg leadingCoeff (RatFunc.num_denom_mul f g)
  simp only [leadingCoeff_mul, (RatFunc.monic_denom _).leadingCoeff, mul_one] at key
  exact key

omit [IsAlgClosed k] [DecidableEq k] in
lemma valInfty_ne_zero {f : RatFunc k} (hf : f ≠ 0) : valInfty f ≠ 0 :=
  leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hf)

omit [IsAlgClosed k] [DecidableEq k] in
lemma valInfty_div {p q : k[X]} (hq : q ≠ 0) :
    valInfty (algebraMap _ _ p / algebraMap _ _ q : RatFunc k) =
      p.leadingCoeff / q.leadingCoeff := by
  have key := congrArg leadingCoeff ((RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl :
    (algebraMap _ _ p / algebraMap _ _ q : RatFunc k).num * q = p * _)
  simp only [leadingCoeff_mul, (RatFunc.monic_denom _).leadingCoeff, mul_one] at key
  rw [valInfty, eq_div_iff (leadingCoeff_ne_zero.mpr hq), key]

omit [IsAlgClosed k] [DecidableEq k] in
lemma ordInfty_div {p q : k[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ordInfty (algebraMap _ _ p / algebraMap _ _ q : RatFunc k) =
      (q.natDegree : ℤ) - p.natDegree := by
  rw [ordInfty, RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hp)
    (RatFunc.algebraMap_ne_zero hq), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial]
  ring

omit [IsAlgClosed k] [DecidableEq k] in
lemma val_div {a : k} {p q : k[X]} (hpa : p.eval a ≠ 0) (hqa : q.eval a ≠ 0) :
    ord a (algebraMap _ _ p / algebraMap _ _ q : RatFunc k) = 0 ∧
      val a (algebraMap _ _ p / algebraMap _ _ q : RatFunc k) = p.eval a / q.eval a := by
  have hp : p ≠ 0 := fun h => hpa (by simp [h])
  have hq : q ≠ 0 := fun h => hqa (by simp [h])
  set f : RatFunc k := algebraMap _ _ p / algebraMap _ _ q
  have hf : f ≠ 0 := div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  have hord : ord a f = 0 := by
    rw [ord_eq_of_eq_div a hp hq rfl, rootMultiplicity_eq_zero hpa,
      rootMultiplicity_eq_zero hqa]
    rfl
  refine ⟨hord, ?_⟩
  have key := congrArg (eval a) ((RatFunc.num_mul_eq_mul_denom_iff hq).mpr rfl :
    f.num * q = p * f.denom)
  simp only [eval_mul] at key
  rw [val, div_eq_div_iff (eval_ne_zero_of_ord_eq_zero hf hord).2 hqa]
  exact key

/-! ### Values at arbitrary cusps -/

/-- The value at a point of `ℙ¹` of a rational function regular and invertible there. -/
def valAt : Option k → RatFunc k → k
  | none => valInfty
  | some a => val a

omit [IsAlgClosed k] [DecidableEq k] in
lemma valAt_mul {x : Option k} {f g : RatFunc k} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfx : ordFun f x = 0) (hgx : ordFun g x = 0) : valAt x (f * g) = valAt x f * valAt x g := by
  cases x with
  | none => exact valInfty_mul f g
  | some a => exact val_mul hf hg hfx hgx

omit [IsAlgClosed k] [DecidableEq k] in
lemma valAt_ne_zero {x : Option k} {f : RatFunc k} (hf : f ≠ 0) (hfx : ordFun f x = 0) :
    valAt x f ≠ 0 := by
  cases x with
  | none => exact valInfty_ne_zero hf
  | some a => exact val_ne_zero hf hfx

omit [IsAlgClosed k] [DecidableEq k] in
lemma valAt_C (x : Option k) (c : k) : valAt x (RatFunc.C c) = c := by
  cases x with
  | none => simp [valAt, valInfty, RatFunc.num_C]
  | some a => simp [valAt, val, RatFunc.num_C, RatFunc.denom_C]

variable {D : Type*} (ι : D → Option k)

/-- The affine cusps `e d ∈ k ⊆ ℙ¹(k)`. -/
def cusps (e : D → k) : D → Option k := fun d => some (e d)

lemma ordFun_eq_zero_of_mem {f : (RatFunc k)ˣ} (hf : f ∈ (curveData (k := k)).unitsAt ι)
    (d : D) : ordFun (f : RatFunc k) (ι d) = 0 := hf d

/-- The values at the cusps (which may include `∞`). -/
def ev : (curveData (k := k)).unitsAt ι →* (D → kˣ) where
  toFun f d := Units.mk0 (valAt (ι d) ((f : (RatFunc k)ˣ) : RatFunc k))
    (valAt_ne_zero (f : (RatFunc k)ˣ).ne_zero (ordFun_eq_zero_of_mem ι f.2 d))
  map_one' := by
    ext d
    simpa using valAt_C (ι d) 1
  map_mul' f g := by
    ext d
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0, Pi.mul_apply]
    exact valAt_mul (f : (RatFunc k)ˣ).ne_zero (g : (RatFunc k)ˣ).ne_zero
      (ordFun_eq_zero_of_mem ι f.2 d) (ordFun_eq_zero_of_mem ι g.2 d)

variable [Finite D]

omit [DecidableEq k] in
/-- **The approximation theorem on `ℙ¹`**: for finitely many distinct points `ι d` of `ℙ¹`
(possibly including `∞`) and values `t d ∈ k^×`, there is a rational function regular and
invertible at every `ι d` with value `t d` there. Writing `s` for the affine cusps `a_d` and
`t_∞` for the prescribed value at `∞` (or `1`), the function is `p / (X - b)^{#s}` with
`p = L + t_∞ ∏_{d ∈ s} (X - a_d)`, `L` the Lagrange interpolation of `t_d (a_d - b)^{#s}` and
`b` any point different from the `a_d`. -/
theorem exists_valAt_eq (hι : Function.Injective ι) (t : D → kˣ) :
    ∃ f : RatFunc k, f ≠ 0 ∧ ∀ d, ordFun f (ι d) = 0 ∧ valAt (ι d) f = t d := by
  classical
  have := Fintype.ofFinite D
  set s : Finset D := Finset.univ.filter fun d => (ι d).isSome
  set v : D → k := fun d => (ι d).getD 0
  have hsv : ∀ d ∈ s, ι d = some (v d) := by
    intro d hd
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hd
    simp [v, ha]
  have hinj : Set.InjOn v s := fun d hd d' hd' h =>
    hι (by rw [hsv d hd, hsv d' hd', h])
  set tinf : kˣ := if h : ∃ d, ι d = none then t h.choose else 1
  have htinf : ∀ d, ι d = none → tinf = t d := by
    intro d hd
    have h : ∃ d, ι d = none := ⟨d, hd⟩
    simp only [tinf, dif_pos h]
    rw [hι (h.choose_spec.trans hd.symm)]
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (s.image v)
  have hbv : ∀ d ∈ s, v d - b ≠ 0 := fun d hd h =>
    hb (Finset.mem_image.mpr ⟨d, hd, sub_eq_zero.mp h⟩)
  set q : k[X] := (X - C b) ^ s.card
  have hqv : ∀ d ∈ s, q.eval (v d) ≠ 0 := fun d hd => by
    simp only [q, eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero _ (hbv d hd)
  have hqm : q.Monic := (monic_X_sub_C b).pow _
  have hqd : q.natDegree = s.card := by simp [q, natDegree_pow]
  set L := Lagrange.interpolate s v (fun d => (t d : k) * q.eval (v d))
  have hL : L.degree < s.card := Lagrange.degree_interpolate_lt _ hinj
  set N := Lagrange.nodal s v
  have hNd : (C (tinf : k) * N).degree = s.card := by
    rw [degree_C_mul tinf.ne_zero, Lagrange.degree_nodal]
  set p := L + C (tinf : k) * N
  have hpd : p.degree = s.card := by
    rw [degree_add_eq_right_of_degree_lt (hL.trans_eq hNd.symm), hNd]
  have hp0 : p ≠ 0 := fun h => by simp [h] at hpd
  have hplc : p.leadingCoeff = tinf := by
    rw [leadingCoeff_add_of_degree_lt (hL.trans_eq hNd.symm), leadingCoeff_C_mul_of_isUnit
      tinf.isUnit, (Lagrange.nodal_monic).leadingCoeff, mul_one]
  have hpv : ∀ d ∈ s, p.eval (v d) = t d * q.eval (v d) := by
    intro d hd
    simp only [p, N, L, eval_add, eval_mul, eval_C, Lagrange.eval_nodal_at_node hd, mul_zero,
      add_zero]
    exact Lagrange.eval_interpolate_at_node _ hinj hd
  have hq0 : q ≠ 0 := hqm.ne_zero
  refine ⟨algebraMap _ _ p / algebraMap _ _ q,
    div_ne_zero (RatFunc.algebraMap_ne_zero hp0) (RatFunc.algebraMap_ne_zero hq0), fun d => ?_⟩
  by_cases hd : d ∈ s
  · have hpa : p.eval (v d) ≠ 0 := by
      rw [hpv d hd]; exact mul_ne_zero (t d).ne_zero (hqv d hd)
    obtain ⟨h1, h2⟩ := val_div hpa (hqv d hd)
    rw [hsv d hd]
    refine ⟨h1, ?_⟩
    change val _ _ = _
    rw [h2, hpv d hd, mul_div_cancel_right₀ _ (hqv d hd)]
  · have hnone : ι d = none := by
      simpa [s] using hd
    rw [hnone]
    refine ⟨?_, ?_⟩
    · change ordInfty _ = 0
      rw [ordInfty_div hp0 hq0, hqd, natDegree_eq_of_degree_eq_some hpd, sub_self]
    · change valInfty _ = _
      rw [valInfty_div hq0, hplc, hqm.leadingCoeff, div_one, htinf d hnone]

/-- **The values at finitely many cusps of `ℙ¹` (possibly including `∞`) satisfy the
interface**: the approximation theorem is `exists_valAt_eq`. -/
def boundaryEvaluation (hι : Function.Injective ι) :
    BoundaryEvaluation (curveData (k := k)) ι where
  ev := ev ι
  ev_const c hc := by
    ext d
    change valAt (ι d) (algebraMap k (RatFunc k) c) = c
    rw [RatFunc.algebraMap_eq_C, valAt_C]
  ev_surjective t := by
    obtain ⟨f, hf, hft⟩ := exists_valAt_eq ι hι t
    refine ⟨⟨Units.mk0 f hf, fun d => (hft d).1⟩, funext fun d => Units.ext ?_⟩
    exact (hft d).2

omit [Field k] [DecidableEq k] [IsAlgClosed k] [Finite D] in
lemma cusps_injective {e : D → k} (he : Function.Injective e) : Function.Injective (cusps e) :=
  (Option.some_injective k).comp he

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

omit [Finite D] in
/-- **`J(k) = 0` for `ℙ¹`**: every degree-zero divisor supported away from the cusps is the
divisor of a function invertible at the cusps. -/
theorem jac_eq_zero (z : (curveData (k := k)).Jac ι) : z = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [QuotientAddGroup.eq_zero_iff]
  have hdiv : divHom (linComb (x : Option k →₀ ℤ)) = x := by
    rw [divHom_linComb, x.2.1, Finsupp.single_zero, sub_zero]
  have hmem : (linComb (x : Option k →₀ ℤ)).toMul ∈ (curveData (k := k)).unitsAt ι :=
    fun d => by
      change divHom (linComb (x : Option k →₀ ℤ)) _ = 0
      rw [hdiv]
      exact x.2.2 d
  exact ⟨.ofMul ⟨_, hmem⟩, Subtype.ext hdiv⟩

variable (hι : Function.Injective ι)

/-- **The generalized Jacobian of `ℙ¹ ∖ D` is the boundary torus**: `T_Y(k) ≅ J_D(k)` for
finitely many cusps, which may include `∞`. -/
def torusEquivGenJac :
    boundaryTorus D k ≃* Multiplicative (boundaryEvaluation ι hι).GenJac :=
  MulEquiv.ofBijective (boundaryEvaluation ι hι).torusToGenJac
    ⟨(boundaryEvaluation ι hι).torusToGenJac_injective, fun x => by
      obtain ⟨τ, hτ⟩ := ((boundaryEvaluation ι hι).genJacToJac_eq_zero_iff x.toAdd).mp
        (jac_eq_zero ι _)
      exact ⟨τ, hτ⟩⟩

end ProjectiveLine


end GeneralizedAlbanese

end
