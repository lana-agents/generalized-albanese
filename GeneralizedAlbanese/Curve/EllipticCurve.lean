/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Curve.GeneralizedJacobian
import EllipticCurves.FunctionField.PlaceResidueDegree
import EllipticCurves.FunctionField.PlaceOrder
import EllipticCurves.FunctionField.DivisorPrincipality
import EllipticCurves.FunctionField.RationalPointDegree
import Mathlib

/-!
# Elliptic curves as an instance of the divisor-theory interface

Let `E : W` be an elliptic curve in Weierstrass form over an algebraically closed field `k`, with
coordinate ring `k[W]`, function field `k(W)` and closed points
`ProjPoint W = Option (HeightOneSpectrum k[W])` (`none` is the origin `O`). The divisor theory of
`k(W)` is that of the `elliptic-curves` repository (`divisorProj`, the places `placeOf`, their
residue fields), and Mathlib's `Point.toClass` identifies `E(k)` with a subgroup of the class group
of `k[W]`.

We show:

* `curveData`: `E` satisfies `CurveDivisorData` (functions without zeros and poles are constant,
  principal divisors have degree zero — every closed point has degree one over `k = k̄`);
* `boundaryEvaluation`: for every finite set of cusps `ι : D ↪ ProjPoint W` (which may contain the
  origin), the values at the cusps satisfy `BoundaryEvaluation`; the approximation theorem
  (`exists_valAt_eq`) is the Chinese remainder theorem in the Dedekind domain `k[W]`, with a
  denominator `1 + g h` of large pole order at `O`;
* `jacEquivPoint`: **`J(k) ≅ E(k)`** for `Y = E ∖ D`, compatible with the Abel–Jacobi map
  `[Q] - [R] ↦ Q - R` (`jacEquivPoint_mk`); the proof compares both sides inside `Cl(k[W])`
  (via `classOfDivisor` and `toClass`) and moves points off the cusps using that `E(k)` is
  infinite;
* `genJacToPoint_surjective`, `genJacToPoint_eq_zero_iff`, with
  `BoundaryEvaluation.torusToGenJac_injective`: the exact sequence
  `0 → T_Y(k) → J_D(k) → E(k) → 0` of the generalized Jacobian of `Y = E ∖ D`.
-/

noncomputable section

open Polynomial IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

namespace GeneralizedAlbanese

namespace EllipticCurve

variable {k : Type*} [Field k] [IsAlgClosed k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]

/-! ### Divisors -/

/-- Every closed point of `E` is a rational point: its maximal ideal is `⟨X - a, Y - b⟩`. -/
theorem exists_eq_pointClosedPoint (v : HeightOneSpectrum W.CoordinateRing) :
    ∃ (a b : k) (h : W.Nonsingular a b), v = pointClosedPoint h.left := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨a, b, hab, hv⟩ :=
    CoordinateRing.exists_equation_and_eq_XYIdeal_of_isMaximal (W := W) v.asIdeal
  have hns : W.Nonsingular a b := equation_iff_nonsingular.mp hab
  exact ⟨a, b, hns, HeightOneSpectrum.ext (by simpa using hv)⟩

/-- Every closed point of `E` has degree one. -/
theorem degProjPt_eq_one (p : ProjPoint W) : degProjPt W p = 1 := by
  cases p with
  | none => exact degProjPt_none
  | some v =>
    obtain ⟨a, b, h, rfl⟩ := exists_eq_pointClosedPoint W v
    exact degPt_pointClosedPoint h

theorem boundaryDegree_eq_degProj (x : ProjPoint W →₀ ℤ) :
    boundaryDegree _ x = degProj W x := by
  simp [boundaryDegree_apply, degProj, degProjPt_eq_one]

/-- The divisor map `k(W)^× → Div(E)`. -/
def divHom : Additive W.FunctionFieldˣ →+ (ProjPoint W →₀ ℤ) where
  toFun f := divisorProj W (f.toMul : W.FunctionField)
  map_zero' := divisorProj_one
  map_add' f g := by
    simp only [toMul_add, Units.val_mul]
    exact divisorProj_mul f.toMul.ne_zero g.toMul.ne_zero

/-- **`E` satisfies the divisor-theory interface.** -/
def curveData : CurveDivisorData k W.FunctionField (ProjPoint W) where
  div := divHom W
  div_eq_zero_iff f := by
    change divisorProj W (f : W.FunctionField) = 0 ↔ _
    rw [divisorProj_eq_zero_iff f.ne_zero]
    constructor
    · rintro ⟨c, hc, hf⟩
      exact ⟨Units.mk0 c hc, Units.ext hf.symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.ne_zero, rfl⟩
  degree_div f := by
    rw [boundaryDegree_eq_degProj]
    exact degProj_divisorProj f.ne_zero

@[simp]
lemma curveData_div (f : W.FunctionFieldˣ) :
    (curveData W).div (.ofMul f) = divisorProj W (f : W.FunctionField) := rfl

/-! ### Values at closed points -/

/-- The residue field of every closed point is `k`. -/
def residueEquiv (p : ProjPoint W) : k ≃+* residueFieldProj W p :=
  RingEquiv.ofBijective (algebraMap k _) (algebraMap_residueFieldProj_bijective p)

open Classical in
/-- The value at `p` of a function regular at `p` (and `0` otherwise). -/
def valAt (p : ProjPoint W) (f : W.FunctionField) : k :=
  if h : f ∈ placeOf W p then (residueEquiv W p).symm (IsLocalRing.residue _ ⟨f, h⟩) else 0

variable {W}

lemma algebraMap_valAt {p : ProjPoint W} {f : W.FunctionField} (h : f ∈ placeOf W p) :
    algebraMap k (residueFieldProj W p) (valAt W p f) =
      IsLocalRing.residue _ (⟨f, h⟩ : placeOf W p) := by
  rw [valAt, dif_pos h]
  exact (residueEquiv W p).apply_symm_apply _

lemma valAt_eq_iff {p : ProjPoint W} {f : W.FunctionField} (h : f ∈ placeOf W p) (c : k) :
    valAt W p f = c ↔ IsLocalRing.residue _ (⟨f, h⟩ : placeOf W p) = algebraMap k _ c := by
  rw [← (algebraMap_residueFieldProj_bijective p).1.eq_iff, algebraMap_valAt h]

omit [IsAlgClosed k] in
lemma mem_placeOf {p : ProjPoint W} {f : W.FunctionField} (hf : f ≠ 0)
    (h : divisorProj W f p = 0) : f ∈ placeOf W p :=
  (mem_placeOf_iff_divisorProj_nonneg p hf).2 h.ge

lemma valAt_mul {p : ProjPoint W} {f g : W.FunctionField} (hf : f ∈ placeOf W p)
    (hg : g ∈ placeOf W p) : valAt W p (f * g) = valAt W p f * valAt W p g := by
  rw [valAt_eq_iff (mul_mem hf hg), map_mul, algebraMap_valAt hf, algebraMap_valAt hg, ← map_mul]
  rfl

lemma valAt_algebraMap (p : ProjPoint W) (c : k) :
    valAt W p (algebraMap k W.FunctionField c) = c := by
  rw [valAt_eq_iff (algebraMap_mem_placeOf p c)]
  rfl

lemma valAt_ne_zero {p : ProjPoint W} {f : W.FunctionField} (hf : f ≠ 0)
    (h : divisorProj W f p = 0) : valAt W p f ≠ 0 := by
  intro hv
  have hm := mem_placeOf hf h
  have hu : IsUnit (⟨f, hm⟩ : placeOf W p) := (isUnit_placeOf_iff _).2 ⟨hf, h⟩
  have := algebraMap_valAt hm
  rw [hv, map_zero] at this
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu this.symm

/-- A function whose residue at `p` is a nonzero constant `c` is invertible at `p` with value
`c`. -/
lemma of_residue_eq {p : ProjPoint W} (x : placeOf W p) {c : k} (hc : c ≠ 0)
    (hx : IsLocalRing.residue _ x = algebraMap k _ c) :
    (x : W.FunctionField) ≠ 0 ∧ divisorProj W (x : W.FunctionField) p = 0 ∧
      valAt W p x = c := by
  have hu : IsUnit x := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hx]
    exact (_root_.map_ne_zero _).2 hc
  obtain ⟨h1, h2⟩ := (isUnit_placeOf_iff x).1 hu
  exact ⟨h1, h2, (valAt_eq_iff x.2 c).2 hx⟩

omit [IsAlgClosed k] in
/-- If `f - c` vanishes at `p`, then `f` is regular at `p` with residue `c`. -/
lemma exists_residue_of_sub {p : ProjPoint W} {f : W.FunctionField} (c : k)
    (h : f - algebraMap k _ c = 0 ∨ 0 < divisorProj W (f - algebraMap k _ c) p) :
    ∃ x : placeOf W p, (x : W.FunctionField) = f ∧
      IsLocalRing.residue _ x = algebraMap k _ c := by
  set g := f - algebraMap k W.FunctionField c with hg
  obtain ⟨y, hy, hy0⟩ : ∃ y : placeOf W p, (y : W.FunctionField) = g ∧
      IsLocalRing.residue _ y = 0 := by
    rcases h with h | h
    · exact ⟨0, h.symm, map_zero _⟩
    · have hg0 : g ≠ 0 := fun h0 => by simp [h0] at h
      have hmem : g ∈ placeOf W p := (mem_placeOf_iff_divisorProj_nonneg p hg0).2 h.le
      exact ⟨⟨g, hmem⟩, rfl, (IsLocalRing.residue_eq_zero_iff _).2
        ((mem_maximalIdeal_placeOf_iff (x := ⟨g, hmem⟩) hg0).2 h)⟩
  refine ⟨y + algebraMap k (placeOf W p) c, ?_, ?_⟩
  · change (y : W.FunctionField) + algebraMap k W.FunctionField c = f
    rw [hy, hg, sub_add_cancel]
  · rw [map_add, hy0, zero_add]
    rfl

omit [IsAlgClosed k] in
/-- At an affine point `v`: if `b ≡ 1` and `a ≡ c` modulo `v`, then `a / b` is regular at `v`
with residue `c`. -/
lemma exists_residue_div (v : HeightOneSpectrum W.CoordinateRing) {a b : W.CoordinateRing}
    (c : k) (hb : b - 1 ∈ v.asIdeal) (ha : a - algebraMap k _ c ∈ v.asIdeal) :
    ∃ x : placeOf W (some v), (x : W.FunctionField) =
        algebraMap _ W.FunctionField a / algebraMap _ W.FunctionField b ∧
      IsLocalRing.residue _ x = algebraMap k _ c := by
  have hkey : ∀ {z w : W.CoordinateRing}, z - w ∈ v.asIdeal →
      residueHomSome v z = residueHomSome v w := by
    intro z w h
    rw [← sub_eq_zero, ← map_sub]
    have : z - w ∈ RingHom.ker ((residueHomSome v).toRingHom :
        W.CoordinateRing →+* residueFieldProj W (some v)) := by
      rw [ker_residueHomSome]; exact h
    exact this
  have hB : residueHomSome v b = 1 := by rw [hkey hb, map_one]
  have hA : residueHomSome v a = algebraMap k _ c := by rw [hkey ha, AlgHom.commutes]
  set A := algebraMap W.CoordinateRing (placeOf W (some v)) a
  set B := algebraMap W.CoordinateRing (placeOf W (some v)) b
  have hBu : IsUnit B := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← residueHomSome_apply, hB]
    exact one_ne_zero
  have hcoe : ∀ z : W.CoordinateRing, ((algebraMap W.CoordinateRing (placeOf W (some v)) z :
      placeOf W (some v)) : W.FunctionField) = algebraMap _ W.FunctionField z := fun z => by
    rw [IsScalarTower.algebraMap_apply W.CoordinateRing (placeOf W (some v)) W.FunctionField]
    rfl
  have hinv : ((↑hBu.unit⁻¹ : placeOf W (some v)) : W.FunctionField) =
      (algebraMap _ W.FunctionField b)⁻¹ := by
    rw [← hcoe b]
    refine (eq_inv_of_mul_eq_one_right ?_)
    have h2 : ((B * ↑hBu.unit⁻¹ : placeOf W (some v)) : W.FunctionField) = 1 := by
      rw [hBu.mul_val_inv]; rfl
    rwa [MulMemClass.coe_mul] at h2
  refine ⟨A * ↑hBu.unit⁻¹, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, hcoe a, hinv, div_eq_mul_inv]
  · have h1 : IsLocalRing.residue _ (↑hBu.unit⁻¹ : placeOf W (some v)) = 1 := by
      have := congrArg (IsLocalRing.residue (placeOf W (some v))) hBu.mul_val_inv
      rw [map_mul, map_one] at this
      change residueHomSome v b * _ = 1 at this
      rwa [hB, one_mul] at this
    rw [map_mul, h1, mul_one]
    exact hA

/-! ### The approximation theorem -/

omit [IsAlgClosed k] [W.IsElliptic] in
lemma deg_one_add {y : W.CoordinateRing} (hy : 0 < deg W y) : deg W (1 + y) = deg W y := by
  apply le_antisymm
  · calc deg W (1 + y) ≤ max (deg W 1) (deg W y) := deg_add_le _ _
      _ = deg W y := by rw [deg_one]; exact max_eq_right (Nat.zero_le _)
  · have h1 : deg W (-1 : W.CoordinateRing) = 0 := by
      rw [show (-1 : W.CoordinateRing) = algebraMap k _ (-1) by simp]
      exact deg_algebraMap _
    have h := deg_add_le (1 + y) (-1 : W.CoordinateRing)
    rw [h1, show 1 + y + -1 = y by ring] at h
    rw [max_def] at h
    split_ifs at h <;> omega

variable {D : Type*} (ι : D → ProjPoint W)

/-- The ideal of the affine part of a closed point (`⊤` at the origin). -/
def affIdeal : ProjPoint W → Ideal W.CoordinateRing
  | none => ⊤
  | some v => v.asIdeal

/-- **The approximation theorem on `E`**: for finitely many distinct closed points `ι d`
(possibly including the origin) and values `t d ∈ k^×`, there is a function regular and
invertible at every `ι d` with value `t d` there.

With `t_O` the value prescribed at the origin (or `1`), the function is `t_O + r / b` where
`r ≡ t_d - t_O` modulo the affine cusps (Chinese remainder theorem in `k[W]`) and
`b = 1 + g h` with `g` vanishing at the affine cusps and `h = x^N` making the pole order of `b`
at `O` larger than that of `r`. -/
theorem exists_valAt_eq [Finite D] (hι : Function.Injective ι) (t : D → kˣ) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      ∀ d, divisorProj W f (ι d) = 0 ∧ valAt W (ι d) f = t d := by
  classical
  have := Fintype.ofFinite D
  set s : Finset D := Finset.univ.filter fun d => (ι d).isSome
  have hs : ∀ d, d ∈ s ↔ ∃ v, ι d = some v := fun d => by
    simp [s, Option.isSome_iff_exists]
  set tinf : kˣ := if h : ∃ d, ι d = none then t h.choose else 1
  have htinf : ∀ d, ι d = none → tinf = t d := by
    intro d hd
    have h : ∃ d, ι d = none := ⟨d, hd⟩
    simp only [tinf, dif_pos h]
    rw [hι (h.choose_spec.trans hd.symm)]
  set P : D → Ideal W.CoordinateRing := fun d => affIdeal (ι d)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) P (fun _ => 1)
    (fun d hd => by
      obtain ⟨v, hv⟩ := (hs d).1 hd
      simp only [P, hv, affIdeal]
      exact v.prime)
    (fun d hd d' hd' hne h => by
      obtain ⟨v, hv⟩ := (hs d).1 hd
      obtain ⟨v', hv'⟩ := (hs d').1 hd'
      simp only [P, hv, hv', affIdeal] at h
      exact hne (hι (by rw [hv, hv', HeightOneSpectrum.ext h])))
    (fun d : s => algebraMap k W.CoordinateRing ((t d : k) - tinf))
  have hP : ∀ d, ∃ g ∈ P d, g ≠ 0 := by
    intro d
    simp only [P]
    cases ι d with
    | none => exact ⟨1, Submodule.mem_top, one_ne_zero⟩
    | some v => exact Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose gd hgd hgd0 using hP
  set g := ∏ d, gd d
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.2 fun d _ => hgd0 d
  have hgP : ∀ d, g ∈ P d := fun d =>
    Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem gd (Finset.mem_univ d)) (hgd d)
  set h : W.CoordinateRing := mk W (C (X ^ (deg W r + 1)))
  have hh0 : h ≠ 0 := mk_C_ne_zero (pow_ne_zero _ X_ne_zero)
  have hdh : deg W h = 2 * (deg W r + 1) := by rw [deg_mk_C, natDegree_X_pow]
  set b : W.CoordinateRing := 1 + g * h
  have hdb : deg W b = deg W g + 2 * (deg W r + 1) := by
    rw [deg_one_add (by rw [deg_mul hg0 hh0, hdh]; omega), deg_mul hg0 hh0, hdh]
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, deg_zero] at hdb; omega
  have hinj := IsFractionRing.injective W.CoordinateRing W.FunctionField
  have hbK : algebraMap W.CoordinateRing W.FunctionField b ≠ 0 :=
    fun h0 => hb0 (hinj (by rw [h0, map_zero]))
  set a : W.CoordinateRing := algebraMap k _ (tinf : k) * b + r
  set f : W.FunctionField :=
    algebraMap _ W.FunctionField a / algebraMap _ W.FunctionField b
  have hfr : f - algebraMap k _ (tinf : k) =
      algebraMap _ W.FunctionField r / algebraMap _ W.FunctionField b := by
    simp only [f, a, map_add, map_mul, ← IsScalarTower.algebraMap_apply]
    field_simp
    ring
  obtain ⟨xinf, hxinf, hxinf'⟩ := exists_residue_of_sub (p := none) (f := f) (tinf : k) (by
    rw [hfr]
    by_cases hr0 : r = 0
    · left
      simp [hr0]
    · right
      have hq0 : algebraMap _ W.FunctionField r / algebraMap _ W.FunctionField b ≠ 0 :=
        div_ne_zero (fun h0 => hr0 (hinj (by rw [h0, map_zero]))) hbK
      rw [divisorProj_apply_none, ordInfty_eq_sub hq0 hb0 (div_mul_cancel₀ _ hbK), hdb]
      omega)
  obtain ⟨hf0, hinf1, hinf2⟩ := of_residue_eq xinf tinf.ne_zero hxinf'
  rw [hxinf] at hf0 hinf1 hinf2
  refine ⟨f, hf0, fun d => ?_⟩
  cases hd : ι d with
  | none => exact ⟨hinf1, hinf2.trans (congrArg _ (htinf d hd))⟩
  | some v =>
    have hds : d ∈ s := (hs d).2 ⟨v, hd⟩
    have hPv : P d = v.asIdeal := by simp [P, hd, affIdeal]
    have hgv : g ∈ v.asIdeal := hPv ▸ hgP d
    obtain ⟨x, hx, hx'⟩ := exists_residue_div v (t d : k) (a := a) (b := b)
      (by simp only [b, add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ hgv)
      (by
        have hrv := hr d hds
        rw [pow_one, hPv] at hrv
        have e : a - algebraMap k _ (t d : k) = algebraMap k _ (tinf : k) * (g * h) +
            (r - algebraMap k W.CoordinateRing ((t d : k) - tinf)) := by
          simp only [a, b, map_sub]
          ring
        rw [e]
        exact add_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hgv)) hrv)
    obtain ⟨-, h1, h2⟩ := of_residue_eq x (t d).ne_zero hx'
    rw [hx] at h1 h2
    exact ⟨h1, h2⟩

/-- The values at the cusps (which may include the origin). -/
def ev : (curveData W).unitsAt ι →* (D → kˣ) where
  toFun f d := Units.mk0 (valAt W (ι d) ((f : W.FunctionFieldˣ) : W.FunctionField))
    (valAt_ne_zero (f : W.FunctionFieldˣ).ne_zero (f.2 d))
  map_one' := by
    ext d
    simpa using valAt_algebraMap (ι d) (1 : k)
  map_mul' f g := by
    ext d
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0, Pi.mul_apply]
    exact valAt_mul (mem_placeOf (f : W.FunctionFieldˣ).ne_zero (f.2 d))
      (mem_placeOf (g : W.FunctionFieldˣ).ne_zero (g.2 d))

/-- **The values at finitely many cusps of `E` (possibly including the origin) satisfy the
interface.** -/
def boundaryEvaluation [Finite D] (hι : Function.Injective ι) :
    BoundaryEvaluation (curveData W) ι where
  ev := ev ι
  ev_const c hc := by
    ext d
    exact valAt_algebraMap (ι d) c
  ev_surjective t := by
    obtain ⟨f, hf, hft⟩ := exists_valAt_eq ι hι t
    exact ⟨⟨Units.mk0 f hf, fun d => (hft d).1⟩, funext fun d => Units.ext (hft d).2⟩

/-! ### `J(k) ≅ E(k)` -/

section Jacobian

variable [DecidableEq k]

omit [DecidableEq k] in
variable (W) in
/-- `E(k)` is infinite: every `x ∈ k` is the abscissa of a point. -/
theorem infinite_point : Infinite W.Point := by
  have hx : ∀ x : k, ∃ y, W.Equation x y := by
    intro x
    set q : k[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    have hq : q.degree = 2 := by simp only [q]; compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hq]; norm_num)
    refine ⟨y, (equation_iff x y).2 ?_⟩
    simp only [q, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy
    linear_combination hy
  choose y hy using hx
  refine Infinite.of_injective (fun x => Point.mk (hy x)) fun x x' h => ?_
  simp only [Point.mk, Point.some.injEq] at h
  exact h.1

variable (W) in
/-- The affine part of a divisor on `E`. -/
def affPart : (ProjPoint W →₀ ℤ) →+ (HeightOneSpectrum W.CoordinateRing →₀ ℤ) :=
  Finsupp.comapDomain.addMonoidHom (Option.some_injective _)

omit [IsAlgClosed k] [DecidableEq k] in
@[simp]
lemma affPart_apply (x : ProjPoint W →₀ ℤ) (v : HeightOneSpectrum W.CoordinateRing) :
    affPart W x v = x (some v) := rfl

omit [IsAlgClosed k] [DecidableEq k] in
lemma affPart_divisorProj (f : W.FunctionField) :
    affPart W (divisorProj W f) = divisor W f := by
  ext v
  simp [divisor_apply]

variable (W) in
/-- The class in `Cl(k[W])` of an affine divisor. -/
def classMap :
    (HeightOneSpectrum W.CoordinateRing →₀ ℤ) →+ Additive (ClassGroup W.CoordinateRing) :=
  AddMonoidHom.mk' (fun x => Additive.ofMul (classOfDivisor W.FunctionField x)) fun x y => by
    rw [classOfDivisor_add, ofMul_mul]

omit [IsAlgClosed k] in
lemma classMap_single {x y : k} (h : W.Nonsingular x y) :
    classMap W (Finsupp.single (pointClosedPoint h.left) 1) = Point.toClass (Point.some x y h) :=
  (congrArg Additive.ofMul (classOfDivisor_single_pointClosedPoint h)).trans (ofMul_toMul _)

variable (W) in
/-- The closed point of `E` underlying a point of `E(k)` (`O ↦ none`). -/
def toProj : W.Point → ProjPoint W
  | .zero => none
  | .some _ _ h => some (pointClosedPoint h.left)

omit [IsAlgClosed k] in
lemma classMap_affPart_single (Q : W.Point) :
    classMap W (affPart W (Finsupp.single (toProj W Q) 1)) = Point.toClass Q := by
  cases Q with
  | zero =>
    have : affPart W (Finsupp.single (toProj W .zero) 1) = 0 := by
      ext v
      simp [toProj]
    rw [this, map_zero]
    rfl
  | some x y h =>
    have : affPart W (Finsupp.single (toProj W (.some x y h)) 1) =
        Finsupp.single (pointClosedPoint h.left) 1 := by
      ext v
      exact Finsupp.single_apply_left (Option.some_injective _) _ _ _
    rw [this, classMap_single]

omit [IsAlgClosed k] [DecidableEq k] in
lemma toProj_injective : Function.Injective (toProj W) := by
  classical
  intro Q R h
  apply Point.toClass_injective
  rw [← classMap_affPart_single, ← classMap_affPart_single, h]

lemma classMap_mem_range (y : HeightOneSpectrum W.CoordinateRing →₀ ℤ) :
    classMap W y ∈ (Point.toClass (W := W)).range := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add y z hy hz => rw [map_add]; exact add_mem hy hz
  | single v n =>
    obtain ⟨a, b, h, rfl⟩ := exists_eq_pointClosedPoint W v
    have e : Finsupp.single (pointClosedPoint h.left) n =
        n • Finsupp.single (pointClosedPoint h.left) 1 := by simp
    rw [e, map_zsmul]
    exact zsmul_mem (AddMonoidHom.mem_range.2 ⟨_, (classMap_single h).symm⟩) n

/-- The comparison `J(k) → Cl(k[W])`: the class of the affine part of a divisor. -/
def jacToClass : (curveData W).Jac ι →+ Additive (ClassGroup W.CoordinateRing) :=
  QuotientAddGroup.lift _ (((classMap W).comp (affPart W)).comp (div0Y ι).subtype) (by
    rintro _ ⟨f, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change classMap W (affPart W (divisorProj W ((f.toMul : W.FunctionFieldˣ) :
      W.FunctionField))) = 0
    rw [affPart_divisorProj]
    change Additive.ofMul _ = 0
    rw [(exists_divisor_eq_iff_classOfDivisor_eq_one _).1
      ⟨_, (f.toMul : W.FunctionFieldˣ).ne_zero, rfl⟩]
    rfl)

omit [DecidableEq k] in
@[simp]
lemma jacToClass_mk (x : div0Y ι) :
    jacToClass ι (QuotientAddGroup.mk x) = classMap W (affPart W x) := rfl

omit [DecidableEq k] in
theorem jacToClass_injective : Function.Injective (jacToClass ι) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have h1 : classOfDivisor W.FunctionField (affPart W x) = 1 := hz
  obtain ⟨g, hg0, hg⟩ := (exists_divisor_eq_iff_classOfDivisor_eq_one _).2 h1
  have hgx : divisorProj W g = x := by
    set z := divisorProj W g - (x : ProjPoint W →₀ ℤ) with hz
    have hzs : z = Finsupp.single none (z none) := by
      ext p
      cases p with
      | none => simp
      | some v =>
        have := DFunLike.congr_fun hg v
        rw [← affPart_divisorProj, affPart_apply, affPart_apply] at this
        simp [z, this]
    have hdeg : boundaryDegree _ z = 0 := by
      rw [hz, map_sub, boundaryDegree_eq_degProj, degProj_divisorProj hg0, x.2.1, sub_zero]
    rw [hzs, boundaryDegree_single] at hdeg
    have : z = 0 := by rw [hzs, hdeg, Finsupp.single_zero]
    exact sub_eq_zero.mp this
  rw [QuotientAddGroup.eq_zero_iff]
  refine ⟨.ofMul ⟨Units.mk0 g hg0, fun d => ?_⟩, Subtype.ext hgx⟩
  change divisorProj W g (ι d) = 0
  rw [hgx]
  exact x.2.2 d

omit [IsAlgClosed k] [DecidableEq k] in
lemma single_sub_single_mem_div0Y {Q R : W.Point} (hQ : toProj W Q ∉ Set.range ι)
    (hR : toProj W R ∉ Set.range ι) :
    Finsupp.single (toProj W Q) 1 - Finsupp.single (toProj W R) 1 ∈ div0Y ι := by
  refine ⟨by simp, fun d => ?_⟩
  have h1 : toProj W Q ≠ ι d := fun h => hQ ⟨d, h.symm⟩
  have h2 : toProj W R ≠ ι d := fun h => hR ⟨d, h.symm⟩
  simp [h1, h2]

lemma jacToClass_single_sub_single {Q R : W.Point} (hQ : toProj W Q ∉ Set.range ι)
    (hR : toProj W R ∉ Set.range ι) :
    jacToClass ι (QuotientAddGroup.mk ⟨_, single_sub_single_mem_div0Y ι hQ hR⟩) =
      Point.toClass (Q - R) := by
  rw [jacToClass_mk, map_sub]
  simp only [map_sub, classMap_affPart_single]

/-- A point `Q` such that neither `Q` nor `Q - P` is a cusp. -/
lemma exists_point_avoiding [Finite D] (P : W.Point) :
    ∃ Q : W.Point, toProj W Q ∉ Set.range ι ∧ toProj W (Q - P) ∉ Set.range ι := by
  haveI := infinite_point W
  have h1 : (toProj W ⁻¹' Set.range ι).Finite :=
    (Set.finite_range ι).preimage (toProj_injective).injOn
  have h2 : ((fun Q => toProj W (Q - P)) ⁻¹' Set.range ι).Finite :=
    (Set.finite_range ι).preimage ((toProj_injective).comp (sub_left_injective)).injOn
  obtain ⟨Q, hQ⟩ := (h1.union h2).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_preimage] at hQ
  exact ⟨Q, hQ⟩

theorem range_jacToClass [Finite D] :
    (jacToClass ι).range = (Point.toClass (W := W)).range := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact classMap_mem_range _
  · rintro _ ⟨P, rfl⟩
    obtain ⟨Q, hQ, hQP⟩ := exists_point_avoiding ι P
    refine ⟨QuotientAddGroup.mk ⟨_, single_sub_single_mem_div0Y ι hQ hQP⟩,
      (jacToClass_single_sub_single ι hQ hQP).trans ?_⟩
    rw [sub_sub_cancel]

/-- **`J(k) ≅ E(k)`** for `Y = E ∖ D`: degree-zero divisors supported on `Y` modulo divisors of
functions invertible at the cusps form the group of points of `E`. -/
def jacEquivPoint [Finite D] : (curveData W).Jac ι ≃+ W.Point :=
  (AddMonoidHom.ofInjective (jacToClass_injective ι)).trans
    ((AddEquiv.addSubgroupCongr (range_jacToClass ι)).trans
      (AddMonoidHom.ofInjective (Point.toClass_injective (W := W))).symm)

lemma toClass_jacEquivPoint [Finite D] (z : (curveData W).Jac ι) :
    Point.toClass (jacEquivPoint ι z) = jacToClass ι z := by
  set e := AddMonoidHom.ofInjective (Point.toClass_injective (W := W))
  have := AddMonoidHom.ofInjective_apply (Point.toClass_injective (W := W))
    (x := jacEquivPoint ι z)
  rw [← this]
  change ((e (e.symm _) : Additive (ClassGroup W.CoordinateRing))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- **The Abel–Jacobi map**: `jacEquivPoint` sends the class of `[Q] - [R]` (`Q`, `R` not
cusps) to `Q - R`. -/
theorem jacEquivPoint_mk [Finite D] {Q R : W.Point} (hQ : toProj W Q ∉ Set.range ι)
    (hR : toProj W R ∉ Set.range ι) :
    jacEquivPoint ι (QuotientAddGroup.mk ⟨_, single_sub_single_mem_div0Y ι hQ hR⟩) = Q - R := by
  apply Point.toClass_injective
  rw [toClass_jacEquivPoint, jacToClass_single_sub_single ι hQ hR]

variable (W) in
/-- **`Pic⁰(E) ≅ E(k)`**: the case without cusps, where the moving lemma is vacuous. -/
def picEquivPoint : (curveData W).Pic0 ≃+ W.Point :=
  ((curveData W).jacEquivPic (PEmpty.elim : PEmpty.{1} → ProjPoint W)
    fun _ => ⟨1, fun d => d.elim⟩).symm.trans (jacEquivPoint _)

/-! ### The exact sequence `0 → T_Y(k) → J_D(k) → E(k) → 0` -/

variable [Finite D] (hι : Function.Injective ι)

/-- **`J_D(k) → E(k)`** for the generalized Jacobian of `Y = E ∖ D`. -/
def genJacToPoint : (boundaryEvaluation ι hι).GenJac →+ W.Point :=
  (jacEquivPoint ι).toAddMonoidHom.comp (boundaryEvaluation ι hι).genJacToJac

/-- `J_D(k) → E(k)` is surjective. -/
theorem genJacToPoint_surjective : Function.Surjective (genJacToPoint ι hι) :=
  (jacEquivPoint ι).surjective.comp (boundaryEvaluation ι hι).genJacToJac_surjective

/-- **Exactness at `J_D(k)`**: the kernel of `J_D(k) → E(k)` is the image of the boundary
torus `T_Y(k) = (k^×)^D / k^×`. Together with `torusToGenJac_injective` and
`genJacToPoint_surjective` this is `0 → T_Y(k) → J_D(k) → E(k) → 0`. -/
theorem genJacToPoint_eq_zero_iff (x : (boundaryEvaluation ι hι).GenJac) :
    genJacToPoint ι hι x = 0 ↔
      ∃ τ : boundaryTorus D k, ((boundaryEvaluation ι hι).torusToGenJac τ).toAdd = x := by
  rw [← (boundaryEvaluation ι hι).genJacToJac_eq_zero_iff]
  exact (jacEquivPoint ι).map_eq_zero_iff

omit [DecidableEq k] in
/-- `T_Y(k) → J_D(k)` is injective (the general `torusToGenJac_injective`). -/
theorem torusToGenJac_injective :
    Function.Injective (boundaryEvaluation ι hι).torusToGenJac :=
  (boundaryEvaluation ι hι).torusToGenJac_injective

end Jacobian

end EllipticCurve

end GeneralizedAlbanese

end
