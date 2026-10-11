/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Boundary divisors and the character lattice of the boundary torus

Let `Z` be a smooth projective variety over an algebraically closed field, `D ⊆ Z` a
normal-crossings divisor with irreducible components indexed by a type `D`, and `Y = Z ∖ D`.
The *boundary divisors* are the formal `ℤ`-combinations `D →₀ ℤ` of the components. The
generalized Albanese of `Y` is an extension `0 → T_Y → Alb(Y) → Alb(Z) → 0` of the Albanese of
`Z` by a torus `T_Y` whose character group is the group of boundary divisors algebraically
equivalent to zero, i.e. the kernel of the class map `(D →₀ ℤ) → NS(Z)`
(Serre, *Morphismes universels*; [AbsTopI, Appendix, Prop. A.8]).

This file provides the purely algebraic side:

* `GeneralizedAlbanese.characterLattice cl`: the kernel of a class map `cl : (D →₀ ℤ) →+ NS`;
* `GeneralizedAlbanese.boundaryDegree`, `GeneralizedAlbanese.boundaryChar`: the curve case, in
  which `NS(Z) = ℤ` via the degree and the character lattice is the group `Div⁰_D` of
  degree-zero boundary divisors;
* `GeneralizedAlbanese.charDual`: the pairing `(D → M) → Hom(Div⁰_D, M)`, and
  `GeneralizedAlbanese.charDualEquiv`: `Hom(Div⁰_D, M) ≃ (D → M) ⧸ M` (the diagonal), for every
  abelian group `M`. For `M = k^×` this is the description `T_Y(k) = (k^×)^D / k^×` of the
  points of the boundary torus, and for `M = ℤ_ℓ(1)` that of its Tate module;
* `GeneralizedAlbanese.boundaryCharEquiv`: `Div⁰_D ≃ ({d // d ≠ d₀} →₀ ℤ)`, so `Div⁰_D` is
  free of rank `#D - 1` and the boundary torus of a curve with `r ≥ 1` cusps has dimension
  `r - 1`.
-/

noncomputable section

namespace GeneralizedAlbanese

variable (D : Type*)

/-- The **character lattice** attached to a class map `cl : (D →₀ ℤ) →+ NS` from boundary
divisors to the Néron–Severi group of the compactification: the boundary divisors that are
algebraically equivalent to zero. It is the character group of the torus part `T_Y` of the
generalized Albanese of `Y = Z ∖ D`. -/
def characterLattice {NS : Type*} [AddCommGroup NS] (cl : (D →₀ ℤ) →+ NS) :
    AddSubgroup (D →₀ ℤ) :=
  cl.ker

/-- The **degree** of a boundary divisor (the class map of a connected curve, `NS = ℤ`). -/
def boundaryDegree : (D →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

variable {D}

@[simp]
lemma boundaryDegree_single (d : D) (n : ℤ) : boundaryDegree D (Finsupp.single d n) = n := by
  simp [boundaryDegree]

lemma boundaryDegree_apply (x : D →₀ ℤ) : boundaryDegree D x = x.sum fun _ n => n := by
  simp [boundaryDegree, Finsupp.liftAddHom_apply]
  rfl

variable (D)

/-- **`Div⁰_D`**: the degree-zero boundary divisors of a curve. This is the character lattice for
the degree map, i.e. the character group of the boundary torus of a punctured curve. -/
def boundaryChar : AddSubgroup (D →₀ ℤ) :=
  characterLattice D (boundaryDegree D)

variable {D}

lemma mem_boundaryChar {x : D →₀ ℤ} : x ∈ boundaryChar D ↔ boundaryDegree D x = 0 :=
  AddMonoidHom.mem_ker

lemma single_sub_single_mem_boundaryChar (d d' : D) :
    Finsupp.single d (1 : ℤ) - Finsupp.single d' 1 ∈ boundaryChar D := by
  simp [mem_boundaryChar]

/-- The retraction `x ↦ x - deg(x) • d₀` of `D →₀ ℤ` onto `Div⁰_D`. -/
def retraction (d₀ : D) : (D →₀ ℤ) →+ boundaryChar D where
  toFun x := ⟨x - Finsupp.single d₀ (boundaryDegree D x), by simp [mem_boundaryChar]⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp; abel

@[simp]
lemma coe_retraction (d₀ : D) (x : D →₀ ℤ) :
    (retraction d₀ x : D →₀ ℤ) = x - Finsupp.single d₀ (boundaryDegree D x) := rfl

lemma retraction_of_mem (d₀ : D) {x : D →₀ ℤ} (hx : x ∈ boundaryChar D) :
    retraction d₀ x = ⟨x, hx⟩ := by
  ext1; simp [mem_boundaryChar.mp hx]

/-! ### Duality: `Hom(Div⁰_D, M) = (D → M) ⧸ M` -/

variable (D) (M : Type*) [AddCommGroup M]

/-- The pairing `⟨f, x⟩ = ∑_d x_d • f d` of an `M`-valued function on the boundary components
with a boundary divisor. -/
def pairing (f : D → M) : (D →₀ ℤ) →+ M :=
  Finsupp.liftAddHom fun d => zmultiplesHom M (f d)

variable {D M}

lemma pairing_apply (f : D → M) (x : D →₀ ℤ) : pairing D M f x = x.sum fun d n => n • f d := by
  simp [pairing, Finsupp.liftAddHom_apply]
  rfl

@[simp]
lemma pairing_single (f : D → M) (d : D) (n : ℤ) : pairing D M f (Finsupp.single d n) = n • f d :=
  by simp [pairing_apply]

lemma pairing_add (f g : D → M) (x : D →₀ ℤ) :
    pairing D M (f + g) x = pairing D M f x + pairing D M g x := by
  simp [pairing_apply, smul_add, Finsupp.sum_add]

lemma pairing_const (m : M) (x : D →₀ ℤ) :
    pairing D M (fun _ => m) x = boundaryDegree D x • m := by
  simp only [pairing_apply, boundaryDegree_apply, Finsupp.sum, Finset.sum_smul]

variable (D M)

/-- The pairing of `M`-valued functions on the boundary components with `Div⁰_D`:
`f ↦ (x ↦ ∑ x_d • f d)`. -/
def charDual : (D → M) →+ (boundaryChar D →+ M) where
  toFun f := (pairing D M f).comp (boundaryChar D).subtype
  map_zero' := by ext; simp [pairing_apply]
  map_add' f g := by ext x; simp [pairing_add]

variable {D M}

lemma charDual_apply (f : D → M) (x : boundaryChar D) :
    charDual D M f x = pairing D M f x := rfl

/-- The **diagonal** `M ⊆ (D → M)` (constant functions). -/
def diagonal : AddSubgroup (D → M) := (Pi.constAddMonoidHom D M).range

lemma mem_diagonal {f : D → M} : f ∈ diagonal (D := D) ↔ ∃ m, f = fun _ => m := by
  simp [diagonal, eq_comm, funext_iff]

variable (D M)

/-- The kernel of the pairing is the diagonal: a function pairs trivially with `Div⁰_D` iff it is
constant. -/
theorem ker_charDual : (charDual D M).ker = diagonal := by
  ext f
  rw [AddMonoidHom.mem_ker, mem_diagonal]
  constructor
  · intro h
    rcases isEmpty_or_nonempty D with hD | ⟨⟨d₀⟩⟩
    · exact ⟨0, funext fun d => (IsEmpty.false d).elim⟩
    refine ⟨f d₀, funext fun d => ?_⟩
    have := DFunLike.congr_fun h ⟨_, single_sub_single_mem_boundaryChar d d₀⟩
    simpa [charDual_apply, sub_eq_zero] using this
  · rintro ⟨m, rfl⟩
    ext x
    rw [charDual_apply, AddMonoidHom.zero_apply, pairing_const, mem_boundaryChar.mp x.2,
      zero_smul]

/-- Every homomorphism `Div⁰_D → M` is induced by a function on the boundary components. -/
theorem charDual_surjective : Function.Surjective (charDual D M) := by
  intro φ
  rcases isEmpty_or_nonempty D with hD | ⟨⟨d₀⟩⟩
  · refine ⟨0, ?_⟩
    ext ⟨x, hx⟩
    obtain rfl : x = 0 := Subsingleton.elim _ _
    exact (map_zero φ).symm
  refine ⟨fun d => φ (retraction d₀ (Finsupp.single d 1)), ?_⟩
  have hψ : pairing D M (fun d => φ (retraction d₀ (Finsupp.single d 1))) =
      φ.comp (retraction d₀) := by
    ext d
    simp
  ext x
  rw [charDual_apply, hψ, AddMonoidHom.comp_apply, retraction_of_mem d₀ x.2]

/-- **`Hom(Div⁰_D, M) ≃ (D → M) ⧸ M`**: homomorphisms from the degree-zero boundary divisors to
`M` are functions on the boundary components modulo constants. For `M = k^×` these are the
`k`-points of the boundary torus `T_Y` of a punctured curve, `T_Y(k) = (k^×)^D / k^×`. -/
def charDualEquiv : (D → M) ⧸ (diagonal : AddSubgroup (D → M)) ≃+ (boundaryChar D →+ M) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_charDual D M).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (charDual_surjective D M))

@[simp]
lemma charDualEquiv_mk (f : D → M) :
    charDualEquiv D M (QuotientAddGroup.mk f) = charDual D M f := rfl

/-! ### `Div⁰_D` is free of rank `#D - 1` -/

variable {D}

/-- **`Div⁰_D ≃ ({d // d ≠ d₀} →₀ ℤ)`**: a degree-zero boundary divisor is determined by its
coefficients away from a fixed component `d₀`, and these are arbitrary. -/
def boundaryCharEquiv [DecidableEq D] (d₀ : D) : boundaryChar D ≃+ ({d // d ≠ d₀} →₀ ℤ) where
  toFun x := (x : D →₀ ℤ).subtypeDomain (· ≠ d₀)
  invFun y := retraction d₀ y.extendDomain
  left_inv x := by
    have h : ((x : D →₀ ℤ).subtypeDomain (· ≠ d₀)).extendDomain =
        (x : D →₀ ℤ) - Finsupp.single d₀ ((x : D →₀ ℤ) d₀) := by
      ext d
      by_cases hd : d = d₀
      · subst hd; simp
      · simp [hd]
    ext1
    change ((retraction d₀) _ : D →₀ ℤ) = _
    rw [h, coe_retraction, map_sub, mem_boundaryChar.mp x.2, boundaryDegree_single]
    simp
  right_inv y := by
    ext d
    simp [d.2.symm]
  map_add' x y := by simp

instance [Nonempty D] : Module.Free ℤ (boundaryChar D) := by
  classical
  obtain ⟨d₀⟩ := ‹Nonempty D›
  exact Module.Free.of_equiv (boundaryCharEquiv d₀).toIntLinearEquiv.symm

/-- **`rank Div⁰_D = #D - 1`**: the boundary torus of a curve with `r ≥ 1` cusps has dimension
`r - 1`. -/
theorem finrank_boundaryChar [Fintype D] [Nonempty D] :
    Module.finrank ℤ (boundaryChar D) = Fintype.card D - 1 := by
  classical
  obtain ⟨d₀⟩ := ‹Nonempty D›
  rw [(boundaryCharEquiv d₀).toIntLinearEquiv.finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-! ### Functoriality in the boundary -/

section Functoriality

variable {D' : Type*} (π : D' → D)

/-- Push-forward of boundary divisors along a map of boundary components (for a finite morphism of
punctured curves `Y' → Y` extending to the compactifications: the induced map on cusps). -/
def pushforward : (D' →₀ ℤ) →+ (D →₀ ℤ) := Finsupp.mapDomain.addMonoidHom π

@[simp]
lemma boundaryDegree_pushforward (x : D' →₀ ℤ) :
    boundaryDegree D (pushforward π x) = boundaryDegree D' x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single d n => simp [pushforward]

/-- Push-forward preserves degree-zero boundary divisors: the map of character lattices
`Div⁰_{D'} → Div⁰_D`, dual to the homomorphism of boundary tori `T_{Y'} → T_Y`. -/
def pushforwardChar : boundaryChar D' →+ boundaryChar D :=
  (pushforward π).restrict (boundaryChar D') |>.codRestrict _ fun x => by
    simp [mem_boundaryChar, mem_boundaryChar.mp x.2]

@[simp]
lemma coe_pushforwardChar (x : boundaryChar D') :
    (pushforwardChar π x : D →₀ ℤ) = pushforward π x := rfl

/-- The duality `charDual` is natural: pulling functions back along `π` corresponds to
precomposing with the push-forward of divisors. -/
theorem charDual_comp (f : D → M) :
    charDual D' M (f ∘ π) = (charDual D M f).comp (pushforwardChar π) := by
  ext x
  simp only [charDual_apply, AddMonoidHom.comp_apply, coe_pushforwardChar]
  induction (x : D' →₀ ℤ) using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single d n => simp [pushforward]

end Functoriality

end GeneralizedAlbanese

end
