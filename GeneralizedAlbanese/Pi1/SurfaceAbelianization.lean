/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Pi1.SurfaceGroup
import Mathlib

/-!
# The abelianisation of a punctured surface group

We compute the abelianisation of `Π_{g,n}`:

  `Π_{g,n}^ab ≅ ℤ^g × ℤ^g × (ℤ^n ⧸ ℤ)`,

where `ℤ ⊆ ℤ^n` is the diagonal and the class of the `j`-th basis vector corresponds to the
inertia generator `cⱼ`. Consequently:

* `Π_{g,n}^ab` is torsion-free (`isMulTorsionFree_abelianization`): it is its own maximal
  torsion-free abelian quotient;
* the sequence `0 → ℤ^n ⧸ ℤ → Π_{g,n}^ab → Π_{g,0}^ab → 0` is exact
  (`cuspMap_injective`, `range_cuspMap`, `abFill_surjective`), the first map sending the class
  of `eⱼ` to the class of the inertia generator `cⱼ`. Since
  `ℤ^n ⧸ ℤ = Hom(Div⁰_D, ℤ)` (`GeneralizedAlbanese.charDualEquiv`), this is the
  discrete (topological) form of `0 → T(T_Y) → T(Alb Y) → T(Alb Z) → 0`, the sequence of
  "Tate modules" of the generalized Albanese of a punctured curve (up to Tate twist).
-/

noncomputable section

namespace GeneralizedAlbanese

namespace SurfaceGroup

open SurfaceGen

variable (g n : ℕ)

/-- The model `ℤ^g × ℤ^g × (ℤ^n ⧸ ℤ)` of `Π_{g,n}^ab`. -/
abbrev AbModel : Type :=
  (Fin g → ℤ) × (Fin g → ℤ) × ((Fin n → ℤ) ⧸ (diagonal : AddSubgroup (Fin n → ℤ)))

variable {g n}

/-- The images of the generators in the model. -/
def modelGen : SurfaceGen g n → Multiplicative (AbModel g n)
  | .a i => .ofAdd (Pi.single i 1, 0, 0)
  | .b i => .ofAdd (0, Pi.single i 1, 0)
  | .c j => .ofAdd (0, 0, QuotientAddGroup.mk (Pi.single j 1))

lemma prod_modelGen_c : ∏ j, modelGen (g := g) (.c j : SurfaceGen g n) = 1 := by
  simp only [modelGen, ← ofAdd_sum]
  rw [← ofAdd_zero]
  congr 1
  refine Prod.ext (by simp [Prod.fst_sum]) (Prod.ext (by simp [Prod.fst_sum, Prod.snd_sum]) ?_)
  simp only [Prod.snd_sum, Prod.snd_zero]
  rw [show (∑ j : Fin n, (QuotientAddGroup.mk (Pi.single j (1 : ℤ)) :
      (Fin n → ℤ) ⧸ (diagonal : AddSubgroup (Fin n → ℤ)))) =
      QuotientAddGroup.mk' _ (∑ j : Fin n, Pi.single j (1 : ℤ)) from
      (map_sum (QuotientAddGroup.mk' (diagonal : AddSubgroup (Fin n → ℤ))) _ _).symm,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mem_diagonal]
  exact ⟨1, funext fun j => by simp [Finset.sum_apply, Pi.single_apply]⟩

/-- The homomorphism `Π_{g,n} → ℤ^g × ℤ^g × (ℤ^n ⧸ ℤ)`. -/
def toModel : SurfaceGroup g n →* Multiplicative (AbModel g n) :=
  lift modelGen prod_modelGen_c

/-- The induced homomorphism on the abelianisation, written additively. -/
def abToModel : Additive (Abelianization (SurfaceGroup g n)) →+ AbModel g n :=
  MonoidHom.toAdditiveLeft (Abelianization.lift toModel)

/-- The class of a generator in the abelianisation, written additively. -/
abbrev abGen (x : SurfaceGen g n) : Additive (Abelianization (SurfaceGroup g n)) :=
  .ofMul (Abelianization.of (PresentedGroup.of x))

lemma sum_abGen_c : ∑ j : Fin n, abGen (g := g) (.c j) = 0 := by
  have := sum_residue (g := g) (n := n)
    (M := Additive (Abelianization (SurfaceGroup g n))) Abelianization.of
  exact this

/-- The homomorphism `ℤ^n ⧸ ℤ → Π_{g,n}^ab`, `[eⱼ] ↦ [cⱼ]`. -/
def cuspMap : ((Fin n → ℤ) ⧸ (diagonal : AddSubgroup (Fin n → ℤ))) →+
    Additive (Abelianization (SurfaceGroup g n)) :=
  QuotientAddGroup.lift _ (∑ j, (zmultiplesHom _ (abGen (.c j))).comp
    (Pi.evalAddMonoidHom (fun _ => ℤ) j)) (by
      intro f hf
      obtain ⟨m, rfl⟩ := mem_diagonal.mp hf
      simp [← Finset.smul_sum, sum_abGen_c])

@[simp]
lemma cuspMap_mk_single (j : Fin n) :
    cuspMap (g := g) (QuotientAddGroup.mk (Pi.single j 1)) = abGen (.c j) := by
  simp [cuspMap, Pi.single_apply]

/-- The homomorphism back from the model. -/
def ofModel : AbModel g n →+ Additive (Abelianization (SurfaceGroup g n)) :=
  ((∑ i, (zmultiplesHom _ (abGen (.a i))).comp (Pi.evalAddMonoidHom (fun _ => ℤ) i)).comp
      (AddMonoidHom.fst _ _)) +
    ((∑ i, (zmultiplesHom _ (abGen (.b i))).comp (Pi.evalAddMonoidHom (fun _ => ℤ) i)).comp
      ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _))) +
    (cuspMap.comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _)))

lemma abToModel_abGen (x : SurfaceGen g n) : abToModel (abGen x) = (modelGen x).toAdd := by
  simp [abToModel, toModel]

/-- Homomorphisms out of `Π_{g,n}^ab` are determined by the classes of the generators. -/
lemma abHom_ext {A : Type*} [AddCommGroup A]
    {f₁ f₂ : Additive (Abelianization (SurfaceGroup g n)) →+ A}
    (h : ∀ x, f₁ (abGen x) = f₂ (abGen x)) : f₁ = f₂ := by
  apply AddMonoidHom.toMultiplicativeRight.injective
  apply Abelianization.hom_ext
  exact PresentedGroup.ext fun x => congrArg Multiplicative.ofAdd (h x)

lemma ofModel_abToModel : ofModel.comp abToModel = AddMonoidHom.id
    (Additive (Abelianization (SurfaceGroup g n))) := by
  refine abHom_ext fun x => ?_
  rw [AddMonoidHom.comp_apply, abToModel_abGen]
  cases x with
  | a i => simp [modelGen, ofModel, Pi.single_apply]
  | b i => simp [modelGen, ofModel, Pi.single_apply]
  | c j => simp [modelGen, ofModel]

lemma abToModel_ofModel : abToModel.comp ofModel = AddMonoidHom.id (AbModel g n) := by
  ext ⟨u, w, q⟩ : 1
  induction q using QuotientAddGroup.induction_on with | H f => ?_
  have hc : cuspMap (g := g) (QuotientAddGroup.mk f) = ∑ j, f j • abGen (.c j) := by
    simp [cuspMap]
  simp only [AddMonoidHom.comp_apply, ofModel, AddMonoidHom.add_apply, AddMonoidHom.coe_fst,
    AddMonoidHom.coe_snd, hc, AddMonoidHom.finsetSum_apply, zmultiplesHom_apply,
    Pi.evalAddMonoidHom_apply, map_add, map_sum, map_zsmul, abToModel_abGen, modelGen,
    toAdd_ofAdd, AddMonoidHom.id_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i; simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · ext i; simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero,
      Finset.sum_const_zero, zero_add]
    have : ∀ x : Fin n, f x • (QuotientAddGroup.mk (Pi.single x 1) :
        (Fin n → ℤ) ⧸ (diagonal : AddSubgroup (Fin n → ℤ))) =
        QuotientAddGroup.mk' diagonal (f x • Pi.single x 1) := fun x => rfl
    simp only [this, ← map_sum]
    rw [QuotientAddGroup.mk'_apply]
    congr 1
    ext j; simp [Finset.sum_apply, Pi.single_apply]

variable (g n) in
/-- **`Π_{g,n}^ab ≅ ℤ^g × ℤ^g × (ℤ^n ⧸ ℤ)`**. -/
def abEquiv : Additive (Abelianization (SurfaceGroup g n)) ≃+ AbModel g n :=
  AddMonoidHom.toAddEquiv abToModel ofModel ofModel_abToModel abToModel_ofModel

/-! ### Torsion-freeness -/

/-- `ℤ^n ⧸ ℤ` is torsion-free. -/
lemma quotient_diagonal_eq_zero {q : (Fin n → ℤ) ⧸ (diagonal : AddSubgroup (Fin n → ℤ))} {k : ℕ}
    (hk : k ≠ 0) (h : k • q = 0) : q = 0 := by
  induction q using QuotientAddGroup.induction_on with | H f => ?_
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, mem_diagonal] at h
  rw [QuotientAddGroup.eq_zero_iff, mem_diagonal]
  obtain ⟨m, hm⟩ := h
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨j₀⟩⟩
  · exact ⟨0, funext fun j => (IsEmpty.false j).elim⟩
  refine ⟨f j₀, funext fun j => ?_⟩
  have h1 := congrFun hm j
  have h2 := congrFun hm j₀
  simp only [Pi.smul_apply, nsmul_eq_mul] at h1 h2
  exact mul_left_cancel₀ (by exact_mod_cast hk) (h1.trans h2.symm)

lemma abModel_eq_zero {v : AbModel g n} {k : ℕ} (hk : k ≠ 0) (h : k • v = 0) : v = 0 := by
  obtain ⟨u, w, q⟩ := v
  simp only [Prod.smul_mk, Prod.mk_eq_zero] at h
  obtain ⟨hu, hw, hq⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ (quotient_diagonal_eq_zero hk hq))
  · exact (smul_eq_zero.mp hu).resolve_left hk
  · exact (smul_eq_zero.mp hw).resolve_left hk

/-- **`Π_{g,n}^ab` is torsion-free**, so it is its own maximal torsion-free abelian quotient. -/
instance isMulTorsionFree_abelianization :
    IsMulTorsionFree (Abelianization (SurfaceGroup g n)) where
  pow_left_injective k hk x y hxy := by
    simp only at hxy
    have h : k • (abEquiv g n (.ofMul (x / y))) = 0 := by
      rw [← map_nsmul, ← ofMul_pow, div_pow]
      change abEquiv g n (.ofMul (x ^ k / y ^ k)) = 0
      rw [hxy, div_self', ofMul_one, map_zero]
    have := abModel_eq_zero hk h
    rw [AddEquiv.map_eq_zero_iff] at this
    exact div_eq_one.mp (congrArg Additive.toMul this)

/-! ### The exact sequence `0 → ℤ^n ⧸ ℤ → Π_{g,n}^ab → Π_{g,0}^ab → 0` -/

/-- Filling in the punctures on abelianisations, written additively. -/
def abFill : Additive (Abelianization (SurfaceGroup g n)) →+
    Additive (Abelianization (SurfaceGroup g 0)) :=
  MonoidHom.toAdditive (Abelianization.map fill)

theorem abFill_surjective : Function.Surjective (abFill (g := g) (n := n)) := by
  intro y
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective y
  induction y using QuotientGroup.induction_on with | H z => ?_
  obtain ⟨x, rfl⟩ := fill_surjective (n := n) z
  exact ⟨.ofMul (Abelianization.of x), rfl⟩

lemma abToModel_cuspMap (q : (Fin n → ℤ) ⧸ (diagonal : AddSubgroup (Fin n → ℤ))) :
    abToModel (cuspMap (g := g) q) = (0, 0, q) := by
  induction q using QuotientAddGroup.induction_on with | H f => ?_
  have hc : cuspMap (g := g) (QuotientAddGroup.mk f) = ∑ j, f j • abGen (.c j) := by
    simp [cuspMap]
  rw [hc]
  simp only [map_sum, map_zsmul, abToModel_abGen, modelGen, toAdd_ofAdd]
  refine Prod.ext (by simp [Prod.fst_sum]) (Prod.ext (by simp [Prod.fst_sum, Prod.snd_sum]) ?_)
  simp only [Prod.snd_sum, Prod.smul_snd]
  have : ∀ x : Fin n, f x • (QuotientAddGroup.mk (Pi.single x 1) :
      (Fin n → ℤ) ⧸ (diagonal : AddSubgroup (Fin n → ℤ))) =
      QuotientAddGroup.mk' diagonal (f x • Pi.single x 1) := fun x => rfl
  simp only [this, ← map_sum]
  rw [QuotientAddGroup.mk'_apply]
  congr 1
  ext j; simp [Finset.sum_apply, Pi.single_apply]

/-- **The inertia generators span a copy of `ℤ^n ⧸ ℤ`** in `Π_{g,n}^ab`: the only relation
among the classes of the `cⱼ` is `∑ⱼ [cⱼ] = 0`. -/
theorem cuspMap_injective : Function.Injective (cuspMap (g := g) (n := n)) := by
  intro q q' h
  have := congrArg abToModel h
  rw [abToModel_cuspMap, abToModel_cuspMap] at this
  exact (Prod.ext_iff.mp (Prod.ext_iff.mp this).2).2

/-- Filling in the punctures in the model: `(u, w, q) ↦ (u, w, 0)`. -/
lemma abToModel_abFill (x : Additive (Abelianization (SurfaceGroup g n))) :
    abToModel (abFill x) = ((abToModel x).1, (abToModel x).2.1, 0) := by
  have key : abToModel.comp abFill = ((AddMonoidHom.fst _ _).prod
      (((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _)).prod 0)).comp
      (abToModel (g := g) (n := n)) := by
    refine abHom_ext fun x => ?_
    cases x with
    | a i =>
      change abToModel (abGen (.a i)) = _
      simp [abToModel_abGen, modelGen]
    | b i =>
      change abToModel (abGen (.b i)) = _
      simp [abToModel_abGen, modelGen]
    | c j =>
      change abToModel (.ofMul (Abelianization.of (fill (PresentedGroup.of (.c j))))) = _
      simp [abToModel_abGen, modelGen]
      rfl
  exact congrArg (fun φ => φ x) key

/-- **Exactness in the middle**: the kernel of `Π_{g,n}^ab → Π_{g,0}^ab` is spanned by the
classes of the inertia generators. -/
theorem range_cuspMap : (cuspMap (g := g) (n := n)).range = (abFill (g := g) (n := n)).ker := by
  ext x
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨q, rfl⟩
    apply (abEquiv g 0).injective
    change abToModel (abFill (cuspMap q)) = abToModel 0
    rw [abToModel_abFill, abToModel_cuspMap, map_zero]
    rfl
  · intro hx
    have h0 := congrArg abToModel hx
    rw [abToModel_abFill, map_zero, Prod.ext_iff, Prod.ext_iff] at h0
    refine ⟨(abToModel x).2.2, (abEquiv g n).injective ?_⟩
    change abToModel (cuspMap _) = abToModel x
    rw [abToModel_cuspMap]
    exact Prod.ext h0.1.symm (Prod.ext h0.2.1.symm rfl)

end SurfaceGroup

end GeneralizedAlbanese

end
