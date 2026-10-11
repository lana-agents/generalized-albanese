/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Boundary.Divisor
import Mathlib

/-!
# Surface groups with punctures and their abelian characters

The (topological, or after profinite completion: geometric étale, in characteristic zero)
fundamental group of a smooth curve of genus `g` with `n` punctures has the presentation

  `Π_{g,n} = ⟨a₁, b₁, …, a_g, b_g, c₁, …, c_n | ∏ᵢ [aᵢ, bᵢ] · ∏ⱼ cⱼ = 1⟩`,

where `cⱼ` generates the inertia group at the `j`-th cusp. Filling in the punctures kills the
`cⱼ` and gives the fundamental group `Π_{g,0}` of the compactification.

This file proves the group-theoretic content of the comparison between the generalized Albanese
and the abelianised fundamental group for punctured curves: for every abelian group `M`,

  `0 → Hom(Π_{g,0}, M) → Hom(Π_{g,n}, M) → {f : Fin n → M | ∑ f = 0} → 0`

is exact, the last map recording the values on the inertia generators (`residue`). For `M = ℤ`
the right-hand term is the group `Div⁰_D` of degree-zero boundary divisors
(`residueEquivBoundaryChar`): the characters of `π₁^ab(Y)` modulo those of `π₁^ab(Z)` are the
characters of the boundary torus `T_Y` of the generalized Albanese.

## Main declarations

* `GeneralizedAlbanese.SurfaceGroup g n`: the presented group `Π_{g,n}`;
* `GeneralizedAlbanese.SurfaceGroup.cusp j`: the inertia generator `cⱼ`;
* `GeneralizedAlbanese.SurfaceGroup.fill`: `Π_{g,n} → Π_{g,0}`, filling in the punctures;
* `GeneralizedAlbanese.SurfaceGroup.residue`: `Hom(Π_{g,n}, M) → (Fin n → M)`;
* `GeneralizedAlbanese.SurfaceGroup.sum_residue`, `residue_surjective`,
  `residue_eq_zero_iff`, `comp_fill_injective`: the exact sequence above.
-/

noncomputable section

namespace GeneralizedAlbanese

/-- Generators of `Π_{g,n}`: `aᵢ, bᵢ` (`i < g`) and the inertia generators `cⱼ` (`j < n`). -/
inductive SurfaceGen (g n : ℕ) : Type
  | a : Fin g → SurfaceGen g n
  | b : Fin g → SurfaceGen g n
  | c : Fin n → SurfaceGen g n
  deriving DecidableEq

namespace SurfaceGen

variable {g n : ℕ}

/-- The surface relator `∏ᵢ [aᵢ, bᵢ] · ∏ⱼ cⱼ`, with `[x, y] = x y x⁻¹ y⁻¹`. -/
def relator (g n : ℕ) : FreeGroup (SurfaceGen g n) :=
  (List.ofFn fun i : Fin g =>
      FreeGroup.of (a i : SurfaceGen g n) * FreeGroup.of (b i) * (FreeGroup.of (a i))⁻¹ *
        (FreeGroup.of (b i))⁻¹).prod *
    (List.ofFn fun j : Fin n => FreeGroup.of (c j : SurfaceGen g n)).prod

/-- In a commutative group the relator maps to the product of the images of the cusps. -/
lemma lift_relator {G : Type*} [CommGroup G] (f : SurfaceGen g n → G) :
    FreeGroup.lift f (relator g n) = ∏ j, f (c j) := by
  simp [relator, map_list_prod, List.prod_ofFn, mul_inv_cancel_comm]

end SurfaceGen

open SurfaceGen

/-- **The surface group** `Π_{g,n}` of a genus `g` curve with `n` punctures. -/
abbrev SurfaceGroup (g n : ℕ) : Type := PresentedGroup {relator g n}

namespace SurfaceGroup

variable {g n : ℕ}

/-- The inertia generator `cⱼ` at the `j`-th cusp. -/
def cusp (j : Fin n) : SurfaceGroup g n := PresentedGroup.of (c j)

/-- Construct a homomorphism to an abelian group from the images of the generators, provided
the images of the inertia generators multiply to one. -/
def lift {G : Type*} [CommGroup G] (f : SurfaceGen g n → G) (hf : ∏ j, f (c j) = 1) :
    SurfaceGroup g n →* G :=
  PresentedGroup.toGroup (rels := {relator g n}) (f := f) (by
    rintro r rfl
    rw [lift_relator, hf])

@[simp]
lemma lift_of {G : Type*} [CommGroup G] (f : SurfaceGen g n → G) (hf : ∏ j, f (c j) = 1)
    (x : SurfaceGen g n) : lift f hf (PresentedGroup.of x) = f x :=
  PresentedGroup.toGroup.of _

/-- The map on generators filling in the punctures. -/
def fillGen : SurfaceGen g n → SurfaceGroup g 0
  | .a i => PresentedGroup.of (.a i)
  | .b i => PresentedGroup.of (.b i)
  | .c _ => 1

/-- **Filling in the punctures**: `Π_{g,n} → Π_{g,0}`, killing the inertia generators. -/
def fill : SurfaceGroup g n →* SurfaceGroup g 0 :=
  PresentedGroup.toGroup (rels := {relator g n}) (f := fillGen) (by
    rintro r rfl
    have h0 := PresentedGroup.one_of_mem (rels := {relator g 0}) (x := relator g 0) rfl
    have hw : relator g 0 = (List.ofFn fun i : Fin g =>
        FreeGroup.of (a i : SurfaceGen g 0) * FreeGroup.of (b i) * (FreeGroup.of (a i))⁻¹ *
          (FreeGroup.of (b i))⁻¹).prod := by
      simp [relator]
    refine Eq.trans ?_ ((congrArg (PresentedGroup.mk {relator g 0}) hw).symm.trans h0)
    have hn : relator g n = (List.ofFn fun i : Fin g =>
        FreeGroup.of (a i : SurfaceGen g n) * FreeGroup.of (b i) * (FreeGroup.of (a i))⁻¹ *
          (FreeGroup.of (b i))⁻¹).prod * (List.ofFn fun j : Fin n => FreeGroup.of (c j)).prod :=
      rfl
    rw [hn]
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
      map_inv, FreeGroup.lift_apply_of, fillGen, List.ofFn_const, List.prod_replicate, one_pow,
      mul_one]
    rfl)

@[simp]
lemma fill_of_a (i : Fin g) :
    fill (n := n) (PresentedGroup.of (.a i)) = PresentedGroup.of (.a i) :=
  PresentedGroup.toGroup.of _

@[simp]
lemma fill_of_b (i : Fin g) :
    fill (n := n) (PresentedGroup.of (.b i)) = PresentedGroup.of (.b i) :=
  PresentedGroup.toGroup.of _

@[simp]
lemma fill_of_c (j : Fin n) : fill (g := g) (PresentedGroup.of (.c j)) = 1 :=
  PresentedGroup.toGroup.of _

@[simp]
lemma fill_cusp (j : Fin n) : fill (g := g) (cusp j) = 1 :=
  fill_of_c j

/-- Filling in the punctures is surjective. -/
theorem fill_surjective : Function.Surjective (fill : SurfaceGroup g n →* SurfaceGroup g 0) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  cases x with
  | a i => exact ⟨_, fill_of_a i⟩
  | b i => exact ⟨_, fill_of_b i⟩
  | c j => exact j.elim0

/-! ### Abelian characters and residues at the cusps -/

variable (M : Type*) [AddCommGroup M]

/-- Characters of `Π_{g,0}` inflate to characters of `Π_{g,n}` along `fill`
(`H¹(Z, M) → H¹(Y, M)`). -/
def inflate : (SurfaceGroup g 0 →* Multiplicative M) →* (SurfaceGroup g n →* Multiplicative M) where
  toFun ψ := ψ.comp fill
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The residues** of a character of `Π_{g,n}`: its values on the inertia generators
(`H¹(Y, M) → ⊕_D M`). -/
def residue : (SurfaceGroup g n →* Multiplicative M) →* Multiplicative (Fin n → M) where
  toFun φ := .ofAdd fun j => (φ (cusp j)).toAdd
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The tuples with sum zero (for `M = ℤ`: the degree-zero boundary divisors). -/
def sumZero : AddSubgroup (Fin n → M) where
  carrier := {f | ∑ j, f j = 0}
  add_mem' {f f'} hf hf' := by simp_all [Finset.sum_add_distrib]
  zero_mem' := by simp
  neg_mem' {f} hf := by simp_all

variable {M}

lemma mem_sumZero {f : Fin n → M} : f ∈ sumZero (n := n) M ↔ ∑ j, f j = 0 := by
  rfl

@[simp]
lemma residue_apply (φ : SurfaceGroup g n →* Multiplicative M) (j : Fin n) :
    (residue M φ).toAdd j = (φ (cusp j)).toAdd := rfl

/-- **The residue theorem**: the residues of a character sum to zero. -/
theorem sum_residue (φ : SurfaceGroup g n →* Multiplicative M) :
    ∑ j, (residue M φ).toAdd j = 0 := by
  have h := congrArg φ (PresentedGroup.one_of_mem (rels := {relator g n}) rfl)
  rw [map_one] at h
  have e : φ.comp (PresentedGroup.mk _) = FreeGroup.lift fun x => φ (PresentedGroup.of x) :=
    FreeGroup.ext_hom _ _ fun _ => by rw [FreeGroup.lift_apply_of]; rfl
  rw [← MonoidHom.comp_apply, e, lift_relator] at h
  simpa [cusp, ← toAdd_prod] using congrArg Multiplicative.toAdd h

variable (M)

/-- **Every residue datum with sum zero occurs**: for `f : Fin n → M` with `∑ f = 0` there is a
character of `Π_{g,n}` (trivial on the `aᵢ, bᵢ`) with residues `f`. -/
theorem exists_residue_eq {f : Fin n → M} (hf : ∑ j, f j = 0) :
    ∃ φ : SurfaceGroup g n →* Multiplicative M, residue M φ = .ofAdd f := by
  let F : SurfaceGen g n → Multiplicative M
    | .a _ => 1
    | .b _ => 1
    | .c j => .ofAdd (f j)
  refine ⟨lift F (by simp [F, ← ofAdd_sum, hf]), ?_⟩
  ext j
  simp [cusp, F]

/-- **The kernel of the residue map is the image of inflation**: a character of `Π_{g,n}` is
trivial on all inertia generators iff it factors through `Π_{g,0}` (an abelian cover of `Y`
unramified at the cusps extends to `Z`). -/
theorem ker_residue : (residue (g := g) (n := n) M).ker = (inflate M).range := by
  ext φ
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro h
    have hc : ∀ j, φ (cusp j) = 1 := fun j => by
      have := congrArg (fun x : Multiplicative (Fin n → M) => x.toAdd j) h
      simpa using this
    let F : SurfaceGen g 0 → Multiplicative M
      | .a i => φ (PresentedGroup.of (.a i))
      | .b i => φ (PresentedGroup.of (.b i))
      | .c j => j.elim0
    refine ⟨lift F (by simp), PresentedGroup.ext fun x => ?_⟩
    cases x with
    | a i => simp [inflate, F]
    | b i => simp [inflate, F]
    | c j => simpa [inflate, cusp] using (hc j).symm
  · rintro ⟨ψ, rfl⟩
    ext j
    simp [inflate]

/-- Inflation is injective (`fill` is surjective). -/
theorem inflate_injective : Function.Injective (inflate (g := g) (n := n) M) := by
  intro ψ ψ' h
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := fill_surjective (n := n) x
  exact DFunLike.congr_fun h y

/-- The residue map with values in the sum-zero tuples. -/
def residueSumZero :
    (SurfaceGroup g n →* Multiplicative M) →* Multiplicative (sumZero (n := n) M) where
  toFun φ := .ofAdd ⟨(residue M φ).toAdd, mem_sumZero.mpr (sum_residue φ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem residueSumZero_surjective : Function.Surjective (residueSumZero (g := g) (n := n) M) := by
  intro f
  obtain ⟨φ, hφ⟩ := exists_residue_eq (g := g) M (mem_sumZero.mp f.toAdd.2)
  refine ⟨φ, ?_⟩
  change Multiplicative.ofAdd _ = f
  exact Subtype.ext (congrArg Multiplicative.toAdd hφ)

theorem ker_residueSumZero : (residueSumZero (g := g) (n := n) M).ker = (inflate M).range := by
  rw [← ker_residue]
  ext φ
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg (fun x : Multiplicative (sumZero (n := n) M) => Multiplicative.ofAdd
      (x.toAdd : Fin n → M)) h
  · intro h
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    exact congrArg Multiplicative.toAdd h

/-- **`H¹(Y, M) / H¹(Z, M) ≅ {f : D → M | ∑ f = 0}`** for the surface group of a punctured
curve, via the residues at the cusps. -/
def characterQuotientEquiv :
    (SurfaceGroup g n →* Multiplicative M) ⧸ (inflate (g := g) (n := n) M).range ≃*
      Multiplicative (sumZero (n := n) M) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_residueSumZero M).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residueSumZero_surjective M))

/-! ### Integral characters and the boundary torus -/

/-- For `M = ℤ`, the sum-zero tuples are the degree-zero boundary divisors `Div⁰_D`, the
character group of the boundary torus. -/
def sumZeroIntEquiv : sumZero (n := n) ℤ ≃+ boundaryChar (Fin n) where
  toFun f := ⟨Finsupp.equivFunOnFinite.symm f, by
    rw [mem_boundaryChar, boundaryDegree_apply, Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact mem_sumZero.mp f.2⟩
  invFun x := ⟨(x : Fin n →₀ ℤ), by
    rw [mem_sumZero, ← mem_boundaryChar.mp x.2, boundaryDegree_apply,
      Finsupp.sum_fintype _ _ (fun _ => rfl)]⟩
  left_inv f := rfl
  right_inv x := Subtype.ext (Finsupp.ext fun _ => rfl)
  map_add' f f' := Subtype.ext (Finsupp.ext fun _ => rfl)

/-- **The characters of `π₁^ab(Y)` modulo those of `π₁^ab(Z)` are the degree-zero boundary
divisors**: `Hom(Π_{g,n}, ℤ) / Hom(Π_{g,0}, ℤ) ≅ Div⁰_D`, the character group of the torus part
`T_Y` of the generalized Albanese of `Y` (up to the Tate twist, which is invisible for the
discrete surface group). -/
def integralCharacterQuotientEquiv :
    (SurfaceGroup g n →* Multiplicative ℤ) ⧸ (inflate (g := g) (n := n) ℤ).range ≃*
      Multiplicative (boundaryChar (Fin n)) :=
  (characterQuotientEquiv ℤ).trans (AddEquiv.toMultiplicative sumZeroIntEquiv)

end SurfaceGroup

end GeneralizedAlbanese

end
