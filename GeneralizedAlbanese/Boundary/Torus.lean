/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Boundary.Divisor
import Mathlib

/-!
# Split tori and the boundary torus

A split torus over a ring `R` with character group `X` (a finitely generated free abelian
group) is `T_X = Spec R[X]`; its points with values in a commutative `R`-algebra `A` are the
group homomorphisms `X → A^×`. We work with this functor of points, which is the form in which
the torus part `T_Y` of the generalized Albanese enters the exact sequence
`0 → T_Y → Alb(Y) → Alb(Z) → 0`.

* `GeneralizedAlbanese.SplitTorus X A`: the group `Hom(X, A^×)` of `A`-points;
* `GeneralizedAlbanese.SplitTorus.algHomEquiv`: `(R[X] →ₐ[R] A) ≃ Hom(X, A^×)`, i.e. `T_X` is
  represented by the group algebra `R[X]` (Yoneda);
* `GeneralizedAlbanese.SplitTorus.scheme`, `GeneralizedAlbanese.SplitTorus.schemeHomEquiv`:
  the affine scheme `Spec R[X]` and its `A`-points as morphisms `Spec A ⟶ Spec R[X]`
  (ring homomorphisms `R[X] → A`);
* `GeneralizedAlbanese.SplitTorus.map`, `GeneralizedAlbanese.SplitTorus.dualMap`: functoriality
  in the coefficient ring (base change: the functor of points only depends on `A`, so the torus
  over `R` is the base change of the torus over `ℤ`) and contravariant functoriality in the
  character group;
* `GeneralizedAlbanese.boundaryTorus D A = SplitTorus (Div⁰_D) A`: the boundary torus of a
  punctured curve, and `GeneralizedAlbanese.boundaryTorusProj`, the exact sequence
  `1 → A^× → (A^×)^D → T_Y(A) → 1` (`boundaryTorusProj_surjective`, `ker_boundaryTorusProj`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GeneralizedAlbanese

universe u v

/-- The `A`-points `Hom(X, A^×)` of the split torus with character group `X`. -/
abbrev SplitTorus (X : Type*) [AddCommGroup X] (A : Type*) [CommMonoid A] :=
  Multiplicative X →* Aˣ

namespace SplitTorus

variable {X : Type*} [AddCommGroup X]

section Points

variable (R : Type*) [CommSemiring R] (A : Type*) [CommSemiring A] [Algebra R A]

/-- **The split torus is represented by the group algebra**: `R`-algebra homomorphisms
`R[X] → A` are the same as homomorphisms `X → A^×`. -/
def algHomEquiv : (AddMonoidAlgebra R X →ₐ[R] A) ≃ SplitTorus X A :=
  (AddMonoidAlgebra.lift R A X).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv

variable {R A}

@[simp]
lemma coe_algHomEquiv_apply (φ : AddMonoidAlgebra R X →ₐ[R] A) (x : Multiplicative X) :
    (algHomEquiv R A φ x : A) = φ (AddMonoidAlgebra.single x.toAdd 1) := by
  simp [algHomEquiv, AddMonoidAlgebra.lift_symm_apply]

end Points

section Functoriality

variable {A B : Type*} [CommMonoid A] [CommMonoid B]

/-- Functoriality in the coefficients (in particular base change along `R → S`). -/
def map (f : A →* B) : SplitTorus X A →* SplitTorus X B where
  toFun t := (Units.map f).comp t
  map_one' := by ext; simp
  map_mul' s t := by ext; simp

@[simp]
lemma map_apply (f : A →* B) (t : SplitTorus X A) (x : Multiplicative X) :
    map f t x = Units.map f (t x) := rfl

lemma map_id (t : SplitTorus X A) : map (MonoidHom.id A) t = t := by ext; simp

lemma map_comp {C : Type*} [CommMonoid C] (f : A →* B) (g : B →* C) (t : SplitTorus X A) :
    map g (map f t) = map (g.comp f) t := by ext; simp

variable {X' : Type*} [AddCommGroup X']

/-- Contravariant functoriality in the character group: a homomorphism of character groups
`X → X'` induces the homomorphism of tori `T_{X'} → T_X`. -/
def dualMap (φ : X →+ X') : SplitTorus X' A →* SplitTorus X A where
  toFun t := t.comp (AddMonoidHom.toMultiplicative φ)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma dualMap_apply (φ : X →+ X') (t : SplitTorus X' A) (x : Multiplicative X) :
    dualMap φ t x = t (Multiplicative.ofAdd (φ x.toAdd)) := rfl

lemma dualMap_map (φ : X →+ X') (f : A →* B) (t : SplitTorus X' A) :
    dualMap φ (map f t) = map f (dualMap φ t) := rfl

end Functoriality

section Scheme

variable (R : Type u) [CommRing R] (X : Type u) [AddCommGroup X]

/-- The split torus `Spec R[X]` as an affine scheme. -/
def scheme : Scheme.{u} := Spec (CommRingCat.of (AddMonoidAlgebra R X))

/-- The points of `Spec R[X]` with values in an affine scheme `Spec A` are the ring homomorphisms
`R[X] → A` (`Spec` is fully faithful); the `R`-linear ones are `SplitTorus X A`
(`algHomEquiv`). -/
def schemeHomEquiv (A : CommRingCat.{u}) :
    (Spec A ⟶ scheme R X) ≃ (CommRingCat.of (AddMonoidAlgebra R X) ⟶ A) :=
  Spec.fullyFaithful.homEquiv.symm.trans Quiver.Hom.opEquiv.symm

end Scheme

end SplitTorus

/-! ### The boundary torus of a punctured curve -/

variable (D : Type*) (A : Type*) [CommMonoid A]

/-- **The boundary torus** `T_Y` of a punctured curve `Y = Z ∖ D`: the torus whose character
group is `Div⁰_D`, the degree-zero boundary divisors. -/
abbrev boundaryTorus := SplitTorus (boundaryChar D) A

/-- The projection `(A^×)^D → T_Y(A)` dual to the inclusion `Div⁰_D ⊆ ℤ^D`:
`(u_d)_d ↦ (x ↦ ∏_d u_d ^ x_d)`. -/
def boundaryTorusProj : (D → Aˣ) →* boundaryTorus D A where
  toFun u := AddMonoidHom.toMultiplicativeLeft (charDual D (Additive Aˣ) fun d => .ofMul (u d))
  map_one' := by
    have : (fun _ => Additive.ofMul (1 : Aˣ)) = (0 : D → Additive Aˣ) := rfl
    ext x
    simp only [Pi.one_apply, this, map_zero]
    rfl
  map_mul' u v := by
    have : (fun d => Additive.ofMul ((u * v) d)) =
      (fun d => Additive.ofMul (u d)) + (fun d => Additive.ofMul (v d)) := rfl
    ext x
    simp only [this, map_add]
    rfl

variable {D A}

lemma toAdditiveRight_boundaryTorusProj (u : D → Aˣ) :
    MonoidHom.toAdditiveRight (boundaryTorusProj D A u) =
      charDual D (Additive Aˣ) (fun d => .ofMul (u d)) := rfl

lemma boundaryTorusProj_apply (u : D → Aˣ) (x : Multiplicative (boundaryChar D)) :
    boundaryTorusProj D A u x =
      Additive.toMul (charDual D (Additive Aˣ) (fun d => .ofMul (u d)) x.toAdd) := rfl

variable (D A)

/-- `(A^×)^D → T_Y(A)` is surjective. -/
theorem boundaryTorusProj_surjective : Function.Surjective (boundaryTorusProj D A) := by
  intro t
  obtain ⟨f, hf⟩ := charDual_surjective D (Additive Aˣ) (MonoidHom.toAdditiveRight t)
  refine ⟨fun d => (f d).toMul, MonoidHom.toAdditiveRight.injective ?_⟩
  rw [toAdditiveRight_boundaryTorusProj, ← hf]
  rfl

/-- The kernel of `(A^×)^D → T_Y(A)` is the diagonal `A^×` (the constants). -/
theorem ker_boundaryTorusProj : (boundaryTorusProj D A).ker = (Pi.constMonoidHom D Aˣ).range := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  have key : boundaryTorusProj D A u = 1 ↔
      (fun d => Additive.ofMul (u d)) ∈ (charDual D (Additive Aˣ)).ker := by
    rw [AddMonoidHom.mem_ker, ← toAdditiveRight_boundaryTorusProj,
      ← MonoidHom.toAdditiveRight.injective.eq_iff]
    rfl
  rw [key, ker_charDual, mem_diagonal]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m.toMul, funext fun d => (congrArg Additive.toMul (congrFun hm d)).symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨.ofMul m, rfl⟩

end GeneralizedAlbanese

end
