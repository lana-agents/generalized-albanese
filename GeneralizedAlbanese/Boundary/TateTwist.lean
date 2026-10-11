/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Boundary.Torus
import Mathlib

/-!
# Torsion of split tori and the Tate twist

The torsion points of a split torus with character group `X` are the homomorphisms from `X` to
the roots of unity: `T_X(A)[n] ≅ Hom(X, μ_n(A))` (`SplitTorus.torsionEquiv`). Hence the Galois
action on them is through the cyclotomic character: for a domain `L` with `n` distinct `n`-th
roots of unity and a ring automorphism `g` of `L`, `g · t = t ^ χ_n(g)` for `t ∈ T_X(L)[n]`
(`SplitTorus.map_eq_pow_modularCyclotomicCharacter`), and on the `p^∞`-torsion `g` acts through
the `p`-adic cyclotomic character (`SplitTorus.map_eq_pow_cyclotomicCharacter`).

In other words `T_X[n] ≅ Hom(X, ℤ/n(1))` and `T_p(T_X) ≅ Hom(X, ℤ_p(1))` as Galois modules: this
is the Tate twist in the description of the Tate module of the torus part of the generalized
Albanese, `T(T_Y) = Hom(Div⁰_D, Ẑ(1))`, specialised to the boundary torus in
`boundaryTorus.torsionEquiv` and `boundaryTorus.map_eq_pow_modularCyclotomicCharacter`.
-/

noncomputable section

namespace GeneralizedAlbanese

namespace SplitTorus

variable (X : Type*) [AddCommGroup X] (A : Type*) [CommMonoid A]

/-- The `n`-torsion `T_X(A)[n]` of a split torus. -/
def torsion (n : ℕ) : Subgroup (SplitTorus X A) := (powMonoidHom n : SplitTorus X A →* _).ker

variable {X A}

lemma mem_torsion {n : ℕ} {t : SplitTorus X A} :
    t ∈ torsion X A n ↔ ∀ x, t x ∈ rootsOfUnity n A := by
  rw [torsion, MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · intro h x
    rw [mem_rootsOfUnity, ← MonoidHom.pow_apply, h, MonoidHom.one_apply]
  · intro h
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.pow_apply, (mem_rootsOfUnity _ _).mp (h x), MonoidHom.one_apply]

variable (X A) in
/-- **`T_X(A)[n] ≅ Hom(X, μ_n(A))`.** -/
def torsionEquiv (n : ℕ) : torsion X A n ≃* (Multiplicative X →* rootsOfUnity n A) where
  toFun t := (t : SplitTorus X A).codRestrict _ (mem_torsion.mp t.2)
  invFun s := ⟨(rootsOfUnity n A).subtype.comp s, mem_torsion.mpr fun x => (s x).2⟩
  left_inv t := by ext; rfl
  right_inv s := by ext; rfl
  map_mul' s t := by ext; rfl

@[simp]
lemma coe_torsionEquiv_apply (n : ℕ) (t : torsion X A n) (x : Multiplicative X) :
    ((torsionEquiv X A n t x : rootsOfUnity n A) : Aˣ) = (t : SplitTorus X A) x := rfl

/-! ### The Galois action on torsion points is through the cyclotomic character -/

variable {L : Type*} [CommRing L] [IsDomain L]

/-- **The Tate twist, mod `n`**: if `L` has `n` distinct `n`-th roots of unity, a ring
automorphism `g` of `L` acts on `T_X(L)[n]` as `t ↦ t ^ χ_n(g)`, with `χ_n` the mod-`n`
cyclotomic character. -/
theorem map_eq_pow_modularCyclotomicCharacter {n : ℕ} [NeZero n]
    (hn : Nat.card (rootsOfUnity n L) = n) (g : L ≃+* L) {t : SplitTorus X L}
    (ht : t ∈ torsion X L n) :
    map (g : L →* L) t = t ^ ((modularCyclotomicCharacter L hn g : ZMod n)).val := by
  refine MonoidHom.ext fun x => ?_
  rw [map_apply, MonoidHom.pow_apply]
  refine Units.ext ?_
  rw [Units.coe_map, Units.val_pow_eq_pow_val]
  exact modularCyclotomicCharacter.spec L hn g (mem_torsion.mp ht x)

/-- **The Tate twist, `p`-adically**: if `L` contains all `p`-power roots of unity, a ring
automorphism `g` of `L` acts on `T_X(L)[p^n]` through the `p`-adic cyclotomic character
`χ_p(g) ∈ ℤ_p^×`, i.e. `T_p(T_X) ≅ Hom(X, ℤ_p(1))` as a Galois module. -/
theorem map_eq_pow_cyclotomicCharacter (p : ℕ) [Fact p.Prime]
    [∀ i, HasEnoughRootsOfUnity L (p ^ i)] {n : ℕ} (g : L ≃+* L) {t : SplitTorus X L}
    (ht : t ∈ torsion X L (p ^ n)) :
    map (g : L →* L) t = t ^ ((cyclotomicCharacter L p g).val.toZModPow n).val := by
  refine MonoidHom.ext fun x => ?_
  rw [map_apply, MonoidHom.pow_apply]
  refine Units.ext ?_
  rw [Units.coe_map, Units.val_pow_eq_pow_val]
  exact cyclotomicCharacter.spec p g _ (by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp (mem_torsion.mp ht x),
      Units.val_one])

end SplitTorus

namespace boundaryTorus

variable (D : Type*)

/-- **The torsion of the boundary torus**: `T_Y(A)[n] ≅ Hom(Div⁰_D, μ_n(A))`. -/
def torsionEquiv (A : Type*) [CommMonoid A] (n : ℕ) :
    SplitTorus.torsion (boundaryChar D) A n ≃*
      (Multiplicative (boundaryChar D) →* rootsOfUnity n A) :=
  SplitTorus.torsionEquiv _ A n

variable {D} {L : Type*} [CommRing L] [IsDomain L]

/-- **`T_Y[n] ≅ Hom(Div⁰_D, ℤ/n(1))` as a Galois module**: automorphisms act on the
`n`-torsion of the boundary torus through the mod-`n` cyclotomic character. -/
theorem map_eq_pow_modularCyclotomicCharacter {n : ℕ} [NeZero n]
    (hn : Nat.card (rootsOfUnity n L) = n) (g : L ≃+* L) {t : boundaryTorus D L}
    (ht : t ∈ SplitTorus.torsion (boundaryChar D) L n) :
    SplitTorus.map (g : L →* L) t = t ^ ((modularCyclotomicCharacter L hn g : ZMod n)).val :=
  SplitTorus.map_eq_pow_modularCyclotomicCharacter hn g ht

end boundaryTorus

end GeneralizedAlbanese

end
