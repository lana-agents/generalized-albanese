/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import GeneralizedAlbanese.Pi1.SurfaceGroup
import Mathlib

/-!
# Abelian étale covers of a punctured curve: the profinite interface

Let `Y = Z ∖ D` be a smooth curve of genus `g` over an algebraically closed field of
characteristic zero, with `n = #D` cusps. The geometric étale fundamental group `π₁(Y)` is the
profinite completion of the surface group `Π_{g,n}`, compatibly with `π₁(Y) ↠ π₁(Z)` and with
the inertia generators at the cusps (Riemann existence theorem, the topology of punctured
surfaces, and GAGA; SGA 1, Exp. XIII). This comparison is *not* formalised here. Instead we
record what the abelian theory uses as an explicit interface:

* `GeneralizedAlbanese.CuspidalPresentation g n GY GZ`: topological groups `GY`, `GZ`
  (to be instantiated with `π₁(Y)`, `π₁(Z)`), a continuous `q : GY → GZ`, and homomorphisms
  `Π_{g,n} → GY`, `Π_{g,0} → GZ` compatible with `q` and `fill`, with dense image, along which
  every homomorphism to a finite abelian group extends continuously.

The profinite completions satisfy the interface (`CuspidalPresentation.completion`), so it is
not vacuous; the content of the comparison theorem is that the étale fundamental groups do.

From the interface we derive the étale form of the comparison between the generalized Albanese
and `π₁^ab` for a punctured curve: for every finite abelian group `M`,

  `0 → Hom_c(GZ, M) → Hom_c(GY, M) → {f : Fin n → M | ∑ f = 0} → 0`

is exact, where the second map records the values on the inertia generators `γⱼ`
(`CuspidalPresentation.inflate_injective`, `sum_residue`, `exists_residue_eq`,
`residue_eq_zero_iff`): abelian covers of `Y` are abelian covers of `Z` together with
ramification data at the cusps subject to the single relation `∑ⱼ γⱼ = 0`, i.e. the characters
of the boundary torus `T_Y`.
-/

noncomputable section

open Topology

namespace GeneralizedAlbanese

open SurfaceGroup

universe u v

/-- **Interface: a cuspidal presentation** of a pair of topological groups `GY → GZ`
(the geometric étale fundamental groups of a punctured curve `Y` of genus `g` with `n` cusps and
of its compactification `Z`) by the surface groups `Π_{g,n} → Π_{g,0}`: the fields say that
`GY`, `GZ` are the profinite completions of `Π_{g,n}`, `Π_{g,0}` as far as abelian characters
are concerned, compatibly with filling in the cusps. The images `γⱼ` of the `cⱼ` are the
inertia generators at the cusps. -/
structure CuspidalPresentation (g n : ℕ) (GY : Type u) (GZ : Type v) [Group GY]
    [TopologicalSpace GY] [Group GZ] [TopologicalSpace GZ] where
  /-- The map `π₁(Y) → π₁(Z)` induced by the open immersion `Y ⊆ Z`. -/
  q : GY →* GZ
  q_continuous : Continuous q
  /-- The comparison map from the surface group of `Y`. -/
  φY : SurfaceGroup g n →* GY
  /-- The comparison map from the surface group of `Z`. -/
  φZ : SurfaceGroup g 0 →* GZ
  comm : q.comp φY = φZ.comp fill
  denseRange_φY : DenseRange φY
  denseRange_φZ : DenseRange φZ
  /-- Abelian characters of `Π_{g,n}` with finite values extend continuously to `GY`. -/
  extendY : ∀ (M : Type) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (ψ : SurfaceGroup g n →* Multiplicative M),
    ∃ χ : GY →* Multiplicative M, Continuous χ ∧ χ.comp φY = ψ
  /-- Abelian characters of `Π_{g,0}` with finite values extend continuously to `GZ`. -/
  extendZ : ∀ (M : Type) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (ψ : SurfaceGroup g 0 →* Multiplicative M),
    ∃ χ : GZ →* Multiplicative M, Continuous χ ∧ χ.comp φZ = ψ

namespace CuspidalPresentation

variable {g n : ℕ} {GY : Type u} {GZ : Type v} [Group GY] [TopologicalSpace GY] [Group GZ]
  [TopologicalSpace GZ] (P : CuspidalPresentation g n GY GZ)

/-- The inertia generator at the `j`-th cusp. -/
def γ (j : Fin n) : GY := P.φY (cusp j)

variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]

/-- Continuous characters agreeing on the (dense) image of `Π_{g,n}` are equal. -/
lemma ext_of_comp_φY_eq {χ χ' : GY →* Multiplicative M} (hχ : Continuous χ)
    (hχ' : Continuous χ') (h : χ.comp P.φY = χ'.comp P.φY) : χ = χ' :=
  MonoidHom.ext fun x => congrFun (P.denseRange_φY.equalizer hχ hχ'
    (funext fun y => DFunLike.congr_fun h y)) x

lemma ext_of_comp_φZ_eq {χ χ' : GZ →* Multiplicative M} (hχ : Continuous χ)
    (hχ' : Continuous χ') (h : χ.comp P.φZ = χ'.comp P.φZ) : χ = χ' :=
  MonoidHom.ext fun x => congrFun (P.denseRange_φZ.equalizer hχ hχ'
    (funext fun y => DFunLike.congr_fun h y)) x

/-- **Inflation is injective** on continuous characters: `H¹(Z, M) → H¹(Y, M)`. -/
theorem inflate_injective {χ χ' : GZ →* Multiplicative M} (hχ : Continuous χ)
    (hχ' : Continuous χ') (h : χ.comp P.q = χ'.comp P.q) : χ = χ' := by
  refine P.ext_of_comp_φZ_eq hχ hχ' (MonoidHom.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := fill_surjective (n := n) x
  have h1 := DFunLike.congr_fun h (P.φY y)
  have h2 : P.q (P.φY y) = P.φZ (fill y) := DFunLike.congr_fun P.comm y
  simp only [MonoidHom.comp_apply, h2] at h1
  exact h1

omit [TopologicalSpace M] [DiscreteTopology M] in
/-- **The residue theorem** for continuous characters: the values on the inertia generators sum
to zero. -/
theorem sum_residue (χ : GY →* Multiplicative M) : ∑ j, (χ (P.γ j)).toAdd = 0 :=
  SurfaceGroup.sum_residue (χ.comp P.φY)

/-- **Every residue datum with sum zero occurs** for a continuous character (`M` finite). -/
theorem exists_residue_eq [Finite M] {f : Fin n → M} (hf : ∑ j, f j = 0) :
    ∃ χ : GY →* Multiplicative M, Continuous χ ∧ ∀ j, (χ (P.γ j)).toAdd = f j := by
  obtain ⟨ψ, hψ⟩ := SurfaceGroup.exists_residue_eq (g := g) M hf
  obtain ⟨χ, hχ, hχψ⟩ := P.extendY M ψ
  refine ⟨χ, hχ, fun j => ?_⟩
  have := congrArg (fun x : Multiplicative (Fin n → M) => x.toAdd j) hψ
  simp only [residue_apply] at this
  rw [γ, ← MonoidHom.comp_apply, hχψ, this]
  rfl

/-- **Exactness in the middle**: a continuous character of `GY` vanishes on all inertia
generators iff it is inflated from a continuous character of `GZ` (`M` finite): an abelian
cover of `Y` unramified at the cusps extends to `Z`. -/
theorem residue_eq_zero_iff [Finite M] {χ : GY →* Multiplicative M} (hχ : Continuous χ) :
    (∀ j, χ (P.γ j) = 1) ↔
      ∃ χZ : GZ →* Multiplicative M, Continuous χZ ∧ χ = χZ.comp P.q := by
  constructor
  · intro h
    have hker : χ.comp P.φY ∈ (residue (g := g) (n := n) M).ker := by
      rw [MonoidHom.mem_ker]
      ext j
      simpa [γ] using congrArg Multiplicative.toAdd (h j)
    rw [ker_residue, MonoidHom.mem_range] at hker
    obtain ⟨ψ, hψ⟩ := hker
    obtain ⟨χZ, hχZ, hχZψ⟩ := P.extendZ M ψ
    refine ⟨χZ, hχZ, P.ext_of_comp_φY_eq hχ (hχZ.comp P.q_continuous) ?_⟩
    rw [MonoidHom.comp_assoc, P.comm, ← MonoidHom.comp_assoc, hχZψ, ← hψ]
    rfl
  · rintro ⟨χZ, -, rfl⟩ j
    have h2 : P.q (P.φY (cusp j)) = P.φZ (fill (cusp j)) := DFunLike.congr_fun P.comm _
    rw [MonoidHom.comp_apply, γ, h2, fill_cusp, map_one, map_one]

/-! ### The profinite completions satisfy the interface -/

section Completion

open CategoryTheory ProfiniteGrp.ProfiniteCompletion

variable (g n)

/-- The profinite surface group `Π̂_{g,n}`. -/
abbrev ProfiniteSurfaceGroup (g n : ℕ) : ProfiniteGrp.{0} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (SurfaceGroup g n))

/-- The profinite completions `Π̂_{g,n} → Π̂_{g,0}` form a cuspidal presentation: the interface
is satisfiable, and an étale fundamental group satisfies it as soon as it is identified with
`Π̂_{g,n}` compatibly with the inertia generators. -/
def completion : CuspidalPresentation g n (ProfiniteSurfaceGroup g n)
    (ProfiniteSurfaceGroup g 0) where
  q := (ProfiniteGrp.profiniteCompletion.map (GrpCat.ofHom fill)).hom.toMonoidHom
  q_continuous := (ProfiniteGrp.profiniteCompletion.map (GrpCat.ofHom fill)).hom.continuous
  φY := (eta (GrpCat.of (SurfaceGroup g n))).hom
  φZ := (eta (GrpCat.of (SurfaceGroup g 0))).hom
  comm := by
    have := lift_eta (P := ProfiniteSurfaceGroup g 0)
      (GrpCat.ofHom (fill (g := g) (n := n)) ≫ eta _)
    exact congrArg GrpCat.Hom.hom this
  denseRange_φY := denseRange _
  denseRange_φZ := denseRange _
  extendY M _ _ _ _ ψ := by
    let P : ProfiniteGrp.{0} := ProfiniteGrp.of (Multiplicative M)
    let f : GrpCat.of (SurfaceGroup g n) ⟶ GrpCat.of P := GrpCat.ofHom ψ
    exact ⟨(lift f).hom.toMonoidHom, (lift f).hom.continuous,
      congrArg GrpCat.Hom.hom (lift_eta f)⟩
  extendZ M _ _ _ _ ψ := by
    let P : ProfiniteGrp.{0} := ProfiniteGrp.of (Multiplicative M)
    let f : GrpCat.of (SurfaceGroup g 0) ⟶ GrpCat.of P := GrpCat.ofHom ψ
    exact ⟨(lift f).hom.toMonoidHom, (lift f).hom.continuous,
      congrArg GrpCat.Hom.hom (lift_eta f)⟩

end Completion

end CuspidalPresentation

end GeneralizedAlbanese

end
