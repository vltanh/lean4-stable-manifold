/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.Linear.Spectral
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Stable and unstable subspaces of a linear map

For a continuous linear map `A` of a real normed space:

* `ContinuousLinearMap.stableSubspace A`: the vectors `v` with `Aⁿ v → 0`;
* `ContinuousLinearMap.unstableSubspace A`: the vectors having a backward orbit tending to `0`
  (`w 0 = v`, `A (w (n + 1)) = w n`, `w n → 0`);
* `ContinuousLinearMap.IsHyperbolic A` (finite dimension): no complex eigenvalue of `A` has
  modulus `1`.

Both subspaces are `A`-invariant, and `A` maps the unstable subspace onto itself
(`map_mem_stableSubspace`, `map_mem_unstableSubspace`, `exists_mem_unstableSubspace_apply_eq`).
For a continuous linear equivalence `e`, the stable subspace of `e⁻¹` is the unstable subspace of
`e` and conversely (`stableSubspace_symm`, `unstableSubspace_symm`). In finite dimension the two
subspaces are always disjoint (`disjoint_stableSubspace_unstableSubspace`, no hyperbolicity
needed), so `A` is injective on the unstable subspace (`injOn_unstableSubspace`). That they span
the space when `A` is hyperbolic is `ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`
(`StableManifold.Linear.Splitting`).

## Proofs (plan)

Size: 150–250 lines.

* Invariance: `Aⁿ (A v) = A (Aⁿ v) → A 0 = 0` (`pow_succ'`, continuity of `A`); for the
  unstable subspace, the backward orbit of `A v` is `0 ↦ A v`, `n + 1 ↦ w n`, and the backward
  orbit of `w 1` (a preimage of `v`) is `n ↦ w (n + 1)`.
* `stableSubspace_symm`, `unstableSubspace_symm`: a backward orbit of `e` is unique,
  `w n = e.symm^[n] v` (induction, `ContinuousLinearEquiv.symm_apply_apply`), and
  `(e.symm : E →L[ℝ] E) ^ n` applied to `v` is that iterate; conversely `n ↦ (e.symm ^ n) v` is a
  backward orbit. Symmetrically, a backward orbit of `e.symm` is the forward orbit of `e`.
* `disjoint_stableSubspace_unstableSubspace`: let `V = Eₛ ⊓ Eᵤ`. `A` maps `V` into `V`, and onto
  `V`: a preimage `w 1 ∈ Eᵤ` of `v ∈ V` lies in `Eₛ` since `Aⁿ⁺¹ (w 1) = Aⁿ v → 0`. So the
  restriction `T : V →L[ℝ] V` (`ContinuousLinearMap.restrict`) is bijective, a continuous linear
  equivalence (finite dimension, `LinearEquiv.ofBijective`). Every `Tⁿ v → 0` (as `v ∈ Eₛ`) and
  every `T⁻ⁿ v → 0` (the backward orbit of `v` lies in `V` and is `n ↦ T⁻ⁿ v`). By
  `exists_norm_pow_lt_one_of_tendsto`, `‖T ^ N‖ < 1` and `‖T⁻¹ ^ M‖ < 1`, so
  `‖1‖ ≤ ‖T ^ (N M)‖ ‖T⁻¹ ^ (N M)‖ < 1` (`norm_pow_le'`), which forces `V = 0`
  (`ContinuousLinearMap.norm_id` on a nontrivial space).
* `injOn_unstableSubspace`: if `v, v' ∈ Eᵤ` and `A v = A v'`, then `v - v' ∈ Eᵤ` and
  `Aⁿ (v - v') = 0` for `n ≥ 1`, so `v - v' ∈ Eₛ ⊓ Eᵤ = 0`.
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **stable subspace** of `A`: the vectors `v` with `Aⁿ v → 0`. For a hyperbolic `A` it is
the sum of the generalized eigenspaces of the eigenvalues of modulus `< 1`. -/
def stableSubspace (A : E →L[ℝ] E) : Submodule ℝ E where
  carrier := {v | Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq, map_add] at hv hw ⊢
    simpa using hv.add hw
  zero_mem' := by simp
  smul_mem' c v hv := by
    simp only [Set.mem_ofPred_eq, map_smul] at hv ⊢
    simpa using hv.const_smul c

/-- The **unstable subspace** of `A`: the vectors `v` having a backward orbit tending to `0`
(`w 0 = v`, `A (w (n + 1)) = w n`, `w n → 0`). For a hyperbolic `A` it is the sum of the
generalized eigenspaces of the eigenvalues of modulus `> 1`. -/
def unstableSubspace (A : E →L[ℝ] E) : Submodule ℝ E where
  carrier := {v | ∃ w : ℕ → E, w 0 = v ∧ (∀ n, A (w (n + 1)) = w n) ∧
    Tendsto w atTop (𝓝 0)}
  add_mem' {v₁ v₂} h₁ h₂ := by
    obtain ⟨w₁, h01, hA1, ht1⟩ := h₁
    obtain ⟨w₂, h02, hA2, ht2⟩ := h₂
    refine ⟨fun n ↦ w₁ n + w₂ n, by simp [h01, h02], fun n ↦ by simp [hA1, hA2], ?_⟩
    simpa using ht1.add ht2
  zero_mem' := ⟨fun _ ↦ 0, rfl, fun _ ↦ by simp, tendsto_const_nhds⟩
  smul_mem' c v h := by
    obtain ⟨w, h0, hA, ht⟩ := h
    refine ⟨fun n ↦ c • w n, by simp [h0], fun n ↦ by simp [hA], ?_⟩
    simpa using ht.const_smul c

theorem mem_stableSubspace {A : E →L[ℝ] E} {v : E} :
    v ∈ A.stableSubspace ↔ Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0) :=
  Iff.rfl

theorem mem_unstableSubspace {A : E →L[ℝ] E} {v : E} :
    v ∈ A.unstableSubspace ↔
      ∃ w : ℕ → E, w 0 = v ∧ (∀ n, A (w (n + 1)) = w n) ∧ Tendsto w atTop (𝓝 0) :=
  Iff.rfl

/-- The stable subspace is `A`-invariant.

Proof: `Aⁿ (A v) = A (Aⁿ v) → A 0 = 0`. -/
theorem map_mem_stableSubspace {A : E →L[ℝ] E} {v : E} (hv : v ∈ A.stableSubspace) :
    A v ∈ A.stableSubspace := by
  sorry

/-- The unstable subspace is `A`-invariant.

Proof: the backward orbit `0 ↦ A v`, `n + 1 ↦ w n`. -/
theorem map_mem_unstableSubspace {A : E →L[ℝ] E} {v : E} (hv : v ∈ A.unstableSubspace) :
    A v ∈ A.unstableSubspace := by
  sorry

/-- `A` maps the unstable subspace onto itself: a vector of the unstable subspace has a preimage
in it.

Proof: `w 1`, with the backward orbit `n ↦ w (n + 1)`. -/
theorem exists_mem_unstableSubspace_apply_eq {A : E →L[ℝ] E} {v : E}
    (hv : v ∈ A.unstableSubspace) : ∃ w ∈ A.unstableSubspace, A w = v := by
  sorry

/-- The stable subspace of `e⁻¹` is the unstable subspace of `e`.

Proof: a backward orbit of `e` is unique, `w n = e⁻ⁿ v`, so `v` lies in the unstable subspace of
`e` if and only if `e⁻ⁿ v → 0`. -/
theorem stableSubspace_symm (e : E ≃L[ℝ] E) :
    stableSubspace (e.symm : E →L[ℝ] E) = unstableSubspace (e : E →L[ℝ] E) := by
  sorry

/-- The unstable subspace of `e⁻¹` is the stable subspace of `e`.

Proof: a backward orbit of `e⁻¹` is unique, `w n = eⁿ v`. -/
theorem unstableSubspace_symm (e : E ≃L[ℝ] E) :
    unstableSubspace (e.symm : E →L[ℝ] E) = stableSubspace (e : E →L[ℝ] E) := by
  sorry

end General

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear map is **hyperbolic** if it has no eigenvalue of absolute value `1`: no complex root
of its characteristic polynomial has modulus `1`. (A real operator may have non-real eigenvalues,
so the eigenvalues are the complex roots of `LinearMap.charpoly`.) -/
def IsHyperbolic (A : E →L[ℝ] E) : Prop :=
  ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ ≠ 1

/-- In finite dimension the stable and unstable subspaces are **disjoint**, for every `A`.

Proof: on `V = Eₛ ⊓ Eᵤ`, `A` restricts to a bijection `T` with `Tⁿ v → 0` and `T⁻ⁿ v → 0` for
every `v`; by `exists_norm_pow_lt_one_of_tendsto` some powers of `T` and `T⁻¹` have norm `< 1`,
so `‖1‖ < 1` on `V`, and `V = 0`. -/
theorem disjoint_stableSubspace_unstableSubspace (A : E →L[ℝ] E) :
    Disjoint A.stableSubspace A.unstableSubspace := by
  sorry

/-- `A` is injective on its unstable subspace.

Proof: if `A v = A v'` then `v - v' ∈ Eᵤ` and `Aⁿ (v - v') = 0` for `n ≥ 1`, so
`v - v' ∈ Eₛ ⊓ Eᵤ = 0` (`disjoint_stableSubspace_unstableSubspace`). -/
theorem injOn_unstableSubspace (A : E →L[ℝ] E) :
    Set.InjOn A (A.unstableSubspace : Set E) := by
  sorry

end FiniteDimensional

end ContinuousLinearMap
