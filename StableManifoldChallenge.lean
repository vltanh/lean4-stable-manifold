/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Challenge: the stable manifold theorem for a hyperbolic fixed point

Statements of record, in Mathlib's vocabulary, for

* **the stable manifold theorem** for a `Cⁿ` map (`1 ≤ n ≤ ∞`) near a hyperbolic fixed point of a
  finite-dimensional real normed space, in graph form, for the local stable and the local
  unstable set (J. Hadamard, *Sur l'itération et les solutions asymptotiques des équations
  différentielles*, Bull. Soc. Math. France 29 (1901), 224–228; O. Perron, *Über Stabilität und
  asymptotisches Verhalten der Lösungen eines Systems endlicher Differenzengleichungen*, J. Reine
  Angew. Math. 161 (1929), 41–64; in this form, M. C. Irwin, *Smooth Dynamical Systems*, Academic
  Press, 1980, Chapter 6);
* **the hyperbolic splitting**: the stable and unstable subspaces of a hyperbolic linear map are
  complementary;
* two facts that tie the definitions of the unstable subspace and of the local unstable set to
  their usual forms for invertible maps.

The proofs are in `StableManifoldSolution.lean`.

## Definitions

The block between the markers `BEGIN SHARED DEFINITIONS` and `END SHARED DEFINITIONS` is a word for
word copy of the block of the library module `StableManifold/Defs.lean`, which imports exactly what
this file imports (`scripts/sync_challenge_defs.py` keeps the two equal), so that the constants of
the statements are the same here and in the library. It defines:

* `Function.localStableSet f p U = {x | ∀ k, fᵏ x ∈ U, and fᵏ x → p}`, for a map `f : X → X` of a
  topological space, a point `p` and a set `U` (`f^[k]` is the `k`-th iterate of `f`);
* `Function.localUnstableSet f p U`: the points `x` that have a backward orbit in `U` tending to
  `p`, that is, a sequence `y` with `y 0 = x`, `y k ∈ U` and `f (y (k + 1)) = y k` for every `k`,
  and `y k → p`. It needs no inverse of `f`; for an invertible `f` it is the local stable set of
  `f⁻¹` (`StableManifoldChallenge.localStableSet_symm` below);
* `ContinuousLinearMap.stableSubspace A = {v | Aᵏ v → 0}`, for a continuous linear map `A` of a
  real normed space `E`, as a `Submodule ℝ E`;
* `ContinuousLinearMap.unstableSubspace A`: the vectors `v` that have a backward orbit tending to
  `0`, that is, a sequence `w` with `w 0 = v`, `A (w (k + 1)) = w k` and `w k → 0`; for an
  invertible `A` it is `{v | A⁻ᵏ v → 0}`, the stable subspace of `A⁻¹`
  (`StableManifoldChallenge.stableSubspace_symm` below);
* `ContinuousLinearMap.IsHyperbolic A`, for `E` finite-dimensional: no complex root `μ` of the
  characteristic polynomial of `A` (an eigenvalue of `A` or of its complexification) has
  `|μ| = 1`.

## Conventions

* A *finite-dimensional real normed space* `E` (`[NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]`) is `ℝᵈ`, for some `d ≥ 0`, with some norm. All norms on it are
  equivalent, and nothing in the statements depends on the choice: neighborhoods, open sets,
  limits, derivatives and smoothness are the same for every norm.
* `𝓝 x` is the filter of neighborhoods of `x`: `V ∈ 𝓝 x` says that `V` is a neighborhood of `x`,
  not necessarily open.
* `n : ℕ∞` with `1 ≤ n` is `1, 2, …` or `∞` (`⊤`). `ContDiffOn ℝ n f W`: `f` is of class `Cⁿ` on
  `W`. With `W ∈ 𝓝 p`, `f` is `Cⁿ` near `p`; `f` is a total function `E → E`, and its values
  outside `W` are arbitrary.
* `fderiv ℝ f p : E →L[ℝ] E` is the derivative `A = Df(p)` of `f` at `p`, which exists since `f` is
  `C¹` near `p`. `(fderiv ℝ f p).IsInvertible`: `A` is a linear isomorphism of `E`, so that `f` is
  a local diffeomorphism at `p`.
* A submodule `K` of `E` is used as a type: its elements are pairs of a vector `x : E` and a proof
  that `x ∈ K`, `↑x : E` is the vector, and `K` carries the norm of `E`, so that `ContDiffOn`,
  `fderiv` and `𝓝` make sense for maps `K → L` between submodules. `0 : K` is the zero vector.
* `(fun x ↦ p + ↑x + ↑(hs x)) '' Vs` is the set `{p + x + hs(x) | x ∈ Vs}`: the graph of
  `hs : Eₛ → Eᵤ` over `Vs`, translated to `p`.
* `IsCompl K L`: `K ⊓ L = 0` and `K ⊔ L = E`, that is, `E = K ⊕ L`.
* `E ≃L[ℝ] E` is the type of linear isomorphisms of `E` (continuous with continuous inverse,
  automatic in finite dimension), `e.symm` the inverse of `e`, and `(e : E →L[ℝ] E)` `e` as a
  continuous linear map.
* An `OpenPartialHomeomorph X X` is a homeomorphism `e` from an open set `e.source` onto an open
  set `e.target`, with inverse `e.symm`; both are total functions `X → X`.

## The theorems

* `StableManifoldChallenge.stable_manifold` (**the stable manifold theorem**): let `f` be `Cⁿ`
  (`1 ≤ n ≤ ∞`) on a neighborhood of a fixed point `p` of a finite-dimensional real normed space
  `E`, with derivative `A = Df(p)` invertible and hyperbolic, and let `Eₛ`, `Eᵤ` be the stable and
  unstable subspaces of `A`. Then there are an open neighborhood `U` of `p` and maps
  `hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ` such that
  - `hₛ` is `Cⁿ` on a neighborhood `Vₛ` of `0` in `Eₛ`, `hₛ 0 = 0`, `Dhₛ(0) = 0`, and the local
    stable set of `f` in `U` is the graph `{p + x + hₛ(x) | x ∈ Vₛ}`;
  - `hᵤ` is `Cⁿ` on a neighborhood `Vᵤ` of `0` in `Eᵤ`, `hᵤ 0 = 0`, `Dhᵤ(0) = 0`, and the local
    unstable set of `f` in `U` is the graph `{p + y + hᵤ(y) | y ∈ Vᵤ}`.

  So, near `p`, the local stable and unstable sets are `Cⁿ` embedded submanifolds through `p`,
  tangent there to `Eₛ` and to `Eᵤ`, of dimensions `dim Eₛ` and `dim Eᵤ`, with
  `dim Eₛ + dim Eᵤ = dim E` by the next theorem. This is the standard formulation of the local
  stable manifold theorem for a `Cⁿ` local diffeomorphism at a hyperbolic fixed point (Irwin's
  book, Chapter 6). The local stable set is the set of points whose forward orbit stays in `U` and
  tends to `p`. Some texts leave out the convergence; for `U` inside a small enough ball around
  `p`, a forward orbit that stays in `U` tends to `p`, and the two definitions agree.
* `StableManifoldChallenge.hyperbolic_splitting` (**the hyperbolic splitting**): for a hyperbolic
  linear map `A` of a finite-dimensional real normed space, `E = Eₛ ⊕ Eᵤ`. (A zero eigenvalue is
  allowed.)
* `StableManifoldChallenge.stableSubspace_symm`: for a linear isomorphism `e`, the stable subspace
  of `e⁻¹` is the unstable subspace of `e`, in any real normed space.
* `StableManifoldChallenge.localStableSet_symm`: for a homeomorphism `e` between open sets of a
  topological space and a set `U` inside both, the local stable set of `e⁻¹` in `U` is the local
  unstable set of `e` in `U`.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS
open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X]

/-- The **local stable set** of `f|_U` at `p`: the points `x` whose forward orbit `fⁿ(x)` stays in
`U` and tends to `p`. (For the iterates of `f|_U` to be defined the orbit must stay in `U`.) -/
def localStableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | (∀ n : ℕ, f^[n] x ∈ U) ∧ Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- The **local unstable set** of `f|_U` at `p`: the points `x` having a backward orbit `y`
(`y 0 = x`, `f (y (n + 1)) = y n`) in `U` that tends to `p`. For an `f` invertible on `U` it is the
local stable set of `f⁻¹|_U`. -/
def localUnstableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | ∃ y : ℕ → X, y 0 = x ∧ (∀ n, y n ∈ U ∧ f (y (n + 1)) = y n) ∧ Tendsto y atTop (𝓝 p)}

end Function

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
(`w 0 = v`, `A (w (n + 1)) = w n`, `w n → 0`). For an invertible `A` it is the stable subspace of
`A⁻¹`; for a hyperbolic `A` it is the sum of the generalized eigenspaces of the eigenvalues of
modulus `> 1`. -/
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

end General

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear map is **hyperbolic** if it has no eigenvalue of absolute value `1`: no complex root
of its characteristic polynomial has modulus `1`. (A real operator may have non-real eigenvalues,
so the eigenvalues are the complex roots of `LinearMap.charpoly`.) -/
def IsHyperbolic (A : E →L[ℝ] E) : Prop :=
  ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ ≠ 1

end FiniteDimensional

end ContinuousLinearMap
-- END SHARED DEFINITIONS

namespace StableManifoldChallenge

/-- **The stable manifold theorem** for a `Cⁿ` map (`1 ≤ n ≤ ∞`) near a fixed point `p` of a
finite-dimensional real normed space, with invertible and hyperbolic derivative `A = Df(p)`: there
are an open neighborhood `U` of `p` and maps `hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ` between the stable and
unstable subspaces of `A`, `Cⁿ` near `0` and vanishing with their derivatives at `0`, such that the
local stable set of `f` in `U` is the graph `{p + x + hₛ x}` of `hₛ` over a neighborhood of `0` in
`Eₛ`, and the local unstable set of `f` in `U` is the graph `{p + y + hᵤ y}` of `hᵤ` over a
neighborhood of `0` in `Eᵤ`. -/
theorem stable_manifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} {p : E} {W : Set E} {n : ℕ∞} (hn : 1 ≤ n)
    (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧
      (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
        ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
          ContDiffOn ℝ n hs Vs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
          Function.localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
      (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
        ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
          ContDiffOn ℝ n hu Vu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
          Function.localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  sorry

/-- **The hyperbolic splitting**: the stable and unstable subspaces of a hyperbolic linear map `A`
of a finite-dimensional real normed space are complementary, `E = Eₛ ⊕ Eᵤ`. -/
theorem hyperbolic_splitting {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    IsCompl A.stableSubspace A.unstableSubspace := by
  sorry

/-- The stable subspace of the inverse of a linear isomorphism `e` is the unstable subspace of
`e`: `{v | e⁻ᵏ v → 0}` is the set of vectors with a backward `e`-orbit tending to `0`. -/
theorem stableSubspace_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] E) :
    ContinuousLinearMap.stableSubspace (e.symm : E →L[ℝ] E) =
      ContinuousLinearMap.unstableSubspace (e : E →L[ℝ] E) := by
  sorry

/-- For a homeomorphism `e` between open sets and a set `U` inside its source and its target, the
local stable set of `e⁻¹` in `U` is the local unstable set of `e` in `U`. -/
theorem localStableSet_symm {X : Type*} [TopologicalSpace X] (e : OpenPartialHomeomorph X X)
    {p : X} {U : Set X} (hU : U ⊆ e.source ∩ e.target) :
    Function.localStableSet e.symm p U = Function.localUnstableSet e p U := by
  sorry

end StableManifoldChallenge
