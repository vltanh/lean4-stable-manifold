/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Powers of a linear operator with spectrum in the open unit disk

For a linear operator `A` of a finite-dimensional real normed space, the eigenvalues are the complex
roots of its characteristic polynomial `LinearMap.charpoly` (a real operator may have non-real
eigenvalues, and `spectrum ℝ` would miss them, so hypotheses are stated with `Polynomial.aeval μ`
for `μ : ℂ`).

* `ContinuousLinearMap.exists_norm_pow_lt_one`: if every complex root of the characteristic
  polynomial of `A` has modulus `< 1`, then `‖A ^ N‖ < 1` for some `N ≥ 1` (Gelfand's formula);
* `ContinuousLinearMap.exists_norm_pow_lt_one_of_aeval_eq_zero`: the same when `A` is annihilated
  by a real polynomial whose complex roots all have modulus `< 1`;
* `ContinuousLinearMap.exists_norm_pow_lt_one_of_tendsto`: if every orbit `Aⁿ v` tends to `0`,
  then `‖A ^ N‖ < 1` for some `N ≥ 1` (finite dimension);
* `ContinuousLinearMap.exists_norm_pow_le_mul_pow`: if `‖A ^ N‖ < 1` with `N ≥ 1`, then
  `‖Aⁿ‖ ≤ C rⁿ` for all `n`, with `r < 1` (any normed space);
* `ContinuousLinearMap.exists_norm_pow_le_mul_pow_of_tendsto`,
  `ContinuousLinearMap.tendsto_pow_apply_of_aeval_eq_zero`: the two combinations used later.

Mathlib has Gelfand's formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`, in
the form `spectrum.spectralRadius_eq_gelfandRadius`) for complex Banach algebras.

## Proofs (plan)

`exists_norm_pow_lt_one` is proved below. Size of the rest: 150–250 lines.

* `exists_norm_pow_lt_one_of_aeval_eq_zero`: as `exists_norm_pow_lt_one`, with the private lemma
  `exists_entry_bound` (stated for a complex matrix whose spectrum lies in the open unit disk).
  For the complexified matrix `M` of `A`, `spectrum.subset_polynomial_aeval` gives
  `q(z) ∈ spectrum ℂ (aeval M q)` for `z ∈ spectrum ℂ M`; and `aeval M q = 0`, since
  `LinearMap.toMatrix` (`LinearMap.toMatrixAlgEquiv`) and the entrywise map `ℝ → ℂ`
  (`AlgHom.mapMatrix`) are algebra homomorphisms (`Polynomial.aeval_algHom_apply`,
  `Polynomial.aeval_algEquiv`). The spectrum of `0` is `{0}` (`spectrum.zero_eq`), so `q(z) = 0`
  and `‖z‖ < 1`.
* `exists_norm_pow_lt_one_of_tendsto`: with a basis `b` (`Module.finBasis`),
  `Module.Basis.opNorm_le` bounds `‖Aⁿ‖` by a constant times `maxᵢ ‖Aⁿ (b i)‖`, which tends to `0`;
  so `‖Aⁿ‖ < 1` for some large `n`.
* `exists_norm_pow_le_mul_pow`: let `ρ = max (1/2) ‖A ^ N‖ < 1` and `r = ρ ^ (1 / N)` (real power).
  Write `n = N q + j` with `j < N` (`Nat.div_add_mod`); then
  `‖Aⁿ‖ ≤ ‖A ^ N‖ ^ q ‖A ^ j‖ ≤ ρ ^ q K ≤ (K / ρ) rⁿ` with `K = max 1 (max_{j < N} ‖A ^ j‖)`
  (`norm_pow_le'`, `Real.rpow_natCast`, `Real.rpow_mul`).
* The two combinations: compose the lemmas above.
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Matrix.Norms.Operator in
/-- Gelfand's formula for a complex matrix whose spectrum lies in the open unit disk: its powers
decay geometrically, entry by entry. (The matrix is normed by the `L∞`-operator norm, a Banach
algebra norm.) -/
private lemma exists_entry_bound {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ z ∈ spectrum ℂ M, ‖z‖ < 1) :
    ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (n : ℕ) (i j : Fin d), ‖(M ^ n) i j‖ ≤ C * r ^ n := by
  have : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℂ _
  have hrad : spectralRadius ℂ M < 1 := by
    rcases (spectrum ℂ M).eq_empty_or_nonempty with h | h
    · simp [spectralRadius_eq_of_unital, h]
    · obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty h
      rw [← hzr]
      have hz1 : ‖z‖ < 1 := hM z hz
      exact_mod_cast hz1
  have hg : gelfandRadius M < 1 := by
    rw [spectrum.spectralRadius_eq_gelfandRadius] at hrad
    exact ENNReal.ofReal_lt_one.1 hrad
  obtain ⟨C, -, hC⟩ :=
    norm_pow_le_mul_pow_of_gelfandRadius_lt M (r := (gelfandRadius M + 1) / 2) (by linarith)
  refine ⟨C, (gelfandRadius M + 1) / 2, by positivity, by linarith, fun n i j ↦ ?_⟩
  exact (Matrix.norm_apply_le_linfty_opNorm _ i j).trans (hC n)

/-- If every complex eigenvalue of a linear operator `A` of a finite-dimensional real normed space
(every root in `ℂ` of its characteristic polynomial) has modulus `< 1`, then some power `A ^ N`,
`N ≥ 1`, has operator norm `< 1`.

Proof: complexify. Choose a basis (`Module.finBasis`), so that `A` is a real matrix `M`, and view
`M` as a complex matrix, normed by the `L∞`-operator norm (a complex Banach algebra). The spectrum
of the complex matrix is the set of roots of its characteristic polynomial
(`Matrix.mem_spectrum_iff_isRoot_charpoly`), which are the complex roots of the characteristic
polynomial of `A` (`Matrix.charpoly_map`, `LinearMap.charpoly_toMatrix`), so its spectral radius
is `< 1`. By Gelfand's formula (`spectrum.spectralRadius_eq_gelfandRadius`,
`norm_pow_le_mul_pow_of_gelfandRadius_lt`), `‖Mⁿ‖ ≤ C rⁿ` with `r < 1`, so the entries of `Mⁿ`
tend to `0`. The linear map from matrices to `E →L[ℝ] E` is continuous (finite dimension), so
`Aⁿ → 0`, and `‖Aⁿ‖ < 1` for large `n`. -/
theorem exists_norm_pow_lt_one (A : E →L[ℝ] E)
    (hA : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  classical
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  -- The complexified matrix: its eigenvalues are the complex roots of the charpoly of `A`.
  obtain ⟨C, r, hr0, hr1, hC⟩ := exists_entry_bound (M.map (algebraMap ℝ ℂ)) fun z hz ↦
    hA z (by
      have hz' := Matrix.mem_spectrum_iff_isRoot_charpoly.1 hz
      rwa [Polynomial.IsRoot.def, Matrix.charpoly_map, LinearMap.charpoly_toMatrix,
        Polynomial.eval_map_algebraMap] at hz')
  -- Hence the real matrices `M ^ n` tend to `0`, entry by entry.
  have hM : Tendsto (fun n : ℕ ↦ M ^ n) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ ?_
    have hlim : Tendsto (fun n : ℕ ↦ C * r ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
    refine squeeze_zero_norm (fun n ↦ ?_) hlim
    have h := hC n i j
    rwa [← Matrix.map_pow, Matrix.map_apply, Complex.coe_algebraMap, Complex.norm_real] at h
  -- Transfer to `E →L[ℝ] E` through the linear map `Matrix → (E →L[ℝ] E)`, which is continuous
  -- since the space of matrices is finite-dimensional.
  let Ψ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →ₗ[ℝ] (E →L[ℝ] E) :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap ∘ₗ
      (Matrix.toLin b b).toLinearMap
  have hΨ : ∀ n : ℕ, Ψ (M ^ n) = A ^ n := by
    intro n
    ext x
    simp [Ψ, M, LinearMap.toMatrix_pow, ← ContinuousLinearMap.toLinearMap_pow]
  have hT : Tendsto (fun n : ℕ ↦ A ^ n) atTop (𝓝 0) := by
    have h := (Ψ.continuous_of_finiteDimensional.tendsto 0).comp hM
    simpa [Function.comp_def, hΨ] using h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.norm.eventually (gt_mem_nhds (a := (1 : ℝ)) (by simp)))
  exact ⟨N + 1, N.succ_pos, hN (N + 1) (by omega)⟩

/-- If a linear operator `A` of a finite-dimensional real normed space is annihilated by a real
polynomial `q` whose complex roots all have modulus `< 1`, then some power `A ^ N`, `N ≥ 1`, has
operator norm `< 1`. (The hypothesis on the roots forces `q ≠ 0`.)

Proof: as `exists_norm_pow_lt_one`, with the spectrum of the complexified matrix `M` of `A`
contained in the roots of `q`: `spectrum.subset_polynomial_aeval` gives
`q(z) ∈ spectrum ℂ (aeval M q) = spectrum ℂ 0 ⊆ {0}` for `z ∈ spectrum ℂ M`, since `aeval M q` is
the complexified matrix of `aeval A q = 0`. -/
theorem exists_norm_pow_lt_one_of_aeval_eq_zero (A : E →L[ℝ] E) {q : Polynomial ℝ}
    (hq : Polynomial.aeval (A : E →ₗ[ℝ] E) q = 0)
    (hroots : ∀ μ : ℂ, Polynomial.aeval μ q = 0 → ‖μ‖ < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  sorry

/-- In finite dimension, if every orbit `Aⁿ v` tends to `0`, then some power `A ^ N`, `N ≥ 1`, has
operator norm `< 1`.

Proof: with a basis `b`, `Module.Basis.opNorm_le` gives `‖Aⁿ‖ ≤ K maxᵢ ‖Aⁿ (b i)‖ → 0`. -/
theorem exists_norm_pow_lt_one_of_tendsto (A : E →L[ℝ] E)
    (hA : ∀ v, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  sorry

omit [FiniteDimensional ℝ E] in
/-- **Geometric decay** from one contracting power: if `‖A ^ N‖ < 1` with `N ≥ 1`, then
`‖Aⁿ‖ ≤ C rⁿ` for all `n`, with `1 ≤ C` and `0 < r < 1`.

Proof: with `ρ = max (1/2) ‖A ^ N‖` and `r = ρ ^ (1 / N)`, write `n = N q + j`, `j < N`; then
`‖Aⁿ‖ ≤ ρ ^ q K ≤ (K / ρ) rⁿ`, where `K` bounds `‖A ^ j‖` for `j < N`. -/
theorem exists_norm_pow_le_mul_pow (A : E →L[ℝ] E) {N : ℕ} (hN : 0 < N) (hA : ‖A ^ N‖ < 1) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n := by
  sorry

/-- In finite dimension, if every orbit `Aⁿ v` tends to `0`, then `‖Aⁿ‖ ≤ C rⁿ` for all `n`, with
`1 ≤ C` and `0 < r < 1`.

Proof: `exists_norm_pow_lt_one_of_tendsto` and `exists_norm_pow_le_mul_pow`. -/
theorem exists_norm_pow_le_mul_pow_of_tendsto (A : E →L[ℝ] E)
    (hA : ∀ v, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n := by
  sorry

/-- If `A` is annihilated by a real polynomial whose complex roots all have modulus `< 1`, then
every orbit `Aⁿ v` tends to `0`.

Proof: `exists_norm_pow_lt_one_of_aeval_eq_zero` and `exists_norm_pow_le_mul_pow` give
`‖Aⁿ v‖ ≤ C rⁿ ‖v‖` with `r < 1`. -/
theorem tendsto_pow_apply_of_aeval_eq_zero (A : E →L[ℝ] E) {q : Polynomial ℝ}
    (hq : Polynomial.aeval (A : E →ₗ[ℝ] E) q = 0)
    (hroots : ∀ μ : ℂ, Polynomial.aeval μ q = 0 → ‖μ‖ < 1) (v : E) :
    Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0) := by
  sorry

end ContinuousLinearMap
