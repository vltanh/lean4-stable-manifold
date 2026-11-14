/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.Linear.Subspaces
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# The hyperbolic splitting

For a hyperbolic linear map `A` of a finite-dimensional real normed space, the stable and unstable
subspaces are complementary, `E = Eₛ ⊕ Eᵤ`
(`ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`). They are the sums of the
generalized eigenspaces of the eigenvalues of modulus `< 1`, resp. `> 1`; a zero eigenvalue is
allowed.

* `Polynomial.norm_eq_of_irreducible`: the complex roots of an irreducible real polynomial all
  have the same modulus;
* `Polynomial.exists_isCoprime_roots_lt_one_one_lt`: a real polynomial without complex roots on
  the unit circle is, up to a unit, a product `pₛ pᵤ` of coprime factors with all roots inside,
  resp. outside, the unit circle;
* `Polynomial.norm_lt_one_of_aeval_reverse_eq_zero`: the roots of the reverse of a polynomial with
  roots outside the unit circle lie inside;
* `ContinuousLinearMap.aeval_symm_reverse_eq_zero`: if `q(T) = 0` for an invertible `T`, then
  `q.reverse (T⁻¹) = 0`;
* `ContinuousLinearMap.ker_aeval_le_stableSubspace`, `ker_aeval_le_unstableSubspace`: the kernel of
  `pₛ(A)` lies in the stable subspace, the kernel of `pᵤ(A)` in the unstable one;
* `ContinuousLinearMap.codisjoint_stableSubspace_unstableSubspace`: for a hyperbolic `A`,
  `Eₛ ⊔ Eᵤ = ⊤`.

## Proofs (plan)

Size: 350–550 lines.

* `norm_eq_of_irreducible`: `natDegree q ≤ 2` (`Irreducible.natDegree_le_two`). If `q` has a real
  root `r` then `X - C r ∣ q` and `q` has degree `1`, with the single root `r`. Otherwise every
  complex root `μ` is non-real (`Complex.conj_eq_iff_real`), `conj μ` is a root too
  (`Polynomial.aeval_conj`), and `q.map ofReal = c (X - μ) (X - conj μ)` (degree `2`), so every
  root is `μ` or `conj μ`, of modulus `‖μ‖` (`Complex.norm_conj`).
* `exists_isCoprime_roots_lt_one_one_lt`: split the normalized factors
  (`UniqueFactorizationMonoid.normalizedFactors p`) by the predicate "all complex roots have
  modulus `< 1`": `pₛ` is the product of those that satisfy it, `pᵤ` of the others
  (`Multiset.prod_filter_mul_prod_filter_not`), and `Associated (pₛ * pᵤ) p`
  (`UniqueFactorizationMonoid.prod_normalizedFactors`). A complex root of a product is a root of a
  factor (`map_multiset_prod`, `Multiset.prod_eq_zero_iff`). An irreducible factor not in `pₛ` has
  some root of modulus `≥ 1`, hence `> 1` (no root of `p` has modulus `1`), hence all its roots
  have modulus `> 1` by `norm_eq_of_irreducible`; it has a root at all since its degree is
  positive (`IsAlgClosed.exists_aeval_eq_zero`). Coprimality: no common complex root
  (`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` with `K = ℂ`).
* `norm_lt_one_of_aeval_reverse_eq_zero`: `q ≠ 0` (else every `μ` is a root, and `1 < ‖0‖`
  fails); `aeval 0 q.reverse = q.leadingCoeff ≠ 0` (`Polynomial.coeff_zero_reverse`), so `ν ≠ 0`,
  and `Polynomial.eval₂_reverse_eq_zero_iff` with `x = ν⁻¹` gives `aeval ν⁻¹ q = 0`, so
  `1 < ‖ν⁻¹‖`.
* `aeval_symm_reverse_eq_zero`: with `q = ∑ cᵢ Xⁱ` of degree `d`,
  `q.reverse (T⁻¹) ∘ Tᵈ = ∑ cᵢ T⁻⁽ᵈ⁻ⁱ⁾ Tᵈ = ∑ cᵢ Tⁱ = q(T) = 0` (`Polynomial.coeff_reverse`,
  `Polynomial.aeval_eq_sum_range`, `T⁻¹` and `T` commute), and `Tᵈ` is invertible.
* `ker_aeval_le_stableSubspace`: `K = ker q(A)` is `A`-invariant (`A` commutes with `q(A)`,
  `Polynomial.aeval_algHom_apply` or `Module.End.mul_apply`); the restriction
  `Aₖ : K →L[ℝ] K` (`ContinuousLinearMap.restrict`) satisfies `q(Aₖ) = 0` (evaluate on `K`, using
  that restriction commutes with polynomials, `LinearMap.restrict` and `aeval`); then
  `tendsto_pow_apply_of_aeval_eq_zero` gives `Aₖⁿ v → 0`, that is `Aⁿ v → 0`.
* `ker_aeval_le_unstableSubspace`: `q.coeff 0 ≠ 0` (`0` is not a root), so `Aₖ` is injective
  (`q(Aₖ) v = q.coeff 0 • v + Aₖ (…)`), hence a continuous linear equivalence `T` of `K` (finite
  dimension). By `aeval_symm_reverse_eq_zero` and `norm_lt_one_of_aeval_reverse_eq_zero`,
  `tendsto_pow_apply_of_aeval_eq_zero` applies to `T⁻¹`: `w n = T⁻ⁿ v → 0` is a backward orbit of
  `v`.
* `codisjoint_stableSubspace_unstableSubspace`: with `χ = charpoly A` (nonzero, monic) and
  `pₛ pᵤ` from `exists_isCoprime_roots_lt_one_one_lt`,
  `ker pₛ(A) ⊔ ker pᵤ(A) = ker (pₛ pᵤ)(A) = ker (u χ)(A) = ⊤`
  (`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`, Cayley–Hamilton
  `LinearMap.aeval_self_charpoly`, a unit `u` of `ℝ[X]` is a nonzero constant,
  `Polynomial.isUnit_iff`), and the two kernels lie in `Eₛ` and `Eᵤ`.
-/

@[expose] public section

open Filter Topology Polynomial

namespace Polynomial

/-- The complex roots of an irreducible real polynomial all have the **same modulus**: an
irreducible real polynomial has degree `1` (one real root) or `2` (a pair of conjugate roots).

Proof: `Irreducible.natDegree_le_two`; in degree `2` the roots are `μ` and `conj μ`. -/
theorem norm_eq_of_irreducible {q : ℝ[X]} (hq : Irreducible q) {μ ν : ℂ} (hμ : aeval μ q = 0)
    (hν : aeval ν q = 0) : ‖μ‖ = ‖ν‖ := by
  sorry

/-- A real polynomial `p ≠ 0` without complex roots on the unit circle is, up to a unit, a product
`pₛ pᵤ` of **coprime factors** with all complex roots inside, resp. outside, the unit circle.

Proof: split the normalized factors of `p` by the modulus of their roots (all roots of an
irreducible factor have the same modulus, `norm_eq_of_irreducible`); the two products have no
common complex root, so they are coprime. -/
theorem exists_isCoprime_roots_lt_one_one_lt {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ μ : ℂ, aeval μ p = 0 → ‖μ‖ ≠ 1) :
    ∃ ps pu : ℝ[X], Associated (ps * pu) p ∧ IsCoprime ps pu ∧
      (∀ μ : ℂ, aeval μ ps = 0 → ‖μ‖ < 1) ∧ (∀ μ : ℂ, aeval μ pu = 0 → 1 < ‖μ‖) := by
  sorry

/-- If every complex root of `q` has modulus `> 1`, every complex root of `q.reverse` has modulus
`< 1`: the roots of the reverse are the inverses of the nonzero roots.

Proof: `q ≠ 0`, `aeval 0 q.reverse = q.leadingCoeff ≠ 0`, and
`Polynomial.eval₂_reverse_eq_zero_iff` at `ν⁻¹`. -/
theorem norm_lt_one_of_aeval_reverse_eq_zero {q : ℝ[X]} (hq : ∀ μ : ℂ, aeval μ q = 0 → 1 < ‖μ‖)
    {ν : ℂ} (hν : aeval ν q.reverse = 0) : ‖ν‖ < 1 := by
  sorry

end Polynomial

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If an invertible operator `T` is annihilated by `q`, its inverse is annihilated by the reverse
of `q`.

Proof: `q.reverse (T⁻¹) ∘ T ^ q.natDegree = q(T) = 0` (`Polynomial.coeff_reverse`), and
`T ^ q.natDegree` is invertible. -/
theorem aeval_symm_reverse_eq_zero (T : E ≃L[ℝ] E) {q : ℝ[X]}
    (hq : aeval ((T : E →L[ℝ] E) : E →ₗ[ℝ] E) q = 0) :
    aeval ((T.symm : E →L[ℝ] E) : E →ₗ[ℝ] E) q.reverse = 0 := by
  sorry

variable [FiniteDimensional ℝ E]

/-- The kernel of `q(A)`, for a real polynomial `q` with all complex roots of modulus `< 1`, lies
in the **stable subspace**.

Proof: the restriction of `A` to the invariant subspace `ker q(A)` is annihilated by `q`, so its
powers tend to `0` (`tendsto_pow_apply_of_aeval_eq_zero`). -/
theorem ker_aeval_le_stableSubspace (A : E →L[ℝ] E) {q : ℝ[X]}
    (hq : ∀ μ : ℂ, aeval μ q = 0 → ‖μ‖ < 1) :
    LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q) ≤ A.stableSubspace := by
  sorry

/-- The kernel of `q(A)`, for a real polynomial `q` with all complex roots of modulus `> 1`, lies
in the **unstable subspace**.

Proof: the restriction `T` of `A` to `ker q(A)` is invertible (`0` is not a root of `q`), and
`T⁻¹` is annihilated by `q.reverse`, whose roots have modulus `< 1`
(`aeval_symm_reverse_eq_zero`, `norm_lt_one_of_aeval_reverse_eq_zero`); so `n ↦ T⁻ⁿ v` is a
backward orbit tending to `0` (`tendsto_pow_apply_of_aeval_eq_zero`). -/
theorem ker_aeval_le_unstableSubspace (A : E →L[ℝ] E) {q : ℝ[X]}
    (hq : ∀ μ : ℂ, aeval μ q = 0 → 1 < ‖μ‖) :
    LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q) ≤ A.unstableSubspace := by
  sorry

/-- For a hyperbolic `A`, the stable and unstable subspaces **span** the space.

Proof: factor the characteristic polynomial `χ` as `pₛ pᵤ` (up to a unit) with coprime factors
(`Polynomial.exists_isCoprime_roots_lt_one_one_lt`); then
`ker pₛ(A) ⊔ ker pᵤ(A) = ker χ(A) = ⊤` (`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`,
`LinearMap.aeval_self_charpoly`), and `ker pₛ(A) ≤ Eₛ`, `ker pᵤ(A) ≤ Eᵤ`. -/
theorem codisjoint_stableSubspace_unstableSubspace {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    Codisjoint A.stableSubspace A.unstableSubspace := by
  sorry

/-- **The hyperbolic splitting**: for a hyperbolic linear map the stable and unstable subspaces are
complementary, `E = Eₛ ⊕ Eᵤ`. -/
theorem isCompl_stableSubspace_unstableSubspace {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    IsCompl (stableSubspace A) (unstableSubspace A) :=
  ⟨A.disjoint_stableSubspace_unstableSubspace, codisjoint_stableSubspace_unstableSubspace hA⟩

end ContinuousLinearMap
