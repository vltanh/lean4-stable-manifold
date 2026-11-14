# The stable manifold theorem in Lean: details

The statements in words and in Lean, what the axiom audit checks, the proof module by module, the
design choices, what Mathlib had and lacked, the sources, the other formalizations, and the files.
The [README](../README.md) has the overview.

- [Statements](#statements)
- [The axiom audit](#the-axiom-audit)
- [The proof, module by module](#the-proof-module-by-module)
- [Design choices](#design-choices)
- [What Mathlib had and lacked](#what-mathlib-had-and-lacked)
- [Sources](#sources)
- [Other formalizations](#other-formalizations)
- [Files](#files)

## Statements

### In words

Let `E` be a finite-dimensional real normed space, `f : E → E` a map that is `Cⁿ`, `1 ≤ n ≤ ∞`,
on a neighborhood of a fixed point `p`, and `A = Df(p)`. Suppose that `A` is invertible and
hyperbolic: no complex eigenvalue of `A` has modulus `1`. Let `Eₛ = {v | Aᵏ v → 0}` and `Eᵤ` (the
vectors with a backward `A`-orbit tending to `0`, that is `{v | A⁻ᵏ v → 0}`) be the stable and
unstable subspaces of `A`; then `E = Eₛ ⊕ Eᵤ`, with `Eₛ = ker pₛ(A)` and `Eᵤ = ker pᵤ(A)` for the
factors `pₛ`, `pᵤ` of the characteristic polynomial with roots inside, resp. outside, the unit
circle. There are a neighborhood `N` of `p` and `Cⁿ` maps `hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ`, with
`hₛ(0) = 0`, `Dhₛ(0) = 0`, `hᵤ(0) = 0`, `Dhᵤ(0) = 0`, such that for every neighborhood `U` of `p`
inside `N`

- the local stable set `{x | fᵏ(x) ∈ U for all k ≥ 0, and fᵏ(x) → p}` is the graph
  `{p + x + hₛ(x) | x ∈ Vₛ}` over a neighborhood `Vₛ` of `0` in `Eₛ`;
- the local unstable set, the points with a backward orbit `x = y₀, y₁, …` in `U`
  (`f(yₖ₊₁) = yₖ`) tending to `p`, is the graph `{p + y + hᵤ(y) | y ∈ Vᵤ}` over a neighborhood
  `Vᵤ` of `0` in `Eᵤ`.

The maps `hₛ`, `hᵤ` do not depend on `U`; `Vₛ`, `Vᵤ` do. Near `p`, both sets are `Cⁿ` embedded
submanifolds through `p`, tangent there to `Eₛ` and `Eᵤ`. Inside a small neighborhood of `p` the
convergence to `p` is automatic: the local stable set in `U` is the set of points whose forward
orbit stays in `U`, and the local unstable set the set of points with a backward orbit in `U`. The
stable side holds without invertibility, with one `hₛ` for every neighborhood `U` inside a small
ball around `p`.

### The definitions

In [`StableManifold/Defs.lean`](../StableManifold/Defs.lean), the module of which the Challenge
carries a copy:

| Lean | Meaning |
| --- | --- |
| [`Function.localStableSet f p U`](../StableManifold/Defs.lean#L45) | `{x \| ∀ k, f^[k] x ∈ U, and f^[k] x → p}` |
| [`Function.localUnstableSet f p U`](../StableManifold/Defs.lean#L51) | the `x` with a sequence `y`, `y 0 = x`, `y k ∈ U`, `f (y (k + 1)) = y k`, `y k → p` |
| [`ContinuousLinearMap.stableSubspace A`](../StableManifold/Defs.lean#L66) | the submodule `{v \| (A ^ k) v → 0}` |
| [`ContinuousLinearMap.unstableSubspace A`](../StableManifold/Defs.lean#L82) | the submodule of the `v` with a sequence `w`, `w 0 = v`, `A (w (k + 1)) = w k`, `w k → 0` |
| [`ContinuousLinearMap.IsHyperbolic A`](../StableManifold/Defs.lean#L105) | `∀ μ : ℂ`, a root of the characteristic polynomial of `A`, `‖μ‖ ≠ 1` |

The unstable objects are defined by backward orbits, so that they need no inverse; for invertible
maps they are the stable objects of the inverse
([`ContinuousLinearMap.stableSubspace_symm`](../StableManifold/Linear/Subspaces.lean#L107),
[`Function.localStableSet_symm_eq_localUnstableSet`](../StableManifold/LocalSets.lean#L155)).

### In Lean

`E` is a finite-dimensional real normed space throughout (`[NormedAddCommGroup E]
[NormedSpace ℝ E] [FiniteDimensional ℝ E]`).

[`Function.exists_nhds_localStableSet_localUnstableSet_eq_graph`](../StableManifold/Theorem.lean#L191),
the stable manifold theorem:

```lean
theorem Function.exists_nhds_localStableSet_localUnstableSet_eq_graph {f : E → E} {p : E}
    {W : Set E} {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W)
    (hfix : f p = p) (hinv : (fderiv ℝ f p).IsInvertible)
    (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ N ∈ 𝓝 p,
      ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
        ContDiff ℝ n hs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
      ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
        ContDiff ℝ n hu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
      ∀ U ∈ 𝓝 p, U ⊆ N →
        (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
        (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
          localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu)
```

[`Function.exists_localStableSet_localUnstableSet_eq_graph`](../StableManifold/Theorem.lean#L239)
is the form with one open neighborhood `U` of `p` and graph maps stated `Cⁿ` on the neighborhoods
`Vₛ`, `Vᵤ` of `0` (the theorem above with `U = interior N`).

[`Function.exists_nhds_localStableSet_localUnstableSet_eq_setOf`](../StableManifold/Theorem.lean#L267),
under the same hypotheses: the convergence in the definitions of the local sets is automatic.

```lean
theorem Function.exists_nhds_localStableSet_localUnstableSet_eq_setOf ... :
    ∃ N ∈ 𝓝 p, ∀ U ⊆ N,
      localStableSet f p U = {x | ∀ k, f^[k] x ∈ U} ∧
      localUnstableSet f p U = {x | ∃ y : ℕ → E, y 0 = x ∧ ∀ k, y k ∈ U ∧ f (y (k + 1)) = y k}
```

[`Function.exists_localStableSet_eq_graph_of_isCompl`](../StableManifold/Local/StableSet.lean#L266),
the stable side for every small neighborhood, assuming only `E = Eₛ ⊕ Eᵤ`:

```lean
theorem Function.exists_localStableSet_eq_graph_of_isCompl {f : E → E} {p : E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hsplit : IsCompl (fderiv ℝ f p).stableSubspace (fderiv ℝ f p).unstableSubspace) :
    ∃ δ > 0, ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
      ContDiff ℝ n hs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
      ∀ U ∈ 𝓝 p, U ⊆ ball p δ →
        ∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs
```

[`ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`](../StableManifold/Linear/Splitting.lean#L400),
the hyperbolic splitting, and
[`ContinuousLinearMap.exists_stableSubspace_unstableSubspace_eq_ker_aeval`](../StableManifold/Linear/Splitting.lean#L384),
the two subspaces as kernels (by the primary decomposition, `ker pₛ(A)` and `ker pᵤ(A)` are the
sums of the generalized eigenspaces of the eigenvalues of modulus `< 1`, resp. `> 1`):

```lean
theorem ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace {A : E →L[ℝ] E}
    (hA : A.IsHyperbolic) : IsCompl A.stableSubspace A.unstableSubspace

theorem ContinuousLinearMap.exists_stableSubspace_unstableSubspace_eq_ker_aeval {A : E →L[ℝ] E}
    (hA : A.IsHyperbolic) :
    ∃ ps pu : ℝ[X], Associated (ps * pu) (LinearMap.charpoly (A : E →ₗ[ℝ] E)) ∧
      IsCoprime ps pu ∧ (∀ μ : ℂ, aeval μ ps = 0 → ‖μ‖ < 1) ∧
      (∀ μ : ℂ, aeval μ pu = 0 → 1 < ‖μ‖) ∧
      A.stableSubspace = LinearMap.ker (aeval (A : E →ₗ[ℝ] E) ps) ∧
      A.unstableSubspace = LinearMap.ker (aeval (A : E →ₗ[ℝ] E) pu)
```

On the way, for a hyperbolic splitting `S` of `A` (an exponential dichotomy, below) and a
globally small Lipschitz perturbation `F = A + φ` (`StableManifold.Perturbation S`), in a real
Banach space of any dimension:

- [`StableManifold.Perturbation.bddOrbit_iff`](../StableManifold/Perron/Graph.lean#L318): the
  forward `F`-orbit of `x` is bounded if and only if `(1 - P) x = F.graph x`, so the points with a
  bounded orbit form the graph of the Lipschitz map `F.graph` over `Eₛ`;
- [`StableManifold.Perturbation.norm_iterate_le`](../StableManifold/Perron/Graph.lean#L332): such
  orbits decay geometrically;
- [`StableManifold.Perturbation.hasFDerivAt_graph_zero`](../StableManifold/Perron/Graph.lean#L349):
  if `Dφ(0) = 0`, the graph is tangent to `Eₛ`;

and, in finite dimension,
[`StableManifold.Perturbation.contDiff_graph`](../StableManifold/Perron/Smooth.lean#L175): if `φ`
is `Cⁿ`, so is `F.graph`.

## The axiom audit

`lake env lean scripts/Audit.lean` prints the axioms of the main theorems. It checks that they,
the Challenge's theorems as [`StableManifoldSolution.lean`](../StableManifoldSolution.lean) proves
them, and every declaration of the library (345, private and auxiliary ones included) depend only
on `propext`, `Classical.choice` and `Quot.sound`.

It also checks that the hypotheses of the main theorem can be met (for `f x = -2 x` at `0`, whose
derivative is invertible and hyperbolic, with characteristic polynomial `(X + 2) ^ d`), and that
the theorems apply in these forms: for a smooth map of `EuclideanSpace ℝ (Fin d)`; one pair of
graph maps for every ball around `p` of small radius; the dimension count
`dim Eₛ + dim Eᵤ = dim E`; and the stable side for a `C¹` map with hyperbolic, possibly singular,
derivative.

## The proof, module by module

Perron's method, on the Banach space `ℕ →ᵇ E` of bounded sequences (Mathlib's bounded continuous
functions on the discrete space `ℕ`, with the sup norm).

1. **Local sets** ([`LocalSets`](../StableManifold/LocalSets.lean)). Elementary facts: the local
   sets of `f` in `U` depend only on `f` on `U`; conjugating by a homeomorphism (a translation)
   carries them along; the local unstable set of an open partial homeomorphism `e` is the local
   stable set of `e⁻¹`, and a forward `e⁻¹`-orbit is a backward `e`-orbit.
2. **Powers of an operator** ([`Linear/Spectral`](../StableManifold/Linear/Spectral.lean)). If
   every complex root of the characteristic polynomial of `A` has modulus `< 1`, then
   `‖A ^ N‖ < 1` for some `N ≥ 1`: Gelfand's formula, applied to the complexified matrix of `A`.
   If every orbit `Aᵏ v` tends to `0`, the same holds (finite dimension). Then `‖Aᵏ‖ ≤ C rᵏ` with
   `r < 1`.
3. **The subspaces** ([`Linear/Subspaces`](../StableManifold/Linear/Subspaces.lean)). `Eₛ` and
   `Eᵤ` are `A`-invariant, `A` maps `Eᵤ` onto itself, the unstable subspace of `e` is the stable
   subspace of `e⁻¹`, and in finite dimension `Eₛ ⊓ Eᵤ = 0` for every `A`.
4. **The splitting** ([`Linear/Splitting`](../StableManifold/Linear/Splitting.lean)). For a
   hyperbolic `A`, the characteristic polynomial factors, up to a unit, as `pₛ pᵤ` with coprime
   factors whose complex roots lie inside, resp. outside, the unit circle (an irreducible real
   polynomial has all its complex roots of the same modulus). By Cayley–Hamilton,
   `ker pₛ(A) + ker pᵤ(A) = E`; on `ker pₛ(A)` the orbits tend to `0` (step 2), and on
   `ker pᵤ(A)`, where `A` is invertible, the orbits of `A⁻¹` do (step 2, for the reversed
   polynomial). So `Eₛ ⊔ Eᵤ = E`, and with `Eₛ ⊓ Eᵤ = 0` (step 3), `Eₛ = ker pₛ(A)` and
   `Eᵤ = ker pᵤ(A)`: `E = ker pₛ(A) ⊕ ker pᵤ(A)`
   ([`exists_stableSubspace_unstableSubspace_eq_ker_aeval`](../StableManifold/Linear/Splitting.lean#L384)).
5. **The exponential dichotomy**
   ([`Linear/HyperbolicSplitting`](../StableManifold/Linear/HyperbolicSplitting.lean)). From
   `E = Eₛ ⊕ Eᵤ`: the projection `P` onto `Eₛ` along `Eᵤ`, the inverse `B` of `A` on `Eᵤ`
   (extended by `0` on `Eₛ`), and constants `C ≥ 1`, `0 < λ < 1` with `‖Aᵏ P‖ ≤ C λᵏ` and
   `‖Bᵏ (1 - P)‖ ≤ C λᵏ`, bundled as a `HyperbolicSplitting`.
6. **Superposition operators** ([`Sequence/Superpose`](../StableManifold/Sequence/Superpose.lean),
   [`Sequence/SuperposeContDiff`](../StableManifold/Sequence/SuperposeContDiff.lean)). A map
   `φ : E → G` acts on bounded sequences by `x ↦ φ ∘ x`. It is `K`-Lipschitz when `φ` is; and
   when `φ` is `Cⁿ`, `n ≤ ∞`, so is the operator, with derivative `y ↦ (k ↦ Dφ(x k) (y k))`: a
   bounded sequence stays in a compact ball of `E`, on which the derivatives of `φ` are uniformly
   continuous.
7. **The linear Lyapunov–Perron operator**
   ([`Perron/Operator`](../StableManifold/Perron/Operator.lean)). The bounded solutions of
   `z (k + 1) = A (z k) + y k` are `z = stableOrbit ξ + perronOp y`, with
   `stableOrbit ξ k = Aᵏ P ξ` and
   `perronOp y k = ∑_{j < k} A^(k-1-j) P (y j) - ∑_{j ≥ 0} B^(j+1) (y (k + j))`, a bounded operator
   of norm at most `3 C / (1 - λ)`, also in a weighted sup norm.
8. **The global stable manifold** ([`Perron/Graph`](../StableManifold/Perron/Graph.lean)). For
   `F = A + φ` with `φ` `L`-Lipschitz, `φ 0 = 0`, `L · 3C/(1 - λ) ≤ 1/2`, the bounded `F`-orbits
   with stable component `P ξ` at time `0` are the fixed points of the `1/2`-contraction
   `x ↦ stableOrbit ξ + perronOp (φ ∘ x)` of `ℕ →ᵇ E`. The fixed point `orbitSeq ξ` depends
   Lipschitz-continuously on `ξ` and decays geometrically; `graph ξ = (1 - P) (orbitSeq ξ 0)`.
   Then a forward orbit is bounded exactly when it starts on the graph, and such orbits tend to `0`.
   If `Dφ(0) = 0`, `graph ξ = o(ξ)`.
9. **Smoothness** ([`Perron/Smooth`](../StableManifold/Perron/Smooth.lean)). The orbits solve
   `x - perronOp (φ ∘ x) = stableOrbit ξ`. The left side is a `1/2`-Lipschitz perturbation of the
   identity of `ℕ →ᵇ E`, hence a homeomorphism; it is `Cⁿ` by step 6, with derivative `1 - T`,
   `‖T‖ ≤ 1/2`, invertible everywhere. So its inverse is `Cⁿ`, and so are
   `orbitSeq = (inverse) ∘ stableOrbit` and `graph`.
10. **The cut-off** ([`Local/Cutoff`](../StableManifold/Local/Cutoff.lean)). If `g` is `Cⁿ` near
    `0`, `g 0 = 0` and `Dg(0) = A`, then for every `η > 0` there are `δ > 0` and a `Cⁿ`,
    globally `η`-Lipschitz `φ`, with `φ 0 = 0` and `Dφ(0) = 0`, such that `g = A + φ` on the
    ball of radius `δ`: multiply `g - A` by a smooth bump function scaled to the ball.
11. **The local stable manifold** ([`Local/StableSet`](../StableManifold/Local/StableSet.lean)).
    Translate `p` to `0`, cut off with `η` small for the dichotomy's constants, and apply step 8
    to the resulting perturbation: for a neighborhood `U` inside the ball, an orbit staying in `U`
    is bounded, hence on the graph, and tends to `0`; the points of the graph whose orbit stays in
    `U` lie over a neighborhood of `0` in `Eₛ`, by the decay estimate. `hₛ` is `graph`, as a map
    `Eₛ → Eᵤ`, `Cⁿ` by step 9. The same argument shows that inside the ball, every forward orbit
    that stays in `U` tends to `p`.
12. **Both sides** ([`Theorem`](../StableManifold/Theorem.lean)). By the inverse function
    theorem, `f` restricts near `p` to an open partial homeomorphism `e` whose inverse is `Cⁿ`
    with derivative `A⁻¹` at `p`. The stable subspace of `A⁻¹` is `Eᵤ` and its unstable subspace
    `Eₛ`, and the local unstable set of `e` is the local stable set of `e⁻¹`. Step 11 for `f` and
    for `e⁻¹`, on a common neighborhood `N` inside both balls and in the source and target of `e`,
    gives the two graphs for every neighborhood `U ⊆ N` of `p`. The form with one open `U` takes
    `U = interior N`. Inside `N`, a forward `e⁻¹`-orbit in `U` is a backward `f`-orbit, so the
    local unstable set in `U` is the set of points with a backward orbit in `U`.

## Design choices

- **Bounded sequences.** The Lyapunov–Perron operator acts on `ℕ →ᵇ E`, a Banach space that
  Mathlib already has, with its sup norm, evaluations and discrete constructions. The orbits of
  `F` through the points of the stable manifold are the fixed points of one contraction, with the
  stable component as a parameter, so the graph map, its Lipschitz bound and its decay come from
  Mathlib's contraction mapping theorem with parameters.
- **Smoothness through composition operators, not fiber contraction.** Many proofs of `Cʳ`
  regularity, by the graph transform or the Lyapunov–Perron method, use the fiber contraction
  theorem or the `Cʳ` section theorem of Hirsch, Pugh and Shub, one derivative at a time. Here the
  orbit map solves `x - perronOp (φ ∘ x) = stableOrbit ξ`, and smoothness of every order, `∞`
  included, follows at once from two facts: the superposition operator `x ↦ φ ∘ x` on bounded
  sequences is `Cⁿ` when `φ` is (this needs finite dimension), and the inverse of a `Cⁿ`
  homeomorphism with invertible derivative is `Cⁿ` (Mathlib's `Homeomorph.contDiff_symm`). The
  same idea, the implicit function theorem on a space of sequences, is Irwin's proof (1970).
- **The unstable side from the stable side.** Rather than a second construction with backward
  orbits, the unstable side applies the stable side to the local inverse of `f`. This is why the
  main theorem assumes `Df(p)` invertible; the stable side does not.
- **Definitions by orbits.** The stable and unstable subspaces are defined by the behaviour of
  orbits, not as sums of generalized eigenspaces, and hyperbolicity by the complex roots of the
  characteristic polynomial. The statements need no complexification and no Jordan form; the
  splitting is proved by factoring the characteristic polynomial over `ℝ`, and for a hyperbolic
  map the two subspaces are the kernels of the two factors (step 4).
- **Endomorphisms, not subtypes.** The dichotomy is stated with the projection `P` and the
  unstable inverse `B` as endomorphisms of `E` (`HyperbolicSplitting`), so that the analysis of
  steps 7–9 never meets subtypes; the subspaces appear as types only in the final statements.
- **A cut-off by a bump function.** It gives a globally Lipschitz perturbation that is still `Cⁿ`
  everywhere, which step 9 needs; a radial retraction is only Lipschitz across its sphere.
- **One `N` for both sides.** The stable side holds for every neighborhood inside a small ball,
  with one graph map, so one neighborhood `N` serves for `f` and its local inverse, and the
  subspaces of `A⁻¹` are identified with those of `A` once, before quantifying over `U`.
- **The definitions in one module.** The definitions in the statements live in
  [`StableManifold/Defs.lean`](../StableManifold/Defs.lean), which imports exactly what the
  Challenge imports, so that the Challenge's copy produces the same constants and Comparator can
  check the Solution against it without bridge lemmas.

## What Mathlib had and lacked

Mathlib (`v4.36.0-rc2`) had the tools: bounded continuous functions `ℕ →ᵇ E` as a Banach space;
the contraction mapping theorem, with Lipschitz dependence on parameters
(`ContractingWith.fixedPoint_lipschitz_in_map`); Lipschitz perturbations of the identity as
homeomorphisms (`ApproximatesLinearOn.toHomeomorph`) and the smoothness of their inverses
(`Homeomorph.contDiff_symm`); the inverse function theorem as an open partial homeomorphism with a
`Cⁿ` inverse (`OpenPartialHomeomorph.contDiffAt_symm`); smooth bump functions in finite dimension
(`ContDiffBump`); the mean value inequality; Gelfand's formula for complex Banach algebras
(`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`); the characteristic polynomial,
Cayley–Hamilton (`LinearMap.aeval_self_charpoly`) and the kernel decomposition for coprime
polynomials (`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`); unique factorization of real
polynomials; projections onto complementary subspaces.

It lacked everything specific to the theorem: hyperbolic linear maps and their stable and unstable
subspaces, the hyperbolic splitting and exponential dichotomies, Gelfand's formula for real
operators (in the form "spectrum in the open disk gives `‖A ^ N‖ < 1`"), superposition operators on
bounded sequences and their smoothness, the Lyapunov–Perron operator, local stable and unstable
sets, and the stable manifold theorem itself. It has no Hartman–Grobman theorem either: its list of
1000+ theorems has an entry for it without a declaration.

## Sources

- **The theorem.** Its classical sources are J. Hadamard (1901), by what is now called the
  graph transform, and O. Perron's papers of 1929 on differential equations and on difference
  equations (maps, the setting here), by the method now called the Lyapunov–Perron method. The
  form proved here, with `Cⁿ` local stable and unstable manifolds as graphs tangent to `Eₛ` and
  `Eᵤ`, is the one of the textbooks: M. C. Irwin, *Smooth Dynamical Systems* (1980), Chapter 6;
  M. W. Hirsch, C. C. Pugh, M. Shub, *Invariant Manifolds* (1977); M. Shub, *Global Stability of
  Dynamical Systems* (1987).
- **The method.** The proof is Perron's method on bounded sequences, with smoothness from the
  inverse function theorem on the space of sequences; M. C. Irwin, *On the stable manifold
  theorem*, Bull. London Math. Soc. 2 (1970), 196–198, also proves the theorem with the implicit
  function theorem on a space of sequences.
- The formalization follows the standard argument rather than one text, and was not compared
  with these texts line by line.

The full references are in the [README](../README.md#references).

## Other formalizations

Searched on 2026-11-14: Mathlib (the pinned revision and `master`) and its pull requests; GitHub
code search for Lean 3 and Lean 4 repositories; the Lean Zulip archive; the Palomar registry; the
Isabelle AFP; Coq/Rocq (MathComp Analysis, Coquelicot, CoqTail); HOL Light; HOL4; Mizar; Metamath;
ACL2; PVS (NASALib); the lists of 1000+ theorems; arXiv, ITP, CPP and JAR. No earlier formal proof
of the stable manifold theorem for maps was found, in any system, and no formal proof of the
Hartman–Grobman theorem. This work does not use or adapt any of the following.

- **Lean 4, TauCeti** (Apache-2.0): the stable and unstable manifold theorem for an equilibrium of
  a `Cⁿ` vector field (a flow, not a map) in a finite-dimensional real normed space, for a
  linearization with an exponential dichotomy: the confined forward solutions near the equilibrium
  form a `Cⁿ` graph over the stable subspace, tangent to it, and backward solutions over the
  unstable one
  ([`exists_localStableGraph_of_contDiffAt`](https://github.com/TauCetiProject/TauCeti/blob/ca32605ff53921fa0689dd312618b7cfaafa7e43/TauCeti/Analysis/ODE/LyapunovPerron/VectorField.lean#L331),
  [`exists_localUnstableGraph_of_contDiffAt`](https://github.com/TauCetiProject/TauCeti/blob/ca32605ff53921fa0689dd312618b7cfaafa7e43/TauCeti/Analysis/ODE/LyapunovPerron/VectorField.lean#L368)),
  by a Lyapunov–Perron contraction on bounded continuous curves and the implicit function
  theorem. It derives that dichotomy from the spectral condition, no eigenvalue on the imaginary
  axis
  ([`exists_projection_exponential_bounds_of_charpoly`](https://github.com/TauCetiProject/TauCeti/blob/ca32605ff53921fa0689dd312618b7cfaafa7e43/TauCeti/Analysis/ODE/ExponentialDichotomy/Hyperbolic.lean#L357)),
  and has superposition operators on bounded continuous functions
  ([`BoundedContinuousFunction.hasFDerivAt_comp`](https://github.com/TauCetiProject/TauCeti/blob/ca32605ff53921fa0689dd312618b7cfaafa7e43/TauCeti/Analysis/Calculus/FDeriv/BoundedContinuousFunction.lean#L152)).
  Concurrent with this work (the vector-field theorem was first committed on 2026-11-06). It
  treats flows, with the spectral condition on the imaginary axis; this work treats maps, with
  the spectral condition on the unit circle, from which it proves the splitting and the discrete
  dichotomy.
- **Lean 4, lean-eval** (Apache-2.0): a benchmark statement, without a public proof, of the
  set-level part of the theorem for a `C¹` map of `ℝⁿ` with invertible hyperbolic derivative at a
  fixed point: some open `U ∋ x₀` has local stable and unstable sets meeting only at `x₀`
  ([`stable_unstable_manifolds_exist`](https://github.com/leanprover/lean-eval/blob/8955681b9914d7ebc7d286414843021b7d6c9de1/LeanEval/Dynamics/StableUnstableManifolds.lean#L51)).
  Its local sets are defined as here; it does not state that they are manifolds. A copy appears as
  a wanted theorem in
  [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean/blob/970aaf746442807f27e40b02f0e36d1098c53ad7/WantedExt/Dynamics/StableUnstableManifoldsWanted.lean#L89).
- **Lean 4, related pieces:** a Lyapunov–Perron transform on bounded sequences for a split
  hyperbolic map with a Lipschitz perturbation, used for shadowing
  ([Manzatto/conditioned-stochastic-stability-hyperbolic](https://github.com/Manzatto/conditioned-stochastic-stability-hyperbolic/blob/0cdb3050d873d931f9f522d60bf6521f7b3ef489/LeanShared/Dynamics/HyperbolicBackwardTransform.lean#L112),
  Apache-2.0); a local `C²` center manifold for a diagonal linear part with a smooth remainder,
  and a hyperbolic splitting in real Hilbert spaces through the Riesz projection
  ([Robertboy18/PDEAtlas](https://github.com/Robertboy18/PDEAtlas/blob/64eb0329c66b121bf37cba88e58f1506b99002a2/PDE/Analysis/Evolution/ODE/InvariantGraph/Local.lean#L36),
  [`exists_unstable_splitting`](https://github.com/Robertboy18/PDEAtlas/blob/64eb0329c66b121bf37cba88e58f1506b99002a2/PDE/Analysis/Spectral/UnstableSplitting.lean#L205),
  Apache-2.0).
- **Isabelle/HOL:** the AFP has spectral radius theory for complex matrices (bounded powers when
  the spectral radius is `< 1`; R. Thiemann and A. Yamada, *Matrices, Jordan Normal Forms, and
  Spectral Radius Theory*, 2015), but no stable manifold or Hartman–Grobman theorem.

## Files

| Path | Content |
| --- | --- |
| [`StableManifold.lean`](../StableManifold.lean) | imports the whole library |
| [`StableManifold/Defs.lean`](../StableManifold/Defs.lean) | the definitions in the statements (local sets, stable and unstable subspaces, hyperbolicity), copied into the Challenge |
| [`StableManifold/LocalSets.lean`](../StableManifold/LocalSets.lean) | the global stable set; congruence, conjugation, unstable for `e` as stable for `e⁻¹`, and forward `e⁻¹`-orbits as backward `e`-orbits |
| [`StableManifold/Linear/Spectral.lean`](../StableManifold/Linear/Spectral.lean) | Gelfand's formula for real operators; geometric decay of powers |
| [`StableManifold/Linear/Subspaces.lean`](../StableManifold/Linear/Subspaces.lean) | invariance, inverses, `Eₛ ⊓ Eᵤ = 0` |
| [`StableManifold/Linear/Splitting.lean`](../StableManifold/Linear/Splitting.lean) | `E = Eₛ ⊕ Eᵤ` for a hyperbolic map, by factoring the characteristic polynomial; `Eₛ`, `Eᵤ` as the kernels of the factors |
| [`StableManifold/Linear/HyperbolicSplitting.lean`](../StableManifold/Linear/HyperbolicSplitting.lean) | the exponential dichotomy: projection, unstable inverse, estimates |
| [`StableManifold/Sequence/Superpose.lean`](../StableManifold/Sequence/Superpose.lean) | the superposition operator on bounded sequences; Lipschitz bounds and continuity |
| [`StableManifold/Sequence/SuperposeContDiff.lean`](../StableManifold/Sequence/SuperposeContDiff.lean) | its `Cⁿ` regularity |
| [`StableManifold/Perron/Operator.lean`](../StableManifold/Perron/Operator.lean) | the linear Lyapunov–Perron operator |
| [`StableManifold/Perron/Graph.lean`](../StableManifold/Perron/Graph.lean) | bounded orbits of a perturbation, the global stable manifold, decay, tangency |
| [`StableManifold/Perron/Smooth.lean`](../StableManifold/Perron/Smooth.lean) | `Cⁿ` regularity of the global stable manifold |
| [`StableManifold/Local/Cutoff.lean`](../StableManifold/Local/Cutoff.lean) | the cut-off to a globally small Lipschitz perturbation |
| [`StableManifold/Local/StableSet.lean`](../StableManifold/Local/StableSet.lean) | the local stable manifold, for every small neighborhood; forward orbits staying in a small ball tend to `p` |
| [`StableManifold/Theorem.lean`](../StableManifold/Theorem.lean) | the local inverse; the stable manifold theorem, both sides, for every small neighborhood and for one; the local sets without the convergence |
| [`StableManifoldChallenge.lean`](../StableManifoldChallenge.lean), [`StableManifoldSolution.lean`](../StableManifoldSolution.lean), [`comparator.json`](../comparator.json), [`formalization.yaml`](../formalization.yaml) | Palomar: the statements of record, their proofs, the Comparator configuration, the metadata |
| [`scripts/Audit.lean`](../scripts/Audit.lean) | the axiom audit |
| [`scripts/sync_challenge_defs.py`](../scripts/sync_challenge_defs.py) | copies the definitions of `StableManifold/Defs.lean` into the Challenge, or checks the copy |
| [`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) | CI: build, import list of the audit, audit, the Challenge's copy of the definitions, line lengths |
