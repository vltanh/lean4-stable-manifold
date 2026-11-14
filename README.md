# The stable manifold theorem in Lean

The stable manifold theorem for a `Cⁿ` map (`1 ≤ n ≤ ∞`) near a hyperbolic fixed point of a
finite-dimensional real normed space, in graph form, in Lean 4 with Mathlib: near the fixed point,
the local stable set is the graph of a `Cⁿ` map from the stable subspace to the unstable one,
tangent to the stable subspace, and symmetrically for the local unstable set.

## Status

| Part | State |
| --- | --- |
| Statements of every module (main theorem and all intermediate results) | done, they elaborate |
| Proofs | open: 88 `sorry`s, each with a proof plan in its module's docstring |
| Lean statement of record (`StableManifoldChallenge.lean`), axiom audit (`scripts/Audit.lean`) | not written yet |

## Main result

`E` is a finite-dimensional real normed space, `Eₛ`, `Eᵤ` the stable and unstable subspaces of
`A = Df(p)`.

| Lean | Statement |
| --- | --- |
| [`Function.exists_localStableSet_localUnstableSet_eq_graph`](StableManifold/Theorem.lean) | for `f` `Cⁿ` near a fixed point `p` with `Df(p)` invertible and hyperbolic: an open `U ∋ p` and `Cⁿ` maps `hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ`, vanishing with their derivatives at `0`, whose graphs `p + x + hₛ x`, `p + y + hᵤ y` over neighborhoods of `0` are the local stable and unstable sets of `f` on `U` |
| [`Function.exists_localStableSet_eq_graph_of_isCompl`](StableManifold/Local/StableSet.lean) | the stable side for every neighborhood `U ⊆ B(p, δ)`, with one `hₛ`; only `Eₛ ⊕ Eᵤ = E` is assumed (no invertibility) |
| [`ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`](StableManifold/Linear/Splitting.lean) | for a hyperbolic `A`, `Eₛ ⊕ Eᵤ = E` |
| [`StableManifold.Perturbation.bddOrbit_iff`](StableManifold/Perron/Graph.lean), [`contDiff_graph`](StableManifold/Perron/Smooth.lean) | for a globally small Lipschitz perturbation `A + φ` of a hyperbolic `A`: the points with bounded forward orbit form the graph of a Lipschitz map over `Eₛ`, `Cⁿ` when `φ` is |

```lean
theorem Function.exists_localStableSet_localUnstableSet_eq_graph {f : E → E} {p : E}
    {W : Set E} {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W)
    (hfix : f p = p) (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧
      (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
        ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
          ContDiffOn ℝ n hs Vs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
      (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
        ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
          ContDiffOn ℝ n hu Vu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
          localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu)
```

`localStableSet f p U` is the set of points whose forward orbit stays in `U` and tends to `p`;
`localUnstableSet f p U` the set of points with a backward orbit in `U` tending to `p`;
`IsHyperbolic` means that no complex eigenvalue has modulus `1`.

## Method

Perron's method (the Lyapunov–Perron operator) on the Banach space `ℕ →ᵇ E` of bounded sequences.

1. Linear algebra: the hyperbolic splitting `E = Eₛ ⊕ Eᵤ` (factoring the characteristic
   polynomial), with exponential estimates `‖Aⁿ P‖, ‖A⁻ⁿ (1 - P)‖ ≤ C λⁿ` on the two parts.
2. A cut-off with a bump function makes `f` near `p` a globally small Lipschitz perturbation
   `A + φ` of its linear part.
3. The bounded orbits of `A + φ` are the fixed points of a contraction of `ℕ →ᵇ E`; they form the
   graph of a Lipschitz map over `Eₛ`, and decay geometrically.
4. Smoothness: the superposition operator `x ↦ φ ∘ x` is `Cⁿ` on bounded sequences (finite
   dimension), so the inverse function theorem in `ℕ →ᵇ E` makes the graph `Cⁿ`, for every `n`
   at once; this replaces the fiber contraction / `C^r` section theorem.
5. Near `p`, the orbits staying in a small `U` are the bounded ones; the unstable side is the
   stable side of the local inverse of `f`.

## Layout

| Module | Content | Planned size |
| --- | --- | --- |
| [`LocalSets`](StableManifold/LocalSets.lean) | local stable and unstable sets, elementary lemmas | 150 |
| [`Linear/Spectral`](StableManifold/Linear/Spectral.lean) | Gelfand's formula for real operators, geometric decay of powers | 250–350 |
| [`Linear/Subspaces`](StableManifold/Linear/Subspaces.lean) | stable and unstable subspaces, invariance, inverse, disjointness | 150–250 |
| [`Linear/Splitting`](StableManifold/Linear/Splitting.lean) | `Eₛ ⊕ Eᵤ = E` for a hyperbolic map | 350–550 |
| [`Linear/HyperbolicSplitting`](StableManifold/Linear/HyperbolicSplitting.lean) | projection, unstable inverse and exponential estimates | 300–450 |
| [`Sequence/Superpose`](StableManifold/Sequence/Superpose.lean) | the superposition operator on bounded sequences | 150–250 |
| [`Sequence/SuperposeContDiff`](StableManifold/Sequence/SuperposeContDiff.lean) | its `Cⁿ` regularity | 300–500 |
| [`Perron/Operator`](StableManifold/Perron/Operator.lean) | the linear Lyapunov–Perron operator | 350–500 |
| [`Perron/Graph`](StableManifold/Perron/Graph.lean) | bounded orbits, the global stable manifold, decay, tangency | 450–700 |
| [`Perron/Smooth`](StableManifold/Perron/Smooth.lean) | `Cⁿ` regularity of the stable manifold | 250–400 |
| [`Local/Cutoff`](StableManifold/Local/Cutoff.lean) | the global Lipschitz cut-off | 300–450 |
| [`Local/StableSet`](StableManifold/Local/StableSet.lean) | the local stable manifold | 300–450 |
| [`Theorem`](StableManifold/Theorem.lean) | local inverse and the main theorem | 200–350 |

[`StableManifold.lean`](StableManifold.lean) imports every module.

## Building

```sh
lake exe cache get   # Mathlib's compiled files
lake build
```

The package uses Lean and Mathlib `v4.36.0-rc2` and imports only Mathlib. To depend on it, add to
your `lakefile.toml` (the repository is not published yet)

```toml
[[require]]
name = "StableManifold"
git = "<repository URL>"
rev = "<commit>"
```

## References

- M. C. Irwin, *Smooth Dynamical Systems*, Academic Press, 1980, Chapter 6.
- M. W. Hirsch, C. C. Pugh, M. Shub, *Invariant Manifolds*, Lecture Notes in Mathematics 583,
  Springer, 1977.
- M. Shub, *Global Stability of Dynamical Systems*, Springer, 1987.

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.

## License

Apache-2.0; see [LICENSE](LICENSE).
