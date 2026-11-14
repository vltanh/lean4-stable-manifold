# The stable manifold theorem in Lean

The stable manifold theorem in Lean 4 with Mathlib, for a `Cⁿ` map (`1 ≤ n ≤ ∞`) near a
hyperbolic fixed point `p` of a finite-dimensional real normed space: the local stable set is the
graph of a `Cⁿ` map from the stable subspace to the unstable one, tangent to the stable subspace
at `p`, and the local unstable set is such a graph over the unstable subspace. The proof is
Perron's method on the Banach space of bounded sequences, with smoothness of every order from the
smoothness of composition operators.

There is no `axiom` or `native_decide`, and no `sorry` outside the statements of
[`StableManifoldChallenge.lean`](StableManifoldChallenge.lean).

## Main results

`E` is a finite-dimensional real normed space, `A = Df(p)`, and `Eₛ = {v | Aᵏ v → 0}`, `Eᵤ` (the
vectors with a backward orbit tending to `0`) the stable and unstable subspaces of `A`. The
statements in words and in Lean, and the proof module by module, are in
[docs/DETAILS.md](docs/DETAILS.md).

| Lean | Statement |
| --- | --- |
| [`Function.exists_localStableSet_localUnstableSet_eq_graph`](StableManifold/Theorem.lean#L133) | if `f` is `Cⁿ` near a fixed point `p` and `A` is invertible and hyperbolic, there are an open `U ∋ p` and `Cⁿ` maps `hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ`, vanishing with their derivatives at `0`, whose graphs `p + x + hₛ x`, `p + y + hᵤ y` over neighborhoods of `0` are the local stable and unstable sets of `f` in `U` |
| [`Function.exists_localStableSet_eq_graph_of_isCompl`](StableManifold/Local/StableSet.lean#L217) | the stable side, with one `hₛ` for every neighborhood `U` inside a small ball around `p`, assuming only `E = Eₛ ⊕ Eᵤ` (`A` may be singular) |
| [`ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`](StableManifold/Linear/Splitting.lean#L346) | the hyperbolic splitting: `E = Eₛ ⊕ Eᵤ` when no complex eigenvalue of `A` has modulus `1` |
| [`StableManifold.Perturbation.bddOrbit_iff`](StableManifold/Perron/Graph.lean#L318), [`contDiff_graph`](StableManifold/Perron/Smooth.lean#L175) | for a globally small Lipschitz perturbation `A + φ` of a linear map with an exponential dichotomy, the points with bounded forward orbit form the graph of a Lipschitz map over `Eₛ` (in any real Banach space), `Cⁿ` when `φ` is (in finite dimension) |

```lean
theorem Function.exists_localStableSet_localUnstableSet_eq_graph {f : E → E} {p : E}
    {W : Set E} {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W)
    (hfix : f p = p) (hinv : (fderiv ℝ f p).IsInvertible)
    (hyp : (fderiv ℝ f p).IsHyperbolic) :
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

`localStableSet f p U` is the set of points whose forward orbit stays in `U` and tends to `p`,
`localUnstableSet f p U` the set of points with a backward orbit in `U` tending to `p`, and
`IsHyperbolic` says that no complex root of the characteristic polynomial has modulus `1`
([the definitions](docs/DETAILS.md#the-definitions)).

## Method

| Step | Modules |
| --- | --- |
| Gelfand's formula for real operators; `E = Eₛ ⊕ Eᵤ` by factoring the characteristic polynomial; an exponential dichotomy `‖Aᵏ P‖, ‖A⁻ᵏ (1 - P)‖ ≤ C λᵏ` | [`Linear/`](StableManifold/Linear) |
| the composition operator `x ↦ φ ∘ x` on bounded sequences, `Cⁿ` when `φ` is | [`Sequence/`](StableManifold/Sequence) |
| the bounded orbits of `A + φ` as the fixed points of a contraction of `ℕ →ᵇ E` built from the Lyapunov–Perron operator; the graph, its decay and tangency; its `Cⁿ` regularity by the inverse function theorem in `ℕ →ᵇ E` | [`Perron/`](StableManifold/Perron) |
| a cut-off by a bump function; the local stable manifold; the unstable side as the stable side of the local inverse | [`Local/`](StableManifold/Local), [`Theorem`](StableManifold/Theorem.lean) |

Smoothness of every order comes at once from the composition operator, in place of the fiber
contraction or `Cʳ` section theorem ([design choices](docs/DETAILS.md#design-choices);
[what Mathlib had and lacked](docs/DETAILS.md#what-mathlib-had-and-lacked)). The proof follows
the standard argument rather than one text ([sources](docs/DETAILS.md#sources)).

## Lean statement of record

[`StableManifoldChallenge.lean`](StableManifoldChallenge.lean) states, with `sorry` and in
Mathlib's vocabulary, four theorems in the namespace `StableManifoldChallenge`: `stable_manifold`
(both sides), `hyperbolic_splitting`, and `stableSubspace_symm` and `localStableSet_symm`, which
tie the backward-orbit definitions of the unstable subspace and of the local unstable set to the
stable ones of the inverse. It carries a word-for-word copy of the definitions of
[`StableManifold/Defs.lean`](StableManifold/Defs.lean), kept equal by
[`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py).
[`StableManifoldSolution.lean`](StableManifoldSolution.lean) proves the four theorems from the
library; [`comparator.json`](comparator.json) configures Palomar's Comparator.

## Trust

- `lake env lean scripts/Audit.lean` checks that the main theorems, the Challenge's theorems as
  the Solution proves them, and every declaration of the library use only `propext`,
  `Classical.choice` and `Quot.sound`, and that the hypotheses of the main theorem can be met
  ([what it checks](docs/DETAILS.md#the-axiom-audit)).
- Comparator, with Lean's kernel and the NanoDa kernel, accepts the Solution against the
  Challenge.

## Other formalizations

No earlier formal proof of the stable manifold theorem for maps was found, in any system, nor of
the Hartman–Grobman theorem; Mathlib `v4.36.0-rc2` has neither
([the search and the list](docs/DETAILS.md#other-formalizations)). This work does not use or adapt
the following.

| Work | Content |
| --- | --- |
| [TauCeti](https://github.com/TauCetiProject/TauCeti/blob/ca32605ff53921fa0689dd312618b7cfaafa7e43/TauCeti/Analysis/ODE/LyapunovPerron/VectorField.lean#L331) (Lean 4, concurrent) | the stable and unstable manifolds of an equilibrium of a `Cⁿ` vector field (flows, not maps), assuming an exponential dichotomy, by a Lyapunov–Perron contraction |
| [lean-eval](https://github.com/leanprover/lean-eval/blob/8955681b9914d7ebc7d286414843021b7d6c9de1/LeanEval/Dynamics/StableUnstableManifolds.lean#L51) (Lean 4) | a benchmark statement, without a public proof: the local stable and unstable sets of a hyperbolic fixed point meet only at the point |
| [Manzatto](https://github.com/Manzatto/conditioned-stochastic-stability-hyperbolic/blob/0cdb3050d873d931f9f522d60bf6521f7b3ef489/LeanShared/Dynamics/HyperbolicBackwardTransform.lean#L112), [PDEAtlas](https://github.com/Robertboy18/PDEAtlas/blob/64eb0329c66b121bf37cba88e58f1506b99002a2/PDE/Analysis/Evolution/ODE/InvariantGraph/Local.lean#L36) (Lean 4) | a Lyapunov–Perron transform on bounded sequences, for shadowing; a local center manifold for a diagonal linear part |

## Using it from another Lake project

Add to the `lakefile.toml` of your project (the repository is not published yet):

```toml
[[require]]
name = "StableManifold"
git = "https://github.com/vltanh/lean4-stable-manifold"
rev = "<commit>"
```

and import `StableManifold`, or a module such as `StableManifold.Theorem`. The package requires
Lean and Mathlib `v4.36.0-rc2` and imports only Mathlib; your project should use the same Mathlib
version.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build                         # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean   # axioms
lake env lake comparator --config=comparator.json   # needs bubblewrap; expect "Your solution is okay!"
```

## Layout

| Path | Content |
| --- | --- |
| [`StableManifold.lean`](StableManifold.lean) | imports the whole library: about 3,500 lines in 14 modules ([each module](docs/DETAILS.md#files)) |
| [`StableManifold/Defs.lean`](StableManifold/Defs.lean), [`LocalSets.lean`](StableManifold/LocalSets.lean), [`Theorem.lean`](StableManifold/Theorem.lean) | the definitions in the statements; local sets; the main theorem |
| [`StableManifold/Linear/`](StableManifold/Linear) | `Spectral`, `Subspaces`, `Splitting`, `HyperbolicSplitting`: the linear theory |
| [`StableManifold/Sequence/`](StableManifold/Sequence) | `Superpose`, `SuperposeContDiff`: composition operators on bounded sequences |
| [`StableManifold/Perron/`](StableManifold/Perron) | `Operator`, `Graph`, `Smooth`: the Lyapunov–Perron operator and the global stable manifold |
| [`StableManifold/Local/`](StableManifold/Local) | `Cutoff`, `StableSet`: the local stable manifold |
| [`StableManifoldChallenge.lean`](StableManifoldChallenge.lean), [`StableManifoldSolution.lean`](StableManifoldSolution.lean), [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml) | Palomar: the statements of record, their proofs, the Comparator configuration, the metadata |
| [`scripts/`](scripts) | `Audit.lean`, the axiom audit; `sync_challenge_defs.py`, the Challenge's copy of the definitions |
| [`.github/workflows/`](.github/workflows) | CI: build, import list of the audit, audit, the Challenge's copy of the definitions, line lengths |

## References

- J. Hadamard, *Sur l'itération et les solutions asymptotiques des équations différentielles*,
  Bull. Soc. Math. France 29 (1901), 224–228.
- O. Perron, *Über Stabilität und asymptotisches Verhalten der Integrale von
  Differentialgleichungssystemen*, Math. Z. 29 (1929), 129–160,
  [doi:10.1007/BF01180524](https://doi.org/10.1007/BF01180524).
- O. Perron, *Über Stabilität und asymptotisches Verhalten der Lösungen eines Systems endlicher
  Differenzengleichungen*, J. Reine Angew. Math. 161 (1929), 41–64,
  [doi:10.1515/crll.1929.161.41](https://doi.org/10.1515/crll.1929.161.41).
- M. C. Irwin, *On the stable manifold theorem*, Bull. London Math. Soc. 2 (1970), 196–198,
  [doi:10.1112/blms/2.2.196](https://doi.org/10.1112/blms/2.2.196).
- M. W. Hirsch, C. C. Pugh, M. Shub, *Invariant Manifolds*, Lecture Notes in Mathematics 583,
  Springer, 1977, [doi:10.1007/BFb0092042](https://doi.org/10.1007/BFb0092042).
- M. C. Irwin, *Smooth Dynamical Systems*, Academic Press, 1980, Chapter 6.
- M. Shub, *Global Stability of Dynamical Systems*, Springer, 1987,
  [doi:10.1007/978-1-4757-1947-5](https://doi.org/10.1007/978-1-4757-1947-5).

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
