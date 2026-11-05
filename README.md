# The orders of primitive permutation groups

This repository contains a Lean 4 proof of Theorem 1.1 of A. Maróti, [*On the orders of primitive groups*](https://doi.org/10.1016/S0021-8693(02)00646-4), J. Algebra 258 (2002) 631–640, using [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG)'s proof of the classification of finite simple groups.

> **Theorem 1.1.** Let `G` be a primitive permutation group of degree `n`. Then one of the following holds.
>
> (i) `G` is a subgroup of `S_m wr S_r` containing `(A_m)^r`, where the action of `S_m` is on `k`-element subsets of `{1, …, m}` and the wreath product has the product action of degree `n = binom(m, k)^r`;
>
> (ii) `G = M₁₁, M₁₂, M₂₃` or `M₂₄` with their 4-transitive action;
>
> (iii) `|G| ≤ n · ∏_{i=0}^{⌊log₂ n⌋-1} (n - 2^i) < n^(1+⌊log₂ n⌋)`.

[`Comparator/Solution.lean`](Comparator/Solution.lean) proves two theorems, one conditional and one unconditional.

The conditional theorem, in [`Maroti/Main.lean`](Maroti/Main.lean), assumes the classification, stated as TauCeti's `ClassificationStatement` (every finite simple group is isomorphic to one on TauCeti's list).

```lean
theorem Maroti.theorem_1_1_of_classification (hCFSG : TauCeti.ClassificationStatement.{0})
    {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Equiv.Perm α))
    [MulAction.IsPreprimitive G α] :
    IsProductActionType G ∨ IsMathieuType G ∨
      (Nat.card G ≤ bound (Nat.card α) ∧
        bound (Nat.card α) < Nat.card α ^ (1 + Nat.log 2 (Nat.card α)))
```

The unconditional theorem applies the conditional theorem to CFSG's proof of the classification, `CFSG.Certified.classification_finite_simple_groups`.

```lean
theorem Maroti.theorem_1_1 {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Equiv.Perm α))
    [MulAction.IsPreprimitive G α] :
    IsProductActionType G ∨ IsMathieuType G ∨
      (Nat.card G ≤ bound (Nat.card α) ∧
        bound (Nat.card α) < Nat.card α ^ (1 + Nat.log 2 (Nat.card α)))
```

- Both theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
- The development consists of about 43,800 lines of Lean, excluding dependencies.

## The statement

The three cases are defined in [`Maroti/Statement.lean`](Maroti/Statement.lean). A permutation group of degree `n` is a subgroup `G` of `Equiv.Perm α` for a finite type `α` with `n` elements, and primitivity is Mathlib's `MulAction.IsPreprimitive`.

- `IsProductActionType G` is case (i). There are `m`, `k`, `r` and an identification of the points with the `r`-tuples of `k`-element subsets of `Fin m`. Read through it, every element of `G` permutes the coordinates and moves each coordinate by a permutation of `Fin m`, and `G` contains `(A_m)^r` acting coordinatewise.
- `IsMathieuType G` is case (ii). The degree is 11, 12, 23 or 24, `G` acts 4-transitively, and `G` is isomorphic to the Mathieu group of that degree on TauCeti's list.
- `bound n` is `n · ∏_{i<⌊log₂ n⌋} (n - 2^i)`.

The formal statement differs from the printed one in two places.

- The degree is at least 2. For `n = 1` the strict inequality in (iii) reads `1 < 1`, so the printed theorem implicitly assumes `n ≥ 2`.
- Case (i) also requires `m ≥ 5`, `1 ≤ k`, `2k < m` and `r ≥ 1`. The printed case (i) has no ranges, so it would also hold for groups such as `S₃` and `S₄` in their natural actions, which belong to case (iii). The ranges come from the paper's proof, where Step 1 uses `m ≥ 5` and `k` can be replaced by `m - k`. They make the formal theorem stronger than the printed one.

## Built on

- **[A. Maróti, *On the orders of primitive groups*](https://doi.org/10.1016/S0021-8693(02)00646-4)**: the structure of the proof
- **[AxiomMath/CFSG](https://github.com/AxiomMath/CFSG)**: the classification, models of the groups on the list identified with TauCeti's carriers, their orders and outer automorphism groups, and local subgroups used for the small cases
- **[TauCeti](https://github.com/TauCetiProject/TauCeti)**: the classification statement and the list
- **[Mathlib](https://github.com/leanprover-community/mathlib4)**
- **[AxiomMath/CFSGCorollary](https://github.com/AxiomMath/CFSGCorollary)**: the import boundary check and the cache download script (see [`THIRD_PARTY.md`](THIRD_PARTY.md))

## The proof

The proof follows the four steps of Section 2 of the paper.

1. **Reduction to almost simple groups.** If `G` is not almost simple, a minimal normal subgroup is regular, or of diagonal type, or gives a product action. In each case the theorem for `G` follows from the theorem for smaller groups and the bound `|Aut(S)| ≤ |S|²` for every nonabelian simple group `S`.
2. **Classical groups other than `PSL`, exceptional groups and sporadic groups.** Here `|G| ≤ |Aut(S)|`, so it is enough to know that every proper subgroup of the socle `S` has large index. The paper takes the exact minimal indices from the literature. We prove weaker lower bounds that are still large enough. Most come from a unipotent subgroup of Heisenberg type that is normalized by a torus: a subgroup of small index would have to meet it in a large subgroup, and the torus moves that subgroup to too many places. The few small groups where this is not enough are handled by counting the fixed points of a Sylow subgroup, or by an explicit subgroup taken from CFSG's models.
3. **Alternating socle.** Either `G` is in case (i) with `r = 1`, or Bochert's bound on the order of a primitive group not containing `A_m` gives case (iii). The paper treats `A₅` and `A₆` in Step 4 as `PSL(2, 4)` and `PSL(2, 9)`. We treat them here.
4. **Socle `PSL(t, q)`.** This is the paper's Lemma 2.2. The lower bounds on indices again come from Heisenberg-type subgroups, with separate arguments for `t = 2` and for small fields.

| Directory | Contents |
| --- | --- |
| `Maroti/Statement.lean` | the three cases and `bound` |
| `Maroti/Bound.lean` | inequalities for `bound` |
| `Maroti/Interface.lean` | what each step proves |
| `Maroti/Reduction` | Step 1: regular, diagonal and product action cases |
| `Maroti/AlmostSimple` | general criteria for almost simple groups |
| `Maroti/MinDegree` | lower bounds on indices from Heisenberg-type subgroups |
| `Maroti/Alternating` | Step 3, with Bochert's theorem |
| `Maroti/Linear` | Step 4 (Lemma 2.2) |
| `Maroti/Classical`, `Symplectic`, `SymplecticSmall`, `Unitary`, `Orthogonal` | Step 2 for the classical groups |
| `Maroti/Exceptional` | Step 2 for the exceptional groups |
| `Maroti/Sporadic` | Step 2 for the 26 sporadic groups |
| `Maroti/Assembly`, `Maroti/Main.lean` | the classification step and the conditional theorem |
| `Checks` | checks that the conditional theorem avoids the classification proof, and an axiom check |
| `Comparator/Solution.lean` | both theorems |
| `Comparator/Challenge.lean` | the statements, for comparator |

## Build

The build uses Lean `v4.35.0-rc3`. Mathlib and TauCeti are pinned to the revisions CFSG uses.

CFSG publishes prebuilt files for Linux x86_64 only, and they take about 230 GB of disk. To download them, along with Mathlib's and TauCeti's, and build:

```sh
ulimit -s 1048576
export RUST_MIN_STACK=1073741824 LAKE_ARTIFACT_CACHE=true
bash tools/lake-cache-get-fast.sh .
lake build
```

On other platforms, Lake compiles the parts of CFSG it needs from source.

If you have built any Mathlib module yourself with this toolchain, the downloaded files won't match and Lake will rebuild CFSG from source. To avoid this, start with an empty Lake cache (`~/.elan/toolchains/<toolchain>/lake/cache`) and `.lake` directory.

`Comparator/Solution.lean` imports CFSG's proof of the classification, about 73,000 modules. Lean maps each imported file into memory, so on Linux systems where `vm.max_map_count` is still the old default of 65,530, this file fails to load. Raise the limit before the build, for example with `sudo sysctl vm.max_map_count=1048576`.

The build prints the axioms each theorem depends on, and two expected `sorry` warnings from `Comparator/Challenge.lean`. To build only the library, run `lake build Maroti`. It doesn't import CFSG's proof of the classification. `tools/check` builds the library and runs the checks in `Checks`.

[`comparator.json`](comparator.json) lists both theorems, but neither has been checked with comparator.

Licensed under [Apache-2.0](LICENSE).
