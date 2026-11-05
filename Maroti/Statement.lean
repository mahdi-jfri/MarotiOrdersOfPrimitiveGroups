module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

/-!
# Maróti's theorem on the orders of primitive groups: the statement

This file defines the three cases of Theorem 1.1 of

> A. Maróti, *On the orders of primitive groups*, J. Algebra **258** (2002), 631–640.

> **Theorem 1.1.** Let `G` be a primitive permutation group of degree `n`. Then one of the
> following holds.
>
> (i) `G` is a subgroup of `S_m wr S_r` containing `(A_m)^r`, where the action of `S_m` is on
> `k`-element subsets of `{1, …, m}` and the wreath product has the product action of degree
> `n = binom(m, k)^r`;
>
> (ii) `G = M₁₁, M₁₂, M₂₃` or `M₂₄` with their 4-transitive action;
>
> (iii) `|G| ≤ n · ∏_{i=0}^{⌊log₂ n⌋-1} (n - 2^i) < n^{1+⌊log₂ n⌋}`.

A permutation group is a subgroup `G` of `Equiv.Perm α` for a finite type `α`, and its degree is
`Nat.card α`. Primitivity is Mathlib's `MulAction.IsPreprimitive`.

* Case (i) is `Maroti.IsProductActionType`. The points are identified with `r`-tuples of
  `k`-element subsets of `Fin m` by an equivalence `e`, with `5 ≤ m`, `1 ≤ k`, `2 * k < m`, and
  `1 ≤ r` (the ranges come from the paper's proof: Section 2, Step 1 uses `m ≥ 5`, and `k` may be
  replaced by `m - k`). Read through `e`, every element of `G` permutes the coordinates and then
  moves each coordinate by a permutation of `Fin m`, and every element of `(A_m)^r`, acting
  coordinatewise, lies in `G`.
* Case (ii) is `Maroti.IsMathieuType`: `G` acts 4-transitively, its degree is 11, 12, 23 or 24,
  and it is isomorphic to the Mathieu group of that degree on TauCeti's list of finite simple
  groups.
* Case (iii) uses `Maroti.bound n = n · ∏_{i<⌊log₂ n⌋} (n - 2^i)`. Here `⌊log₂ n⌋` is
  `Nat.log 2 n`.
-/

@[expose] public section

namespace Maroti

open Equiv

/-- The `k`-element subsets of `Fin m`. -/
abbrev KSubset (m k : ℕ) : Type := {A : Finset (Fin m) // A.card = k}

/-- A permutation of `Fin m`, acting on the `k`-element subsets of `Fin m`. -/
def kSubsetPerm {m k : ℕ} (h : Perm (Fin m)) : Perm (KSubset m k) where
  toFun A := ⟨A.1.map h.toEmbedding, by rw [Finset.card_map]; exact A.2⟩
  invFun A := ⟨A.1.map h.symm.toEmbedding, by rw [Finset.card_map]; exact A.2⟩
  left_inv A := by
    apply Subtype.ext
    simp [Finset.map_map]
  right_inv A := by
    apply Subtype.ext
    simp [Finset.map_map]

/-- The element `(σ; h)` of `S_m wr S_r` in the product action on `r`-tuples of `k`-element
subsets of `Fin m`: coordinate `i` of a tuple moves to coordinate `σ i`, where it is moved by
`h (σ i)`. -/
def productActionPerm {m k r : ℕ} (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)) :
    Perm (Fin r → KSubset m k) where
  toFun x i := kSubsetPerm (h i) (x (σ.symm i))
  invFun y j := (kSubsetPerm (h (σ j))).symm (y (σ j))
  left_inv x := by
    funext j
    simp
  right_inv y := by
    funext i
    simp

/-- Case (i) of Theorem 1.1: there are `m`, `k`, `r` with `5 ≤ m`, `1 ≤ k`, `2 * k < m`, and
`1 ≤ r` (the ranges come from the paper's proof: Section 2, Step 1 uses `m ≥ 5`, and `k` may be
replaced by `m - k`) and an identification `e` of the points with the `r`-tuples of `k`-element
subsets of `Fin m` such that, read through `e`, every element of `G` is an element of `S_m wr S_r`
in the product action, and `G` contains `(A_m)^r` acting coordinatewise. -/
def IsProductActionType {α : Type*} (G : Subgroup (Perm α)) : Prop :=
  ∃ (m k r : ℕ) (e : α ≃ (Fin r → KSubset m k)), 5 ≤ m ∧ 1 ≤ k ∧ 2 * k < m ∧ 1 ≤ r ∧
    (∀ g ∈ G, ∃ (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)),
      e.permCongr g = productActionPerm σ h) ∧
    ∀ a : Fin r → alternatingGroup (Fin m),
      e.symm.permCongr (productActionPerm 1 fun i => (a i : Perm (Fin m))) ∈ G

/-- The Mathieu groups `M₁₁`, `M₁₂`, `M₂₃` and `M₂₄`, each with the degree of its 4-transitive
action. -/
def fourTransitiveMathieu : List (TauCeti.SporadicName × ℕ) :=
  [(.M11, 11), (.M12, 12), (.M23, 23), (.M24, 24)]

/-- Case (ii) of Theorem 1.1: `G` is `M₁₁`, `M₁₂`, `M₂₃` or `M₂₄` with its 4-transitive action.
That is, the degree of `G` is 11, 12, 23 or 24, `G` acts 4-transitively, and `G` is isomorphic
to the Mathieu group of that degree. -/
def IsMathieuType {α : Type*} (G : Subgroup (Perm α)) : Prop :=
  ∃ s ∈ fourTransitiveMathieu, Nat.card α = s.2 ∧
    MulAction.IsMultiplyPretransitive G α 4 ∧ Nonempty (G ≃* s.1.Group)

/-- The bound of case (iii) of Theorem 1.1: `n · ∏_{i=0}^{⌊log₂ n⌋-1} (n - 2^i)`. -/
def bound (n : ℕ) : ℕ :=
  n * ∏ i ∈ Finset.range (Nat.log 2 n), (n - 2 ^ i)

end Maroti
