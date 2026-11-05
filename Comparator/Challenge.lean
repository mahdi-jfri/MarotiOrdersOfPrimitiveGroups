module

public import Maroti.Statement

/-!
# Maróti's theorem on the orders of primitive groups: statements to be proved

* `Maroti.theorem_1_1`: Theorem 1.1 of A. Maróti, *On the orders of primitive groups*,
  J. Algebra **258** (2002), 631–640. A primitive permutation group of degree `n ≥ 2` is of product
  action type, is a Mathieu group in its 4-transitive action, or has order at most
  `n · ∏_{i<⌊log₂ n⌋} (n - 2^i) < n^(1+⌊log₂ n⌋)`.
* `Maroti.theorem_1_1_of_classification`: the same, assuming the classification of finite simple
  groups in the form of TauCeti's `ClassificationStatement`.

The three cases are defined in `Maroti/Statement.lean`. `Comparator/Solution.lean` proves both
theorems.
-/

public section

universe u

namespace Maroti

/-- **Theorem 1.1** (Maróti 2002). Every primitive permutation group `G` of degree `n ≥ 2` is of
product action type, is `M₁₁`, `M₁₂`, `M₂₃` or `M₂₄` in its 4-transitive action, or satisfies
`|G| ≤ n · ∏_{i<⌊log₂ n⌋} (n - 2^i) < n^(1+⌊log₂ n⌋)`. -/
theorem theorem_1_1 {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Equiv.Perm α))
    [MulAction.IsPreprimitive G α] :
    IsProductActionType G ∨ IsMathieuType G ∨
      (Nat.card G ≤ bound (Nat.card α) ∧
        bound (Nat.card α) < Nat.card α ^ (1 + Nat.log 2 (Nat.card α))) :=
  sorry

/-- Theorem 1.1 of Maróti (2002) for primitive permutation groups of degree `n ≥ 2`, assuming the
classification of finite simple groups. -/
theorem theorem_1_1_of_classification (hCFSG : TauCeti.ClassificationStatement.{0})
    {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Equiv.Perm α))
    [MulAction.IsPreprimitive G α] :
    IsProductActionType G ∨ IsMathieuType G ∨
      (Nat.card G ≤ bound (Nat.card α) ∧
        bound (Nat.card α) < Nat.card α ^ (1 + Nat.log 2 (Nat.card α))) :=
  sorry

end Maroti
