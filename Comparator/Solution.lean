module

public import Maroti.Main
import CFSG.Certified.Classification

/-!
# Maróti's theorem on the orders of primitive groups

This file proves the statements of `Comparator/Challenge.lean`.

The theorem `Maroti.theorem_1_1_of_classification` (`Maroti/Main.lean`) proves Theorem 1.1 of
A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002), 631–640, assuming the
classification of finite simple groups, stated as TauCeti's `TauCeti.ClassificationStatement`.
AxiomMath/CFSG's proof of the classification, `CFSG.Certified.classification_finite_simple_groups`,
then removes the hypothesis. This file is the only place where that proof is imported, and
`Checks.ImportBoundary` checks that the conditional theorem does not use it.

## Main results

* The theorem `Maroti.theorem_1_1_of_classification`: assuming the classification, every primitive
  permutation group of degree at least 2 satisfies one of the three cases of Theorem 1.1.
* The theorem `Maroti.theorem_1_1`: every primitive permutation group of degree at least 2
  satisfies one of the three cases of Theorem 1.1.
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
  theorem_1_1_of_classification
    (TauCeti.classificationStatement_iff.2 fun G _ _ _ =>
      CFSG.Certified.classification_finite_simple_groups G) G

end Maroti

#print axioms Maroti.theorem_1_1
#print axioms Maroti.theorem_1_1_of_classification
