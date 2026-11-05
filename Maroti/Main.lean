module

public import Maroti.Statement
import Maroti.Assembly.Classification
import Maroti.Alternating.Case
import Maroti.Alternating.AutBound
import Maroti.Linear.Main
import Maroti.Linear.OrderAut
import Maroti.Classical.Case
import Maroti.Classical.AutBound
import Maroti.Exceptional.Case
import Maroti.Exceptional.AutBound
import Maroti.Sporadic.Case
import Maroti.Sporadic.AutBound

/-!
# Theorem 1.1, assuming the classification

This file proves Theorem 1.1 of A. Maróti, *On the orders of primitive groups*, J. Algebra 258
(2002), 631–640, assuming the classification of finite simple groups in the form of TauCeti's
`ClassificationStatement`.

The theorem `theorem_1_1_of_families` (`Maroti/Assembly/Classification.lean`) reduces the theorem
to two facts about each family of nonabelian simple groups on the classification list: the theorem
for the primitive almost simple groups with socle in the family (`AlmostSimpleCase`), and the bound
`|Aut(S)| ≤ |S|²` (`AutBound`). The families and the theorems proving these facts are:

* alternating groups: `alternatingCase` and `autBound_alternating`,
* linear groups `PSL(n, q)`: `linearCase` and `autBound_linear`,
* the other classical groups: `otherClassicalCase` and `autBound_otherClassical`,
* the exceptional groups of Lie type: `exceptionalCase` and `autBound_exceptional`,
* the sporadic groups: `sporadicCase` and `autBound_sporadic`.

The file `Comparator/Solution.lean` removes the hypothesis with AxiomMath/CFSG's proof of the
classification.
-/

public section

universe u

namespace Maroti

/-- **Theorem 1.1** of Maróti (2002) for primitive permutation groups of degree at least 2,
assuming the classification of finite simple groups. -/
theorem theorem_1_1_of_classification (hCFSG : TauCeti.ClassificationStatement.{0})
    {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Equiv.Perm α))
    [MulAction.IsPreprimitive G α] :
    IsProductActionType G ∨ IsMathieuType G ∨
      (Nat.card G ≤ bound (Nat.card α) ∧
        bound (Nat.card α) < Nat.card α ^ (1 + Nat.log 2 (Nat.card α))) :=
  theorem_1_1_of_families hCFSG alternatingCase linearCase otherClassicalCase exceptionalCase
    sporadicCase autBound_alternating autBound_linear autBound_otherClassical
    autBound_exceptional autBound_sporadic G

end Maroti
