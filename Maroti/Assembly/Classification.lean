module

public import Maroti.Assembly.Transfer
public import CFSG.RankThree.PartOne.TCB.Final

/-!
# Dispatch through the classification of finite simple groups

This file connects the classification of finite simple groups (`TauCeti.ClassificationStatement`)
to the five socle families of `Maroti/Interface.lean` and assembles Theorem 1.1 of A. Maróti,
*On the orders of primitive groups*, J. Algebra 258 (2002), pages 631–640, from the family
theorems.

By `CFSG.RankThree.PartOne.TCB.catalogBridgeFor_all` (`CFSG/RankThree/PartOne/TCB/Final.lean`),
every finite simple group `S` under `TauCeti.ClassificationStatement.{0}` satisfies
`CFSG.Blueprint.Catalog S`. When `S` is nonabelian, the cyclic case of `Catalog S` is ruled out,
and splitting the classical case on the tag `t` via `CFSG.Milestones.statedClassicalModel_tag_mem`
(`CFSG/Milestones/Main.lean`) places `S` into one of `AlternatingSocle`, `LinearSocle`,
`OtherClassicalSocle`, `ExceptionalSocle`, or `SporadicSocle` (`socle_of_isNonabelianSimple`).

Combining the five `AlmostSimpleCase` family theorems gives `AlmostSimpleCase fun _ _ => True`
(`almostSimpleCase_of_families`), and combining the five `AutBound` family theorems gives
`AutBound IsNonabelianSimple` (`autBound_of_families`). Passing both into `theorem_1_1_of_step1`
yields `theorem_1_1_of_families`.
-/

@[expose] public section

universe u

namespace Maroti

/-- Assuming the classification of finite simple groups (`TauCeti.ClassificationStatement.{0}`),
every finite nonabelian simple group belongs to one of the five socle families:
`AlternatingSocle`, `LinearSocle`, `OtherClassicalSocle`, `ExceptionalSocle`, or
`SporadicSocle`. -/
theorem socle_of_isNonabelianSimple (hCFSG : TauCeti.ClassificationStatement.{0})
    (S : Type) [Group S] [Finite S] (hS : IsNonabelianSimple S) :
    AlternatingSocle S ∨ LinearSocle S ∨ OtherClassicalSocle S ∨
      ExceptionalSocle S ∨ SporadicSocle S := by
  obtain ⟨hSimple, a, b, hab⟩ := hS
  obtain ⟨i, hi⟩ := TauCeti.classificationStatement_iff.1 hCFSG S
  rcases CFSG.RankThree.PartOne.TCB.catalogBridgeFor_all i S hi with
    ⟨p, -, ⟨e⟩⟩ | hAlt | ⟨t, n, p, f, hCl⟩ | hEx | hSp
  · exfalso
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact Or.inl hAlt
  · rcases CFSG.Milestones.statedClassicalModel_tag_mem S t n p f hCl with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨n, p, f, hCl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨.PSU, n, p, f, by decide, hCl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.PSp, n, p, f, by decide, hCl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.POmegaOdd, n, p, f, by decide, hCl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.POmegaPlus, n, p, f, by decide, hCl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.POmegaMinus, n, p, f, by decide, hCl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hEx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hSp)))

/-- Dispatch `AlmostSimpleCase` across the five socle families using the classification of finite
simple groups. -/
theorem almostSimpleCase_of_families (hCFSG : TauCeti.ClassificationStatement.{0})
    (hAlt : AlmostSimpleCase AlternatingSocle) (hLin : AlmostSimpleCase LinearSocle)
    (hCl : AlmostSimpleCase OtherClassicalSocle) (hEx : AlmostSimpleCase ExceptionalSocle)
    (hSp : AlmostSimpleCase SporadicSocle) : AlmostSimpleCase fun _ _ => True := by
  intro α _ G S _ hG hAS _
  have : Finite S := hAS.finite
  rcases socle_of_isNonabelianSimple hCFSG S hAS.isNonabelianSimple with
    h | h | h | h | h
  · exact hAlt α G S hG hAS h
  · exact hLin α G S hG hAS h
  · exact hCl α G S hG hAS h
  · exact hEx α G S hG hAS h
  · exact hSp α G S hG hAS h

/-- Dispatch `AutBound` across the five socle families using the classification of finite simple
groups. -/
theorem autBound_of_families (hCFSG : TauCeti.ClassificationStatement.{0})
    (hAlt : AutBound AlternatingSocle) (hLin : AutBound LinearSocle)
    (hCl : AutBound OtherClassicalSocle) (hEx : AutBound ExceptionalSocle)
    (hSp : AutBound SporadicSocle) : AutBound IsNonabelianSimple := by
  intro S _ _ hS
  rcases socle_of_isNonabelianSimple hCFSG S hS with h | h | h | h | h
  · exact hAlt S h
  · exact hLin S h
  · exact hCl S h
  · exact hEx S h
  · exact hSp S h

/-- Theorem 1.1 of Maróti (2002), deduced from `TauCeti.ClassificationStatement.{0}` and the ten
socle-family theorems (`AlmostSimpleCase` and `AutBound` for alternating, linear, other classical,
exceptional, and sporadic socles). -/
theorem theorem_1_1_of_families (hCFSG : TauCeti.ClassificationStatement.{0})
    (hAlt : AlmostSimpleCase AlternatingSocle) (hLin : AlmostSimpleCase LinearSocle)
    (hCl : AlmostSimpleCase OtherClassicalSocle) (hEx : AlmostSimpleCase ExceptionalSocle)
    (hSp : AlmostSimpleCase SporadicSocle)
    (hAlt' : AutBound AlternatingSocle) (hLin' : AutBound LinearSocle)
    (hCl' : AutBound OtherClassicalSocle) (hEx' : AutBound ExceptionalSocle)
    (hSp' : AutBound SporadicSocle)
    {α : Type u} [Finite α] [Nontrivial α] (G : Subgroup (Equiv.Perm α))
    [MulAction.IsPreprimitive G α] :
    IsProductActionType G ∨ IsMathieuType G ∨
      (Nat.card G ≤ bound (Nat.card α) ∧
        bound (Nat.card α) < Nat.card α ^ (1 + Nat.log 2 (Nat.card α))) :=
  theorem_1_1_of_step1
    (almostSimpleCase_of_families hCFSG hAlt hLin hCl hEx hSp)
    (autBound_of_families hCFSG hAlt' hLin' hCl' hEx' hSp') G

end Maroti
