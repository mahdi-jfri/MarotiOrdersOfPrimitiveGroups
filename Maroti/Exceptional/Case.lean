module

public import Maroti.Exceptional.ChevalleyE
public import Maroti.Exceptional.G2
public import Maroti.Exceptional.F4
public import Maroti.Exceptional.TwistedE6
public import Maroti.Exceptional.TrialityD4
public import Maroti.Exceptional.Ree
public import Maroti.Exceptional.Suzuki
public import Maroti.Exceptional.Tits

/-!
# The exceptional groups of Lie type

This file collects the exceptional families into one statement for Step 2 of Maróti's proof
(A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002), Section 2, page 634).
CFSG's `CFSG.Blueprint.ExceptionalRep` lists three kinds of models: the Chevalley groups of the
tags in `chevalleyExceptionalTags` (`G₂`, `F₄`, `E₆`, `E₇`, `E₈`, `²E₆`, `³D₄`), the Ree groups and
the Tits group (`reeTitsTags`), and the Suzuki groups. Each model has its own theorem
`card_le_bound_of_…` in the other files of this directory. The theorem here splits on the model
and applies the matching one.

The theorem `exceptionalCase_of_G2` takes the bound for `G₂(q)` as a hypothesis, and
`exceptionalCase` supplies it from `card_le_bound_of_chevalley_G2`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint

/-- Maróti's bound for primitive almost simple groups whose socle is an exceptional group of Lie
type, given the bound for socle `G₂(q)`. -/
theorem exceptionalCase_of_G2
    (hG2 : ∀ {α : Type} [Finite α] {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
      {S : Type} [Group S] {p f : ℕ}, IsAlmostSimpleWith G S →
      ChevalleyExceptionalModel S .G2 p f → Nat.card G ≤ bound (Nat.card α)) :
    AlmostSimpleCase ExceptionalSocle := by
  intro α _ G S _ hG hAS hS
  have : MulAction.IsPreprimitive G α := hG
  right; right
  rcases hS with ⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hG2 hAS h
    · exact card_le_bound_of_chevalley_F4 hAS h
    · exact card_le_bound_of_chevalley_E6 hAS h
    · exact card_le_bound_of_chevalley_E7 hAS h
    · exact card_le_bound_of_chevalley_E8 hAS h
    · exact card_le_bound_of_chevalley_twistedE6 hAS h
    · exact card_le_bound_of_chevalley_trialityD4 hAS h
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact card_le_bound_of_reeTitsModel_twistedG2 hAS h
    · exact card_le_bound_of_reeTitsModel_twistedF4 hAS h
    · exact card_le_bound_of_reeTitsModel_Tits hAS h
  · exact card_le_bound_of_suzukiModel hAS h

/-- Maróti's bound for primitive almost simple groups whose socle is an exceptional group of Lie
type. -/
theorem exceptionalCase : AlmostSimpleCase ExceptionalSocle :=
  exceptionalCase_of_G2 fun hAS h => card_le_bound_of_chevalley_G2 hAS h

end Maroti
