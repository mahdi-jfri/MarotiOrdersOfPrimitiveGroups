module

public import Maroti.AlmostSimple.Basic
public import Maroti.Interface
import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuterAux
import CFSG.Open.MonsterY443Finiteness

/-!
# Outer Automorphism Bounds for Sporadic Simple Groups

This file proves that every sporadic simple group `S` has outer automorphism group of order
dividing `2`, hence `|Aut(S)| ≤ 2 |S|` and `|Aut(S)| ≤ |S|²` (`Maroti.autBound_sporadic`,
Maróti, Section 2, Step 1, page 634).
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint

/-- For every sporadic simple group `S`, `|OuterAut S|` divides `2`. -/
theorem card_outer_dvd_two_of_sporadicSocle {S : Type} [Group S]
    (hS : NativeSporadic.SporadicRep S) :
    Nat.card (OuterAut S) ∣ 2 := by
  rcases hS with ⟨s, ⟨e⟩⟩
  change Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.AGLEmbedding.card_outer_carrier_dvd_two
    CFSG.Open.Open.monster_y443_derived_simple s

/-- For every sporadic simple group `S`, `|Aut(S)| ≤ 2 * |S|`. -/
theorem card_mulAut_le_two_mul_card_of_sporadicSocle {S : Type} [Group S] [Finite S]
    (hS : NativeSporadic.SporadicRep S) :
    Nat.card (MulAut S) ≤ 2 * Nat.card S := by
  have hdvd : Nat.card (OuterAut S) ∣ 2 := card_outer_dvd_two_of_sporadicSocle hS
  have hle2 : Nat.card (OuterAut S) ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  calc
    Nat.card (MulAut S) ≤ Nat.card S * Nat.card (OuterAut S) :=
      card_mulAut_le_card_mul_outerAut S
    _ ≤ Nat.card S * 2 := Nat.mul_le_mul_left (Nat.card S) hle2
    _ = 2 * Nat.card S := Nat.mul_comm _ _

/-- Every sporadic simple group `S` satisfies `|Aut(S)| ≤ |S|²` (Maróti, Section 2, Step 1,
page 634). -/
theorem autBound_sporadic : AutBound SporadicSocle := by
  intro S _ _ hS
  have hle : Nat.card (MulAut S) ≤ 2 * Nat.card S :=
    card_mulAut_le_two_mul_card_of_sporadicSocle hS
  by_cases h2 : 2 ≤ Nat.card S
  · calc
      Nat.card (MulAut S) ≤ 2 * Nat.card S := hle
      _ ≤ Nat.card S * Nat.card S := Nat.mul_le_mul_right (Nat.card S) h2
      _ = Nat.card S ^ 2 := (sq (Nat.card S)).symm
  · have h1 : Nat.card S ≤ 1 := by omega
    have hsub : Subsingleton S := Finite.card_le_one_iff_subsingleton.mp h1
    have hAutSub : Subsingleton (MulAut S) :=
      ⟨fun f g => MulEquiv.ext fun x => @Subsingleton.elim S hsub _ _⟩
    have hAut : Nat.card (MulAut S) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hAutSub
    have hpos : 1 ≤ Nat.card S := Nat.succ_le_of_lt Nat.card_pos
    calc
      Nat.card (MulAut S) ≤ 1 := hAut
      _ ≤ Nat.card S ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul hpos hpos

end Maroti
