module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Basic
import Maroti.MinDegree.Extraspecial
import CFSG.Sporadic.J1
import CFSG.Monster.B.Cbar.LocalStructure
import CFSG.Sporadic.Schreier.BSchreierCase
import CFSG.Monster.Existence.BabyOrder
import CFSG.Monster.Existence.TwoB
import CFSG.RankThree.PartOne.SPOR.OuterM
import CFSG.Open.MonsterY443Finiteness
import CFSG.Sporadic.Bridge.Y443Relabel

/-!
# Sporadic Simple Groups `J₁`, `B`, and `M`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to:
* Janko's first group `J₁` (via `19 ∣ |J₁|`, giving minimum index `≥ 19 ≥ 17`).
* the Baby Monster `B` (via its extraspecial `2^(1+22)` subgroup `Ebar` of order `2^23`, giving
  minimum index `≥ 2^12 = 4096 ≥ 1317`).
* the Monster `M` (via its extraspecial `2^(1+24)` subgroup `rhoQvis` of order `2^25`, giving
  minimum index `≥ 2^13 = 8192`).
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint

/-- Every proper subgroup of `J₁` has index at least `19`. -/
theorem index_ge_J1 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .J1) {H : Subgroup S} (hH : H ≠ ⊤) :
    19 ≤ H.index := by
  have hcard : Nat.card S = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  exact prime_le_index_of_ne_top hH (by decide : Nat.Prime 19) (by rw [hcard]; decide)

/-- Maróti's bound for primitive almost simple groups with socle `J₁`. -/
theorem sporadicCase_J1 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .J1)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 19) (c := 2) (by decide)
    (fun H hH => index_ge_J1 e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.J1, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

/-- Every proper subgroup of the Baby Monster `B` has index at least `2 ^ 12 = 4096`. -/
theorem index_ge_B {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .B) {H : Subgroup S} (hH : H ≠ ⊤) :
    4096 ≤ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := CFSG.Monster.B.Ebar_extraspecial
  have : Finite CFSG.Monster.B.Ebar :=
    Nat.finite_of_card_ne_zero (by rw [hE.2]; decide)
  let eB : CFSG.Monster.B.Cbar ≃* S :=
    CFSG.Sporadic.BSchreier.nativeBEquivCbar.symm.trans e.symm
  let f : CFSG.Monster.B.Ebar →* S := eB.toMonoidHom.comp CFSG.Monster.B.Ebar.subtype
  have hf : Function.Injective f := eB.injective.comp Subtype.coe_injective
  have hidx := pow_le_index_of_injective_of_isExtraspecialPGroup (p := 2) (m := 11)
    hE.1 hE.2 hH f hf
  simpa using hidx

/-- Maróti's bound for primitive almost simple groups with socle `B`. -/
theorem sporadicCase_B {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .B)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 4154781481226426191177580544000000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Monster.Existence.card_nativeB
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 4096) (c := 2) (by decide)
    (fun H hH => index_ge_B e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.B, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

/-- Every proper subgroup of the Monster `M` has index at least `2 ^ 13 = 8192`. -/
theorem index_ge_M {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .M) {H : Subgroup S} (hH : H ≠ ⊤) :
    8192 ≤ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eG⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  have hQ := CFSG.Monster.Existence.isExtraspecialPGroup_rhoQvis
  have hQcard : Nat.card CFSG.Monster.Visible.rhoQvis = 2 ^ (1 + 2 * 12) :=
    CFSG.Monster.Existence.natCard_rhoQvis
  have : Finite CFSG.Monster.Visible.rhoQvis :=
    Nat.finite_of_card_ne_zero (by rw [hQcard]; decide)
  let fGmat : CFSG.Monster.Visible.rhoQvis →* CFSG.Monster.Generated.Gmat :=
    (CFSG.Monster.Existence.cent CFSG.Monster.Existence.xGmat).subtype.comp
      (CFSG.Monster.Existence.centGmatEquiv.symm.toMonoidHom.comp
        CFSG.Monster.Visible.rhoQvis.subtype)
  have hfGmat : Function.Injective fGmat := by
    intro x y hxy
    exact Subtype.coe_injective
      (CFSG.Monster.Existence.centGmatEquiv.symm.injective (Subtype.coe_injective hxy))
  let f : CFSG.Monster.Visible.rhoQvis →* S := eG.symm.toMonoidHom.comp fGmat
  have hf : Function.Injective f := eG.symm.injective.comp hfGmat
  have hidx := pow_le_index_of_injective_of_isExtraspecialPGroup (p := 2) (m := 12)
    hQ hQcard hH f hf
  simpa using hidx

/-- Maróti's bound for primitive almost simple groups with socle `M`. -/
theorem sporadicCase_M {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .M)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 808017424794512875886459904961710757005754368000000000 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card NativeSporadic.M = _
    rw [Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv]
    exact CFSG.Open.Open.monster_y443_derived_card
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 8192) (c := 2) (by decide)
    (fun H hH => index_ge_M e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.M, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
