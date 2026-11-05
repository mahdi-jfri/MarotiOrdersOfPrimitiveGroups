module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.ExtraspecialExt
import CFSG.Sporadic.Co2Schreier.QAut

/-!
# Conway's Second Sporadic Simple Group `Co₂`

This file proves `index_ge_Co2` (`224 ≤ H.index` for every proper subgroup `H` of `Co₂`) and
`sporadicCase_Co2` using the `2`-local subgroup `locC = 2^(1+8) : Sp₆(2)` constructed in
`CFSG.Sporadic.Co2Schreier.QAut`, where `locQ ◁ locC` is extraspecial of order `2^9 = 512`, the
quotient `locC ⧸ locQ ≅ Sp₆(2)` is simple of order `1451520` (divisible by `7`), and `locC` acts
irreducibly on `QV = locQ ⧸ Z(locQ)` (`qmod_irr`).
-/

@[expose] public section

namespace Maroti

open Subgroup CFSG.Blueprint CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- Every proper subgroup of Conway's group `Co₂` has index at least `224`. -/
theorem index_ge_Co2 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Co2) {H : Subgroup S} (hH : H ≠ ⊤) :
    224 ≤ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_Q : Nat.card (locQ.subgroupOf locC) = 2 ^ (1 + 2 * 4) := by
    rw [card_qc]
    decide
  let f : locC →* S :=
    (e.trans co2PermEquiv).symm.toMonoidHom.comp (Subgroup.inclusion locC_le_P)
  have hf : Function.Injective f :=
    (e.trans co2PermEquiv).symm.injective.comp (Subgroup.inclusion_injective locC_le_P)
  refine ExtraspecialExt.index_ge_of_normal_extraspecial_of_injective
    (locQ.subgroupOf locC) qc_extraspecial hcard_Q isSimpleGroup_quotCQ
    (q := 7) (by decide) (by rw [card_quotient_CQ]; decide)
    (n₀ := 224) (by decide) (by decide)
    (fun W hWZ hinv => ?_) f hf hH
  let U : Submodule (ZMod 2) QV :=
    ExtraspecialExt.submoduleOfSubgroup qπ qπ_one qπ_mul W
  have hU_inv : ∀ h : locC, ∀ v ∈ U,
      ((conjGL (Q := locQ.subgroupOf locC) h :
        LinearMap.GeneralLinearGroup (ZMod 2) QV) : Module.End (ZMod 2) QV) v ∈ U := by
    rintro h _ ⟨w, hwW, rfl⟩
    obtain ⟨w', hw'W, hmem_Z⟩ := hinv h w hwW
    refine ⟨w', hw'W, ?_⟩
    have h0 : qπ ((MulAut.conjNormal h w)⁻¹ * w') = 0 :=
      (qπ_eq_zero_iff _).mpr hmem_Z
    have hqπ_eq : qπ w' = qπ (MulAut.conjNormal h w) := by
      rw [qπ_mul, qπ_inv, neg_add_eq_zero] at h0
      exact h0.symm
    rw [hqπ_eq]
    rfl
  exact ExtraspecialExt.eq_bot_of_submoduleOfSubgroup_eq_bot_or_top
    qc_extraspecial qπ qπ_one qπ_mul qπ_eq_zero_iff hWZ (qmod_irr U hU_inv)

/-- Maróti's bound for primitive almost simple groups with socle `Co₂`. -/
theorem sporadicCase_Co2 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Co2)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 42305421312000 := by
    rw [Nat.card_congr (e.trans co2PermEquiv).toEquiv]
    exact card_co2P
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 224) (c := 2) (by decide)
    (fun H hH => index_ge_Co2 e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Co2, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
