module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.ExtraspecialExt
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
import CFSG.Sporadic.SuzOddCore.SmallModel

/-!
# Suzuki's Sporadic Simple Group `Suz`

This file proves `index_ge_Suz` (`80 ≤ H.index` for every proper subgroup `H` of `Suz`) and
`sporadicCase_Suz` using the `2`-local subgroup `invE 1 = 2^(1+6)_.Ω⁻₆(2)` of `Suz` constructed in
`CFSG.ComponentClassification.AS81.SuzB0`, where `coord_qVec.Q ◁ invE 1` is extraspecial of order
`2^7 = 128`, the quotient `invE 1 ⧸ coord_qVec.Q ≅ Ω⁻₆(2)` is simple of order `25920` (divisible by
`5`), and `Ω⁻₆(2)` acts irreducibly on `(ZMod 2)^6` (`eq_bot_or_eq_top_of_timmesfeldOmega`).
-/

@[expose] public section

namespace Maroti

open Subgroup CFSG.Blueprint CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.ComponentClassification.PSL3Four CFSG.Open

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-- Every proper subgroup of Suzuki's group `Suz` has index at least `80`. -/
theorem index_ge_Suz {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Suz) {H : Subgroup S} (hH : H ≠ ⊤) :
    80 ≤ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (coord_qVec.Q.subgroupOf (invE 1)).Normal := ker_rho1 ▸ inferInstance
  have hQ_card : Nat.card coord_qVec.Q = 2 ^ (1 + 2 * 3) := by
    rw [coord_qVec.card_Q]
    decide
  let e_quot : (invE 1 ⧸ coord_qVec.Q.subgroupOf (invE 1)) ≃* ↥(timmesfeldOmega qMinus) :=
    (QuotientGroup.quotientMulEquivOfEq ker_rho1.symm).trans
      ((QuotientGroup.quotientKerEquivRange rho1).trans (MulEquiv.subgroupCongr range_rho1))
  have hω := omega_facts b0_parts.2.2.2.2.2.2
  have hSimple : IsSimpleGroup (invE 1 ⧸ coord_qVec.Q.subgroupOf (invE 1)) :=
    (MulEquiv.isSimpleGroup_congr e_quot).mpr hω.2.2.1
  have hcard_quot : Nat.card (invE 1 ⧸ coord_qVec.Q.subgroupOf (invE 1)) = 25920 :=
    (Nat.card_congr e_quot.toEquiv).trans hω.1
  have hE_le_M : invE 1 ≤ suzM := (invE_le_centM (by norm_num : 1 < 4)).trans inf_le_right
  let f : ↥(invE 1) →* S :=
    (e.trans suzEquivM).symm.toMonoidHom.comp (Subgroup.inclusion hE_le_M)
  have hf : Function.Injective f :=
    (e.trans suzEquivM).symm.injective.comp (Subgroup.inclusion_injective hE_le_M)
  let ψ : coord_qVec.Q → (Fin 6 → ZMod 2) :=
    fun q => Coord.psi (t := suzInv 1) (q := qVec) (q : Equiv.Perm (Fin 1782))
  have hψ_mul : ∀ a b : coord_qVec.Q, ψ (a * b) = ψ a + ψ b :=
    fun a b => coord_qVec.psi_mul a.2 b.2
  have hψ_one : ψ 1 = 0 := by
    apply add_left_cancel (a := ψ 1)
    rw [← hψ_mul 1 1, mul_one, add_zero]
  have hψ_ker : ∀ a : coord_qVec.Q, ψ a = 0 ↔ a ∈ center coord_qVec.Q := fun a => by
    rw [ show ψ a = 0 ↔ (a : Equiv.Perm (Fin 1782)) ∈ zpowers (suzInv 1) from
      coord_qVec.psi_eq_zero_iff a.2, ← coord_qVec.isExtraspecialPGroup_Q.2]
    simp
  refine ExtraspecialExt.index_ge_of_normal_extraspecial_subgroupOf_injective
    Q_le_invE coord_qVec.isExtraspecialPGroup_Q.1 hQ_card hSimple
    (q := 5) (by decide) (by rw [hcard_quot]; decide)
    (n₀ := 80) (by decide) (by decide)
    (fun W hWZ hinv => ?_) f hf hH
  let U : Submodule (ZMod 2) (Fin 6 → ZMod 2) :=
    ExtraspecialExt.submoduleOfSubgroup ψ hψ_one hψ_mul W
  have hU_inv : ∀ γ ∈ timmesfeldOmega qMinus, ∀ v ∈ U, γ v ∈ U := by
    rintro γ hγ _ ⟨w, hwW, rfl⟩
    rw [← range_rho1] at hγ
    obtain ⟨c, rfl⟩ := hγ
    obtain ⟨w', hw'W, hmem_Z⟩ := hinv (c : Equiv.Perm (Fin 1782)) c.2 w hwW
    refine ⟨w', hw'W, ?_⟩
    have hψ_eq : ψ ⟨(c : Equiv.Perm (Fin 1782)) * (w : Equiv.Perm (Fin 1782)) *
        (c : Equiv.Perm (Fin 1782))⁻¹,
        ExtraspecialExt.conj_mem_of_normal_subgroupOf Q_le_invE c.2 w.2⟩ = ψ w' :=
      ExtraspecialExt.psi_eq_of_inv_mul_mem_center ψ hψ_mul hψ_ker hmem_Z
    have hrho_eq : rho1 c (ψ w) =
        ψ ⟨(c : Equiv.Perm (Fin 1782)) * (w : Equiv.Perm (Fin 1782)) *
          (c : Equiv.Perm (Fin 1782))⁻¹,
          ExtraspecialExt.conj_mem_of_normal_subgroupOf Q_le_invE c.2 w.2⟩ :=
      coord_qVec.rho_psi invE_le c w.2
    rw [hrho_eq, hψ_eq]
  exact ExtraspecialExt.eq_bot_of_submoduleOfSubgroup_eq_bot_or_top
    coord_qVec.isExtraspecialPGroup_Q.1 ψ hψ_one hψ_mul hψ_ker hWZ
    (Sec2Omega.eq_bot_or_eq_top_of_timmesfeldOmega hU_inv)

/-- Maróti's bound for primitive almost simple groups with socle `Suz`. -/
theorem sporadicCase_Suz {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Suz)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 448345497600 := by
    rw [Nat.card_congr (e.trans suzEquivM).toEquiv]
    exact suzM_card
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 80) (c := 2) (by decide)
    (fun H hH => index_ge_Suz e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Suz, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
