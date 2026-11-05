module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.Sporadic.ExtraspecialExt
import CFSG.Sporadic.Th.Certificate
import CFSG.Sporadic.Th.Recog.EightDim

/-!
# Thompson's Sporadic Simple Group `Th`

This file proves `index_ge_Th` (`224 ≤ H.index` for every proper subgroup `H` of `Th`) and
`sporadicCase_Th` using the `2`-local subgroup `M = 2^(1+8).A₉` of `Th` constructed in
`CFSG.Sporadic.Th.Max3` and the irreducibility of `A₉` on `Q ⧸ Z(Q) ≅ (ZMod 2)^8` from
`CFSG.Sporadic.Th.Recog.EightDim`.
-/

@[expose] public section

namespace Maroti

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
  CFSG.Sporadic.Th.Max3.InvRep CFSG.Sporadic.Th.Recog

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem exists_nonsing_sum_sing :
    ∃ u : V8, u ≠ 0 ∧ e01 + u ≠ 0 ∧ qf u = 1 ∧ qf (e01 + u) = 0 := by
  decide +kernel

private theorem vy_ne_zero : vy ≠ 0 := by decide +kernel
private theorem qf_vy : qf vy = 0 := by decide +kernel
private theorem e0_add_vy : e0 + vy = e01 := by decide +kernel

/-- Every `rho8a`-invariant additive subset of `V8 = (Fin 8 → ZMod 2)` is `{0}` or `Set.univ`. -/
private theorem rho8a_irreducible (P : V8 → Prop) (hP0 : P 0)
    (hPadd : ∀ u v : V8, P u → P v → P (u + v))
    (hU : ∀ (g : alternatingGroup (Fin 9)) (v : V8), P v → P (rho8a g v)) :
    (∀ v : V8, P v → v = 0) ∨ (∀ v : V8, P v) := by
  by_cases hbot : ∀ v : V8, P v → v = 0
  · exact Or.inl hbot
  · right
    push Not at hbot
    obtain ⟨v₀, hv₀U, hv₀_ne⟩ := hbot
    have hsing_of : ∀ v : V8, P v → v ≠ 0 → qf v = 0 → ∀ w : V8, w ≠ 0 → qf w = 0 → P w := by
      intro v hvU hv_ne hv_qf w hw_ne hw_qf
      obtain ⟨g, rfl⟩ := exists_rho8a_eq hv_ne hw_ne (hv_qf.trans hw_qf.symm)
      exact hU g v hvU
    have hnonsing_of : ∀ v : V8, P v → v ≠ 0 → qf v = 1 → ∀ w : V8, w ≠ 0 → qf w = 1 → P w := by
      intro v hvU hv_ne hv_qf w hw_ne hw_qf
      obtain ⟨g, rfl⟩ := exists_rho8a_eq hv_ne hw_ne (hv_qf.trans hw_qf.symm)
      exact hU g v hvU
    have he01_and_e0 : P e01 ∧ P e0 := by
      rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (qf v₀) with hq0 | hq1
      · have he0 : P e0 := hsing_of v₀ hv₀U hv₀_ne hq0 e0 e0_ne_zero qf_e0
        have hvy : P vy := hsing_of v₀ hv₀U hv₀_ne hq0 vy vy_ne_zero qf_vy
        have he01 : P e01 := e0_add_vy ▸ hPadd e0 vy he0 hvy
        exact ⟨he01, he0⟩
      · have he01 : P e01 := hnonsing_of v₀ hv₀U hv₀_ne hq1 e01 e01_ne_zero qf_e01
        obtain ⟨u, hu_ne, heu_ne, hu_qf, heu_qf⟩ := exists_nonsing_sum_sing
        have huU : P u := hnonsing_of v₀ hv₀U hv₀_ne hq1 u hu_ne hu_qf
        have heuU : P (e01 + u) := hPadd e01 u he01 huU
        have he0 : P e0 := hsing_of (e01 + u) heuU heu_ne heu_qf e0 e0_ne_zero qf_e0
        exact ⟨he01, he0⟩
    intro w
    by_cases hw : w = 0
    · exact hw ▸ hP0
    · rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases (qf w) with hqw0 | hqw1
      · exact hsing_of e0 he01_and_e0.2 e0_ne_zero qf_e0 w hw hqw0
      · exact hnonsing_of e01 he01_and_e0.1 e01_ne_zero qf_e01 w hw hqw1

/-- Every proper subgroup of Thompson's group `Th` has index at least `224`. -/
theorem index_ge_Th {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Th) {H : Subgroup S} (hH : H ≠ ⊤) :
    224 ≤ H.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_J : Nat.card J = 90745943887872000 := by
    rw [← Nat.card_congr thEquivJ.toEquiv]
    exact card_nativeTh_kernel
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [hcard_J]; decide)
  have hQ_card : Nat.card Q = 2 ^ (1 + 2 * 4) := by
    rw [card_Q]
    decide
  let ψ : Q → V8 := fun q => Multiplicative.toAdd (theta.symm (QuotientGroup.mk q))
  have hψ_one : ψ 1 = 0 := by
    simp [ψ, QuotientGroup.mk_one]
  have hψ_mul : ∀ a b : Q, ψ (a * b) = ψ a + ψ b := fun a b => by
    simp only [ψ, QuotientGroup.mk_mul, map_mul, toAdd_mul]
  have hψ_ker : ∀ a : Q, ψ a = 0 ↔ a ∈ center Q := fun a => by
    simp only [ψ, toAdd_eq_zero, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ExtraspecialExt.index_ge_of_normal_extraspecial_simple_quotient
    Q_le_M isExtraspecialPGroup_Q hQ_card AltQuot.isSimpleGroup_MQ
    (q := 7) (by decide) (by rw [AltQuot.card_MQ]; decide)
    (n₀ := 224) (by decide) (by decide)
    (fun W hWZ hinv => ?_) (e.trans thEquivJ) hH
  have hP0 : ∃ w ∈ W, ψ w = 0 := ⟨1, W.one_mem, hψ_one⟩
  have hPadd : ∀ u v : V8, (∃ w ∈ W, ψ w = u) → (∃ w ∈ W, ψ w = v) →
      (∃ w ∈ W, ψ w = u + v) := by
    rintro _ _ ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    exact ⟨w₁ * w₂, W.mul_mem hw₁ hw₂, hψ_mul w₁ w₂⟩
  have hU_inv : ∀ (g : alternatingGroup (Fin 9)) (v : V8),
      (∃ w ∈ W, ψ w = v) → (∃ w ∈ W, ψ w = rho8a g v) := by
    rintro g _ ⟨w, hwW, rfl⟩
    obtain ⟨m, hm_proj⟩ := AltQuot.proj_surjective (kappa.symm g)
    have hkap_m : kap m = g := by
      change kappa (AltQuot.proj m) = g
      rw [hm_proj, MulEquiv.apply_symm_apply]
    obtain ⟨w', hw'W, hmem_Z⟩ := hinv (m : J) m.2 w hwW
    refine ⟨w', hw'W, ?_⟩
    have hmk_eq : (QuotientGroup.mk ⟨(m : J) * (w : J) * (m : J)⁻¹,
        AltQuot.conj_mem_Q_of_mem_M m.2 w.2⟩ : Q ⧸ center Q) = QuotientGroup.mk w' :=
      QuotientGroup.eq.mpr hmem_Z
    have htheta_eq : theta (Multiplicative.ofAdd (rho8a (kap m) (ψ w))) =
        QuotientGroup.mk w' :=
      (theta_rho8a_kap m w (ψ w) (MulEquiv.apply_symm_apply theta (QuotientGroup.mk w))).trans
        hmk_eq
    have hrho_eq : rho8a (kap m) (ψ w) = ψ w' := by
      change Multiplicative.toAdd (Multiplicative.ofAdd (rho8a (kap m) (ψ w))) =
        Multiplicative.toAdd (theta.symm (QuotientGroup.mk w'))
      rw [← htheta_eq, MulEquiv.symm_apply_apply]
    rw [← hkap_m, hrho_eq]
  rcases rho8a_irreducible (fun v => ∃ w ∈ W, ψ w = v) hP0 hPadd hU_inv with hbot | htop
  · rw [eq_bot_iff]
    intro w hw
    have h0 : ψ w = 0 := hbot (ψ w) ⟨w, hw, rfl⟩
    have hzc : w ∈ W ⊓ center Q := ⟨hw, (hψ_ker w).mp h0⟩
    rwa [ExtraspecialExt.inf_center_eq_bot_of_not_le isExtraspecialPGroup_Q hWZ] at hzc
  · exfalso
    refine ExtraspecialExt.not_forall_exists_inv_mul_mem_center_of_not_le
      isExtraspecialPGroup_Q hWZ fun q => ?_
    obtain ⟨w, hw, hqw⟩ := htop (ψ q)
    have hmk : (QuotientGroup.mk q : Q ⧸ center Q) = QuotientGroup.mk w :=
      theta.symm.injective (Multiplicative.toAdd.injective hqw.symm)
    exact ⟨w, hw, QuotientGroup.eq.mp hmk⟩

/-- Maróti's bound for primitive almost simple groups with socle `Th`. -/
theorem sporadicCase_Th {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Th)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 90745943887872000 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_nativeTh_kernel
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 224) (c := 2) (by decide)
    (fun H hH => index_ge_Th e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Th, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
