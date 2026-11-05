module

public import Maroti.Linear.DegreeBoundCharTwo
public import Maroti.Linear.NumericBound
public import CFSG.Adapters.StatedPSLTwoSeven

/-!
# Proof of Lemma 2.2 and the linear socle case of Maróti's Theorem 1.1

This file assembles the degree lower bounds from `Maroti/Linear/DegreeBoundTwo.lean`,
`Maroti/Linear/DegreeBoundHigher.lean`, `Maroti/Linear/DegreeBoundFourThree.lean`, and
`Maroti/Linear/DegreeBoundCharTwo.lean` with the automorphism group order bounds from
`Maroti/Linear/OrderAut.lean` and `Maroti/Linear/NumericBound.lean` to prove:

* The theorem `Maroti.lemma_2_2` proves Lemma 2.2 of Maróti (2002), page 634: if `G ≤ Perm α` is a
  primitive almost simple group with socle `S ≅ PSL(t, p^f)` not containing `alternatingGroup α`,
  then `Nat.card G ≤ bound (Nat.card α)`.
* The theorem `Maroti.linearCase` proves `AlmostSimpleCase LinearSocle` (Step 4 of Maróti (2002),
  Section 2, page 635).
-/

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace Maroti

open Subgroup Equiv
open CFSG.Open
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

/-- Every group `S` with `StatedClassicalModel S .PSL t p f` has `30 ≤ Nat.card S`. -/
theorem thirty_le_card_of_statedClassicalModel_psl {S : Type} [Group S] {t p f : ℕ}
    (h : StatedClassicalModel S .PSL t p f) :
    30 ≤ Nat.card S := by
  have h' := h
  obtain ⟨⟨hp, hf, ht2, h22, h23⟩, -⟩ := h'
  have hcard := StatedAPI.card_of_statedClassicalModel_psl (by omega : 0 < t) h
  set q := p ^ f with hq_def
  have hq2 : 2 ≤ q := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hgcd_pos : 0 < t.gcd (q - 1) := Nat.gcd_pos_of_pos_right t (by omega)
  rw [hcard, Nat.le_div_iff_mul_le hgcd_pos]
  rcases eq_or_lt_of_le ht2 with rfl | ht3
  · have hq4 : 4 ≤ q := by
      by_contra hlt
      interval_cases hq_val : q
      · exact h22 rfl
      · exact h23 rfl
    have hprod : ∏ i ∈ Finset.Icc 2 2, (q ^ i - 1) = q ^ 2 - 1 := by simp
    have hpow : 2 * (2 - 1) / 2 = 1 := rfl
    rw [hpow, pow_one, hprod]
    have hg2 : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left (q - 1) (by omega)
    have hsq : 16 ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
    calc 30 * Nat.gcd 2 (q - 1) ≤ 30 * 2 := Nat.mul_le_mul_left 30 hg2
      _ = 4 * 15 := rfl
      _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq4 (by omega)
  · have hpow_ge : q ^ 3 ≤ q ^ (t * (t - 1) / 2) := by
      refine Nat.pow_le_pow_right (by omega) ?_
      have : 3 * 2 ≤ t * (t - 1) := Nat.mul_le_mul ht3 (by omega)
      omega
    have hprod_ge : q ^ 3 - 1 ≤ ∏ i ∈ Finset.Icc 2 t, (q ^ i - 1) := by
      have hmem : 3 ∈ Finset.Icc 2 t := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [← Finset.mul_prod_erase (Finset.Icc 2 t) (fun i => q ^ i - 1) hmem]
      refine Nat.le_mul_of_pos_right _ (Finset.prod_pos fun i hi => ?_)
      have hi2 : 2 ≤ i := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)).1
      have : 4 ≤ q ^ i := le_trans (by decide : 4 ≤ 2 ^ 2)
        (le_trans (Nat.pow_le_pow_left hq2 2) (Nat.pow_le_pow_right (by omega) hi2))
      omega
    have hnum_ge : q ^ 3 * (q ^ 3 - 1) ≤
        q ^ (t * (t - 1) / 2) * ∏ i ∈ Finset.Icc 2 t, (q ^ i - 1) :=
      Nat.mul_le_mul hpow_ge hprod_ge
    have hgcd_le : t.gcd (q - 1) ≤ q - 1 := Nat.gcd_le_right t (by omega)
    have hq3 : 8 ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
    have hq_sq : 4 ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
    have h1 : 30 * t.gcd (q - 1) ≤ q ^ 3 * (q ^ 3 - 1) := by
      calc 30 * t.gcd (q - 1)
        _ ≤ 30 * (q - 1) := Nat.mul_le_mul_left 30 hgcd_le
        _ ≤ (8 * (q ^ 2 + q + 1)) * (q - 1) :=
            Nat.mul_le_mul_right (q - 1) (by omega)
        _ = 8 * (q ^ 3 - 1) := by
            zify [show 1 ≤ q by omega, show 1 ≤ q ^ 3 by omega]
            ring
        _ ≤ q ^ 3 * (q ^ 3 - 1) := Nat.mul_le_mul_right _ hq3
    exact le_trans h1 hnum_ge

/-- If `G ≤ Perm α` is almost simple with socle `S` satisfying `LinearSocle S`, then
`5 ≤ Nat.card α` and `30 ≤ Nat.card G`. -/
theorem five_le_card_and_thirty_le_card_of_linearSocle {α : Type*} [Finite α]
    (G : Subgroup (Perm α)) (S : Type) [Group S]
    (hS : IsAlmostSimpleWith G S) (hL : LinearSocle S) :
    5 ≤ Nat.card α ∧ 30 ≤ Nat.card G := by
  obtain ⟨T, hTG, _, _, _, _, ⟨eTS⟩⟩ := hS
  obtain ⟨t, p, f, hModel⟩ := hL
  obtain ⟨hfinS, _⟩ := finite_and_card_pos_of_statedClassicalModel_psl hModel
  have _ : Finite S := hfinS
  have h30_S : 30 ≤ Nat.card S := thirty_le_card_of_statedClassicalModel_psl hModel
  have hTS : Nat.card T = Nat.card S := Nat.card_congr eTS.toEquiv
  have hTG_le : Nat.card T ≤ Nat.card G := Subgroup.card_le_of_le hTG
  have h30_G : 30 ≤ Nat.card G := by omega
  have hdvd : Nat.card S ∣ (Nat.card α).factorial := card_dvd_factorial_of_equiv eTS
  have hfact_pos : 0 < (Nat.card α).factorial := Nat.factorial_pos _
  have h30_fact : 30 ≤ (Nat.card α).factorial := le_trans h30_S (Nat.le_of_dvd hfact_pos hdvd)
  refine ⟨?_, h30_G⟩
  by_contra! hlt
  set n := Nat.card α
  revert h30_fact
  interval_cases n <;> decide

/-- In a pretransitive action of `T` on `α`, if `5 ≤ Nat.card α`, then `ptStab e x ≠ ⊤` for all
`x : α`. -/
theorem ptStab_ne_top_of_five_le {α S : Type*} [Finite α] [Group S] {T : Subgroup (Perm α)}
    [MulAction.IsPretransitive T α] (e : T ≃* S) (h5 : 5 ≤ Nat.card α) (x : α) :
    ptStab e x ≠ ⊤ := by
  intro htop
  have hidx := index_ptStab_eq_card e x
  rw [htop, Subgroup.index_top] at hidx
  omega

/-- Lemma 2.2 for `3 ≤ t`: if `G ≤ Perm α` is primitive almost simple with socle `S` satisfying
`StatedClassicalModel S .PSL t p f` for `3 ≤ t` and `¬ alternatingGroup α ≤ G`, then
`Nat.card G ≤ bound (Nat.card α)`. -/
theorem card_le_bound_of_three_le {α : Type} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) (S : Type) [Group S]
    (hG : MulAction.IsPreprimitive G α) (hS : IsAlmostSimpleWith G S)
    {t p f : ℕ} (ht : 3 ≤ t) (hModel : StatedClassicalModel S .PSL t p f)
    (hA : ¬ alternatingGroup α ≤ G) :
    Nat.card G ≤ bound (Nat.card α) := by
  have hG_le_up : Nat.card G ≤ pslAutUpper t p f :=
    le_trans hS.card_le_card_mulAut
      (le_trans (card_mulAut_le_of_statedClassicalModel_psl hModel)
        (pslOuterBound_mul_card_le_pslAutUpper hModel))
  obtain ⟨h5, _⟩ := five_le_card_and_thirty_le_card_of_linearSocle G S hS ⟨t, p, f, hModel⟩
  have hS' := hS
  obtain ⟨T, hTG, hnorm, _, _, hcent, ⟨eTS⟩⟩ := hS'
  have _ : MulAction.IsPreprimitive G α := hG
  have _ : MulAction.IsPretransitive T α := isPretransitive_socle hTG hnorm
  obtain ⟨⟨x₀⟩, -⟩ := Nat.card_pos_iff.mp (by omega : 0 < Nat.card α)
  have hModel' := hModel
  obtain ⟨⟨hp, hf, _, _, _⟩, K, _, _, hK, ⟨eS⟩⟩ := hModel'
  have hK_pos : 0 < Nat.card K := by
    rw [hK]
    exact pow_pos hp.pos f
  have _ : Finite K := Nat.finite_of_card_ne_zero hK_pos.ne'
  let eS_proj : S ≃* projectiveSL t K :=
    (eS.trans (projectiveSpecialLinearGroupEquivStatedProj t K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL t K)
  let e : T ≃* projectiveSL t K := eTS.trans eS_proj
  have hH_ne : ptStab e x₀ ≠ ⊤ := ptStab_ne_top_of_five_le e h5 x₀
  have hH_idx : (ptStab e x₀).index = Nat.card α := index_ptStab_eq_card e x₀
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rcases eq_or_lt_of_le hq2 with hq_eq2 | hq3
  · have hf1 : f = 1 := by
      by_contra hf_ne
      have hf2 : 2 ≤ f := by omega
      have : 4 ≤ p ^ f := le_trans (by decide : 4 ≤ 2 ^ 2)
        (le_trans (Nat.pow_le_pow_left hp.two_le 2) (Nat.pow_le_pow_right hp.pos hf2))
      omega
    subst hf1
    have hp2 : p = 2 := by rw [pow_one] at hq_eq2; exact hq_eq2.symm
    subst hp2
    rw [pow_one] at hK
    have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have _ : CharP K 2 := charP_two_of_card_two hK
    rcases index_eq_eight_or_two_pow_sub_one_le_of_card_two ht hK hH_ne with
      ⟨rfl, hidx8⟩ | hidx_ge
    · exfalso
      have hn8 : Nat.card α = 8 := hH_idx.symm.trans hidx8
      have hcard_T : Nat.card T = 20160 := by
        rw [Nat.card_congr e.toEquiv]
        exact card_projectiveSL_four_two hK
      have hcard_G : 20160 ≤ Nat.card G := hcard_T ▸ Subgroup.card_le_of_le hTG
      apply hA
      apply alternatingGroup_le_of_factorial_le_two_mul_card G
      rw [hn8, show (8 : ℕ).factorial = 40320 by decide]
      omega
    · rcases eq_or_lt_of_le hidx_ge with hidx_eq | hidx_gt
      · have hM : ptStab e x₀ ∈ extremalParabolics (projectiveSL t K) 2 :=
          mem_extremalParabolics_of_index_eq_two_pow_sub_one ht hK hidx_eq.symm
        have hG_le_proj :=
          card_le_card_of_ptStab_mem_extremalParabolics_two hnorm hcent ht hK e hM
        have hproj_eq_S : Nat.card (projectiveSL t K) = Nat.card S :=
          (Nat.card_congr eS_proj.toEquiv).symm
        have hn_eq : Nat.card α = 2 ^ t - 1 := hH_idx.symm.trans hidx_eq.symm
        rw [hproj_eq_S] at hG_le_proj
        rw [hn_eq]
        exact le_trans hG_le_proj (card_le_bound_two_pow_sub_one ht hModel)
      · have hn_ge : 2 ^ t ≤ Nat.card α := by omega
        exact le_trans hG_le_up (pslAutUpper_le_bound_two_pow ht hn_ge)
  · by_cases h33 : t = 3 ∧ p ^ f = 3
    · rcases h33 with ⟨rfl, hpf3⟩
      have hf1 : f = 1 := by
        by_contra hf_ne
        have hf2 : 2 ≤ f := by omega
        have : 4 ≤ p ^ f := le_trans (by decide : 4 ≤ 2 ^ 2)
          (le_trans (Nat.pow_le_pow_left hp.two_le 2) (Nat.pow_le_pow_right hp.pos hf2))
        omega
      subst hf1
      have hp3 : p = 3 := by rw [pow_one] at hpf3; exact hpf3
      subst hp3
      rw [pow_one] at hK
      have h13 : 13 ≤ Nat.card α := hH_idx ▸ thirteen_le_index_of_three_three hK hH_ne
      exact le_trans hG_le_up (pslAutUpper_three_three_le_bound h13)
    · by_cases h43 : t = 4 ∧ p ^ f = 3
      · rcases h43 with ⟨rfl, hpf3⟩
        have hf1 : f = 1 := by
          by_contra hf_ne
          have hf2 : 2 ≤ f := by omega
          have : 4 ≤ p ^ f := le_trans (by decide : 4 ≤ 2 ^ 2)
            (le_trans (Nat.pow_le_pow_left hp.two_le 2) (Nat.pow_le_pow_right hp.pos hf2))
          omega
        subst hf1
        have hp3 : p = 3 := by rw [pow_one] at hpf3; exact hpf3
        subst hp3
        rw [pow_one] at hK
        have h32 : 32 ≤ Nat.card α := thirty_two_le_card_of_four_three e hK
        exact le_trans hG_le_up (pslAutUpper_four_three_le_bound h32)
      · have hpow_le : (p ^ f) ^ (t - 1) ≤ Nat.card α := by
          rw [← hK, ← hH_idx]
          exact card_pow_pred_le_index_of_ne_top ht hH_ne
        exact le_trans hG_le_up
          (pslAutUpper_le_bound_of_three_le hp hf ht hq3 h33 h43 hpow_le)

open Classical in
attribute [local instance] Fintype.ofFinite in
/-- **Lemma 2.2** of Maróti (2002), p. 634: if `G ≤ Perm α` is a primitive almost simple group
with socle `S ≅ PSL(t, p^f)` (`LinearSocle S`) and does not contain `alternatingGroup α`, then
`Nat.card G ≤ bound (Nat.card α)`. -/
theorem lemma_2_2 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] (hG : MulAction.IsPreprimitive G α) (hS : IsAlmostSimpleWith G S) (hL : LinearSocle S)
    (hA : ¬ alternatingGroup α ≤ G) : Nat.card G ≤ bound (Nat.card α) := by
  let _ : Fintype α := Fintype.ofFinite α
  let _ : DecidableEq α := Classical.decEq α
  obtain ⟨t, p, f, hModel⟩ := hL
  have hModel' := hModel
  obtain ⟨⟨hp, hf, ht2, h22, h23⟩, K, _, _, hK, ⟨eS⟩⟩ := hModel'
  rcases lt_or_eq_of_le ht2 with ht3 | rfl
  · exact card_le_bound_of_three_le G S hG hS ht3 hModel hA
  have hG_le_up : Nat.card G ≤ pslAutUpper 2 p f :=
    le_trans hS.card_le_card_mulAut
      (le_trans (card_mulAut_le_of_statedClassicalModel_psl hModel)
        (pslOuterBound_mul_card_le_pslAutUpper hModel))
  have hS' := hS
  obtain ⟨T, hTG, hnorm, _, _, _, ⟨eTS⟩⟩ := hS'
  have _ : MulAction.IsPreprimitive G α := hG
  have _ : MulAction.IsPretransitive T α := isPretransitive_socle hTG hnorm
  have hK_pos : 0 < Nat.card K := by
    rw [hK]
    exact pow_pos hp.pos f
  have _ : Finite K := Nat.finite_of_card_ne_zero hK_pos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have _ : Fact p.Prime := ⟨hp⟩
  have _ : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  let eS_proj : S ≃* projectiveSL 2 K :=
    (eS.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K)
  let e : T ≃* projectiveSL 2 K := eTS.trans eS_proj
  have hT_card_eq : Nat.card T = Nat.card S := Nat.card_congr eTS.toEquiv
  have hproj_card_eq : Nat.card (projectiveSL 2 K) = Nat.card S :=
    (Nat.card_congr eS_proj.toEquiv).symm
  have hTG_le : Nat.card T ≤ Nat.card G := Subgroup.card_le_of_le hTG
  rcases eq_or_lt_of_le hf with rfl | hf2_lt
  · rw [pow_one] at hK h22 h23
    have hp_dvd : p ∣ Nat.card S := by
      rw [← hproj_card_eq]
      have hU : Nat.card (projUnitriangular 2 K) = p := by
        rw [card_projUnitriangular, hK, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one]
      rw [← hU]
      exact (projUnitriangular 2 K).card_subgroup_dvd_card
    have hp_le_n : p ≤ Nat.card α :=
      prime_le_card_of_faithfulSMul (G := T) (α := α) hp (hT_card_eq.symm ▸ hp_dvd)
    rcases le_or_gt 11 p with hp11 | hplt11
    · exact le_trans hG_le_up (pslAutUpper_two_one_le_bound hp11 hp_le_n)
    · have hp_cases : p = 5 ∨ p = 7 := by
        have hp2_le := hp.two_le
        have hp_ne2 : p ≠ 2 := fun h => h22 (by rw [h])
        have hp_ne3 : p ≠ 3 := fun h => h23 (by rw [h])
        revert hp hp_ne2 hp_ne3
        interval_cases p <;> decide
      rcases hp_cases with rfl | rfl
      · have hS60 : Nat.card S = 60 := by
          rw [StatedAPI.card_of_statedClassicalModel_psl (by decide : 0 < 2) hModel]
          decide
        rcases eq_or_lt_of_le hp_le_n with hn5 | hn6
        · exfalso
          apply hA
          apply alternatingGroup_le_of_factorial_le_two_mul_card G
          rw [← hn5, show (5 : ℕ).factorial = 120 by decide]
          omega
        · exact le_trans hG_le_up (pslAutUpper_two_five_one_le_bound hn6)
      · exact card_le_bound_of_three_le G S hG hS (by decide : 3 ≤ 3)
          (StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven hModel) hA
  · have hf2 : 2 ≤ f := hf2_lt
    rcases eq_or_lt_of_le hp.two_le with hp2 | hp3
    · have hp_eq2 : p = 2 := hp2.symm
      subst hp_eq2
      rcases eq_or_lt_of_le hf2 with rfl | hf3_lt
      · have hS60 : Nat.card S = 60 := by
          rw [StatedAPI.card_of_statedClassicalModel_psl (by decide : 0 < 2) hModel]
          decide
        have h5_dvd : 5 ∣ Nat.card S := by rw [hS60]; decide
        have h5_le : 5 ≤ Nat.card α :=
          prime_le_card_of_faithfulSMul (G := T) (α := α) (by decide : Nat.Prime 5)
            (hT_card_eq.symm ▸ h5_dvd)
        rcases eq_or_lt_of_le h5_le with hn5 | hn6
        · exfalso
          apply hA
          apply alternatingGroup_le_of_factorial_le_two_mul_card G
          rw [← hn5, show (5 : ℕ).factorial = 120 by decide]
          omega
        · exact le_trans hG_le_up (pslAutUpper_two_two_two_le_bound hn6)
      · have hf3 : 3 ≤ f := hf3_lt
        rcases eq_or_lt_of_le hf3 with rfl | hf4
        · have hS504 : Nat.card (projectiveSL 2 K) = 504 := by
            rw [hproj_card_eq,
              StatedAPI.card_of_statedClassicalModel_psl (by decide : 0 < 2) hModel]
            decide
          have hn9 : 9 ≤ Nat.card α := nine_le_card_of_eight e hK hS504
          exact le_trans hG_le_up (pslAutUpper_two_two_three_le_bound hn9)
        · obtain ⟨x, _, hrel_le, _, hp2_bound, _⟩ := exists_borel_index_two e hp
          have h2f_le : 2 ^ f ≤ Nat.card α := by
            rw [← hK]
            exact le_trans (hp2_bound rfl) hrel_le
          exact le_trans hG_le_up (pslAutUpper_two_two_le_bound hf4 h2f_le)
    · have hq9 : 9 ≤ Nat.card K := by
        rw [hK]
        exact le_trans (by decide : 9 ≤ 3 ^ 2)
          (le_trans (Nat.pow_le_pow_left hp3 2) (Nat.pow_le_pow_right hp.pos hf2))
      have hhalf : (p ^ f + 1) / 2 ≤ Nat.card α := by
        rw [← hK]
        exact half_card_add_one_le_card_of_odd e hp hp3 hq9
      rcases le_or_gt 4 f with hf4 | hflt4
      · exact le_trans hG_le_up (pslAutUpper_two_odd_four_le_f_le_bound hp3 hf4 hhalf)
      · rcases le_or_gt 49 (p ^ f) with hq49 | hq_lt49
        · exact le_trans hG_le_up
            (pslAutUpper_two_odd_small_f_le_bound hf2 (by omega) hq49 hhalf)
        · rcases eq_or_lt_of_le hf2 with rfl | hf3_lt
          · have hp_lt7 : p < 7 := by
              by_contra! hp7
              have : 49 ≤ p ^ 2 := Nat.pow_le_pow_left hp7 2
              omega
            have hp_cases : p = 3 ∨ p = 5 := by
              revert hp hq_lt49
              interval_cases p <;> decide
            rcases hp_cases with rfl | rfl
            · have hS360 : Nat.card (projectiveSL 2 K) = 360 := by
                rw [hproj_card_eq,
                  StatedAPI.card_of_statedClassicalModel_psl (by decide : 0 < 2) hModel]
                decide
              rcases six_or_nine_le_card_of_nine e hK hS360 with hn6 | hn9
              · exfalso
                apply hA
                apply alternatingGroup_le_of_factorial_le_two_mul_card G
                rw [hn6, show (6 : ℕ).factorial = 720 by decide]
                omega
              · exact le_trans hG_le_up (pslAutUpper_two_three_two_le_bound hn9)
            · have hS7800 : Nat.card (projectiveSL 2 K) = 7800 := by
                rw [hproj_card_eq,
                  StatedAPI.card_of_statedClassicalModel_psl (by decide : 0 < 2) hModel]
                decide
              have hn16 : 16 ≤ Nat.card α := sixteen_le_card_of_twenty_five e hK hS7800
              exact le_trans hG_le_up (pslAutUpper_two_five_two_le_bound hn16)
          · have hf_eq3 : f = 3 := by omega
            subst hf_eq3
            have hp_lt4 : p < 4 := by
              by_contra! hp4
              have : 64 ≤ p ^ 3 := Nat.pow_le_pow_left hp4 3
              omega
            have hp_eq3 : p = 3 := by omega
            subst hp_eq3
            have hn18 : 18 ≤ Nat.card α := eighteen_le_card_of_twenty_seven e hK
            exact le_trans hG_le_up (pslAutUpper_two_three_three_le_bound (by omega))

/-- Step 4 of Maróti (2002), Section 2, page 635: `AlmostSimpleConclusion G` holds for every
primitive almost simple group `G` whose socle `S` is a projective special linear group
(`LinearSocle S`). -/
theorem linearCase : AlmostSimpleCase LinearSocle := by
  intro α _ G S _ hG hS hL
  classical
  let _ : Fintype α := Fintype.ofFinite α
  by_cases hA : alternatingGroup α ≤ G
  · obtain ⟨h5, _⟩ := five_le_card_and_thirty_le_card_of_linearSocle G S hS hL
    exact Or.inl (isSubsetActionType_of_alternatingGroup_le G h5 hA)
  · exact Or.inr (Or.inr (lemma_2_2 G S hG hS hL hA))

end Maroti
