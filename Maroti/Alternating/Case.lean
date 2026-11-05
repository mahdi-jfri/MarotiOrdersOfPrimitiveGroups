module

public import Maroti.Alternating.Action
public import Maroti.Alternating.Bochert
public import Maroti.Alternating.Small

/-!
# Alternating socle case of Maróti's Theorem 1.1

This file completes Step 3 of Section 2 of A. Maróti, *On the orders of primitive groups*,
J. Algebra 258 (2002), page 635, proving
`Maroti.alternatingCase : AlmostSimpleCase AlternatingSocle`.

When `7 ≤ m` and the image `H` of the point stabilizer `stabilizer G ω` in `Perm (Fin m)` acts
primitively on `Fin m`, `H` is a proper subgroup of `G'` of index `n ≥ m ≥ 7` and therefore cannot
contain `alternatingGroup (Fin m)`. Applying Bochert's theorem (`Maroti.bochert`, together with
`Maroti.bochert_eight` for `m = 8` and `factorial_le_bound_of_bochert` for `m ≥ 9`) gives
`Nat.card G ≤ bound (Nat.card α)` (`primitive_card_le_bound`). Combining the primitive,
imprimitive, and intransitive cases for `m ≥ 7` (`alternatingCase_ge_seven`) with the small cases
`m = 5` and `m = 6` (`alternatingCase_five`, `alternatingCase_six`) yields `alternatingCase`.
-/

@[expose] public section

namespace Maroti

namespace Alternating

open Equiv Equiv.Perm MulAction Subgroup
open scoped Nat

/-- If `H ≤ G' ≤ Perm (Fin m)` (`7 ≤ m`, `alternatingGroup (Fin m) ≤ G'`) acts primitively on
`Fin m` and `m ≤ (H.subgroupOf G').index`, then `Nat.card G' ≤ bound (H.subgroupOf G').index`. -/
theorem primitive_card_le_bound {m : ℕ} (hm : 7 ≤ m)
    (G' H : Subgroup (Perm (Fin m))) (hA : alternatingGroup (Fin m) ≤ G') (hHG' : H ≤ G')
    (hm_le_n : m ≤ (H.subgroupOf G').index) (h_prim : IsPreprimitive H (Fin m)) :
    Nat.card G' ≤ bound (H.subgroupOf G').index := by
  set n := (H.subgroupOf G').index
  have hH_sub_card : Nat.card (H.subgroupOf G') = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG').toEquiv
  have hHG'_mul : Nat.card H * n = Nat.card G' := by
    rw [← hH_sub_card]
    exact Subgroup.card_mul_index (H.subgroupOf G')
  have hG'_mul : Nat.card G' * G'.index = m ! := by
    have h := Subgroup.card_mul_index G'
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hH_mul : Nat.card H * H.index = m ! := by
    have h := Subgroup.card_mul_index H
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hH_pos : 0 < Nat.card H := Nat.card_pos
  have hH_idx_eq : H.index = n * G'.index := by
    apply Nat.eq_of_mul_eq_mul_left hH_pos
    rw [hH_mul, ← mul_assoc, hHG'_mul, hG'_mul]
  have hA_card : Nat.card (alternatingGroup (Fin m)) = m ! / 2 :=
    nat_card_alternatingGroup_fin (by omega)
  have hm_even : 2 * (m ! / 2) = m ! :=
    Nat.mul_div_cancel' (Nat.dvd_factorial (by decide) (by omega))
  have hm_fact_pos : 5040 ≤ m ! := (by decide : 5040 ≤ 7 !).trans (Nat.factorial_le hm)
  have hG'_card_ge : m ! / 2 ≤ Nat.card G' := by
    rw [← hA_card]
    exact Subgroup.card_le_of_le hA
  have hG'_idx_cases : G'.index = 1 ∨ G'.index = 2 := by
    by_contra hlt
    have h3 : G'.index = 0 ∨ 3 ≤ G'.index := by omega
    rcases h3 with h0 | h3
    · rw [h0] at hG'_mul; omega
    · have : (m ! / 2) * 3 ≤ Nat.card G' * G'.index := Nat.mul_le_mul hG'_card_ge h3
      omega
  have hnotA : ¬ alternatingGroup (Fin m) ≤ H := by
    intro hAH
    have hH_ge : m ! / 2 ≤ Nat.card H := by
      rw [← hA_card]
      exact Subgroup.card_le_of_le hAH
    have hidx_ge : 7 ≤ H.index := by
      rcases hG'_idx_cases with h | h <;> { rw [hH_idx_eq, h]; omega }
    have : (m ! / 2) * 7 ≤ Nat.card H * H.index := Nat.mul_le_mul hH_ge hidx_ge
    omega
  have hG'_le_fact : Nat.card G' ≤ m ! := by
    have h := Subgroup.card_le_card_group G'
    rwa [Nat.card_perm, Nat.card_fin] at h
  rcases eq_or_ne m 7 with rfl | hm7
  · have hboc := Maroti.bochert H h_prim hnotA
    have h24 : ((7 + 1) / 2)! = 24 := by decide
    rw [h24, hH_idx_eq] at hboc
    have hn12 : 12 ≤ n := by
      rcases hG'_idx_cases with h | h <;> { rw [h] at hboc; omega }
    have hb12 : 7 ! ≤ bound 12 := by decide
    exact (hG'_le_fact.trans hb12).trans (bound_mono hn12)
  · rcases eq_or_ne m 8 with rfl | hm8
    · have hboc8 := Maroti.bochert_eight H h_prim hnotA
      rw [hH_idx_eq] at hboc8
      rcases hG'_idx_cases with h1 | h2
      · rw [h1, mul_one] at hboc8
        have hb30 : 8 ! ≤ bound 30 := by decide
        exact (hG'_le_fact.trans hb30).trans (bound_mono hboc8)
      · rw [h2] at hboc8 hG'_mul
        have hn15 : 15 ≤ n := by omega
        have h8fact : 8 ! = 40320 := by decide
        have hG'_eq : Nat.card G' = 20160 := by omega
        have hb15 : 20160 ≤ bound 15 := by decide
        rw [hG'_eq]
        exact hb15.trans (bound_mono hn15)
    · have hm9 : 9 ≤ m := by omega
      have hboc := Maroti.bochert H h_prim hnotA
      have hboc_le : ((m + 1) / 2)! ≤ 2 * n := by
        rw [hH_idx_eq] at hboc
        rcases hG'_idx_cases with h | h <;> { rw [h] at hboc; omega }
      exact hG'_le_fact.trans (factorial_le_bound_of_bochert hm9 hboc_le)

/-- The conclusion `AlmostSimpleConclusion G` holds when `G` has socle `alternatingGroup (Fin m)`
for `7 ≤ m`. -/
theorem alternatingCase_ge_seven {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) {S : Type*} [Group S]
    (hG : IsPreprimitive G α) (hS : IsAlmostSimpleWith G S)
    {m : ℕ} (hm : 7 ≤ m) (eS : S ≃* alternatingGroup (Fin m)) :
    AlmostSimpleConclusion G := by
  obtain ⟨hm_le, _, _, _, ψ, hψ_inj, hA, _⟩ :=
    exists_injective_hom_perm_of_ne_six G hG hS (by omega) (by omega) eS
  have hα_ne : Nonempty α := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card α)).1
  obtain ⟨ω⟩ := hα_ne
  set M := stabilizer G ω
  set G' := ψ.range
  set H := M.map ψ
  have hHG' : H ≤ G' := Subgroup.map_le_range ψ M
  by_cases h_trans : IsPretransitive H (Fin m)
  · right; right
    have hG_card : Nat.card G = Nat.card G' :=
      Nat.card_congr (Equiv.ofInjective ψ hψ_inj)
    have horb : orbit G ω = Set.univ := orbit_eq_univ G ω
    let eUniv : α ≃ orbit G ω :=
      { toFun := fun x => ⟨x, horb.symm ▸ Set.mem_univ x⟩
        invFun := fun x => x.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hn_M : Nat.card α = M.index :=
      Nat.card_congr (eUniv.trans (orbitEquivQuotientStabilizer G ω))
    let q : G ⧸ M → G' ⧸ H.subgroupOf G' :=
      Quotient.lift (fun g : G => (⟦⟨ψ g, ⟨g, rfl⟩⟩⟧ : G' ⧸ H.subgroupOf G')) (by
        intro a b hab
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        rw [Subgroup.mem_subgroupOf]
        exact ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by simp⟩)
    have hq_bij : Function.Bijective q := by
      refine ⟨?_, ?_⟩
      · rintro ⟨a⟩ ⟨b⟩ heq
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        have hmem : (⟨ψ a, ⟨a, rfl⟩⟩⁻¹ * ⟨ψ b, ⟨b, rfl⟩⟩ : G').1 ∈ H :=
          Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp (Quotient.exact heq))
        rcases hmem with ⟨c, hcM, hc_eq⟩
        have h_eq : c = a⁻¹ * b := by
          apply hψ_inj
          rw [map_mul, map_inv]
          exact hc_eq
        exact h_eq ▸ hcM
      · rintro ⟨⟨_, ⟨g, rfl⟩⟩⟩
        exact ⟨⟦g⟧, rfl⟩
    have hn_eq : Nat.card α = (H.subgroupOf G').index :=
      hn_M.trans (Nat.card_congr (Equiv.ofBijective q hq_bij))
    rw [hG_card, hn_eq]
    by_cases h_prim : IsPreprimitive H (Fin m)
    · exact primitive_card_le_bound hm G' H hA hHG' (hn_eq ▸ hm_le) h_prim
    · exact imprimitive_card_le_bound hm G' H hA h_trans h_prim
  · left
    exact intransitive_isSubsetActionType G hG ω (by omega) hm_le ψ hA h_trans

end Alternating

/-- Step 3 of Maróti (2002), Section 2, page 635: every primitive permutation group `G` that is
almost simple with alternating socle `alternatingGroup (Fin m)` (`5 ≤ m`) satisfies
`AlmostSimpleConclusion G`. -/
theorem alternatingCase : AlmostSimpleCase AlternatingSocle := by
  intro α hfin G S hgrp hG hS ⟨m, hm, ⟨eS⟩⟩
  cases nonempty_fintype α
  classical
  rcases eq_or_ne m 5 with rfl | hm5
  · exact Alternating.alternatingCase_five G hG hS eS
  · rcases eq_or_ne m 6 with rfl | hm6
    · exact Alternating.alternatingCase_six G hG hS eS
    · exact Alternating.alternatingCase_ge_seven G hG hS (by omega) eS

end Maroti
