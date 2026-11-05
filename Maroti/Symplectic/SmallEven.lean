module

public import Maroti.Symplectic.OrderBound
public import Maroti.Symplectic.PointRadicalEven

/-!
# Assembly of `symplecticCase_even_of_small` for Even-Characteristic Symplectic Groups

This file combines the point-radical minimum degree bounds from
`Maroti/Symplectic/PointRadicalEven.lean` with the order and outer-automorphism bounds from
`Maroti/Symplectic/OrderBound.lean` and the small-group hypotheses `h62`, `h44`, and `h82` to prove
`Maroti.symplecticCase_even_of_small : AlmostSimpleCase SymplecticSocleEven`.

## Main results

* The lemma `Maroti.card_outerAut_psp_even_dvd`: for `PSp(2n, 2^f)`,
  `Nat.card (OuterAut S) ∣ 2 * f`.
* The lemma `Maroti.index_ge_psp_four_four_of_ne`: every proper subgroup `H ≠ ⊤` of `PSp(4, 4)`
  has index at least `25`, given `H.index ≠ 24`.
* The lemma `Maroti.index_ge_psp_eight_two_of_not_mem`: every proper subgroup `H ≠ ⊤` of
  `PSp(8, 2)` has index at least `64`, given `¬ (56 ≤ H.index ∧ H.index ≤ 63)`.
* The theorem `Maroti.symplecticCase_even_of_small`: `AlmostSimpleCase SymplecticSocleEven`
  (Maróti, Section 2, Step 2, page 634).
-/

@[expose] public section

namespace Maroti

open CFSG.Open

/-- For `PSp(2n, 2^f)`, `Nat.card (OuterAut S)` divides `2 * f`. -/
theorem card_outerAut_psp_even_dvd {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) :
    Nat.card (OuterAut S) ∣ 2 * f := by
  have hdvd := card_outerAut_psp_dvd h
  rwa [gcd_two_two_pow_sub_one h.1.2.1, mul_one] at hdvd

/-- Every proper subgroup `H ≠ ⊤` of `PSp(4, 4)` (`n = 2, f = 2`) has index at least `25`,
given that no subgroup has index `24`. -/
theorem index_ge_psp_four_four_of_ne {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 2 2 2)
    (h44 : ∀ H : Subgroup S, H.index ≠ 24)
    {H : Subgroup S} (hH : H ≠ ⊤) :
    25 ≤ H.index := by
  have h24 : 24 ≤ H.index := index_ge_psp_four_four h hH
  have hne : H.index ≠ 24 := h44 H
  omega

/-- Every proper subgroup `H ≠ ⊤` of `PSp(8, 2)` (`n = 4, f = 1`) has index at least `64`,
given that no subgroup has index in `[56, 63]`. -/
theorem index_ge_psp_eight_two_of_not_mem {S : Type} [Group S]
    (h : StatedClassicalModel S .PSp 4 2 1)
    (h82 : ∀ H : Subgroup S, 56 ≤ H.index → H.index ≤ 63 → False)
    {H : Subgroup S} (hH : H ≠ ⊤) :
    64 ≤ H.index := by
  have h56 : 56 ≤ H.index := index_ge_psp_two h hH
  by_contra! hlt
  exact h82 H h56 (by omega)

/-- Theorem 1.1 for almost simple groups with socle `PSp(2n, 2^f)` (`SymplecticSocleEven`),
assuming the small-group index bounds for `PSp(6, 2)`, `PSp(4, 4)`, and `PSp(8, 2)`. -/
theorem symplecticCase_even_of_small
    (h62 : ∀ (S : Type) [Group S], CFSG.Open.StatedClassicalModel S .PSp 3 2 1 →
      ∀ H : Subgroup S, H ≠ ⊤ → 23 ≤ H.index)
    (h44 : ∀ (S : Type) [Group S], CFSG.Open.StatedClassicalModel S .PSp 2 2 2 →
      ∀ H : Subgroup S, H.index ≠ 24)
    (h82 : ∀ (S : Type) [Group S], CFSG.Open.StatedClassicalModel S .PSp 4 2 1 →
      ∀ H : Subgroup S, 56 ≤ H.index → H.index ≤ 63 → False) :
    AlmostSimpleCase SymplecticSocleEven := by
  intro α _ G S _ hprim hAS ⟨n, f, hModel⟩
  right; right
  obtain ⟨hp, hf, hn, hne22⟩ := hModel.1
  have hout : Nat.card (OuterAut S) ∣ 2 * f := card_outerAut_psp_even_dvd hModel
  have hc0 : 0 < 2 * f := by omega
  rcases eq_or_lt_of_le hf with rfl | hf2
  · have hn2 : n ≠ 2 := fun h => hne22 (Prod.ext h rfl)
    have hn3 : 3 ≤ n := by omega
    rcases eq_or_lt_of_le hn3 with rfl | hn4
    · exact hAS.card_le_bound_of_outerAut_dvd hc0 (h62 S hModel) hout
        (card_mul_outer_le_bound_psp_six_two hModel)
    · rcases eq_or_lt_of_le (show 4 ≤ n by omega) with rfl | hn5
      · exact hAS.card_le_bound_of_outerAut_dvd hc0
          (fun H hH => index_ge_psp_eight_two_of_not_mem hModel (h82 S hModel) hH) hout
          (card_mul_outer_le_bound_psp_eight_two hModel)
      · exact hAS.card_le_bound_of_outerAut_dvd hc0
          (fun H hH => index_ge_psp_two hModel hH) hout
          (card_mul_outer_le_bound_psp_two_of_five_le hModel (by omega))
  · by_cases h22 : n = 2 ∧ f = 2
    · rcases h22 with ⟨rfl, rfl⟩
      exact hAS.card_le_bound_of_outerAut_dvd hc0
        (fun H hH => index_ge_psp_four_four_of_ne hModel (h44 S hModel) hH) hout
        (card_mul_outer_le_bound_psp_four_four hModel)
    · exact hAS.card_le_bound_of_outerAut_dvd hc0
        (fun H hH => index_ge_psp_even_of_two_le_f hModel (by omega) hH) hout
        (card_mul_outer_le_bound_psp_even_of_two_le_f hModel (by omega) h22)

end Maroti
