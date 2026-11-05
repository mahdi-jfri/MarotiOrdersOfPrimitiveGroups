module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Bochert's theorem on the index of primitive permutation groups

This file proves Bochert's theorem (`Maroti.bochert`, Bochert, *Math. Ann.* 33 (1889), 572–583),
which states that if `H` is a primitive subgroup of `Equiv.Perm (Fin m)` that does not contain
`alternatingGroup (Fin m)`, then `((m + 1) / 2)! ≤ H.index`. It also proves the sharpened bound
`30 ≤ H.index` for `m = 8` (`Maroti.bochert_eight`).

The proof follows Dixon and Mortimer, *Permutation Groups* (Springer, 1996), Chapter 3,
Section 3.3, Theorem 3.3B, pages 80–81, and Wielandt, *Finite Permutation Groups* (Academic Press,
1964), Chapter II, Section 14, Theorem 14.2. If two permutations `g, h : Perm α` have supports
meeting in a single point `{a}`, then their commutator `g * h * g⁻¹ * h⁻¹` is the 3-cycle
`swap a (h a) * swap a (g a)` (`isThreeCycle_commutator_of_support_inter_eq_singleton`). By
Jordan's theorem (`Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`), `H`
contains no 3-cycle, so no two elements of `H` have supports intersecting in a single point.

Let `B : Finset (Fin m)` be a base of `H` (`fixingSubgroup H (B : Set (Fin m)) = ⊥`) of minimal
cardinality `b = B.card`. If `m / 2 < b`, then `Bᶜ` has size `m - b < b` and is not a base, giving
a nontrivial element `g ∈ H` fixing `Bᶜ` pointwise with some `a ∈ g.support ⊆ B`. Because
`B.erase a` has size `b - 1 < b`, there is also a nontrivial `h ∈ H` fixing `B.erase a` pointwise,
which moves `a` since `B` is a base. Then `g.support ∩ h.support = {a}`, which is impossible.
Therefore `b ≤ m / 2`, and the pointwise stabilizer of `B` in `Perm (Fin m)` has cardinality
`(m - b)!` and intersection `⊥` with `H`, giving `((m + 1) / 2)! ≤ (m - b)! ≤ H.index`.
-/

@[expose] public section

namespace Maroti

open Equiv Equiv.Perm MulAction Subgroup

open scoped Nat

variable {α : Type*}

private theorem perm_inv_apply_self (f : Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

private theorem perm_apply_inv_self (f : Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

variable [Fintype α] [DecidableEq α]

/-- If the supports of `g, h : Perm α` intersect in `{a}`, then their commutator
`g * h * g⁻¹ * h⁻¹` is a 3-cycle. -/
private theorem isThreeCycle_commutator_of_support_inter_eq_singleton
    {g h : Perm α} {a : α} (h_inter : g.support ∩ h.support = {a}) :
    IsThreeCycle (g * h * g⁻¹ * h⁻¹) := by
  have ha_inter : a ∈ g.support ∩ h.support := by
    rw [h_inter]
    exact Finset.mem_singleton_self a
  have hag : a ∈ g.support := (Finset.mem_inter.mp ha_inter).1
  have hah : a ∈ h.support := (Finset.mem_inter.mp ha_inter).2
  have hga_ne : g a ≠ a := mem_support.mp hag
  have hha_ne : h a ≠ a := mem_support.mp hah
  have not_mem_h_of_ne : ∀ {x : α}, x ≠ a → x ∈ g.support → x ∉ h.support := by
    intro x hxa hxg hxh
    apply hxa
    have : x ∈ g.support ∩ h.support := Finset.mem_inter.mpr ⟨hxg, hxh⟩
    rwa [h_inter, Finset.mem_singleton] at this
  have not_mem_g_of_ne : ∀ {x : α}, x ≠ a → x ∈ h.support → x ∉ g.support := by
    intro x hxa hxh hxg
    exact not_mem_h_of_ne hxa hxg hxh
  have hga_not_h : g a ∉ h.support :=
    not_mem_h_of_ne hga_ne (apply_mem_support.mpr hag)
  have hha_not_g : h a ∉ g.support :=
    not_mem_g_of_ne hha_ne (apply_mem_support.mpr hah)
  have hga_ne_ha : g a ≠ h a := by
    intro heq
    apply hha_not_g
    rw [← heq]
    exact apply_mem_support.mpr hag
  have h_eq : g * h * g⁻¹ * h⁻¹ = swap a (h a) * swap a (g a) := by
    ext x
    simp only [Perm.mul_apply]
    by_cases hxa : x = a
    · rw [hxa]
      have hhinv_mem : h⁻¹ a ∈ h.support := by
        rw [← support_inv]
        exact apply_mem_support.mpr (by rwa [support_inv])
      have hhinv_ne : h⁻¹ a ≠ a := by
        intro heq
        apply hha_ne
        simpa [perm_apply_inv_self] using congrArg h heq.symm
      have hginv_hinv : g⁻¹ (h⁻¹ a) = h⁻¹ a :=
        notMem_support.mp (by rw [support_inv]; exact not_mem_g_of_ne hhinv_ne hhinv_mem)
      rw [hginv_hinv, perm_apply_inv_self, swap_apply_left,
        swap_apply_of_ne_of_ne hga_ne hga_ne_ha]
    · by_cases hx_ha : x = h a
      · rw [hx_ha]
        have hginv_mem : g⁻¹ a ∈ g.support := by
          rw [← support_inv]
          exact apply_mem_support.mpr (by rwa [support_inv])
        have hginv_ne : g⁻¹ a ≠ a := by
          intro heq
          apply hga_ne
          simpa [perm_apply_inv_self] using congrArg g heq.symm
        have hh_ginv : h (g⁻¹ a) = g⁻¹ a :=
          notMem_support.mp (not_mem_h_of_ne hginv_ne hginv_mem)
        rw [perm_inv_apply_self, hh_ginv, perm_apply_inv_self,
          swap_apply_of_ne_of_ne hha_ne hga_ne_ha.symm, swap_apply_right]
      · by_cases hx_ga : x = g a
        · rw [hx_ga]
          have hhinv_ga : h⁻¹ (g a) = g a := by
            apply notMem_support.mp
            rwa [support_inv]
          rw [hhinv_ga, perm_inv_apply_self, notMem_support.mp hha_not_g,
            swap_apply_right, swap_apply_left]
        · rw [swap_apply_of_ne_of_ne hxa hx_ga, swap_apply_of_ne_of_ne hxa hx_ha]
          by_cases hxh : x ∈ h.support
          · have hhinv_mem : h⁻¹ x ∈ h.support := by
              rw [← support_inv]
              exact apply_mem_support.mpr (by rwa [support_inv])
            have hhinv_ne : h⁻¹ x ≠ a := by
              intro heq
              apply hx_ha
              simpa [perm_apply_inv_self] using congrArg h heq
            have hginv_hinv : g⁻¹ (h⁻¹ x) = h⁻¹ x :=
              notMem_support.mp (by rw [support_inv]; exact not_mem_g_of_ne hhinv_ne hhinv_mem)
            have hg_x : g x = x := notMem_support.mp (not_mem_g_of_ne hxa hxh)
            rw [hginv_hinv, perm_apply_inv_self, hg_x]
          · have hhinv_x : h⁻¹ x = x := by
              apply notMem_support.mp
              rwa [support_inv]
            rw [hhinv_x]
            by_cases hxg : x ∈ g.support
            · have hginv_mem : g⁻¹ x ∈ g.support := by
                rw [← support_inv]
                exact apply_mem_support.mpr (by rwa [support_inv])
              have hginv_ne : g⁻¹ x ≠ a := by
                intro heq
                apply hx_ga
                simpa [perm_apply_inv_self] using congrArg g heq
              have hh_ginv : h (g⁻¹ x) = g⁻¹ x :=
                notMem_support.mp (not_mem_h_of_ne hginv_ne hginv_mem)
              rw [hh_ginv, perm_apply_inv_self]
            · have hginv_x : g⁻¹ x = x := by
                apply notMem_support.mp
                rwa [support_inv]
              rw [hginv_x, notMem_support.mp hxh, notMem_support.mp hxg]
  rw [h_eq]
  exact isThreeCycle_swap_mul_swap_same hha_ne.symm hga_ne.symm hga_ne_ha.symm

/-- For any subset `B : Finset α`, the subgroup `fixingSubgroup (Perm α) (B : Set α)` has
cardinality `(Fintype.card α - B.card)!`. -/
theorem nat_card_fixingSubgroup_perm (B : Finset α) :
    Nat.card (fixingSubgroup (Perm α) (B : Set α)) = (Fintype.card α - B.card)! := by
  let p : α → Prop := fun x => x ∈ Bᶜ
  let e : Perm (Subtype p) ≃ fixingSubgroup (Perm α) (B : Set α) :=
    { toFun := fun g => ⟨ofSubtype g, by
        rw [mem_fixingSubgroup_iff]
        intro y hy
        have hy' : ¬ p y := by
          simp only [p, Finset.mem_compl, not_not]
          exact Finset.mem_coe.mp hy
        exact ofSubtype_apply_of_not_mem g hy'⟩
      invFun := fun g => subtypePerm g.1 (by
        intro x
        simp only [Finset.mem_compl]
        constructor
        · intro hgx hx
          have := (mem_fixingSubgroup_iff (Perm α)).mp g.2 x (Finset.mem_coe.mpr hx)
          rw [Perm.smul_def] at this
          rw [this] at hgx
          exact hgx hx
        · intro hx hgx
          have := (mem_fixingSubgroup_iff (Perm α)).mp (Subgroup.inv_mem _ g.2)
            (g.1 x) (Finset.mem_coe.mpr hgx)
          rw [Perm.smul_def, perm_inv_apply_self] at this
          rw [this] at hx
          exact hx hgx)
      left_inv := fun g => by
        ext ⟨x, hx⟩
        simp
      right_inv := fun g => by
        ext x
        by_cases hx : p x
        · simp [ofSubtype_apply_of_mem _ hx]
        · rw [ofSubtype_apply_of_not_mem _ hx]
          have hxB : x ∈ (B : Set α) := by
            simp only [p, Finset.mem_compl, not_not] at hx
            exact Finset.mem_coe.mpr hx
          exact ((mem_fixingSubgroup_iff (Perm α)).mp g.2 x hxB).symm }
  rw [← Nat.card_congr e, Nat.card_perm, Nat.card_eq_fintype_card]
  have hcard : Fintype.card (Subtype p) = Fintype.card α - B.card := by
    rw [← Finset.card_compl]
    exact Fintype.card_coe Bᶜ
  rw [hcard]

/-- If `fixingSubgroup H (B : Set α) = ⊥`, then `(Fintype.card α - B.card)! ≤ H.index`. -/
private theorem factorial_card_sub_le_index_of_fixingSubgroup_eq_bot
    {H : Subgroup (Perm α)} {B : Finset α} (hB : fixingSubgroup H (B : Set α) = ⊥) :
    (Fintype.card α - B.card)! ≤ H.index := by
  set K := fixingSubgroup (Perm α) (B : Set α)
  rw [← nat_card_fixingSubgroup_perm B]
  let f : K → Perm α ⧸ H := fun k => (k.1 : Perm α)
  have hf : Function.Injective f := by
    rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ heq
    rw [Subtype.mk.injEq]
    have hmem : k₁⁻¹ * k₂ ∈ H := QuotientGroup.leftRel_apply.mp (Quotient.exact heq)
    have hfix : (⟨k₁⁻¹ * k₂, hmem⟩ : H) ∈ fixingSubgroup H (B : Set α) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      have hk : k₁⁻¹ * k₂ ∈ K := K.mul_mem (K.inv_mem hk₁) hk₂
      exact (mem_fixingSubgroup_iff (Perm α)).mp hk y hy
    rw [hB, Subgroup.mem_bot, Subtype.ext_iff] at hfix
    exact inv_mul_eq_one.mp hfix
  exact Nat.card_le_card_of_injective f hf

/-- Bochert's theorem (Bochert, *Math. Ann.* 33 (1889), 572–583, Dixon and Mortimer,
*Permutation Groups*, Chapter 3, Theorem 3.3B, and Wielandt, *Finite Permutation Groups*,
Chapter II, Theorem 14.2): if `H` is a primitive subgroup of `Equiv.Perm (Fin m)` that does not
contain `alternatingGroup (Fin m)`, then `((m + 1) / 2)! ≤ H.index`. -/
theorem bochert {m : ℕ} (H : Subgroup (Perm (Fin m)))
    (hH : IsPreprimitive H (Fin m)) (hA : ¬ alternatingGroup (Fin m) ≤ H) :
    ((m + 1) / 2)! ≤ H.index := by
  have hex : ∃ n : ℕ, ∃ B : Finset (Fin m), B.card = n ∧
      fixingSubgroup H (B : Set (Fin m)) = ⊥ := by
    refine ⟨m, Finset.univ, Finset.card_fin m, ?_⟩
    rw [eq_bot_iff]
    rintro ⟨g, hg⟩ hg_fix
    rw [Subgroup.mem_bot, Subtype.ext_iff]
    ext x
    have hx := (mem_fixingSubgroup_iff H).mp hg_fix x (Finset.mem_coe.mpr (Finset.mem_univ x))
    exact congrArg Fin.val hx
  classical
  set b := Nat.find hex
  obtain ⟨B, hB_card, hB_bot⟩ := Nat.find_spec hex
  have hb_min : ∀ C : Finset (Fin m), C.card < b → fixingSubgroup H (C : Set (Fin m)) ≠ ⊥ := by
    intro C hC hC_bot
    exact Nat.find_min hex hC ⟨C, rfl, hC_bot⟩
  have hb_le : b ≤ m / 2 := by
    by_contra hlt
    have hlt' : m - b < b := by omega
    have hBc_card : Bᶜ.card < b := by
      rw [Finset.card_compl, Fintype.card_fin, hB_card]
      exact hlt'
    have hBc_ne : fixingSubgroup H ((Bᶜ : Finset (Fin m)) : Set (Fin m)) ≠ ⊥ :=
      hb_min Bᶜ hBc_card
    obtain ⟨⟨⟨g, hgH⟩, hg_fix⟩, hg_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBc_ne
    have hg_ne' : g ≠ 1 := by
      rintro rfl
      exact hg_ne rfl
    have hg_supp_nonempty : g.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (support_eq_empty_iff.not.mpr hg_ne')
    obtain ⟨a, hag⟩ := hg_supp_nonempty
    have hg_supp_le : g.support ⊆ B := by
      intro x hx
      by_contra hxB
      have hxBc : x ∈ ((Bᶜ : Finset (Fin m)) : Set (Fin m)) := by
        simp [hxB]
      have hfix := (mem_fixingSubgroup_iff H).mp hg_fix x hxBc
      exact (mem_support.mp hx) hfix
    have haB : a ∈ B := hg_supp_le hag
    have hBe_card : (B.erase a).card < b := by
      rw [Finset.card_erase_of_mem haB, hB_card]
      exact Nat.sub_lt (by omega) (by decide)
    have hBe_ne : fixingSubgroup H ((B.erase a : Finset (Fin m)) : Set (Fin m)) ≠ ⊥ :=
      hb_min (B.erase a) hBe_card
    obtain ⟨⟨⟨h, hhH⟩, hh_fix⟩, hh_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBe_ne
    have hh_not_fix_a : h a ≠ a := by
      intro hha
      have hh_mem_B : (⟨h, hhH⟩ : H) ∈ fixingSubgroup H (B : Set (Fin m)) := by
        rw [mem_fixingSubgroup_iff]
        intro y hy
        by_cases hya : y = a
        · rw [hya]
          exact hha
        · have hyBe : y ∈ ((B.erase a : Finset (Fin m)) : Set (Fin m)) :=
            Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hya, hy⟩)
          exact (mem_fixingSubgroup_iff H).mp hh_fix y hyBe
      rw [hB_bot, Subgroup.mem_bot] at hh_mem_B
      exact hh_ne (Subtype.ext hh_mem_B)
    have hah : a ∈ h.support := mem_support.mpr hh_not_fix_a
    have h_inter : g.support ∩ h.support = {a} := by
      apply Finset.Subset.antisymm
      · intro x hx
        rw [Finset.mem_singleton]
        by_contra hxa
        have hxg : x ∈ g.support := (Finset.mem_inter.mp hx).1
        have hxh : x ∈ h.support := (Finset.mem_inter.mp hx).2
        have hxBe : x ∈ ((B.erase a : Finset (Fin m)) : Set (Fin m)) :=
          Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxa, hg_supp_le hxg⟩)
        exact (mem_support.mp hxh) ((mem_fixingSubgroup_iff H).mp hh_fix x hxBe)
      · rw [Finset.singleton_subset_iff, Finset.mem_inter]
        exact ⟨hag, hah⟩
    have h3 : IsThreeCycle (g * h * g⁻¹ * h⁻¹) :=
      isThreeCycle_commutator_of_support_inter_eq_singleton h_inter
    have hcomm_mem : g * h * g⁻¹ * h⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hgH hhH) (H.inv_mem hgH)) (H.inv_mem hhH)
    exact hA (alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hH h3 hcomm_mem)
  have h_sub : (m + 1) / 2 ≤ Fintype.card (Fin m) - B.card := by
    rw [Fintype.card_fin, hB_card]
    omega
  exact (Nat.factorial_le h_sub).trans (factorial_card_sub_le_index_of_fixingSubgroup_eq_bot hB_bot)

/-- For `H : Subgroup (Perm (Fin 8))` and `C : Finset (Fin 8)` with `C.card = 3`,
`(fixingSubgroup H (C : Set (Fin 8))).index ≤ 336`. -/
private theorem index_fixingSubgroup_le_336 (H : Subgroup (Perm (Fin 8)))
    {C : Finset (Fin 8)} (hC : C.card = 3) :
    (fixingSubgroup H (C : Set (Fin 8))).index ≤ 336 := by
  set H_C := fixingSubgroup H (C : Set (Fin 8))
  set K_C := fixingSubgroup (Perm (Fin 8)) (C : Set (Fin 8))
  have hKC_card : Nat.card K_C = 120 := by
    rw [nat_card_fixingSubgroup_perm C, Fintype.card_fin, hC]
    decide
  have hKC_index : K_C.index = 336 := by
    have hmul := Subgroup.card_mul_index K_C
    rw [hKC_card, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hmul
    have h8 : 8 ! = 40320 := by decide
    omega
  rw [← hKC_index]
  let f : H ⧸ H_C → Perm (Fin 8) ⧸ K_C :=
    Quotient.lift (fun h : H => ((h.1 : Perm (Fin 8)) : Perm (Fin 8) ⧸ K_C)) (by
      intro a b hab
      apply Quotient.sound
      have hab' : a⁻¹ * b ∈ H_C := QuotientGroup.leftRel_apply.mp hab
      exact QuotientGroup.leftRel_apply.mpr
        ((mem_fixingSubgroup_iff (Perm (Fin 8))).mpr
          ((mem_fixingSubgroup_iff H).mp hab')))
  have hf : Function.Injective f := by
    rintro ⟨a⟩ ⟨b⟩ heq
    apply Quotient.sound
    have hab : a.1⁻¹ * b.1 ∈ K_C := QuotientGroup.leftRel_apply.mp (Quotient.exact heq)
    exact QuotientGroup.leftRel_apply.mpr
      ((mem_fixingSubgroup_iff H).mpr
        ((mem_fixingSubgroup_iff (Perm (Fin 8))).mp hab))
  exact Nat.card_le_card_of_injective f hf

omit [Fintype α] [DecidableEq α] in
/-- If `g : Perm α` fixes `C : Finset α` pointwise and `x ∉ C`, then `g x ∉ C`. -/
private theorem apply_notMem_of_mem_fixingSubgroup {H : Subgroup (Perm α)} {C : Finset α}
    (h : fixingSubgroup H (C : Set α)) {x : α} (hx : x ∉ C) :
    h.1.1 x ∉ C := by
  intro hmem
  have hfix := (mem_fixingSubgroup_iff H).mp (Subgroup.inv_mem _ h.2) (h.1.1 x)
    (Finset.mem_coe.mpr hmem)
  change h.1.1⁻¹ (h.1.1 x) = h.1.1 x at hfix
  rw [perm_inv_apply_self] at hfix
  rw [← hfix] at hmem
  exact hx hmem

omit [Fintype α] in
/-- Evaluation at `x` on `fixingSubgroup H (C : Set α)` when `fixingSubgroup H (insert x C) = ⊥`
is injective. -/
private theorem eval_injective_of_fixingSubgroup_insert_eq_bot
    {H : Subgroup (Perm α)} {C : Finset α} {x : α}
    (hB : fixingSubgroup H ((insert x C : Finset α) : Set α) = ⊥) :
    Function.Injective (fun h : fixingSubgroup H (C : Set α) => h.1.1 x) := by
  intro h₁ h₂ heq
  change h₁.1.1 x = h₂.1.1 x at heq
  have hdiff_mem : h₁.1⁻¹ * h₂.1 ∈ fixingSubgroup H ((insert x C : Finset α) : Set α) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyC
    · change h₁.1.1⁻¹ (h₂.1.1 y) = y
      rw [← heq, perm_inv_apply_self]
    · exact (mem_fixingSubgroup_iff H).mp
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁.2) h₂.2) y (Finset.mem_coe.mpr hyC)
  rw [hB, Subgroup.mem_bot] at hdiff_mem
  exact Subtype.ext (inv_mul_eq_one.mp hdiff_mem)

/-- Suppose `1344 < Nat.card H`, `B : Finset (Fin 8)` has `B.card = 4` and
`fixingSubgroup H (B : Set (Fin 8)) = ⊥`, and `a ∈ B`. Then for every `b ∈ Bᶜ`, the fixing
subgroup `fixingSubgroup H (insert b (B.erase a))` is trivial, and there exists an element
`g ∈ fixingSubgroup H (B.erase a)` with `g a = b` and `g b ∈ Bᶜ.erase b`. -/
private theorem exists_elem_and_fixingSubgroup_insert_erase_eq_bot
    {H : Subgroup (Perm (Fin 8))} (hH_card : 1344 < Nat.card H)
    {B : Finset (Fin 8)} (hB_card : B.card = 4)
    (hB : fixingSubgroup H (B : Set (Fin 8)) = ⊥)
    {a : Fin 8} (ha : a ∈ B) {b : Fin 8} (hb : b ∈ Bᶜ) :
    fixingSubgroup H ((insert b (B.erase a) : Finset (Fin 8)) : Set (Fin 8)) = ⊥ ∧
    ∃ g : fixingSubgroup H ((B.erase a : Finset (Fin 8)) : Set (Fin 8)),
      g.1.1 a = b ∧ g.1.1 b ∈ Bᶜ.erase b := by
  set C := B.erase a
  set H_C := fixingSubgroup H (C : Set (Fin 8))
  have hC_card : C.card = 3 := by rw [Finset.card_erase_of_mem ha, hB_card]
  have ha_not_C : a ∉ C := Finset.notMem_erase a B
  have hins_C : insert a C = B := Finset.insert_erase ha
  have hB' : fixingSubgroup H ((insert a C : Finset (Fin 8)) : Set (Fin 8)) = ⊥ := by
    rwa [hins_C]
  have hev_inj : Function.Injective (fun h : H_C => h.1.1 a) :=
    eval_injective_of_fixingSubgroup_insert_eq_bot hB'
  let ev : H_C → (Cᶜ : Finset (Fin 8)) := fun h =>
    ⟨h.1.1 a, Finset.mem_compl.mpr (apply_notMem_of_mem_fixingSubgroup h ha_not_C)⟩
  have hev : Function.Injective ev := fun h₁ h₂ heq => hev_inj (Subtype.mk.inj heq)
  have hCc_card : Nat.card (Cᶜ : Finset (Fin 8)) = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hC_card]
  have hHC_le : Nat.card H_C ≤ 5 := by
    rw [← hCc_card]
    exact Nat.card_le_card_of_injective ev hev
  have hHC_idx : H_C.index ≤ 336 := index_fixingSubgroup_le_336 H hC_card
  have hHC_mul : Nat.card H_C * H_C.index = Nat.card H := Subgroup.card_mul_index H_C
  have hHC_eq : Nat.card H_C = 5 := by
    by_contra hne
    have hle4 : Nat.card H_C ≤ 4 := by omega
    have hmul_le : Nat.card H_C * H_C.index ≤ 4 * 336 := Nat.mul_le_mul hle4 hHC_idx
    omega
  set D := insert b C
  have hb_not_B : b ∉ B := Finset.mem_compl.mp hb
  have hb_not_C : b ∉ C := fun hmem => hb_not_B (Finset.mem_of_mem_erase hmem)
  have hba : b ≠ a := fun heq => hb_not_B (heq ▸ ha)
  have hD_card : D.card = 4 := by rw [Finset.card_insert_of_notMem hb_not_C, hC_card]
  set S := fixingSubgroup H (D : Set (Fin 8))
  have ha_not_D : a ∉ D := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hba.symm, ha_not_C⟩
  have hC_sub_D : (C : Set (Fin 8)) ⊆ (D : Set (Fin 8)) :=
    Finset.coe_subset.mpr (Finset.subset_insert b C)
  let ι : S →* H_C :=
    { toFun := fun s => ⟨s.1, (mem_fixingSubgroup_iff H).mpr fun y hy =>
        (mem_fixingSubgroup_iff H).mp s.2 y (hC_sub_D hy)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι_inj : Function.Injective ι := fun s₁ s₂ heq => Subtype.ext (Subtype.mk.inj heq)
  let evS : S → (Dᶜ : Finset (Fin 8)) := fun s =>
    ⟨s.1.1 a, Finset.mem_compl.mpr (apply_notMem_of_mem_fixingSubgroup s ha_not_D)⟩
  have hevS_inj : Function.Injective evS :=
    fun s₁ s₂ heq => hι_inj (hev_inj (Subtype.mk.inj heq))
  have hDc_card : Nat.card (Dᶜ : Finset (Fin 8)) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hD_card]
  have hS_le : Nat.card S ≤ 4 := by
    rw [← hDc_card]
    exact Nat.card_le_card_of_injective evS hevS_inj
  have hS_dvd : Nat.card S ∣ 5 := by
    rw [← hHC_eq]
    exact Subgroup.card_dvd_of_injective ι hι_inj
  have hS_card_one : Nat.card S = 1 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by decide) _ hS_dvd) with h1 | h5
    · exact h1
    · omega
  have hS_bot : S = ⊥ := (Subgroup.card_eq_one.mp hS_card_one)
  refine ⟨hS_bot, ?_⟩
  have hev_surj : Function.Surjective ev := by
    let : Fintype H_C := Fintype.ofFinite H_C
    refine ((Fintype.bijective_iff_injective_and_card ev).mpr ⟨hev, ?_⟩).2
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hHC_eq, hCc_card]
  obtain ⟨g, hg⟩ := hev_surj ⟨b, Finset.mem_compl.mpr hb_not_C⟩
  have hga : g.1.1 a = b := Subtype.mk.inj hg
  refine ⟨g, hga, ?_⟩
  rw [Finset.mem_erase, Finset.mem_compl]
  refine ⟨?_, ?_⟩
  · intro hgb
    have hg_mem_S : g.1 ∈ S := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hyC
      · exact hgb
      · exact (mem_fixingSubgroup_iff H).mp g.2 y (Finset.mem_coe.mpr hyC)
    rw [hS_bot, Subgroup.mem_bot] at hg_mem_S
    have h1a : g.1.1 a = a := by
      rw [hg_mem_S]
      rfl
    exact hba (hga.symm.trans h1a)
  · intro hgb_B
    rcases Finset.mem_insert.mp (hins_C ▸ hgb_B) with hgb_a | hgb_C
    · have hg2_a : (g * g).1.1 a = a := by
        change g.1.1 (g.1.1 a) = a
        rw [hga, hgb_a]
      have hg2_eq_one : g ^ 2 = 1 := by
        rw [sq]
        exact hev_inj (hg2_a.trans rfl)
      have hg5_eq_one : g ^ 5 = 1 := by
        rw [← hHC_eq]
        exact pow_card_eq_one'
      have hg4_eq_one : g ^ 4 = 1 := by
        rw [show 4 = 2 * 2 from rfl, pow_mul, hg2_eq_one, one_pow]
      have hg_eq_one : g = 1 := by
        calc g = g ^ 4 * g := by rw [hg4_eq_one, one_mul]
          _ = g ^ 5 := (pow_succ g 4).symm
          _ = 1 := hg5_eq_one
      have h1a : g.1.1 a = a := by
        rw [hg_eq_one]
        rfl
      exact hba (hga.symm.trans h1a)
    · exact apply_notMem_of_mem_fixingSubgroup g hb_not_C hgb_C

/-- For `m = 8`, any primitive subgroup `H ≤ Perm (Fin 8)` not containing `alternatingGroup (Fin 8)`
has index at least `30` (corresponding to `AGL(3, 2)` of order `1344`). -/
theorem bochert_eight (H : Subgroup (Perm (Fin 8)))
    (hH : IsPreprimitive H (Fin 8)) (hA : ¬ alternatingGroup (Fin 8) ≤ H) :
    30 ≤ H.index := by
  have hex : ∃ n : ℕ, ∃ B : Finset (Fin 8), B.card = n ∧
      fixingSubgroup H (B : Set (Fin 8)) = ⊥ := by
    refine ⟨8, Finset.univ, Finset.card_fin 8, ?_⟩
    rw [eq_bot_iff]
    rintro ⟨g, hg⟩ hg_fix
    rw [Subgroup.mem_bot, Subtype.ext_iff]
    ext x
    have hx := (mem_fixingSubgroup_iff H).mp hg_fix x (Finset.mem_coe.mpr (Finset.mem_univ x))
    exact congrArg Fin.val hx
  classical
  set b := Nat.find hex
  obtain ⟨B, hB_card, hB_bot⟩ := Nat.find_spec hex
  change B.card = b at hB_card
  have hb_min : ∀ C : Finset (Fin 8), C.card < b → fixingSubgroup H (C : Set (Fin 8)) ≠ ⊥ := by
    intro C hC hC_bot
    exact Nat.find_min hex hC ⟨C, rfl, hC_bot⟩
  have hBc_bot : fixingSubgroup H ((Bᶜ : Finset (Fin 8)) : Set (Fin 8)) = ⊥ := by
    by_contra hBc_ne
    obtain ⟨⟨⟨g, hgH⟩, hg_fix⟩, hg_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBc_ne
    have hg_ne' : g ≠ 1 := by rintro rfl; exact hg_ne rfl
    obtain ⟨a, hag⟩ :=
      Finset.nonempty_iff_ne_empty.mpr (support_eq_empty_iff.not.mpr hg_ne')
    have hg_supp_le : g.support ⊆ B := by
      intro x hx
      by_contra hxB
      have hxBc : x ∈ ((Bᶜ : Finset (Fin 8)) : Set (Fin 8)) := by simp [hxB]
      exact (mem_support.mp hx) ((mem_fixingSubgroup_iff H).mp hg_fix x hxBc)
    have haB : a ∈ B := hg_supp_le hag
    have hBe_card : (B.erase a).card < b := by
      rw [Finset.card_erase_of_mem haB, hB_card]
      exact Nat.sub_lt (by rw [← hB_card]; exact Finset.card_pos.mpr ⟨a, haB⟩) (by decide)
    obtain ⟨⟨⟨h, hhH⟩, hh_fix⟩, hh_ne⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (hb_min (B.erase a) hBe_card)
    have hh_not_fix_a : h a ≠ a := by
      intro hha
      have hh_mem_B : (⟨h, hhH⟩ : H) ∈ fixingSubgroup H (B : Set (Fin 8)) := by
        rw [mem_fixingSubgroup_iff]
        intro y hy
        by_cases hya : y = a
        · rw [hya]; exact hha
        · exact (mem_fixingSubgroup_iff H).mp hh_fix y
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hya, hy⟩))
      rw [hB_bot, Subgroup.mem_bot] at hh_mem_B
      exact hh_ne (Subtype.ext hh_mem_B)
    have h_inter : g.support ∩ h.support = {a} := by
      apply Finset.Subset.antisymm
      · intro x hx
        rw [Finset.mem_singleton]
        by_contra hxa
        exact (mem_support.mp (Finset.mem_inter.mp hx).2)
          ((mem_fixingSubgroup_iff H).mp hh_fix x
            (Finset.mem_coe.mpr
              (Finset.mem_erase.mpr ⟨hxa, hg_supp_le (Finset.mem_inter.mp hx).1⟩)))
      · rw [Finset.singleton_subset_iff, Finset.mem_inter]
        exact ⟨hag, mem_support.mpr hh_not_fix_a⟩
    exact hA (alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hH
      (isThreeCycle_commutator_of_support_inter_eq_singleton h_inter)
      (H.mul_mem (H.mul_mem (H.mul_mem hgH hhH) (H.inv_mem hgH)) (H.inv_mem hhH)))
  have hb_le : b ≤ 4 := by
    by_contra hlt
    have hBc_card : Bᶜ.card < b := by
      rw [Finset.card_compl, Fintype.card_fin, hB_card]
      omega
    exact hb_min Bᶜ hBc_card hBc_bot
  by_cases hb4 : B.card = 4
  · by_contra hidx_lt
    have hH_card : 1344 < Nat.card H := by
      by_contra hle
      have hmul := Subgroup.card_mul_index H
      rw [Nat.card_perm, Nat.card_fin] at hmul
      have h8 : 8 ! = 40320 := by decide
      have hprod_le : Nat.card H * H.index ≤ 1344 * 29 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have hBc_card : Bᶜ.card = 4 := by
      rw [Finset.card_compl, Fintype.card_fin, hb4]
    obtain ⟨a₁, ha₁⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
    obtain ⟨b₁, hb₁⟩ := Finset.card_pos.mp (by omega : 0 < Bᶜ.card)
    obtain ⟨_, g₀, hg₀_a₁, hg₀_b₁⟩ :=
      exists_elem_and_fixingSubgroup_insert_erase_eq_bot hH_card hb4 hB_bot ha₁ hb₁
    have ha₁_Bcc : a₁ ∈ Bᶜᶜ := by rwa [compl_compl]
    obtain ⟨_, k₀, hk₀_b₁, hk₀_a₁⟩ :=
      exists_elem_and_fixingSubgroup_insert_erase_eq_bot hH_card hBc_card hBc_bot hb₁ ha₁_Bcc
    rw [compl_compl] at hk₀_a₁
    set b₂ := g₀.1.1 b₁
    set a₂ := k₀.1.1 a₁
    have hb₂_ne_b₁ : b₂ ≠ b₁ := (Finset.mem_erase.mp hg₀_b₁).1
    have hb₂_Bc : b₂ ∈ Bᶜ := (Finset.mem_erase.mp hg₀_b₁).2
    have ha₂_ne_a₁ : a₂ ≠ a₁ := (Finset.mem_erase.mp hk₀_a₁).1
    have ha₂_B : a₂ ∈ B := (Finset.mem_erase.mp hk₀_a₁).2
    have hBc_erase_card : 1 < ((Bᶜ.erase b₁).erase b₂).card := by
      rw [Finset.card_erase_of_mem hg₀_b₁, Finset.card_erase_of_mem hb₁, hBc_card]
      decide
    obtain ⟨b₃, hb₃, b₄, hb₄, hb₃₄⟩ := Finset.one_lt_card.mp hBc_erase_card
    have hb₃_ne_b₂ : b₃ ≠ b₂ := (Finset.mem_erase.mp hb₃).1
    have hb₃_ne_b₁ : b₃ ≠ b₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hb₃)).1
    have hb₃_Bc : b₃ ∈ Bᶜ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb₃)
    have hb₄_ne_b₂ : b₄ ≠ b₂ := (Finset.mem_erase.mp hb₄).1
    have hb₄_ne_b₁ : b₄ ≠ b₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hb₄)).1
    have hb₄_Bc : b₄ ∈ Bᶜ := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb₄)
    obtain ⟨hD_bot, _⟩ :=
      exists_elem_and_fixingSubgroup_insert_erase_eq_bot hH_card hb4 hB_bot ha₂_B hb₃_Bc
    set D := insert b₃ (B.erase a₂)
    have hb₃_not_B : b₃ ∉ B := Finset.mem_compl.mp hb₃_Bc
    have hb₃_not_Be : b₃ ∉ B.erase a₂ := fun h => hb₃_not_B (Finset.mem_of_mem_erase h)
    have hD_card : D.card = 4 := by
      rw [Finset.card_insert_of_notMem hb₃_not_Be, Finset.card_erase_of_mem ha₂_B, hb4]
    have ha₁_D : a₁ ∈ D :=
      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ha₂_ne_a₁.symm, ha₁⟩)
    have hb₄_Dc : b₄ ∈ Dᶜ := by
      rw [Finset.mem_compl, Finset.mem_insert, not_or]
      exact ⟨hb₃₄.symm, fun h => Finset.mem_compl.mp hb₄_Bc (Finset.mem_of_mem_erase h)⟩
    obtain ⟨hE_bot, _⟩ :=
      exists_elem_and_fixingSubgroup_insert_erase_eq_bot hH_card hD_card hD_bot ha₁_D hb₄_Dc
    set E := insert b₄ (D.erase a₁)
    set c : H := g₀.1 * k₀.1 * g₀.1⁻¹ * k₀.1⁻¹
    have hc_E : c ∈ fixingSubgroup H (E : Set (Fin 8)) := by
      rw [mem_fixingSubgroup_iff]
      intro z hz
      have hzE : z ∈ E := Finset.mem_coe.mp hz
      have fix_Bc : ∀ y ∈ (Bᶜ.erase b₁).erase b₂, c.1 y = y := by
        intro y hy
        have hy_ne_b₂ : y ≠ b₂ := (Finset.mem_erase.mp hy).1
        have hy_Bce : y ∈ Bᶜ.erase b₁ := (Finset.mem_erase.mp hy).2
        have hy_ne_b₁ : y ≠ b₁ := (Finset.mem_erase.mp hy_Bce).1
        have hy_Bc : y ∈ Bᶜ := (Finset.mem_erase.mp hy_Bce).2
        have hk₀_inv_y : k₀.1.1⁻¹ y = y :=
          (mem_fixingSubgroup_iff H).mp (Subgroup.inv_mem _ k₀.2) y (Finset.mem_coe.mpr hy_Bce)
        have hg₀_inv_y_Bce : g₀.1.1⁻¹ y ∈ Bᶜ.erase b₁ := by
          rw [Finset.mem_erase, Finset.mem_compl]
          refine ⟨?_, ?_⟩
          · intro heq
            apply hy_ne_b₂
            simpa [b₂, perm_apply_inv_self] using congrArg g₀.1.1 heq
          · intro hmemB
            by_cases heq : g₀.1.1⁻¹ y = a₁
            · apply hy_ne_b₁
              simpa [hg₀_a₁, perm_apply_inv_self] using congrArg g₀.1.1 heq
            · have hmemBe : g₀.1.1⁻¹ y ∈ B.erase a₁ := Finset.mem_erase.mpr ⟨heq, hmemB⟩
              have hfix := (mem_fixingSubgroup_iff H).mp g₀.2 (g₀.1.1⁻¹ y)
                (Finset.mem_coe.mpr hmemBe)
              change g₀.1.1 (g₀.1.1⁻¹ y) = g₀.1.1⁻¹ y at hfix
              rw [perm_apply_inv_self] at hfix
              rw [← hfix] at hmemBe
              exact Finset.mem_compl.mp hy_Bc (Finset.mem_of_mem_erase hmemBe)
        have hk₀_ginv : k₀.1.1 (g₀.1.1⁻¹ y) = g₀.1.1⁻¹ y :=
          (mem_fixingSubgroup_iff H).mp k₀.2 (g₀.1.1⁻¹ y) (Finset.mem_coe.mpr hg₀_inv_y_Bce)
        change g₀.1.1 (k₀.1.1 (g₀.1.1⁻¹ (k₀.1.1⁻¹ y))) = y
        rw [hk₀_inv_y, hk₀_ginv, perm_apply_inv_self]
      rcases Finset.mem_insert.mp hzE with rfl | hzDe
      · exact fix_Bc z hb₄
      · have hz_ne_a₁ : z ≠ a₁ := (Finset.mem_erase.mp hzDe).1
        rcases Finset.mem_insert.mp (Finset.mem_erase.mp hzDe).2 with rfl | hzBe
        · exact fix_Bc z hb₃
        · have hz_ne_a₂ : z ≠ a₂ := (Finset.mem_erase.mp hzBe).1
          have hz_B : z ∈ B := (Finset.mem_erase.mp hzBe).2
          have hz_Be₁ : z ∈ B.erase a₁ := Finset.mem_erase.mpr ⟨hz_ne_a₁, hz_B⟩
          have hk₀_inv_z_Be₁ : k₀.1.1⁻¹ z ∈ B.erase a₁ := by
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro heq
              apply hz_ne_a₂
              simpa [a₂, perm_apply_inv_self] using congrArg k₀.1.1 heq
            · by_contra hnotB
              have hmemBc : k₀.1.1⁻¹ z ∈ Bᶜ := Finset.mem_compl.mpr hnotB
              by_cases heq : k₀.1.1⁻¹ z = b₁
              · apply hz_ne_a₁
                simpa [hk₀_b₁, perm_apply_inv_self] using congrArg k₀.1.1 heq
              · have hmemBce : k₀.1.1⁻¹ z ∈ Bᶜ.erase b₁ := Finset.mem_erase.mpr ⟨heq, hmemBc⟩
                have hfix := (mem_fixingSubgroup_iff H).mp k₀.2 (k₀.1.1⁻¹ z)
                  (Finset.mem_coe.mpr hmemBce)
                change k₀.1.1 (k₀.1.1⁻¹ z) = k₀.1.1⁻¹ z at hfix
                rw [perm_apply_inv_self] at hfix
                rw [← hfix] at hmemBce
                exact Finset.mem_compl.mp (Finset.mem_of_mem_erase hmemBce) hz_B
          have hg₀_inv_kinv : g₀.1.1⁻¹ (k₀.1.1⁻¹ z) = k₀.1.1⁻¹ z :=
            (mem_fixingSubgroup_iff H).mp (Subgroup.inv_mem _ g₀.2) (k₀.1.1⁻¹ z)
              (Finset.mem_coe.mpr hk₀_inv_z_Be₁)
          have hg₀_z : g₀.1.1 z = z :=
            (mem_fixingSubgroup_iff H).mp g₀.2 z (Finset.mem_coe.mpr hz_Be₁)
          change g₀.1.1 (k₀.1.1 (g₀.1.1⁻¹ (k₀.1.1⁻¹ z))) = z
          rw [hg₀_inv_kinv, perm_apply_inv_self, hg₀_z]
    rw [hE_bot, Subgroup.mem_bot] at hc_E
    have hcb₂_eq_b₂ : c.1 b₂ = b₂ := by
      rw [hc_E]
      rfl
    have hcb₂_eq_b₁ : c.1 b₂ = b₁ := by
      have hk₀_inv_b₂ : k₀.1.1⁻¹ b₂ = b₂ :=
        (mem_fixingSubgroup_iff H).mp (Subgroup.inv_mem _ k₀.2) b₂ (Finset.mem_coe.mpr hg₀_b₁)
      change g₀.1.1 (k₀.1.1 (g₀.1.1⁻¹ (k₀.1.1⁻¹ b₂))) = b₁
      rw [hk₀_inv_b₂, perm_inv_apply_self, hk₀_b₁, hg₀_a₁]
    exact hb₂_ne_b₁ (hcb₂_eq_b₂.symm.trans hcb₂_eq_b₁)
  · have h_sub : 5 ≤ Fintype.card (Fin 8) - B.card := by
      rw [Fintype.card_fin]
      omega
    have h120 : 120 ≤ (Fintype.card (Fin 8) - B.card)! :=
      (by decide : 120 ≤ 5 !).trans (Nat.factorial_le h_sub)
    exact (by decide : 30 ≤ 120).trans
      (h120.trans (factorial_card_sub_le_index_of_fixingSubgroup_eq_bot hB_bot))

end Maroti
