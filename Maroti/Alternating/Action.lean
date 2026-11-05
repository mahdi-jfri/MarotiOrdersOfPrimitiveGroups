module

public import Maroti.Alternating.Bound
public import Maroti.Alternating.Lemma21
public import Maroti.Alternating.SubsetAction
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Intransitive and imprimitive stabilizer actions for alternating socles

Let `G ≤ Perm α` be a primitive group embedded via `ψ : G →* Perm (Fin m)` into `Perm (Fin m)`
such that `alternatingGroup (Fin m) ≤ ψ.range`, and let `H := (stabilizer G ω).map ψ`.
This file handles the intransitive and imprimitive cases of the action of `H` on `Fin m` in Step 3
of Section 2 of A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002), page 635.

If `H` is not pretransitive on `Fin m`, then `H` stabilizes a nonempty proper orbit `A₀` of size
`k` (`1 ≤ k < m`). By maximality of `stabilizer G ω` in `G` and transitivity of
`alternatingGroup (Fin m)` on `KSubset m k` (`exists_mem_alternatingGroup_kSubsetPerm_eq`),
`stabilizer G ω` is the full stabilizer of `A₀` in `G`, yielding `IsSubsetActionType G`
(`intransitive_isSubsetActionType`).

If `H` is pretransitive but not preprimitive on `Fin m` (`7 ≤ m`), then `H` preserves a nontrivial
block system `ℬ = orbit H B` of `a ≥ 2` blocks of size `b ≥ 2` with `m = a * b`, which forces
`8 ≤ m`. Bounding the block-system stabilizer `W ≤ Perm (Fin m)` by `b ! ^ a * a !` and applying
`Maroti.lemma_2_1` yields `Nat.card G ≤ bound (Nat.card α)` (`imprimitive_card_le_bound`).
-/

@[expose] public section

namespace Maroti.Alternating

open Equiv Equiv.Perm MulAction Subgroup
open scoped Nat Pointwise

/-- For `3 ≤ m`, `alternatingGroup (Fin m)` acts transitively on `KSubset m k` via `kSubsetPerm`. -/
theorem exists_mem_alternatingGroup_kSubsetPerm_eq {m k : ℕ} (hm : 3 ≤ m)
    (A B : KSubset m k) :
    ∃ σ ∈ alternatingGroup (Fin m), kSubsetPerm σ A = B := by
  have hm_card : 3 ≤ Nat.card (Fin m) := by
    rw [Nat.card_fin]
    exact hm
  have : IsPretransitive (alternatingGroup (Fin m)) (Set.powersetCard (Fin m) k) :=
    Set.powersetCard.isPretransitive_alternatingGroup hm_card
  let A' : Set.powersetCard (Fin m) k := ⟨A.1, Set.powersetCard.mem_iff.mpr A.2⟩
  let B' : Set.powersetCard (Fin m) k := ⟨B.1, Set.powersetCard.mem_iff.mpr B.2⟩
  obtain ⟨g, hAB⟩ := exists_smul_eq (alternatingGroup (Fin m)) A' B'
  refine ⟨g.1, g.2, Subtype.ext ?_⟩
  have hval : (g.1 • A.1 : Finset (Fin m)) = B.1 := congr_arg Subtype.val hAB
  rw [Finset.smul_finset_def] at hval
  change A.1.map g.1.toEmbedding = B.1
  rw [Finset.map_eq_image]
  exact hval

/-- If the image of a point stabilizer `stabilizer G ω` under `ψ : G →* Perm (Fin m)` is
intransitive on `Fin m`, then `IsSubsetActionType G`. -/
theorem intransitive_isSubsetActionType {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) (hG : IsPreprimitive G α) (ω : α)
    {m : ℕ} (hm : 5 ≤ m) (hm_le : m ≤ Nat.card α)
    (ψ : G →* Perm (Fin m))
    (hA : alternatingGroup (Fin m) ≤ ψ.range)
    (h_intrans : ¬ IsPretransitive ((stabilizer G ω).map ψ) (Fin m)) :
    IsSubsetActionType G := by
  classical
  set M := stabilizer G ω
  set H := M.map ψ
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hM_coatom : IsCoatom M := IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G ω
  have hex : ∃ x₀ y₀ : Fin m, y₀ ∉ orbit H x₀ := by
    by_contra! hall
    exact h_intrans ⟨fun x y => hall x y⟩
  obtain ⟨x₀, y₀, hy₀⟩ := hex
  set s : Finset (Fin m) := (orbit H x₀).toFinset
  set k := s.card
  have hx₀_s : x₀ ∈ s := Set.mem_toFinset.mpr (mem_orbit_self x₀)
  have hy₀_s : y₀ ∉ s := fun h => hy₀ (Set.mem_toFinset.mp h)
  have hk1 : 1 ≤ k := Finset.card_pos.mpr ⟨x₀, hx₀_s⟩
  have hkm : k < m := by
    have hlt : s.card < (Finset.univ : Finset (Fin m)).card :=
      Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => hy₀_s (h ▸ Finset.mem_univ y₀))
    rwa [Finset.card_univ, Fintype.card_fin] at hlt
  let A₀ : KSubset m k := ⟨s, rfl⟩
  let S : Subgroup G :=
    ((stabilizer (Perm (KSubset m k)) A₀).comap (kSubsetPermHom m k)).comap ψ
  have hmem_S : ∀ g : G, g ∈ S ↔ kSubsetPerm (ψ g) A₀ = A₀ := fun _ => Iff.rfl
  have hM_le_S : M ≤ S := by
    intro g hg
    rw [hmem_S]
    apply Subtype.ext
    change s.map (ψ g).toEmbedding = s
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rcases Finset.mem_map.mp hz with ⟨w, hw, rfl⟩
      rw [Set.mem_toFinset] at hw ⊢
      obtain ⟨k, rfl⟩ := hw
      exact ⟨⟨ψ g, ⟨g, hg, rfl⟩⟩ * k, mul_smul _ _ _⟩
    · rw [Finset.card_map]
  have hS_ne_top : S ≠ ⊤ := by
    have hy₀_er : y₀ ∉ s.erase x₀ := fun h => hy₀_s (Finset.mem_of_mem_erase h)
    let B₀ : KSubset m k :=
      ⟨insert y₀ (s.erase x₀), by
        rw [Finset.card_insert_of_notMem hy₀_er, Finset.card_erase_of_mem hx₀_s]
        omega⟩
    have hBA : B₀ ≠ A₀ := by
      intro heq
      have hy : y₀ ∈ A₀.1 := heq ▸ Finset.mem_insert_self y₀ (s.erase x₀)
      exact hy₀_s hy
    obtain ⟨σ, hσA, hσ_eq⟩ := exists_mem_alternatingGroup_kSubsetPerm_eq (by omega : 3 ≤ m) A₀ B₀
    obtain ⟨g₀, hg₀⟩ := hA hσA
    intro htop
    have hg₀S : g₀ ∈ S := htop ▸ Subgroup.mem_top g₀
    rw [hmem_S, hg₀, hσ_eq] at hg₀S
    exact hBA hg₀S
  have hMS : M = S := hM_le_S.eq_or_lt.resolve_right fun hlt => hS_ne_top (hM_coatom.2 S hlt)
  have hM_iff : ∀ g : G, g ∈ M ↔ kSubsetPerm (ψ g) A₀ = A₀ := by
    intro g
    rw [hMS, hmem_S]
  let f₁ : G ⧸ M → α :=
    Quotient.lift (fun g : G => g.1 ω) (by
      intro a b hab
      have h : a⁻¹ * b ∈ M := QuotientGroup.leftRel_apply.mp hab
      have h' : a.1.symm (b.1 ω) = ω := h
      have h'' := congr_arg a.1 h'
      rw [a.1.apply_symm_apply] at h''
      exact h''.symm)
  have hf₁_bij : Function.Bijective f₁ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨a⟩ ⟨b⟩ heq
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change a.1.symm (b.1 ω) = ω
      have heq' : a.1 ω = b.1 ω := heq
      rw [← heq', a.1.symm_apply_apply]
    · intro x
      obtain ⟨g, rfl⟩ := hG.toIsPretransitive.exists_smul_eq ω x
      exact ⟨⟦g⟧, rfl⟩
  let f₂ : G ⧸ M → KSubset m k :=
    Quotient.lift (fun g : G => kSubsetPerm (ψ g) A₀) (by
      intro a b hab
      have h : kSubsetPerm (ψ (a⁻¹ * b)) A₀ = A₀ := (hM_iff (a⁻¹ * b)).mp
        (QuotientGroup.leftRel_apply.mp hab)
      change (kSubsetPermHom m k (ψ a)) A₀ = (kSubsetPermHom m k (ψ b)) A₀
      have h' : (kSubsetPermHom m k (ψ a)).symm ((kSubsetPermHom m k (ψ b)) A₀) = A₀ := by
        change ((kSubsetPermHom m k (ψ a))⁻¹ * (kSubsetPermHom m k (ψ b))) A₀ = A₀
        rw [← map_inv, ← map_mul, ← map_inv, ← map_mul]
        exact h
      have h'' := congr_arg (kSubsetPermHom m k (ψ a)) h'
      rw [(kSubsetPermHom m k (ψ a)).apply_symm_apply] at h''
      exact h''.symm)
  have hf₂_bij : Function.Bijective f₂ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨a⟩ ⟨b⟩ heq
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      rw [hM_iff]
      change (kSubsetPermHom m k (ψ (a⁻¹ * b))) A₀ = A₀
      have heq' : (kSubsetPermHom m k (ψ a)) A₀ = (kSubsetPermHom m k (ψ b)) A₀ := heq
      rw [map_mul, map_inv, map_mul, map_inv, Perm.mul_apply, ← heq']
      exact (kSubsetPermHom m k (ψ a)).symm_apply_apply A₀
    · intro B
      obtain ⟨σ, hσA, hσ_eq⟩ := exists_mem_alternatingGroup_kSubsetPerm_eq (by omega : 3 ≤ m) A₀ B
      obtain ⟨g, hg⟩ := hA hσA
      refine ⟨⟦g⟧, ?_⟩
      change kSubsetPerm (ψ g) A₀ = B
      rw [hg, hσ_eq]
  let e₁ : G ⧸ M ≃ α := Equiv.ofBijective f₁ hf₁_bij
  let e₂ : G ⧸ M ≃ KSubset m k := Equiv.ofBijective f₂ hf₂_bij
  let e : α ≃ KSubset m k := e₁.symm.trans e₂
  have he_conj : ∀ g : G, e.permCongr g.1 = kSubsetPerm (ψ g) := by
    intro g
    ext B x
    obtain ⟨⟨a⟩, rfl⟩ := e₂.surjective B
    have h1 : e.symm (e₂ ⟦a⟧) = a.1 ω := by
      change e₁ (e₂.symm (e₂ ⟦a⟧)) = a.1 ω
      rw [e₂.symm_apply_apply]
      rfl
    have h2 : g.1 (a.1 ω) = e₁ ⟦g * a⟧ := rfl
    have h3 : e (e₁ ⟦g * a⟧) = e₂ ⟦g * a⟧ := by
      change e₂ (e₁.symm (e₁ ⟦g * a⟧)) = e₂ ⟦g * a⟧
      rw [e₁.symm_apply_apply]
    have h4 : e₂ ⟦g * a⟧ = kSubsetPerm (ψ g) (e₂ ⟦a⟧) := by
      change (kSubsetPermHom m k (ψ (g * a))) A₀ =
        (kSubsetPermHom m k (ψ g)) ((kSubsetPermHom m k (ψ a)) A₀)
      rw [map_mul, map_mul, Perm.mul_apply]
    change x ∈ (e (g.1 (e.symm (e₂ ⟦a⟧)))).1 ↔ x ∈ (kSubsetPerm (ψ g) (e₂ ⟦a⟧)).1
    rw [h1, h2, h3, h4]
  refine isSubsetActionType_of_equiv G hm e (fun g hg => ⟨ψ ⟨g, hg⟩, he_conj ⟨g, hg⟩⟩) ?_
  intro a
  obtain ⟨g, hg⟩ := hA a.2
  have hperm : e.symm.permCongr (kSubsetPerm (a : Perm (Fin m))) = g.1 := by
    rw [← hg, ← he_conj g]
    ext x
    simp [Equiv.permCongr_apply]
  rw [hperm]
  exact g.2

/-- The subgroup of `Perm (Fin m)` preserving a set of blocks `ℬ : Set (Set (Fin m))`. -/
def blockSystemStabilizer {m : ℕ} (ℬ : Set (Set (Fin m))) : Subgroup (Perm (Fin m)) where
  carrier := { σ : Perm (Fin m) | ∀ C : Set (Fin m), C ∈ ℬ ↔ σ • C ∈ ℬ }
  one_mem' := by intro C; simp
  mul_mem' := by intro σ₁ σ₂ h₁ h₂ C; rw [mul_smul, ← h₁ (σ₂ • C), ← h₂ C]
  inv_mem' := by intro σ h C; rw [h (σ⁻¹ • C), smul_inv_smul]

/-- If `H ≤ G' ≤ Perm (Fin m)` (`7 ≤ m`, `alternatingGroup (Fin m) ≤ G'`) acts transitively
but imprimitively on `Fin m`, then `Nat.card G' ≤ bound (H.subgroupOf G').index`. -/
theorem imprimitive_card_le_bound {m : ℕ} (hm : 7 ≤ m)
    (G' H : Subgroup (Perm (Fin m))) (hA : alternatingGroup (Fin m) ≤ G')
    (h_trans : IsPretransitive H (Fin m)) (h_imprim : ¬ IsPreprimitive H (Fin m)) :
    Nat.card G' ≤ bound (H.subgroupOf G').index := by
  classical
  have h_ex_block : ∃ B : Set (Fin m), IsBlock H B ∧ ¬ IsTrivialBlock B := by
    by_contra hall
    push Not at hall
    exact h_imprim ⟨fun {B} hB => hall B hB⟩
  obtain ⟨B, hB, hB_nt⟩ := h_ex_block
  have hB_nontriv : ¬ B.Subsingleton := fun h => hB_nt (Or.inl h)
  have hB_ne_univ : B ≠ Set.univ := fun h => hB_nt (Or.inr h)
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := Set.not_subsingleton_iff.mp hB_nontriv
  have hB_ne : B.Nonempty := ⟨x₀, hx₀⟩
  set ℬ : Set (Set (Fin m)) := orbit H B
  set b := B.ncard
  set a := ℬ.ncard
  have hb : 2 ≤ b := (Set.one_lt_ncard_iff B.toFinite).mpr ⟨x₀, y₀, hx₀, hy₀, hxy₀⟩
  have hab : m = a * b := by
    have hmul := hB.ncard_block_mul_ncard_orbit_eq hB_ne
    rw [Nat.card_fin, mul_comm] at hmul
    exact hmul.symm
  have ha : 2 ≤ a := by
    have hlt : b < m := by
      have hss : B ⊂ Set.univ := Set.ssubset_univ_iff.mpr hB_ne_univ
      have hlt' := Set.ncard_lt_ncard hss
      rwa [Set.ncard_univ, Nat.card_fin] at hlt'
    by_contra hlt2
    have : a = 0 ∨ a = 1 := by omega
    rcases this with ha0 | ha1
    · rw [ha0] at hab; omega
    · rw [ha1] at hab; omega
  have hm8 : 8 ≤ m := by
    by_contra hlt8
    have hm7 : m = 7 := by omega
    have ha3 : a ≤ 3 := by
      by_contra ha4
      have : 4 * 2 ≤ a * b := Nat.mul_le_mul (by omega) hb
      omega
    have : a = 2 ∨ a = 3 := by omega
    rcases this with ha2 | ha3'
    · rw [ha2] at hab; omega
    · rw [ha3'] at hab; omega
  set W := blockSystemStabilizer ℬ
  have hHW : H ≤ W := by
    intro h hh C
    change C ∈ orbit H B ↔ (⟨h, hh⟩ : H) • C ∈ orbit H B
    refine ⟨fun ⟨k, hk⟩ => ⟨⟨h, hh⟩ * k, ?_⟩, fun ⟨k, hk⟩ => ⟨⟨h, hh⟩⁻¹ * k, ?_⟩⟩
    · change k • B = C at hk
      change (⟨h, hh⟩ * k) • B = (⟨h, hh⟩ : H) • C
      rw [mul_smul, hk]
    · change k • B = (⟨h, hh⟩ : H) • C at hk
      change (⟨h, hh⟩⁻¹ * k) • B = C
      rw [mul_smul, hk, inv_smul_smul]
  have hswap_fix : ∀ C ∈ ℬ, swap x₀ y₀ • C = C := by
    rintro C ⟨k, rfl⟩
    change swap x₀ y₀ • (k • B) = k • B
    rcases hB.smul_eq_or_disjoint k with heq | hdisj
    · rw [heq]
      exact Equiv.Perm.swap_mem_stabilizer hx₀ hy₀
    · ext z
      simp only [Set.mem_smul_set, Perm.smul_def]
      have hz_not : ∀ w ∈ (k • B : Set (Fin m)), w ≠ x₀ ∧ w ≠ y₀ := by
        intro w hw
        have hwB : w ∉ B := Set.disjoint_left.mp hdisj hw
        exact ⟨fun h => hwB (h ▸ hx₀), fun h => hwB (h ▸ hy₀)⟩
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [swap_apply_of_ne_of_ne (hz_not w hw).1 (hz_not w hw).2]
        exact hw
      · intro hz
        exact ⟨z, hz, swap_apply_of_ne_of_ne (hz_not z hz).1 (hz_not z hz).2⟩
  have hswap_W : swap x₀ y₀ ∈ W := by
    intro C
    refine ⟨fun hC => (hswap_fix C hC).symm ▸ hC, fun hC => ?_⟩
    have hfix := hswap_fix (swap x₀ y₀ • C) hC
    rw [smul_smul, swap_mul_self, one_smul] at hfix
    exact hfix ▸ hC
  have hW_idx : W.index = (W.subgroupOf G').index := by
    let q : G' ⧸ W.subgroupOf G' → Perm (Fin m) ⧸ W :=
      Quotient.lift (fun g : G' => ((g.1 : Perm (Fin m)) : Perm (Fin m) ⧸ W)) (by
        intro x y hxy
        apply Quotient.sound
        exact QuotientGroup.leftRel_apply.mpr
          (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hxy)))
    have hq_bij : Function.Bijective q := by
      refine ⟨?_, ?_⟩
      · rintro ⟨x⟩ ⟨y⟩ heq
        apply Quotient.sound
        exact QuotientGroup.leftRel_apply.mpr
          (Subgroup.mem_subgroupOf.mpr (QuotientGroup.leftRel_apply.mp (Quotient.exact heq)))
      · rintro ⟨σ⟩
        rcases Int.units_eq_one_or (sign σ) with hpos | hneg
        · have hσG' : σ ∈ G' := hA (mem_alternatingGroup.mpr hpos)
          exact ⟨⟦⟨σ, hσG'⟩⟧, rfl⟩
        · have hσ_swap : σ * swap x₀ y₀ ∈ G' := by
            apply hA
            rw [mem_alternatingGroup, map_mul, hneg, sign_swap hxy₀]
            decide
          refine ⟨⟦⟨σ * swap x₀ y₀, hσ_swap⟩⟧, ?_⟩
          apply Quotient.sound
          apply QuotientGroup.leftRel_apply.mpr
          have : (σ * swap x₀ y₀)⁻¹ * σ = swap x₀ y₀ := by
            rw [mul_inv_rev, Equiv.swap_inv, mul_assoc, inv_mul_cancel, mul_one]
          rw [this]
          exact hswap_W
    exact (Nat.card_congr (Equiv.ofBijective q hq_bij)).symm
  have hW_idx_le : W.index ≤ (H.subgroupOf G').index := by
    rw [hW_idx]
    have hle : H.subgroupOf G' ≤ W.subgroupOf G' := fun g hg => hHW hg
    let p : G' ⧸ H.subgroupOf G' → G' ⧸ W.subgroupOf G' :=
      Quotient.lift (fun g : G' => (g : G' ⧸ W.subgroupOf G')) (by
        intro x y hxy
        apply Quotient.sound
        exact QuotientGroup.leftRel_apply.mpr (hle (QuotientGroup.leftRel_apply.mp hxy)))
    have hp_surj : Function.Surjective p := by
      rintro ⟨g⟩
      exact ⟨⟦g⟧, rfl⟩
    exact Nat.card_le_card_of_surjective p hp_surj
  let π : W →* Perm ℬ :=
    { toFun := fun σ =>
        { toFun := fun C => ⟨σ.1 • C.1, (σ.2 C.1).mp C.2⟩
          invFun := fun C => ⟨σ.1⁻¹ • C.1, (W.inv_mem σ.2 C.1).mp C.2⟩
          left_inv := fun C => Subtype.ext (inv_smul_smul σ.1 C.1)
          right_inv := fun C => Subtype.ext (smul_inv_smul σ.1 C.1) }
      map_one' := Equiv.ext fun C => Subtype.ext (one_smul _ C.1)
      map_mul' := fun σ₁ σ₂ => Equiv.ext fun C => Subtype.ext (mul_smul σ₁.1 σ₂.1 C.1) }
  let ρ : π.ker →* (∀ C : ℬ, Perm C.1) :=
    { toFun := fun σ C =>
        { toFun := fun x => ⟨σ.1.1 x.1, by
            have hC : σ.1.1 • C.1 = C.1 := congr_arg Subtype.val (Equiv.congr_fun σ.2 C)
            have hmem : σ.1.1 x.1 ∈ σ.1.1 • C.1 := Set.smul_mem_smul_set x.2
            rwa [hC] at hmem⟩
          invFun := fun x => ⟨σ.1.1⁻¹ x.1, by
            have hC : σ.1.1⁻¹ • C.1 = C.1 :=
              congr_arg Subtype.val (Equiv.congr_fun (π.ker.inv_mem σ.2) C)
            have hmem : σ.1.1⁻¹ x.1 ∈ σ.1.1⁻¹ • C.1 := Set.smul_mem_smul_set x.2
            rwa [hC] at hmem⟩
          left_inv := fun x => Subtype.ext (σ.1.1.symm_apply_apply x.1)
          right_inv := fun x => Subtype.ext (σ.1.1.apply_symm_apply x.1) }
      map_one' := funext fun C => Equiv.ext fun x => rfl
      map_mul' := fun σ₁ σ₂ => funext fun C => Equiv.ext fun x => rfl }
  have hρ_inj : Function.Injective ρ := by
    intro σ₁ σ₂ heq
    apply Subtype.ext (Subtype.ext (Equiv.ext fun x => ?_))
    obtain ⟨g, rfl⟩ := h_trans.exists_smul_eq x₀ x
    let C : ℬ := ⟨g • B, ⟨g, rfl⟩⟩
    have hxC : g • x₀ ∈ C.1 := Set.smul_mem_smul_set hx₀
    exact congr_arg Subtype.val (Equiv.congr_fun (congr_fun heq C) ⟨g • x₀, hxC⟩)
  have hℬ_card : Nat.card ℬ = a := Nat.card_coe_set_eq ℬ
  have hC_card : ∀ C : ℬ, Nat.card (Perm C.1) = b ! := by
    rintro ⟨C, ⟨k, rfl⟩⟩
    rw [Nat.card_perm]
    let eB : B ≃ (k • B : Set (Fin m)) :=
      { toFun := fun x => ⟨k.1 x.1, Set.smul_mem_smul_set x.2⟩
        invFun := fun x => ⟨k.1.symm x.1, by
          obtain ⟨y, hy, hyx⟩ := x.2
          change k.1 y = x.1 at hyx
          have hy_eq : y = k.1.symm x.1 := by
            rw [← hyx, k.1.symm_apply_apply]
          exact hy_eq ▸ hy⟩
        left_inv := fun x => Subtype.ext (k.1.symm_apply_apply x.1)
        right_inv := fun x => Subtype.ext (k.1.apply_symm_apply x.1) }
    have hcard_eq : Nat.card (k • B : Set (Fin m)) = b := by
      rw [Nat.card_congr eB.symm, Nat.card_coe_set_eq]
    rw [hcard_eq]
  have hker_le : Nat.card π.ker ≤ b ! ^ a := by
    have hpi_card : Nat.card (∀ C : ℬ, Perm C.1) = b ! ^ a := by
      rw [Nat.card_pi]
      simp_rw [hC_card]
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hℬ_card]
    rw [← hpi_card]
    exact Nat.card_le_card_of_injective ρ hρ_inj
  have hidx_le : π.ker.index ≤ a ! := by
    have heq : π.ker.index = Nat.card π.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv
    have hperm_card : Nat.card (Perm ℬ) = a ! := by
      rw [Nat.card_perm, hℬ_card]
    rw [heq, ← hperm_card]
    exact Subgroup.card_le_card_group π.range
  have hW_card_le : Nat.card W ≤ b ! ^ a * a ! := by
    rw [← Subgroup.card_mul_index π.ker]
    exact Nat.mul_le_mul hker_le hidx_le
  set N := m ! / (b ! ^ a * a !)
  have hdiv_le_n : N ≤ (H.subgroupOf G').index := by
    have hW_mul : Nat.card W * W.index = m ! := by
      have h := Subgroup.card_mul_index W
      rwa [Nat.card_perm, Nat.card_fin] at h
    have hpos : 0 < Nat.card W := Nat.card_pos
    have h1 : N ≤ m ! / Nat.card W :=
      Nat.div_le_div_left hW_card_le hpos
    have h2 : m ! / Nat.card W = W.index := by
      rw [← hW_mul, mul_comm, Nat.mul_div_cancel _ hpos]
    exact (h1.trans h2.le).trans hW_idx_le
  have hG'_le : Nat.card G' ≤ m ! := by
    have h := Subgroup.card_le_card_group G'
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hlem : m ! ≤ N ^ Nat.log 2 N := Maroti.lemma_2_1 a b m hm8 ha hb hab
  have hN1 : 1 ≤ N := by
    by_contra hN0
    have h0 : N = 0 := Nat.lt_one_iff.mp (not_le.mp hN0)
    have hpow0 : N ^ Nat.log 2 N = 1 := by rw [h0]; rfl
    have hm_le1 : m ! ≤ 1 := hlem.trans hpow0.le
    have hm_gt : 2 ≤ m ! := (by decide : 2 ≤ 2 !).trans (Nat.factorial_le (by omega))
    omega
  exact ((hG'_le.trans hlem).trans (pow_log_mono hN1 hdiv_le_n)).trans
    (pow_log_le_bound (hN1.trans hdiv_le_n))

end Maroti.Alternating
