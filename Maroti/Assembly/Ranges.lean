module

public import Maroti.Interface

/-!
# Parameter ranges for the product action case of Theorem 1.1

This file proves `Maroti.IsWreathType.isProductActionType`, which shows that a primitive
permutation group `G ≤ Perm α` on a nontrivial type `α` satisfying `IsWreathType G` (Section 2,
Step 1 of A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002), pages 633–634)
satisfies `IsProductActionType G` with the parameter ranges `5 ≤ m`, `1 ≤ k`, `2 * k < m`, and
`1 ≤ r`.

The proof proceeds in three steps:
1. Since `α` is nontrivial and `α ≃ (Fin r → KSubset m k)`, the function space is not a
   subsingleton, which gives `1 ≤ r` and `Nontrivial (KSubset m k)`, hence `1 ≤ k` and `k < m`
   (`one_le_r_of_nontrivial`, `one_le_k_and_k_lt_m_of_nontrivial`).
2. When `k ≤ m`, the complement map `A ↦ Aᶜ` defines an equivalence
   `kSubsetCompl : KSubset m k ≃ KSubset m (m - k)` commuting with `kSubsetPerm h` for every
   `h : Perm (Fin m)`. Applying it in each coordinate (`tupleComplEquiv`) replaces `k` by `m - k`,
   so `m < 2 * k` reduces to `2 * (m - k) < m`.
3. When `2 * k = m`, coordinatewise complementation induces a fixed-point-free involution on `α`
   that commutes with the action of `G`. For any `x₀ : α`, the two-element set
   `{x₀, complPt x₀}` is a block of `G`. Since `5 ≤ m` implies `3 ≤ k` and
   `Nat.choose (2 * k) k ≥ 20` (`twenty_le_centralBinom`), this block is neither a subsingleton
   nor `Set.univ`, contradicting `MulAction.IsPreprimitive G α` (`two_mul_k_ne_m`).
-/

@[expose] public section

namespace Maroti

open Equiv MulAction
open scoped Pointwise

variable {α : Type*}

/-- For `3 ≤ k`, the central binomial coefficient `(2 * k).choose k` is at least `20`. -/
theorem twenty_le_centralBinom {k : ℕ} (hk : 3 ≤ k) : 20 ≤ (2 * k).choose k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    have h1 : (2 * k).choose k ≤ (2 * k + 1).choose k := Nat.choose_le_succ (2 * k) k
    have h2 : (2 * k + 1).choose k ≤ (2 * (k + 1)).choose (k + 1) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.choose_succ_succ]
      exact Nat.le_add_right _ _
    omega

/-- The cardinality of `KSubset m k` is `m.choose k`. -/
theorem card_kSubset (m k : ℕ) : Fintype.card (KSubset m k) = m.choose k := by
  rw [Fintype.card_finset_len, Fintype.card_fin]

/-- If `Fin r → KSubset m k` is nontrivial, then `1 ≤ r`. -/
theorem one_le_r_of_nontrivial {m k r : ℕ} (h : Nontrivial (Fin r → KSubset m k)) : 1 ≤ r := by
  by_contra hr
  have hr0 : r = 0 := by omega
  subst hr0
  exact not_subsingleton (Fin 0 → KSubset m k) inferInstance

/-- If `Fin r → KSubset m k` is nontrivial, then `KSubset m k` is nontrivial. -/
theorem nontrivial_kSubset_of_nontrivial_pi {m k r : ℕ}
    (h : Nontrivial (Fin r → KSubset m k)) : Nontrivial (KSubset m k) := by
  by_contra hsub
  rw [not_nontrivial_iff_subsingleton] at hsub
  exact not_subsingleton (Fin r → KSubset m k) inferInstance

/-- If `KSubset m k` is nontrivial, then `1 ≤ k` and `k < m`. -/
theorem one_le_k_and_k_lt_m_of_nontrivial {m k : ℕ} (h : Nontrivial (KSubset m k)) :
    1 ≤ k ∧ k < m := by
  obtain ⟨A, B, hAB⟩ := exists_pair_ne (KSubset m k)
  have hkm : k ≤ m := by
    rw [← A.2]
    exact A.1.card_le_univ.trans (by rw [Fintype.card_fin])
  refine ⟨?_, ?_⟩
  · by_contra hk0
    have hk_eq : k = 0 := by omega
    apply hAB
    apply Subtype.ext
    rw [Finset.card_eq_zero.mp (A.2.trans hk_eq), Finset.card_eq_zero.mp (B.2.trans hk_eq)]
  · by_contra hkm'
    have hk_eq : k = m := by omega
    apply hAB
    apply Subtype.ext
    have hA : A.1 = Finset.univ := Finset.eq_univ_of_card A.1 (by rw [A.2, hk_eq, Fintype.card_fin])
    have hB : B.1 = Finset.univ := Finset.eq_univ_of_card B.1 (by rw [B.2, hk_eq, Fintype.card_fin])
    rw [hA, hB]

/-- The complement equivalence `KSubset m k ≃ KSubset m (m - k)` when `k ≤ m`. -/
def kSubsetCompl {m k : ℕ} (hk : k ≤ m) : KSubset m k ≃ KSubset m (m - k) where
  toFun A := ⟨A.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, A.2]⟩
  invFun B := ⟨B.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, B.2, Nat.sub_sub_self hk]⟩
  left_inv A := Subtype.ext (compl_compl A.1)
  right_inv B := Subtype.ext (compl_compl B.1)

theorem kSubsetCompl_kSubsetPerm {m k : ℕ} (hk : k ≤ m) (h : Perm (Fin m)) (A : KSubset m k) :
    kSubsetCompl hk (kSubsetPerm h A) = kSubsetPerm h (kSubsetCompl hk A) := by
  apply Subtype.ext
  ext x
  simp [kSubsetCompl, kSubsetPerm, Finset.mem_map_equiv]

/-- The coordinatewise complement equivalence `(Fin r → KSubset m k) ≃ (Fin r → KSubset m (m - k))`
when `k ≤ m`. -/
def tupleComplEquiv {m k r : ℕ} (hk : k ≤ m) :
    (Fin r → KSubset m k) ≃ (Fin r → KSubset m (m - k)) :=
  Equiv.piCongrRight fun _ => kSubsetCompl hk

theorem permCongr_tupleComplEquiv_productActionPerm {m k r : ℕ} (hk : k ≤ m)
    (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)) :
    (tupleComplEquiv hk).permCongr (productActionPerm σ h) = productActionPerm σ h := by
  apply Equiv.ext
  intro y
  funext i
  change kSubsetCompl hk (kSubsetPerm (h i) ((kSubsetCompl hk).symm (y (σ.symm i)))) =
    kSubsetPerm (h i) (y (σ.symm i))
  rw [kSubsetCompl_kSubsetPerm, Equiv.apply_symm_apply]

theorem symm_permCongr_tupleComplEquiv_productActionPerm {m k r : ℕ} (hk : k ≤ m)
    (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)) :
    (tupleComplEquiv hk).symm.permCongr (productActionPerm σ h) = productActionPerm σ h := by
  rw [← permCongr_tupleComplEquiv_productActionPerm hk σ h]
  ext y
  simp

/-- When `2 * k = m`, the complement of a `k`-subset of `Fin m` is again a `k`-subset of `Fin m`. -/
def kSubsetComplSelf {m k : ℕ} (hm_eq : 2 * k = m) (A : KSubset m k) : KSubset m k :=
  ⟨A.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, A.2]; omega⟩

theorem kSubsetComplSelf_involutive {m k : ℕ} (hm_eq : 2 * k = m) (A : KSubset m k) :
    kSubsetComplSelf hm_eq (kSubsetComplSelf hm_eq A) = A :=
  Subtype.ext (compl_compl A.1)

theorem kSubsetComplSelf_ne {m k : ℕ} (hm : 5 ≤ m) (hm_eq : 2 * k = m) (A : KSubset m k) :
    kSubsetComplSelf hm_eq A ≠ A := by
  intro h
  have h1 := Finset.ext_iff.mp (congrArg Subtype.val h) ⟨0, by omega⟩
  rw [kSubsetComplSelf, Finset.mem_compl] at h1
  exact not_iff_self h1

theorem kSubsetPerm_kSubsetComplSelf {m k : ℕ} (hm_eq : 2 * k = m) (h : Perm (Fin m))
    (A : KSubset m k) :
    kSubsetPerm h (kSubsetComplSelf hm_eq A) = kSubsetComplSelf hm_eq (kSubsetPerm h A) := by
  apply Subtype.ext
  ext x
  simp [kSubsetComplSelf, kSubsetPerm, Finset.mem_map_equiv]

/-- Coordinatewise complementation on `Fin r → KSubset m k` when `2 * k = m`. -/
def tupleComplSelf {m k r : ℕ} (hm_eq : 2 * k = m) (x : Fin r → KSubset m k) :
    Fin r → KSubset m k :=
  fun i => kSubsetComplSelf hm_eq (x i)

theorem tupleComplSelf_involutive {m k r : ℕ} (hm_eq : 2 * k = m) (x : Fin r → KSubset m k) :
    tupleComplSelf hm_eq (tupleComplSelf hm_eq x) = x :=
  funext fun i => kSubsetComplSelf_involutive hm_eq (x i)

theorem tupleComplSelf_ne {m k r : ℕ} (hm : 5 ≤ m) (hr : 1 ≤ r) (hm_eq : 2 * k = m)
    (x : Fin r → KSubset m k) :
    tupleComplSelf hm_eq x ≠ x := by
  intro h
  exact kSubsetComplSelf_ne hm hm_eq (x ⟨0, hr⟩) (congrFun h ⟨0, hr⟩)

theorem productActionPerm_tupleComplSelf {m k r : ℕ} (hm_eq : 2 * k = m)
    (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)) (x : Fin r → KSubset m k) :
    productActionPerm σ h (tupleComplSelf hm_eq x) =
      tupleComplSelf hm_eq (productActionPerm σ h x) := by
  funext i
  exact kSubsetPerm_kSubsetComplSelf hm_eq (h i) (x (σ.symm i))

/-- In the product action with `5 ≤ m` and `1 ≤ r`, if `G` acts preprimitively on `α`, then
`2 * k ≠ m`. -/
theorem two_mul_k_ne_m [Nonempty α] {G : Subgroup (Perm α)} [IsPreprimitive G α]
    {m k r : ℕ} (e : α ≃ (Fin r → KSubset m k)) (hm : 5 ≤ m) (hr : 1 ≤ r)
    (hG : ∀ g ∈ G, ∃ (σ : Perm (Fin r)) (h : Fin r → Perm (Fin m)),
      e.permCongr g = productActionPerm σ h) :
    2 * k ≠ m := by
  intro hm_eq
  let complPt : α → α := fun x => e.symm (tupleComplSelf hm_eq (e x))
  have hcompl_inv : ∀ x : α, complPt (complPt x) = x := fun x => by
    simp [complPt, tupleComplSelf_involutive]
  have hcompl_ne : ∀ x : α, complPt x ≠ x := fun x h =>
    tupleComplSelf_ne hm hr hm_eq (e x) (by simpa [complPt] using congrArg e h)
  have hcompl_smul : ∀ (g : G) (x : α), g • complPt x = complPt (g • x) := by
    intro g x
    obtain ⟨σ, h, hgh⟩ := hG g.1 g.2
    have hge : ∀ y : α, e (g • y) = productActionPerm σ h (e y) := fun y => by
      have := congrArg (fun p : Perm (Fin r → KSubset m k) => p (e y)) hgh
      exact (by simpa [Equiv.permCongr_apply] using this : e (g.1 y) = _)
    apply e.injective
    rw [hge (complPt x), Equiv.apply_symm_apply, productActionPerm_tupleComplSelf,
      ← hge x, Equiv.apply_symm_apply]
  obtain ⟨x₀⟩ := ‹Nonempty α›
  let B : Set α := {x₀, complPt x₀}
  have hB_block : IsBlock G B := by
    rw [isBlock_iff_smul_eq_of_mem]
    intro g a ha hga
    have hgx₀ : g • x₀ = x₀ ∨ g • x₀ = complPt x₀ := by
      rcases ha with rfl | rfl
      · exact hga
      · rw [hcompl_smul] at hga
        rcases hga with h1 | h2
        · right
          have := congrArg complPt h1
          rwa [hcompl_inv] at this
        · left
          have := congrArg complPt h2
          rwa [hcompl_inv, hcompl_inv] at this
    ext z
    simp only [B, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      rcases hgx₀ with h1 | h2
      · rcases hz with hz1 | hz2
        · left
          calc z = g • g⁻¹ • z := (smul_inv_smul g z).symm
            _ = g • x₀ := by rw [hz1]
            _ = x₀ := h1
        · right
          calc z = g • g⁻¹ • z := (smul_inv_smul g z).symm
            _ = g • complPt x₀ := by rw [hz2]
            _ = complPt (g • x₀) := hcompl_smul g x₀
            _ = complPt x₀ := by rw [h1]
      · rcases hz with hz1 | hz2
        · right
          calc z = g • g⁻¹ • z := (smul_inv_smul g z).symm
            _ = g • x₀ := by rw [hz1]
            _ = complPt x₀ := h2
        · left
          calc z = g • g⁻¹ • z := (smul_inv_smul g z).symm
            _ = g • complPt x₀ := by rw [hz2]
            _ = complPt (g • x₀) := hcompl_smul g x₀
            _ = complPt (complPt x₀) := by rw [h2]
            _ = x₀ := hcompl_inv x₀
    · intro hz
      rcases hgx₀ with h1 | h2
      · rcases hz with rfl | rfl
        · left
          exact inv_smul_eq_iff.mpr h1.symm
        · right
          apply inv_smul_eq_iff.mpr
          rw [hcompl_smul, h1]
      · rcases hz with rfl | rfl
        · right
          apply inv_smul_eq_iff.mpr
          rw [hcompl_smul, h2, hcompl_inv]
        · left
          exact inv_smul_eq_iff.mpr h2.symm
  rcases hB_block.subsingleton_or_eq_univ with hsub | huniv
  · exact hcompl_ne x₀ (hsub (Set.mem_insert_of_mem _ rfl) (Set.mem_insert _ _))
  · have hsub_univ : (Finset.univ : Finset (Fin r → KSubset m k)) ⊆
        {e x₀, tupleComplSelf hm_eq (e x₀)} := by
      intro y _
      have hy : e.symm y ∈ B := huniv ▸ Set.mem_univ (e.symm y)
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hy with hy1 | hy2
      · left
        simpa using congrArg e hy1
      · right
        simpa [complPt] using congrArg e hy2
    have hcard_le : Fintype.card (Fin r → KSubset m k) ≤ 2 := by
      calc Fintype.card (Fin r → KSubset m k)
          = (Finset.univ : Finset (Fin r → KSubset m k)).card := rfl
        _ ≤ ({e x₀, tupleComplSelf hm_eq (e x₀)} : Finset (Fin r → KSubset m k)).card :=
            Finset.card_le_card hsub_univ
        _ ≤ 2 := Finset.card_le_two
    have hk3 : 3 ≤ k := by omega
    have h20 : 20 ≤ Fintype.card (KSubset m k) := by
      rw [card_kSubset, ← hm_eq]
      exact twenty_le_centralBinom hk3
    have hcard_ge : 20 ≤ Fintype.card (Fin r → KSubset m k) := by
      rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact h20.trans (Nat.le_self_pow (by omega) _)
    omega

/-- Any primitive group `G ≤ Perm α` on a nontrivial type `α` that satisfies `IsWreathType G`
satisfies `IsProductActionType G` with `5 ≤ m`, `1 ≤ k`, `2 * k < m`, and `1 ≤ r`. -/
theorem IsWreathType.isProductActionType [Nontrivial α] {G : Subgroup (Perm α)}
    [IsPreprimitive G α] (h : IsWreathType G) : IsProductActionType G := by
  obtain ⟨m, k, r, e, hm, hG, hAlt⟩ := h
  have hnt_pi : Nontrivial (Fin r → KSubset m k) := e.symm.nontrivial
  have hr : 1 ≤ r := one_le_r_of_nontrivial hnt_pi
  have ⟨hk1, hkm⟩ :=
    one_le_k_and_k_lt_m_of_nontrivial (nontrivial_kSubset_of_nontrivial_pi hnt_pi)
  have hne : 2 * k ≠ m := two_mul_k_ne_m e hm hr hG
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨m, k, r, e, hm, hk1, hlt, hr, hG, hAlt⟩
  · refine ⟨m, m - k, r, e.trans (tupleComplEquiv hkm.le), hm, by omega, by omega, hr, ?_, ?_⟩
    · intro g hg
      obtain ⟨σ, h_perm, hgh⟩ := hG g hg
      refine ⟨σ, h_perm, ?_⟩
      have h1 : (e.trans (tupleComplEquiv hkm.le)).permCongr g =
          (tupleComplEquiv hkm.le).permCongr (e.permCongr g) := by
        ext y
        simp
      rw [h1, hgh, permCongr_tupleComplEquiv_productActionPerm]
    · intro a
      have h1 : (e.trans (tupleComplEquiv hkm.le)).symm.permCongr
          (productActionPerm 1 fun i => (a i : Perm (Fin m))) =
        e.symm.permCongr ((tupleComplEquiv hkm.le).symm.permCongr
          (productActionPerm 1 fun i => (a i : Perm (Fin m)))) := by
        ext x
        simp
      rw [h1, symm_permCongr_tupleComplEquiv_productActionPerm]
      exact hAlt a

end Maroti
