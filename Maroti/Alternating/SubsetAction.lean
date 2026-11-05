module

public import Maroti.Interface
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Subset action type for alternating and symmetric groups

This file proves transfer lemmas for `Maroti.IsSubsetActionType`, corresponding to case (i) of
Theorem 1.1 with `r = 1` in A. Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002),
pages 631 and 635.

If a permutation group `G` on `α` is permutation-isomorphic via `e : α ≃ KSubset m k` to the action
of a subgroup of `Perm (Fin m)` containing `alternatingGroup (Fin m)` on `k`-element subsets, then
`IsSubsetActionType G` holds (`isSubsetActionType_of_equiv`). In particular, if `5 ≤ Nat.card α`
and `alternatingGroup α ≤ G`, identifying `α` with the `1`-element subsets of `Fin (Nat.card α)`
via `finEquivKSubsetOne` shows that `IsSubsetActionType G` holds with `m = Nat.card α` and `k = 1`
(`isSubsetActionType_of_alternatingGroup_le`).
-/

@[expose] public section

namespace Maroti

open Equiv

/-- The natural equivalence between `Fin m` and the `1`-element subsets of `Fin m`. -/
noncomputable def finEquivKSubsetOne (m : ℕ) : Fin m ≃ KSubset m 1 where
  toFun i := ⟨{i}, Finset.card_singleton i⟩
  invFun A := (Finset.card_eq_one.mp A.2).choose
  left_inv i := by
    have h := (Finset.card_eq_one.mp (Finset.card_singleton i)).choose_spec
    exact Finset.singleton_injective h.symm
  right_inv A := by
    apply Subtype.ext
    exact (Finset.card_eq_one.mp A.2).choose_spec.symm

@[simp]
theorem finEquivKSubsetOne_apply (m : ℕ) (i : Fin m) :
    (finEquivKSubsetOne m i).1 = {i} := rfl

/-- The action `kSubsetPerm` packaged as a monoid homomorphism
`Perm (Fin m) →* Perm (KSubset m k)`. -/
def kSubsetPermHom (m k : ℕ) : Perm (Fin m) →* Perm (KSubset m k) where
  toFun := kSubsetPerm
  map_one' := by
    ext A x
    simp [kSubsetPerm, Perm.one_def]
  map_mul' f g := by
    ext A x
    simp [kSubsetPerm, Perm.mul_def, Finset.map_map]

@[simp]
theorem kSubsetPermHom_apply {m k : ℕ} (h : Perm (Fin m)) :
    kSubsetPermHom m k h = kSubsetPerm h := rfl

@[simp]
theorem kSubsetPerm_one {m k : ℕ} :
    kSubsetPerm (1 : Perm (Fin m)) = (1 : Perm (KSubset m k)) :=
  (kSubsetPermHom m k).map_one

@[simp]
theorem kSubsetPerm_mul {m k : ℕ} (f g : Perm (Fin m)) :
    kSubsetPerm (f * g) = (kSubsetPerm f : Perm (KSubset m k)) * kSubsetPerm g :=
  (kSubsetPermHom m k).map_mul f g

@[simp]
theorem kSubsetPerm_inv {m k : ℕ} (f : Perm (Fin m)) :
    kSubsetPerm f⁻¹ = (kSubsetPerm f : Perm (KSubset m k))⁻¹ :=
  (kSubsetPermHom m k).map_inv f

/-- Conjugating a permutation `h` of `Fin m` by `finEquivKSubsetOne m` gives `kSubsetPerm h`
on `1`-element subsets. -/
theorem permCongr_finEquivKSubsetOne {m : ℕ} (h : Perm (Fin m)) :
    (finEquivKSubsetOne m).permCongr h = kSubsetPerm h := by
  ext A x
  simp only [permCongr_apply, kSubsetPerm, Finset.mem_map,
    Equiv.toEmbedding_apply, finEquivKSubsetOne, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp A.2
  have hchoose : (Finset.card_eq_one.mp A.2).choose = a := by
    have spec := (Finset.card_eq_one.mp A.2).choose_spec
    exact Finset.singleton_injective (spec.symm.trans ha)
  rw [hchoose, ha, Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨a, Finset.mem_singleton_self a, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    rw [Finset.mem_singleton.mp hb]

/-- General transfer lemma for `IsSubsetActionType`: if `e : α ≃ KSubset m k` conjugates every
element of `G` into `kSubsetPerm h` for some `h : Perm (Fin m)` and pulls back `kSubsetPerm` of
every alternating permutation into `G`, then `IsSubsetActionType G` holds. -/
theorem isSubsetActionType_of_equiv {α : Type*} (G : Subgroup (Perm α))
    {m k : ℕ} (hm : 5 ≤ m) (e : α ≃ KSubset m k)
    (hG : ∀ g ∈ G, ∃ h : Perm (Fin m), e.permCongr g = kSubsetPerm h)
    (hA : ∀ a : alternatingGroup (Fin m), e.symm.permCongr (kSubsetPerm (a : Perm (Fin m))) ∈ G) :
    IsSubsetActionType G :=
  ⟨m, k, e, hm, hG, hA⟩

/-- If `G ≤ Perm α` contains `alternatingGroup α` and `5 ≤ Nat.card α`, then `G` is of subset
action type (with `m = Nat.card α` and `k = 1`). -/
theorem isSubsetActionType_of_alternatingGroup_le {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) (h5 : 5 ≤ Nat.card α) (hA : alternatingGroup α ≤ G) :
    IsSubsetActionType G := by
  set m := Nat.card α
  have hm : Fintype.card α = m := (Nat.card_eq_fintype_card (α := α)).symm
  let e₀ : α ≃ Fin m := Fintype.equivFinOfCardEq hm
  let e : α ≃ KSubset m 1 := e₀.trans (finEquivKSubsetOne m)
  refine ⟨m, 1, e, h5, ?_, ?_⟩
  · intro g _
    refine ⟨e₀.permCongr g, ?_⟩
    rw [← permCongr_finEquivKSubsetOne]
    ext x
    simp [e, Equiv.permCongr_apply]
  · intro a
    have hperm : e.symm.permCongr (kSubsetPerm (a : Perm (Fin m))) =
        e₀.symm.permCongr (a : Perm (Fin m)) := by
      rw [← permCongr_finEquivKSubsetOne]
      ext x
      simp [e, Equiv.permCongr_apply]
    rw [hperm]
    apply hA
    rw [Equiv.Perm.mem_alternatingGroup]
    have ha : Perm.sign (a : Perm (Fin m)) = 1 := Equiv.Perm.mem_alternatingGroup.mp a.2
    rw [Perm.sign_permCongr, ha]

end Maroti
