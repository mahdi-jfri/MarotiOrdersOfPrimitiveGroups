module

public import Maroti.Alternating.AutBound
public import Maroti.Alternating.Bochert
public import Maroti.Alternating.Bound
public import Maroti.Alternating.SubsetAction
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Almost simple setup and small alternating socles (`m = 5` and `m = 6`)

This file establishes the general structure of a primitive permutation group `G ≤ Perm α` that is
almost simple with socle isomorphic to `alternatingGroup (Fin m)` (`5 ≤ m`), and completes the
proof of `Maroti.AlmostSimpleConclusion G` in the cases `m = 5` and `m = 6` (Maróti, Section 2,
Step 3, page 635).

For any `5 ≤ m`, the socle `T` has order `m! / 2`, acts transitively on `α` with `m ≤ Nat.card α`,
and embeds `G` injectively into `MulAut (alternatingGroup (Fin m))` by conjugation
(`almostSimple_alternating_setup`). When `m = 5`, either `Nat.card α = 5` and `G` contains
`alternatingGroup α` (`IsSubsetActionType G`), or `6 ≤ Nat.card α` and
`Nat.card G ≤ 120 ≤ bound (Nat.card α)` (`alternatingCase_five`). When `m = 6`, the automorphism
bound `Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ 1440` from
`CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le`
(`CFSG/HardMathSupport/Timmesfeld/Balance/Alt/AutSix.lean`) together with the nonexistence of
order-45 subgroups in `Perm (Fin 6)` (`card_subgroup_perm_fin_six_ne_45`) shows that either
`Nat.card α = 6` (`IsSubsetActionType G`) or `9 ≤ Nat.card α` and
`Nat.card G ≤ 1440 ≤ bound (Nat.card α)` (`alternatingCase_six`). Finally, when `5 ≤ m` and
`m ≠ 6`, `permMulEquivMulAutAlternating` embeds `G` into `Perm (Fin m)` as a subgroup containing
`alternatingGroup (Fin m)` (`exists_injective_hom_perm_of_ne_six`).
-/

@[expose] public section

namespace Maroti.Alternating

open Equiv Equiv.Perm MulAction Subgroup
open scoped Nat

/-- No subgroup of `Perm (Fin 6)` has cardinality `45`. -/
theorem card_subgroup_perm_fin_six_ne_45 (K : Subgroup (Perm (Fin 6))) :
    Nat.card K ≠ 45 := by
  intro hK
  set K₀ := fixingSubgroup K (({(0 : Fin 6)} : Finset (Fin 6)) : Set (Fin 6))
  set K₁ := fixingSubgroup K (({(1 : Fin 6)} : Finset (Fin 6)) : Set (Fin 6))
  set K₀₁ := fixingSubgroup K (({(0 : Fin 6), 1} : Finset (Fin 6)) : Set (Fin 6))
  have h1_card : ∀ x : Fin 6,
      Nat.card (fixingSubgroup K (({x} : Finset (Fin 6)) : Set (Fin 6))) ∣ 120 ∧
      (fixingSubgroup K (({x} : Finset (Fin 6)) : Set (Fin 6))).index ≤ 6 := by
    intro x
    set Kx := fixingSubgroup K (({x} : Finset (Fin 6)) : Set (Fin 6))
    set Px := fixingSubgroup (Perm (Fin 6)) (({x} : Finset (Fin 6)) : Set (Fin 6))
    have hPx_card : Nat.card Px = 120 := by
      rw [nat_card_fixingSubgroup_perm ({x} : Finset (Fin 6)), Fintype.card_fin,
        Finset.card_singleton]
      decide
    have hPx_idx : Px.index = 6 := by
      have hmul := Subgroup.card_mul_index Px
      rw [hPx_card, Nat.card_perm, Nat.card_fin] at hmul
      have : 6 ! = 720 := by decide
      omega
    let ι : Kx →* Px :=
      { toFun := fun k => ⟨k.1.1, (mem_fixingSubgroup_iff (Perm (Fin 6))).mpr
          ((mem_fixingSubgroup_iff K).mp k.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι_inj : Function.Injective ι :=
      fun a b heq => Subtype.ext (Subtype.ext (Subtype.mk.inj heq))
    have hdvd : Nat.card Kx ∣ 120 := by
      rw [← hPx_card]
      exact Subgroup.card_dvd_of_injective ι hι_inj
    let f : K ⧸ Kx → Perm (Fin 6) ⧸ Px :=
      Quotient.lift (fun k : K => ((k.1 : Perm (Fin 6)) : Perm (Fin 6) ⧸ Px)) (by
        intro a b hab
        apply Quotient.sound
        have hab' : a⁻¹ * b ∈ Kx := QuotientGroup.leftRel_apply.mp hab
        exact QuotientGroup.leftRel_apply.mpr
          ((mem_fixingSubgroup_iff (Perm (Fin 6))).mpr
            ((mem_fixingSubgroup_iff K).mp hab')))
    have hf_inj : Function.Injective f := by
      rintro ⟨a⟩ ⟨b⟩ heq
      apply Quotient.sound
      have hab : a.1⁻¹ * b.1 ∈ Px := QuotientGroup.leftRel_apply.mp (Quotient.exact heq)
      exact QuotientGroup.leftRel_apply.mpr
        ((mem_fixingSubgroup_iff K).mpr
          ((mem_fixingSubgroup_iff (Perm (Fin 6))).mp hab))
    have hidx : Kx.index ≤ 6 := (Nat.card_le_card_of_injective f hf_inj).trans hPx_idx.le
    exact ⟨hdvd, hidx⟩
  obtain ⟨⟨c₀, hc₀⟩, hK₀_idx⟩ := h1_card 0
  obtain ⟨⟨c₁, hc₁⟩, hK₁_idx⟩ := h1_card 1
  change 120 = Nat.card K₀ * c₀ at hc₀
  change K₀.index ≤ 6 at hK₀_idx
  change 120 = Nat.card K₁ * c₁ at hc₁
  change K₁.index ≤ 6 at hK₁_idx
  have hK₀_mul : Nat.card K₀ * K₀.index = 45 := (Subgroup.card_mul_index K₀).trans hK
  have hK₁_mul : Nat.card K₁ * K₁.index = 45 := (Subgroup.card_mul_index K₁).trans hK
  have hK₀_eq : Nat.card K₀ = 15 := by
    have : K₀.index = 0 ∨ K₀.index = 1 ∨ K₀.index = 2 ∨ K₀.index = 3 ∨
        K₀.index = 4 ∨ K₀.index = 5 ∨ K₀.index = 6 := by omega
    rcases this with h | h | h | h | h | h | h <;>
      first
      | { rw [h] at hK₀_mul; omega }
      | { rw [h] at hK₀_mul
          have hk : Nat.card K₀ = 45 ∨ Nat.card K₀ = 9 := by omega
          rcases hk with hk | hk <;> { rw [hk] at hc₀; omega } }
  have hK₁_idx_eq : K₁.index = 3 := by
    have : K₁.index = 0 ∨ K₁.index = 1 ∨ K₁.index = 2 ∨ K₁.index = 3 ∨
        K₁.index = 4 ∨ K₁.index = 5 ∨ K₁.index = 6 := by omega
    rcases this with h | h | h | h | h | h | h <;>
      first
      | { rw [h] at hK₁_mul; omega }
      | { rw [h] at hK₁_mul
          have hk : Nat.card K₁ = 45 ∨ Nat.card K₁ = 9 := by omega
          rcases hk with hk | hk <;> { rw [hk] at hc₁; omega } }
  set P₀₁ := fixingSubgroup (Perm (Fin 6)) (({(0 : Fin 6), 1} : Finset (Fin 6)) : Set (Fin 6))
  have hP₀₁_card : Nat.card P₀₁ = 24 := by
    rw [nat_card_fixingSubgroup_perm ({(0 : Fin 6), 1} : Finset (Fin 6)), Fintype.card_fin]
    decide
  let ι₀₁ : K₀₁ →* P₀₁ :=
    { toFun := fun k => ⟨k.1.1, (mem_fixingSubgroup_iff (Perm (Fin 6))).mpr
        ((mem_fixingSubgroup_iff K).mp k.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι₀₁_inj : Function.Injective ι₀₁ :=
    fun a b heq => Subtype.ext (Subtype.ext (Subtype.mk.inj heq))
  have hK₀₁_dvd : Nat.card K₀₁ ∣ 24 := by
    rw [← hP₀₁_card]
    exact Subgroup.card_dvd_of_injective ι₀₁ hι₀₁_inj
  have hK₀₁_le : K₀₁ ≤ K₀ := by
    intro k hk
    rw [mem_fixingSubgroup_iff] at hk ⊢
    intro y hy
    exact hk y (by simp [Finset.mem_singleton.mp (Finset.mem_coe.mp hy)])
  set L := K₀₁.subgroupOf K₀
  have hL_card : Nat.card L = Nat.card K₀₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀₁_le).toEquiv
  have hL_mul : Nat.card K₀₁ * L.index = 15 := by
    rw [← hL_card, ← hK₀_eq]
    exact Subgroup.card_mul_index L
  let q : K₀ ⧸ L → K ⧸ K₁ :=
    Quotient.lift (fun x : K₀ => ((x.1 : K) : K ⧸ K₁)) (by
      intro a b hab
      apply Quotient.sound
      have hab' : (a⁻¹ * b).1 ∈ K₀₁ :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)
      refine QuotientGroup.leftRel_apply.mpr ((mem_fixingSubgroup_iff K).mpr ?_)
      intro y hy
      rw [Finset.mem_singleton.mp (Finset.mem_coe.mp hy)]
      exact (mem_fixingSubgroup_iff K).mp hab' 1 (by simp))
  have hq_inj : Function.Injective q := by
    rintro ⟨a⟩ ⟨b⟩ heq
    apply Quotient.sound
    have hab : a.1⁻¹ * b.1 ∈ K₁ := QuotientGroup.leftRel_apply.mp (Quotient.exact heq)
    refine QuotientGroup.leftRel_apply.mpr
      (Subgroup.mem_subgroupOf.mpr ((mem_fixingSubgroup_iff K).mpr ?_))
    intro y hy
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with rfl | hy1
    · exact (mem_fixingSubgroup_iff K).mp (K₀.mul_mem (K₀.inv_mem a.2) b.2) 0 (by simp)
    · rw [Finset.mem_singleton.mp hy1]
      exact (mem_fixingSubgroup_iff K).mp hab 1 (by simp)
  have hL_idx_le : L.index ≤ 3 := (Nat.card_le_card_of_injective q hq_inj).trans hK₁_idx_eq.le
  rcases hK₀₁_dvd with ⟨d, hd⟩
  have : L.index = 0 ∨ L.index = 1 ∨ L.index = 2 ∨ L.index = 3 := by omega
  rcases this with h | h | h | h <;>
    first
    | { rw [h] at hL_mul; omega }
    | { rw [h] at hL_mul
        have hk : Nat.card K₀₁ = 15 ∨ Nat.card K₀₁ = 5 := by omega
        rcases hk with hk | hk <;> { rw [hk] at hd; omega } }

/-- Given `IsAlmostSimpleWith G S` and `eS : S ≃* alternatingGroup (Fin m)` (`5 ≤ m`),
construct the socle `T ≤ G`, the isomorphism `eT : T ≃* alternatingGroup (Fin m)`,
and the injective conjugation homomorphism `fAut : G →* MulAut (alternatingGroup (Fin m))`. -/
theorem almostSimple_alternating_setup {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) {S : Type*} [Group S]
    (hG : IsPreprimitive G α) (hS : IsAlmostSimpleWith G S)
    {m : ℕ} (hm : 5 ≤ m) (eS : S ≃* alternatingGroup (Fin m)) :
    m ≤ Nat.card α ∧
    ∃ (T : Subgroup (Perm α)) (hTG : T ≤ G) (eT : T ≃* alternatingGroup (Fin m))
      (fAut : G →* MulAut (alternatingGroup (Fin m))),
      Nat.card T = m ! / 2 ∧
      IsPretransitive T α ∧
      Function.Injective fAut ∧
      ∀ a : alternatingGroup (Fin m),
        fAut ⟨(eT.symm a).1, hTG (eT.symm a).2⟩ = MulAut.conjNormal (a : Perm (Fin m)) := by
  obtain ⟨T, hTG, hT_norm, _, _, hT_cent, ⟨eTS⟩⟩ := hS
  let eT : T ≃* alternatingGroup (Fin m) := eTS.trans eS
  have hT_card : Nat.card T = m ! / 2 := by
    rw [Nat.card_congr eT.toEquiv, nat_card_alternatingGroup_fin (by omega)]
  have hm_le_card : m ≤ Nat.card α := by
    have hT_le_perm : Nat.card T ≤ (Nat.card α)! := by
      have := Subgroup.card_le_card_group T
      rwa [Nat.card_perm] at this
    by_contra hlt
    have hle : (Nat.card α)! ≤ (m - 1)! := Nat.factorial_le (by omega)
    have hm_fact : m ! = m * (m - 1)! := by
      cases m with
      | zero => omega
      | succ k => simp [Nat.factorial_succ]
    have hpos : 1 ≤ (m - 1)! := Nat.factorial_pos (m - 1)
    have h5 : 5 * (m - 1)! ≤ m * (m - 1)! := Nat.mul_le_mul_right _ hm
    omega
  let conjT : G →* MulAut T :=
    { toFun := fun g =>
        { toFun := fun t => ⟨g.1 * t.1 * g.1⁻¹, hT_norm g.1 g.2 t.1 t.2⟩
          invFun := fun t => ⟨g.1⁻¹ * t.1 * (g.1⁻¹)⁻¹, hT_norm g.1⁻¹ (G.inv_mem g.2) t.1 t.2⟩
          left_inv := fun t => Subtype.ext (by simp; group)
          right_inv := fun t => Subtype.ext (by simp; group)
          map_mul' := fun t₁ t₂ => Subtype.ext (by
            change g.1 * (t₁.1 * t₂.1) * g.1⁻¹ = (g.1 * t₁.1 * g.1⁻¹) * (g.1 * t₂.1 * g.1⁻¹)
            group) }
      map_one' := MulEquiv.ext fun t => Subtype.ext (by simp)
      map_mul' := fun g₁ g₂ => MulEquiv.ext fun t => Subtype.ext (by
        change (g₁.1 * g₂.1) * t.1 * (g₁.1 * g₂.1)⁻¹ = g₁.1 * (g₂.1 * t.1 * g₂.1⁻¹) * g₁.1⁻¹
        group) }
  have hconjT_inj : Function.Injective conjT := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    apply hT_cent g.1 g.2
    intro t ht
    have hgt : (conjT g ⟨t, ht⟩).1 = t := by
      rw [hg]
      rfl
    change g.1 * t * g.1⁻¹ = t at hgt
    exact mul_inv_eq_iff_eq_mul.mp hgt
  let fAut : G →* MulAut (alternatingGroup (Fin m)) :=
    (MulAut.congr eT).toMonoidHom.comp conjT
  have hfAut_inj : Function.Injective fAut := (MulAut.congr eT).injective.comp hconjT_inj
  have hfAut_alt : ∀ a : alternatingGroup (Fin m),
      fAut ⟨(eT.symm a).1, hTG (eT.symm a).2⟩ = MulAut.conjNormal (a : Perm (Fin m)) := by
    intro a
    refine MulEquiv.ext fun b => Subtype.ext ?_
    have hconj : conjT ⟨(eT.symm a).1, hTG (eT.symm a).2⟩ (eT.symm b) =
        eT.symm a * eT.symm b * (eT.symm a)⁻¹ := rfl
    change (eT (conjT ⟨(eT.symm a).1, hTG (eT.symm a).2⟩ (eT.symm b))).1 =
      (a * b * a⁻¹).1
    rw [hconj, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hT_trans : IsPretransitive T α := by
    set N := T.subgroupOf G
    have hN_normal : N.Normal :=
      ⟨fun n hn g => hT_norm g.1 g.2 n.1 hn⟩
    have hT_nt : Nontrivial T := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      have : 120 ≤ m ! := (by decide : 120 ≤ 5 !).trans (Nat.factorial_le hm)
      omega
    obtain ⟨t, ht_ne⟩ := exists_ne (1 : T)
    have ht_ne' : t.1 ≠ 1 := fun h => ht_ne (Subtype.ext h)
    have h_not_fix : ∃ x : α, t.1 x ≠ x := by
      by_contra hall
      push Not at hall
      exact ht_ne' (Equiv.ext hall)
    obtain ⟨x₀, hx₀⟩ := h_not_fix
    have hN_fp : fixedPoints N α ≠ Set.univ := by
      intro huniv
      have hx₀_fp : x₀ ∈ fixedPoints N α := huniv ▸ Set.mem_univ x₀
      have hfix := hx₀_fp ⟨⟨t.1, hTG t.2⟩, t.2⟩
      exact hx₀ hfix
    have hN_trans : IsPretransitive N α :=
      IsQuasiPreprimitive.isPretransitive_of_normal hN_fp
    refine ⟨fun x y => ?_⟩
    obtain ⟨⟨⟨g, hgG⟩, hgT⟩, rfl⟩ := hN_trans.exists_smul_eq x y
    exact ⟨⟨g, hgT⟩, rfl⟩
  exact ⟨hm_le_card, T, hTG, eT, fAut, hT_card, hT_trans, hfAut_inj, hfAut_alt⟩

/-- The conclusion `AlmostSimpleConclusion G` holds when `G` has socle
`alternatingGroup (Fin 5)`. -/
theorem alternatingCase_five {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) {S : Type*} [Group S]
    (hG : IsPreprimitive G α) (hS : IsAlmostSimpleWith G S)
    (eS : S ≃* alternatingGroup (Fin 5)) :
    AlmostSimpleConclusion G := by
  obtain ⟨h5_le, T, hTG, _, fAut, hT_card, _, hfAut_inj, _⟩ :=
    almostSimple_alternating_setup G hG hS (by decide : 5 ≤ 5) eS
  have hT_card60 : Nat.card T = 60 := by
    rw [hT_card]
    decide
  have hG_le120 : Nat.card G ≤ 120 := by
    let eAut := permMulEquivMulAutAlternating (by decide : 5 ≤ 5) (by decide : 5 ≠ 6)
    have hAut_card : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
      rw [← Nat.card_congr eAut.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    rw [← hAut_card]
    exact Nat.card_le_card_of_injective fAut hfAut_inj
  by_cases hn5 : Nat.card α = 5
  · left
    apply isSubsetActionType_of_alternatingGroup_le G h5_le
    apply alternatingGroup_le_of_index_le_two
    have hT_le_G : 60 ≤ Nat.card G := by
      rw [← hT_card60]
      exact Subgroup.card_le_of_le hTG
    have hmul := Subgroup.card_mul_index G
    rw [Nat.card_perm, hn5] at hmul
    have : 5 ! = 120 := by decide
    by_contra hlt
    have : 60 * 3 ≤ Nat.card G * G.index := Nat.mul_le_mul hT_le_G (by omega)
    omega
  · right; right
    have hn6 : 6 ≤ Nat.card α := by omega
    have hb6 : 120 ≤ bound 6 := by decide
    exact (hG_le120.trans hb6).trans (bound_mono hn6)

/-- The conclusion `AlmostSimpleConclusion G` holds when `G` has socle
`alternatingGroup (Fin 6)`. -/
theorem alternatingCase_six {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) {S : Type*} [Group S]
    (hG : IsPreprimitive G α) (hS : IsAlmostSimpleWith G S)
    (eS : S ≃* alternatingGroup (Fin 6)) :
    AlmostSimpleConclusion G := by
  obtain ⟨h6_le, T, hTG, eT, fAut, hT_card, hT_trans, hfAut_inj, _⟩ :=
    almostSimple_alternating_setup G hG hS (by decide : 5 ≤ 6) eS
  have hT_card360 : Nat.card T = 360 := by
    rw [hT_card]
    decide
  obtain ⟨hAut_fin, hAut_le1440⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.finite_and_card_mulAut_alternatingGroup_six_le
  have hG_le1440 : Nat.card G ≤ 1440 :=
    (Nat.card_le_card_of_injective fAut hfAut_inj).trans hAut_le1440
  by_cases hn6 : Nat.card α = 6
  · left
    apply isSubsetActionType_of_alternatingGroup_le G (by omega)
    apply alternatingGroup_le_of_index_le_two
    have hT_le_G : 360 ≤ Nat.card G := by
      rw [← hT_card360]
      exact Subgroup.card_le_of_le hTG
    have hmul := Subgroup.card_mul_index G
    rw [Nat.card_perm, hn6] at hmul
    have : 6 ! = 720 := by decide
    by_contra hlt
    have : 360 * 3 ≤ Nat.card G * G.index := Nat.mul_le_mul hT_le_G (by omega)
    omega
  · right; right
    have hα_ne : Nonempty α := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card α)).1
    obtain ⟨ω⟩ := hα_ne
    have horb : orbit T ω = Set.univ := orbit_eq_univ T ω
    let eUniv : α ≃ orbit T ω :=
      { toFun := fun x => ⟨x, horb.symm ▸ Set.mem_univ x⟩
        invFun := fun x => x.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let eOrb : α ≃ T ⧸ stabilizer T ω := eUniv.trans (orbitEquivQuotientStabilizer T ω)
    have hn_idx : Nat.card α = (stabilizer T ω).index := Nat.card_congr eOrb
    have hmul_T : Nat.card (stabilizer T ω) * Nat.card α = 360 := by
      rw [hn_idx, ← hT_card360]
      exact Subgroup.card_mul_index (stabilizer T ω)
    let ι : T →* Perm (Fin 6) := (alternatingGroup (Fin 6)).subtype.comp eT.toMonoidHom
    have hι_inj : Function.Injective ι :=
      Subtype.val_injective.comp eT.injective
    set K := (stabilizer T ω).map ι
    have hK_card : Nat.card K = Nat.card (stabilizer T ω) :=
      Nat.card_congr ((stabilizer T ω).equivMapOfInjective ι hι_inj).symm.toEquiv
    have hK_ne45 : Nat.card (stabilizer T ω) ≠ 45 := by
      rw [← hK_card]
      exact card_subgroup_perm_fin_six_ne_45 K
    have hn9 : 9 ≤ Nat.card α := by
      by_contra hlt9
      have : Nat.card α = 7 ∨ Nat.card α = 8 := by omega
      rcases this with h7 | h8
      · rw [h7] at hmul_T
        omega
      · rw [h8] at hmul_T
        exact hK_ne45 (by omega)
    have hb9 : 1440 ≤ bound 9 := by decide
    exact (hG_le1440.trans hb9).trans (bound_mono hn9)

/-- For `5 ≤ m` with `m ≠ 6`, construct the injective homomorphism `ψ : G →* Perm (Fin m)`
embedding `G` into `Perm (Fin m)` with `alternatingGroup (Fin m) ≤ ψ.range`. -/
theorem exists_injective_hom_perm_of_ne_six {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) {S : Type*} [Group S]
    (hG : IsPreprimitive G α) (hS : IsAlmostSimpleWith G S)
    {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6) (eS : S ≃* alternatingGroup (Fin m)) :
    m ≤ Nat.card α ∧
    ∃ (T : Subgroup (Perm α)) (hTG : T ≤ G) (eT : T ≃* alternatingGroup (Fin m))
      (ψ : G →* Perm (Fin m)),
      Function.Injective ψ ∧
      alternatingGroup (Fin m) ≤ ψ.range ∧
      ∀ a : alternatingGroup (Fin m),
        ψ ⟨(eT.symm a).1, hTG (eT.symm a).2⟩ = (a : Perm (Fin m)) := by
  obtain ⟨hm_le, T, hTG, eT, fAut, _, _, hfAut_inj, hfAut_alt⟩ :=
    almostSimple_alternating_setup G hG hS hm eS
  let eAut := permMulEquivMulAutAlternating hm hm6
  let ψ : G →* Perm (Fin m) := eAut.symm.toMonoidHom.comp fAut
  have hψ_inj : Function.Injective ψ := eAut.symm.injective.comp hfAut_inj
  have hψ_alt : ∀ a : alternatingGroup (Fin m),
      ψ ⟨(eT.symm a).1, hTG (eT.symm a).2⟩ = (a : Perm (Fin m)) := by
    intro a
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe]
    rw [hfAut_alt a]
    exact eAut.symm_apply_apply (a : Perm (Fin m))
  have hA_le : alternatingGroup (Fin m) ≤ ψ.range := by
    intro h hh
    exact ⟨⟨(eT.symm ⟨h, hh⟩).1, hTG (eT.symm ⟨h, hh⟩).2⟩, hψ_alt ⟨h, hh⟩⟩
  exact ⟨hm_le, T, hTG, eT, ψ, hψ_inj, hA_le, hψ_alt⟩

end Maroti.Alternating
