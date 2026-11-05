module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Basic
import Maroti.MinDegree.Extraspecial
import CFSG.Sporadic.Co1Patterson.NativeSetting
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Local

/-!
# Conway's Sporadic Simple Group `Co₁`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Conway's group `Co₁` (Maróti, *On the orders of
primitive groups*, J. Algebra 258 (2002), Theorem 1.1).

The minimum degree lower bound `288 ≤ H.index` (hence `230 ≤ H.index` and `249 ≤ H.index`) uses
the 2-local setting `nativeSetting : Setting NativeSporadic.Co1` (`CFSG.Sporadic.Co1Patterson`),
where the centralizer `M` of a 2A-involution `aNC` has a normal extraspecial subgroup
`twoAQC = 2 ^ (1 + 8)_+` of order `2 ^ 9` with simple quotient `Mbar ≅ Ω⁺(8, 2)` of order
`174182400 > 8!` acting irreducibly on the central quotient (`32 * 9 = 288`).
-/

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Maroti

open Subgroup Module QuadraticMap
open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open CFSG.Sporadic.Co1Patterson
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open scoped commutatorElement

private lemma index_map_le_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {f : A →* B} (hf : Function.Surjective f) (N : Subgroup A) :
    (N.map f).index ≤ N.index := by
  let π : A ⧸ N → B ⧸ N.map f :=
    Quotient.lift (fun a : A => QuotientGroup.mk (f a)) fun a₁ a₂ h => by
      have h1 : (QuotientGroup.mk a₁ : A ⧸ N) = QuotientGroup.mk a₂ := Quotient.sound h
      rw [QuotientGroup.eq] at h1
      exact QuotientGroup.eq.mpr ⟨a₁⁻¹ * a₂, h1, by rw [map_mul, map_inv]⟩
  have hπ : Function.Surjective π := by
    intro q
    induction q using QuotientGroup.induction_on with | H b =>
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk a, rfl⟩
  exact Nat.card_le_card_of_surjective π hπ

private lemma index_ge_288_of_setting {G : Type} [Group G] [Finite G] (S : Setting G)
    (hΩ : S.Mbar.map S.O.subtype = CFSG.Open.timmesfeldOmega S.q)
    (h8 : finrank (ZMod 2) S.Qt = 8)
    (hcardQ : Nat.card S.Q = 2 ^ 9)
    (hcardMbar : Nat.card S.Mbar = 174182400)
    {H' : Subgroup S.M} (hzH' : ¬Subgroup.zpowers S.zM ≤ H') :
    288 ≤ H'.index := by
  have hz_not_mem : S.zM ∉ H' := fun h => hzH' (Subgroup.zpowers_le.mpr h)
  have hnot_center : ¬Subgroup.center S.Q ≤ H'.subgroupOf S.Q := by
    rw [S.center_Q_eq_zpowers_setting, Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    exact hz_not_mem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardQ' : Nat.card S.Q = 2 ^ (1 + 2 * 4) := hcardQ
  have h32 : 32 ≤ H'.relIndex S.Q :=
    pow_le_index_of_isExtraspecialPGroup S.extraspecial hcardQ' hnot_center
  have hH'_mul : H'.relIndex S.Q * (H' ⊔ S.Q).index ≤ H'.index := by
    rw [← Subgroup.relIndex_mul_index (le_sup_left : H' ≤ H' ⊔ S.Q)]
    exact Nat.mul_le_mul_right _ (relIndex_le_relIndex_of_le H' S.Q (H' ⊔ S.Q) le_sup_right)
  set Z : Subgroup S.M := Subgroup.zpowers S.zM
  set K : Subgroup S.M := H' ⊓ S.Q
  set L : Subgroup S.M := K ⊔ Z
  have hZ_le_Q : Z ≤ S.Q := Subgroup.zpowers_le.mpr S.zM_mem_Q
  have hLQ : L ≤ S.Q := sup_le inf_le_right hZ_le_Q
  have hzM_zz : S.zM * S.zM = 1 := Subtype.ext S.z_mul_z
  have hZ_comm : ∀ c : S.M, c * S.zM = S.zM * c := fun c => Subtype.ext (S.z_comm c.2)
  have hL_cases : ∀ x ∈ L, x ∈ K ∨ x * S.zM ∈ K := by
    let S_L : Subgroup S.M :=
      { carrier := {x : S.M | x ∈ K ∨ x * S.zM ∈ K}
        one_mem' := Or.inl K.one_mem
        mul_mem' := fun {a b} ha hb => by
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (K.mul_mem ha hb)
          · right
            rw [mul_assoc]
            exact K.mul_mem ha hb
          · right
            have hbz : b * S.zM = S.zM * b := hZ_comm b
            have habz : a * b * S.zM = a * S.zM * b := by rw [mul_assoc, hbz, ← mul_assoc]
            rw [habz]
            exact K.mul_mem ha hb
          · left
            have hbz : S.zM * (b * S.zM) = b * (S.zM * S.zM) := by
              calc S.zM * (b * S.zM) = (S.zM * b) * S.zM := (mul_assoc S.zM b S.zM).symm
                _ = (b * S.zM) * S.zM := by rw [hZ_comm b]
                _ = b * (S.zM * S.zM) := mul_assoc b S.zM S.zM
            have hab : a * b = (a * S.zM) * (b * S.zM) := by
              calc a * b = a * (b * (S.zM * S.zM)) := by rw [hzM_zz, mul_one]
                _ = a * (S.zM * (b * S.zM)) := by rw [← hbz]
                _ = (a * S.zM) * (b * S.zM) := (mul_assoc a S.zM (b * S.zM)).symm
            rw [hab]
            exact K.mul_mem ha hb
        inv_mem' := fun {a} ha => by
          rcases ha with ha | ha
          · exact Or.inl (K.inv_mem ha)
          · right
            have haz : a⁻¹ * S.zM = (a * S.zM)⁻¹ := by
              apply mul_left_cancel (a := a * S.zM)
              rw [mul_inv_cancel]
              calc (a * S.zM) * (a⁻¹ * S.zM) = a * (S.zM * a⁻¹) * S.zM := by group
                _ = a * (a⁻¹ * S.zM) * S.zM := by rw [hZ_comm a⁻¹]
                _ = S.zM * S.zM := by group
                _ = 1 := hzM_zz
            rw [haz]
            exact K.inv_mem ha }
    have hL_le : L ≤ S_L := by
      refine sup_le (fun k hk => Or.inl hk) ?_
      rw [Subgroup.zpowers_le]
      change S.zM ∈ K ∨ S.zM * S.zM ∈ K
      right
      rw [hzM_zz]
      exact K.one_mem
    exact fun x hx => hL_le hx
  have hQ_comm : ∀ q ∈ S.Q, ∀ r ∈ S.Q, ⁅q, r⁆ = 1 ∨ ⁅q, r⁆ = S.zM := by
    intro q hq r hr
    have hqG : (q : G) ∈ S.QG := ⟨q, hq, rfl⟩
    have hrG : (r : G) ∈ S.QG := ⟨r, hr, rfl⟩
    rcases S.commutator_eq_one_or_z hqG hrG with h1 | hz
    · left
      exact Subtype.ext h1
    · right
      exact Subtype.ext hz
  have hL_ne_Q : L ≠ S.Q := by
    intro hLQ_eq
    obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ :=
      Setting.s12_exists_not_commute_of_extraspecial S.extraspecial
    have hq₁L : q₁ ∈ L := hLQ_eq.symm ▸ hq₁
    have hq₂L : q₂ ∈ L := hLQ_eq.symm ▸ hq₂
    have hcomm_K : ∀ a b : S.M,
        (a ∈ K ∨ a * S.zM ∈ K) → (b ∈ K ∨ b * S.zM ∈ K) → ⁅a, b⁆ ∈ K := by
      intro a b ha hb
      have hz_inv : S.zM⁻¹ = S.zM := inv_eq_of_mul_eq_one_right hzM_zz
      have hcomm_z_right : ∀ x y : S.M, ⁅x, y * S.zM⁆ = ⁅x, y⁆ := fun x y => by
        simp only [commutatorElement_def, mul_inv_rev, hz_inv]
        calc x * (y * S.zM) * x⁻¹ * (S.zM * y⁻¹)
            = x * y * (S.zM * x⁻¹) * S.zM * y⁻¹ := by group
          _ = x * y * (x⁻¹ * S.zM) * S.zM * y⁻¹ := by rw [hZ_comm x⁻¹]
          _ = x * y * x⁻¹ * (S.zM * S.zM) * y⁻¹ := by group
          _ = x * y * x⁻¹ * y⁻¹ := by rw [hzM_zz, mul_one]
      have hcomm_z_left : ∀ x y : S.M, ⁅x * S.zM, y⁆ = ⁅x, y⁆ := fun x y => by
        simp only [commutatorElement_def, mul_inv_rev, hz_inv]
        calc x * S.zM * y * (S.zM * x⁻¹) * y⁻¹
            = x * (S.zM * y) * S.zM * x⁻¹ * y⁻¹ := by group
          _ = x * (y * S.zM) * S.zM * x⁻¹ * y⁻¹ := by rw [hZ_comm y]
          _ = x * y * (S.zM * S.zM) * x⁻¹ * y⁻¹ := by group
          _ = x * y * x⁻¹ * y⁻¹ := by rw [hzM_zz, mul_one]
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      · rw [← hcomm_z_right a b]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      · rw [← hcomm_z_left a b]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      · rw [← hcomm_z_left a b, ← hcomm_z_right (a * S.zM) b]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    have hq_comm_K : ⁅q₁, q₂⁆ ∈ K :=
      hcomm_K q₁ q₂ (hL_cases q₁ hq₁L) (hL_cases q₂ hq₂L)
    rcases hQ_comm q₁ hq₁ q₂ hq₂ with h1 | hz
    · exact hne (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exact hz_not_mem (hz ▸ hq_comm_K.1)
  set N : Subgroup S.M := Subgroup.normalizer (L : Set S.M)
  have hZ_le_comap : ∀ c : S.M, Z ≤ L.comap (MulAut.conj c).toMonoidHom := by
    intro c
    rw [Subgroup.zpowers_le]
    change c * S.zM * c⁻¹ ∈ L
    have hc : c * S.zM * c⁻¹ = S.zM := by rw [hZ_comm c, mul_inv_cancel_right]
    rw [hc]
    exact (le_sup_right : Z ≤ L) (Subgroup.mem_zpowers S.zM)
  have hH'_le_N : H' ≤ N := by
    refine le_normalizer_of_conj_mem fun h hh => sup_le ?_ (hZ_le_comap h)
    intro k hk
    change h * k * h⁻¹ ∈ L
    exact (le_sup_left : K ≤ L)
      ⟨H'.mul_mem (H'.mul_mem hh hk.1) (H'.inv_mem hh), S.normal.conj_mem k hk.2 h⟩
  have hQ_le_N : S.Q ≤ N := by
    refine le_normalizer_of_conj_mem fun q hq => sup_le ?_ (hZ_le_comap q)
    intro k hk
    change q * k * q⁻¹ ∈ L
    have heq : q * k * q⁻¹ = ⁅q, k⁆ * k := by simp [commutatorElement_def]
    rw [heq]
    have hcomm_L : ⁅q, k⁆ ∈ L := by
      rcases hQ_comm q hq k hk.2 with h1 | hz
      · rw [h1]
        exact L.one_mem
      · rw [hz]
        exact (le_sup_right : Z ≤ L) (Subgroup.mem_zpowers S.zM)
    exact L.mul_mem hcomm_L ((le_sup_left : K ≤ L) hk)
  have hHQ_le_N : H' ⊔ S.Q ≤ N := sup_le hH'_le_N hQ_le_N
  have hN_le_HQ : N.index ≤ (H' ⊔ S.Q).index := index_le_of_le hHQ_le_N
  have hΩ' : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate := by
    rw [hΩ, CFSG.LargeExtraspecial.s12_timmesfeldOmega_eq S.q S.q_nondegenerate]
  by_cases hN_top : N = ⊤
  · set LG : Subgroup G := L.map S.M.subtype
    have hLG_le : LG ≤ S.QG := Subgroup.map_mono hLQ
    have hz_mem_LG : S.z ∈ LG :=
      ⟨S.zM, (le_sup_right : Z ≤ L) (Subgroup.mem_zpowers S.zM), rfl⟩
    set W : Submodule (ZMod 2) S.Qt := S.clSub LG
    have hWinv : ∀ g ∈ omegaGroup S.q S.q_nondegenerate, ∀ v ∈ W,
        ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt → S.Qt) v ∈ W := by
      intro g hg v hv
      rw [← hΩ'] at hg
      obtain ⟨γ, ⟨m, rfl⟩, rfl⟩ := hg
      obtain ⟨x, ⟨y, hyL, rfl⟩, hxQ, rfl⟩ := S.mem_clSub_iff.1 hv
      have hyQ : (y : G) ∈ S.QG := hxQ
      change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (y : G)) ∈ W
      rw [S.ρ_cl m hyQ]
      have hmN : m ∈ N := by
        rw [hN_top]
        exact Subgroup.mem_top m
      have hconj_L : m * y * m⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hmN y).mp hyL
      exact S.cl_mem_clSub ⟨m * y * m⁻¹, hconj_L, rfl⟩ (S.conj_mem_QG m.2 hyQ)
    by_cases hW_bot : W = ⊥
    · have hbot : H'.subgroupOf S.Q = ⊥ := by
        rw [eq_bot_iff]
        intro q hq
        have hqK : (q : S.M) ∈ K := ⟨hq, q.2⟩
        have hqLG : ((q : S.M) : G) ∈ LG := ⟨q, (le_sup_left : K ≤ L) hqK, rfl⟩
        have hqQG : ((q : S.M) : G) ∈ S.QG := ⟨q, q.2, rfl⟩
        have hcl_mem : S.cl ((q : S.M) : G) ∈ W := S.cl_mem_clSub hqLG hqQG
        rw [hW_bot, Submodule.mem_bot] at hcl_mem
        rcases (S.cl_eq_zero_iff hqQG).mp hcl_mem with h1 | hz
        · exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h1))
        · have hqm : (q : S.M) = S.zM := Subtype.ext hz
          exact False.elim (hz_not_mem (hqm ▸ hq))
      have hrel_card : H'.relIndex S.Q = 2 ^ 9 := by
        rw [Subgroup.relIndex, hbot, Subgroup.index_bot, hcardQ]
      have hle_idx : H'.relIndex S.Q ≤ H'.index := relIndex_le_index H' S.Q
      omega
    · have hW_top : W = ⊤ :=
        eq_top_of_omega_invariant S.q_nondegenerate h8 W hWinv hW_bot
      have hLG_eq : LG = S.QG := by
        calc LG = S.clPre W := (S.clPre_clSub hLG_le hz_mem_LG).symm
          _ = S.clPre ⊤ := by rw [hW_top]
          _ = S.QG := S.clPre_top
      have hL_eq : L = S.Q := Subgroup.map_injective S.M.subtype_injective hLG_eq
      exact False.elim (hL_ne_Q hL_eq)
  · have hsimpΩ : IsSimpleGroup (omegaGroup S.q S.q_nondegenerate) :=
      CFSG.LargeExtraspecial.S45Q.isSimpleGroup_omegaGroup_of_six_le S.q_nondegenerate (by omega)
    let eΩ : S.Mbar ≃* omegaGroup S.q S.q_nondegenerate :=
      (S.Mbar.equivMapOfInjective S.O.subtype S.O.subtype_injective).trans
        (MulEquiv.subgroupCongr hΩ')
    have : IsSimpleGroup S.Mbar := eΩ.isSimpleGroup
    let ρ' : S.M →* S.Mbar := S.ρ.rangeRestrict
    have hρ's : Function.Surjective ρ' := S.ρ.rangeRestrict_surjective
    have hker : ∀ m : S.M, ρ' m = 1 ↔ m ∈ S.Q := fun m =>
      ⟨fun h => S.mem_Q_of_ρ_eq_one (congrArg Subtype.val h),
       fun h => Subtype.ext (S.ρ_eq_one_of_mem_Q h)⟩
    let P : Subgroup S.Mbar := N.map ρ'
    have hP_ne_top : P ≠ ⊤ := by
      intro hP_top
      apply hN_top
      rw [eq_top_iff]
      intro m _
      have hmP : ρ' m ∈ P := hP_top ▸ Subgroup.mem_top _
      obtain ⟨n, hnN, hnm⟩ := hmP
      have h1 : ρ' (n⁻¹ * m) = 1 := by rw [map_mul, map_inv, hnm, inv_mul_cancel]
      have h2 : n⁻¹ * m ∈ N := hQ_le_N ((hker _).mp h1)
      have heq : m = n * (n⁻¹ * m) := by group
      rw [heq]
      exact N.mul_mem hnN h2
    have hcard_le : Nat.card S.Mbar ≤ P.index.factorial :=
      card_le_index_factorial_of_ne_top hP_ne_top
    have h9 : 9 ≤ P.index := by
      by_contra! hlt
      have hle8 : P.index ≤ 8 := by omega
      have hfact : P.index.factorial ≤ (8 : ℕ).factorial := Nat.factorial_le hle8
      have h8fact : (8 : ℕ).factorial = 40320 := by decide
      omega
    have hP_le_N : P.index ≤ N.index := index_map_le_of_surjective hρ's N
    have h288 : 32 * 9 ≤ H'.relIndex S.Q * (H' ⊔ S.Q).index :=
      Nat.mul_le_mul h32 (by omega)
    omega

private lemma le_index_of_setting {S : Type*} {G : Type} [Group S] [Group G] [Finite S] [Finite G]
    [IsSimpleGroup S] (e : S ≃* G) {H : Subgroup S} (hH : H ≠ ⊤)
    (S₀ : Setting G)
    (hΩ : S₀.Mbar.map S₀.O.subtype = CFSG.Open.timmesfeldOmega S₀.q)
    (h8 : finrank (ZMod 2) S₀.Qt = 8)
    (hcardQ : Nat.card S₀.Q = 2 ^ 9)
    (hcardMbar : Nat.card S₀.Mbar = 174182400) :
    288 ≤ H.index := by
  have hz1 : S₀.zM ≠ 1 := fun h => S₀.z_ne_one (congrArg Subtype.val h)
  exact le_index_of_injective_of_forall_not_le_index hH
    (f := e.symm.toMonoidHom.comp S₀.M.subtype)
    (e.symm.injective.comp S₀.M.subtype_injective)
    (Subgroup.zpowers_ne_bot.mpr hz1)
    fun H' hzH' => index_ge_288_of_setting S₀ hΩ h8 hcardQ hcardMbar hzH'

private theorem index_ge_288_Co1 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Co1) {H : Subgroup S} (hH : H ≠ ⊤) :
    288 ≤ H.index := by
  have hfin : Finite NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  have hΩ : nativeSetting.Mbar.map nativeSetting.O.subtype =
      CFSG.Open.timmesfeldOmega nativeSetting.q :=
    map_Mbar_eq_omega_of_card nativeSetting width_nativeSetting card_Mbar_nativeSetting
  have h8 : finrank (ZMod 2) nativeSetting.Qt = 8 := by
    rw [nativeSetting.finrank_Qt_eq_two_mul_width, width_nativeSetting]
  exact @le_index_of_setting S NativeSporadic.Co1 _ Units.instGroup _ hfin _ e H hH
    nativeSetting hΩ h8 card_twoAQC card_Mbar_nativeSetting

/-- Every proper subgroup of `Co₁` has index at least `230`. -/
theorem index_ge_Co1 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Co1) {H : Subgroup S} (hH : H ≠ ⊤) :
    230 ≤ H.index :=
  le_trans (by decide : 230 ≤ 288) (index_ge_288_Co1 e hH)

/-- Maróti's bound for primitive almost simple groups with socle `Co₁`. -/
theorem sporadicCase_Co1 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Co1)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 4157776806543360000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co1.card_Co1
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 249) (c := 2) (by decide)
    (fun H hH => le_trans (by decide : 249 ≤ 288) (index_ge_288_Co1 e hH))
    (card_outer_dvd_two_of_sporadicSocle ⟨.Co1, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
