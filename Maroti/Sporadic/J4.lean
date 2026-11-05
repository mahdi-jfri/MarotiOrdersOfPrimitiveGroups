module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Basic
import Maroti.MinDegree.Extraspecial
import CFSG.Sporadic.J4
import CFSG.Sporadic.Schreier.J4SElevenBase1
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeCore

/-!
# Sporadic Simple Group `J₄`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Janko's fourth group `J₄` (Maróti, *On the orders of
primitive groups*, J. Algebra 258 (2002), Theorem 1.1).

The minimum degree lower bound `363 ≤ H.index` (hence `256 ≤ H.index`) uses the extraspecial
Sylow `11`-subgroup `Q11` of order `11 ^ 3` and its normalizer element `nrm₁` from
`CFSG.Sporadic.Schreier.J4SElevenBase1`, which acts irreducibly on `Q11 / Z(Q11) ≅ (ZMod 11) ^ 2`.
-/

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Maroti

open CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open CFSG.AGLEmbedding.KFactProofs.OrbitsCube
open scoped commutatorElement

private lemma three_le_relIndex_of_not_mem {G : Type*} [Group G] [Finite G] {M N : Subgroup G}
    {g : G} (hgN : g ∈ N) (hg1 : g ∉ M) (hg2 : g ^ 2 ∉ M) :
    3 ≤ M.relIndex N := by
  let f : Fin 3 → N ⧸ M.subgroupOf N := fun i =>
    match i with
    | ⟨0, _⟩ => QuotientGroup.mk 1
    | ⟨1, _⟩ => QuotientGroup.mk ⟨g, hgN⟩
    | ⟨2, _⟩ => QuotientGroup.mk ⟨g ^ 2, N.pow_mem hgN 2⟩
  have hinj : Function.Injective f := by
    intro a b hij
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      have h := QuotientGroup.eq.mp hij
      rw [inv_one, one_mul, Subgroup.mem_subgroupOf] at h
      exact hg1 h
    · exfalso
      have h := QuotientGroup.eq.mp hij
      rw [inv_one, one_mul, Subgroup.mem_subgroupOf] at h
      exact hg2 h
    · exfalso
      have h := QuotientGroup.eq.mp hij.symm
      rw [inv_one, one_mul, Subgroup.mem_subgroupOf] at h
      exact hg1 h
    · rfl
    · exfalso
      have h := QuotientGroup.eq.mp hij
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
      change g⁻¹ * g ^ 2 ∈ M at h
      rw [sq, inv_mul_cancel_left] at h
      exact hg1 h
    · exfalso
      have h := QuotientGroup.eq.mp hij.symm
      rw [inv_one, one_mul, Subgroup.mem_subgroupOf] at h
      exact hg2 h
    · exfalso
      have h := QuotientGroup.eq.mp hij.symm
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
      change g⁻¹ * g ^ 2 ∈ M at h
      rw [sq, inv_mul_cancel_left] at h
      exact hg1 h
    · rfl
  have hcard := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_fin] at hcard

private lemma nrm1_Δ :
    ∀ i j : ZMod 11, (i ≠ 0 ∨ j ≠ 0) →
      i * ((3 : ℕ) * i + (3 : ℕ) * j) - j * ((7 : ℕ) * i + (3 : ℕ) * j) ≠ 0 := by
  decide

private lemma nrm1_sq_Δ :
    ∀ i j : ZMod 11, (i ≠ 0 ∨ j ≠ 0) →
      i * ((30 : ℕ) * i + (18 : ℕ) * j) - j * ((58 : ℕ) * i + (30 : ℕ) * j) ≠ 0 := by
  decide

private lemma commutator_nrm1_ne_one {t : J} (ht : t ∈ Q11)
    (htZ : (⟨t, ht⟩ : Q11) ∉ Subgroup.center Q11) :
    ⁅t, nrm₁ * t * nrm₁⁻¹⁆ ≠ 1 := by
  have hp : Nat.Prime 11 := by norm_num
  have hnc : ∃ a ∈ Q11, ∃ b ∈ Q11, a * b ≠ b * a := by
    refine ⟨qx, qx_mem, qy, qy_mem, fun h => qz_ne_one ?_⟩
    exact commutatorElement_eq_one_iff_mul_comm.mpr h
  have htn : ∃ b' ∈ Q11, t * b' ≠ b' * t := by
    by_contra! hall
    apply htZ
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (hall b b.2).symm
  exact noncomm_conj_of_anisotropic hp Q11 card_Q11 hnc rfl qx_pow_eleven qy_pow_eleven
    qz_ne_one nrm₁_mem_normalizer 7 3 3 3 2 9 nrm₁_qx nrm₁_qy nrm1_Δ ht htn

private lemma commutator_nrm1_sq_ne_one {t : J} (ht : t ∈ Q11)
    (htZ : (⟨t, ht⟩ : Q11) ∉ Subgroup.center Q11) :
    ⁅t, nrm₁ ^ 2 * t * (nrm₁ ^ 2)⁻¹⁆ ≠ 1 := by
  have hp : Nat.Prime 11 := by norm_num
  have : Fact (Nat.Prime 11) := ⟨hp⟩
  have hclass : commutator Q11 ≤ Subgroup.center Q11 := commutator_Q11.le
  obtain ⟨xS, hxc⟩ : ∃ xS : Q11, (xS : J) = qx := ⟨⟨qx, qx_mem⟩, rfl⟩
  obtain ⟨yS, hyc⟩ : ∃ yS : Q11, (yS : J) = qy := ⟨⟨qy, qy_mem⟩, rfl⟩
  have hcomm_coe : ∀ u v : Q11, (((⁅u, v⁆ : Q11)) : J) = ⁅(u : J), (v : J)⁆ := fun u v => by
    simp [commutatorElement_def]
  have hxp : xS ^ 11 = 1 := pow_eleven_Q11 xS
  have hyp : yS ^ 11 = 1 := pow_eleven_Q11 yS
  have hz1 : (⁅xS, yS⁆ : Q11) ≠ 1 := by
    intro h1
    apply qz_ne_one
    have := congrArg Subtype.val h1
    rw [hcomm_coe, hxc, hyc] at this
    exact this
  have hgen : Subgroup.closure ({xS, yS} : Set Q11) = ⊤ := by
    have h1 : ({xS, yS} : Set Q11) = ((↑) : Q11 → J) ⁻¹' ({qx, qy} : Set J) := by
      ext u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro (rfl | rfl)
        · left; exact hxc
        · right; exact hyc
      · rintro (h | h)
        · left; exact Subtype.ext (h.trans hxc.symm)
        · right; exact Subtype.ext (h.trans hyc.symm)
    rw [h1]
    exact Subgroup.closure_closure_coe_preimage
  obtain ⟨α, hα⟩ : ∃ α : MulAut Q11, ∀ u : Q11, ((α u : Q11) : J) = nrm₁ * u * nrm₁⁻¹ :=
    ⟨Q11.normalizerMonoidHom ⟨nrm₁, nrm₁_mem_normalizer⟩, fun _ => rfl⟩
  have hαx : α xS = xS ^ 7 * yS ^ 3 * (⁅xS, yS⁆ : Q11) ^ 2 := by
    apply Subtype.ext
    rw [hα, hxc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
      Subgroup.coe_pow, hcomm_coe, hxc, hyc]
    exact nrm₁_qx
  have hαy : α yS = xS ^ 3 * yS ^ 3 * (⁅xS, yS⁆ : Q11) ^ 9 := by
    apply Subtype.ext
    rw [hα, hyc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
      Subgroup.coe_pow, hcomm_coe, hxc, hyc]
    exact nrm₁_qy
  obtain ⟨i, j, w, hw, ht_eq⟩ :=
    exists_normalForm (by norm_num : 0 < 11) hclass hgen hxp hyp (⟨t, ht⟩ : Q11)
  obtain ⟨w₁, hw₁, hα1⟩ := map_normalForm hclass xS yS α 7 3 3 3 2 9 i j hw hαx hαy
  obtain ⟨w₂, hw₂, hα2⟩ :=
    map_normalForm hclass xS yS α 7 3 3 3 2 9 (7 * i + 3 * j) (3 * i + 3 * j) hw₁ hαx hαy
  have hlin1 : 7 * (7 * i + 3 * j) + 3 * (3 * i + 3 * j) = 58 * i + 30 * j := by ring
  have hlin2 : 3 * (7 * i + 3 * j) + 3 * (3 * i + 3 * j) = 30 * i + 18 * j := by ring
  rw [hlin1, hlin2] at hα2
  have hcomm_eq : ⁅(⟨t, ht⟩ : Q11), α (α ⟨t, ht⟩)⁆ =
      (⁅xS, yS⁆ : Q11) ^ ((30 * i + 18 * j) * i) *
        ((⁅xS, yS⁆ : Q11)⁻¹) ^ ((58 * i + 30 * j) * j) := by
    conv_lhs => rw [ht_eq, hα1, hα2]
    exact commutator_normalForm hclass xS yS i j (58 * i + 30 * j) (30 * i + 18 * j) hw hw₂
  have hzp : (⁅xS, yS⁆ : Q11) ^ 11 = 1 := pow_eleven_Q11 _
  have hzo : orderOf (⁅xS, yS⁆ : Q11) = 11 := orderOf_eq_prime hzp hz1
  intro h1
  have h1' : ⁅(⟨t, ht⟩ : Q11), α (α ⟨t, ht⟩)⁆ = 1 := by
    apply Subtype.ext
    rw [hcomm_coe, hα, hα, Subgroup.coe_one]
    simpa [sq, mul_assoc] using h1
  rw [hcomm_eq] at h1'
  have h2 : (⁅xS, yS⁆ : Q11) ^
      ((((30 * i + 18 * j) * i : ℕ) : ℤ) - (((58 * i + 30 * j) * j : ℕ) : ℤ)) = 1 := by
    rw [sub_eq_add_neg, zpow_add, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow]
    exact h1'
  have h3 : ((orderOf (⁅xS, yS⁆ : Q11) : ℕ) : ℤ) ∣
      (((30 * i + 18 * j) * i : ℕ) : ℤ) - (((58 * i + 30 * j) * j : ℕ) : ℤ) :=
    orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hzo] at h3
  have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).mpr h3
  push_cast at h5
  by_cases hij : (i : ZMod 11) ≠ 0 ∨ (j : ZMod 11) ≠ 0
  · exact nrm1_sq_Δ i j hij (by linear_combination h5)
  · push Not at hij
    obtain ⟨hi0, hj0⟩ := hij
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff i 11).mp hi0
    obtain ⟨n, hn⟩ := (ZMod.natCast_eq_zero_iff j 11).mp hj0
    apply htZ
    have htw : (⟨t, ht⟩ : Q11) = w := by
      rw [ht_eq, hm, hn, pow_mul, pow_mul, hxp, hyp]
      simp
    rw [htw]
    exact hw

private theorem index_ge_of_extraspecial_eleven {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQ_ext : CFSG.IsExtraspecialPGroup 11 Q)
    (hQ_card : Nat.card Q = 11 ^ 3) (hQ_comm : commutator Q = Subgroup.center Q)
    (hZ_card : Nat.card (Subgroup.center Q) = 11)
    (z : G) (hzQ : z ∈ Q) (hZ_eq : Subgroup.center Q = Subgroup.zpowers ⟨z, hzQ⟩)
    (hpow : ∀ u : Q, u ^ 11 = 1) (hz_comm : ∀ q ∈ Q, q * z = z * q)
    (nrm : G) (hnrm_N : nrm ∈ Subgroup.normalizer (Q : Set G)) (hnrm_z : nrm * z * nrm⁻¹ = z)
    (hnrm1 : ∀ (t : G) (ht : t ∈ Q), (⟨t, ht⟩ : Q) ∉ Subgroup.center Q → ⁅t, nrm * t * nrm⁻¹⁆ ≠ 1)
    (hnrm2 : ∀ (t : G) (ht : t ∈ Q),
      (⟨t, ht⟩ : Q) ∉ Subgroup.center Q → ⁅t, nrm ^ 2 * t * (nrm ^ 2)⁻¹⁆ ≠ 1)
    {H' : Subgroup G} (hg₀ : ¬ Subgroup.zpowers z ≤ H') :
    256 ≤ H'.index := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hz_not_mem : z ∉ H' := fun hz => hg₀ (Subgroup.zpowers_le.mpr hz)
  let K₀ : Subgroup Q := H'.subgroupOf Q
  have hK₀Z : ¬ Subgroup.center Q ≤ K₀ := by
    intro hle
    have hmem : (⟨z, hzQ⟩ : Q) ∈ Subgroup.center Q := by
      rw [hZ_eq]
      exact Subgroup.mem_zpowers _
    exact hz_not_mem (hle hmem)
  have hK₀_idx : 121 ≤ K₀.index := by
    have := pow_le_index_of_isExtraspecialPGroup (p := 11) (m := 1) hQ_ext hQ_card hK₀Z
    simpa using this
  have hK₀_mul : K₀.index * Nat.card K₀ = 1331 := by
    have h := Subgroup.index_mul_card K₀
    rwa [hQ_card] at h
  have hK₀_pos : 0 < Nat.card K₀ := Nat.card_pos
  have hK₀_le11 : Nat.card K₀ ≤ 11 := by
    have : 121 * Nat.card K₀ ≤ 1331 := hK₀_mul ▸ Nat.mul_le_mul_right _ hK₀_idx
    omega
  by_cases hK₀_one : Nat.card K₀ ≤ 1
  · have hK₀_eq1 : Nat.card K₀ = 1 := by omega
    rw [hK₀_eq1, mul_one] at hK₀_mul
    have hle : K₀.index ≤ H'.index := relIndex_le_index H' Q
    omega
  · push Not at hK₀_one
    have : Nontrivial K₀ := Finite.one_lt_card_iff_nontrivial.mp hK₀_one
    obtain ⟨u, hu1⟩ := exists_ne (1 : K₀)
    let uQ : Q := u.1
    let t : G := uQ.1
    have htQ : t ∈ Q := uQ.2
    have htH' : t ∈ H' := u.2
    have huQ1 : uQ ≠ 1 := fun h => hu1 (Subtype.ext h)
    have huQ_ord : orderOf uQ = 11 := orderOf_eq_prime (hpow uQ) huQ1
    have huQ_not_Z : uQ ∉ Subgroup.center Q := by
      intro huZ
      apply hK₀Z
      have hzp_eq : Subgroup.zpowers uQ = Subgroup.center Q := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huZ)
        rw [Nat.card_zpowers, huQ_ord, hZ_card]
      rw [← hzp_eq, Subgroup.zpowers_le]
      exact u.2
    have hK₀_eq : Subgroup.zpowers uQ = K₀ := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.2)
      rw [Nat.card_zpowers, huQ_ord]
      exact hK₀_le11
    have hHQ_le : H' ⊓ Q ≤ Subgroup.zpowers t := by
      intro x hx
      have hxK₀ : (⟨x, hx.2⟩ : Q) ∈ K₀ := hx.1
      rw [← hK₀_eq] at hxK₀
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxK₀
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
    let N : Subgroup G := Subgroup.normalizer (Q : Set G) ⊓ Subgroup.centralizer ({z} : Set G)
    have hQN : Q ≤ N :=
      le_inf Subgroup.le_normalizer fun q hq =>
        Subgroup.mem_centralizer_iff.mpr fun _ hg => hg ▸ (hz_comm q hq).symm
    let M : Subgroup G := Q ⊔ (H' ⊓ N)
    have hMN : M ≤ N := sup_le hQN inf_le_right
    let XJ : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers t
    have hXJ_cent : XJ ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [sup_le_iff, Subgroup.zpowers_le, Subgroup.zpowers_le]
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun _ hg => hg ▸ hz_comm t htQ,
        Subgroup.mem_centralizer_iff.mpr fun _ hg => hg ▸ rfl⟩
    have hQ_norm_XJ : Q ≤ Subgroup.normalizer (XJ : Set G) := by
      refine le_normalizer_of_conj_mem fun q hq => ?_
      rw [sup_le_iff, Subgroup.zpowers_le, Subgroup.zpowers_le]
      refine ⟨?_, ?_⟩
      · change q * z * q⁻¹ ∈ XJ
        rw [hz_comm q hq, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
      · change q * t * q⁻¹ ∈ XJ
        have hcomm_mem : (⟨⁅q, t⁆, Q.mul_mem (Q.mul_mem (Q.mul_mem hq htQ) (Q.inv_mem hq))
            (Q.inv_mem htQ)⟩ : Q) ∈ Subgroup.center Q := by
          rw [← hQ_comm, commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top ⟨q, hq⟩) (Subgroup.mem_top uQ)
        rw [hZ_eq] at hcomm_mem
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm_mem
        have hcomm_XJ : ⁅q, t⁆ ∈ XJ := by
          apply Subgroup.mem_sup_left
          exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
        have hqt : q * t * q⁻¹ = ⁅q, t⁆ * t := by
          rw [commutatorElement_def]
          group
        rw [hqt]
        exact XJ.mul_mem hcomm_XJ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hHN_norm_XJ : H' ⊓ N ≤ Subgroup.normalizer (XJ : Set G) := by
      refine le_normalizer_of_conj_mem fun h ⟨hhH', hhN, hhqz⟩ => ?_
      rw [sup_le_iff, Subgroup.zpowers_le, Subgroup.zpowers_le]
      refine ⟨?_, ?_⟩
      · change h * z * h⁻¹ ∈ XJ
        have hc : z * h = h * z := Subgroup.mem_centralizer_iff.mp hhqz z rfl
        rw [← hc, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
      · change h * t * h⁻¹ ∈ XJ
        have hhtH' : h * t * h⁻¹ ∈ H' := H'.mul_mem (H'.mul_mem hhH' htH') (H'.inv_mem hhH')
        have hhtQ : h * t * h⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hhN t).mp htQ
        exact Subgroup.mem_sup_right (hHQ_le ⟨hhtH', hhtQ⟩)
    have hM_norm_XJ : M ≤ Subgroup.normalizer (XJ : Set G) :=
      sup_le hQ_norm_XJ hHN_norm_XJ
    have hcomm_of_mem_M : ∀ g ∈ M, ⁅t, g * t * g⁻¹⁆ = 1 := by
      intro g hgM
      have htXJ : t ∈ XJ := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      have hgtXJ : g * t * g⁻¹ ∈ XJ :=
        (Subgroup.mem_normalizer_iff.mp (hM_norm_XJ hgM) t).mp htXJ
      have hc : t * (g * t * g⁻¹) = g * t * g⁻¹ * t :=
        Subgroup.mem_centralizer_iff.mp (hXJ_cent hgtXJ) t rfl
      exact commutatorElement_eq_one_iff_mul_comm.mpr hc
    have hnrm_N' : nrm ∈ N := by
      refine ⟨hnrm_N, Subgroup.mem_centralizer_iff.mpr fun _ hg => ?_⟩
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (mul_inv_eq_iff_eq_mul.mp hnrm_z).symm
    have hnrm_not_M : nrm ∉ M :=
      fun hM => hnrm1 t htQ huQ_not_Z (hcomm_of_mem_M nrm hM)
    have hnrm_sq_not_M : nrm ^ 2 ∉ M :=
      fun hM => hnrm2 t htQ huQ_not_Z (hcomm_of_mem_M (nrm ^ 2) hM)
    have h3_le : 3 ≤ M.relIndex N :=
      three_le_relIndex_of_not_mem hnrm_N' hnrm_not_M hnrm_sq_not_M
    have hrel_eq : (H' ⊓ N).relIndex Q = K₀.index := by
      rw [← Subgroup.inf_relIndex_right (H' ⊓ N) Q, inf_assoc, inf_of_le_right hQN,
        Subgroup.inf_relIndex_right]
      rfl
    have hrel_le_M : 121 ≤ (H' ⊓ N).relIndex M := by
      refine hK₀_idx.trans ?_
      rw [← hrel_eq]
      exact Subgroup.relIndex_le_of_le_right le_sup_left Nat.card_pos.ne'
    have hrel_mul : (H' ⊓ N).relIndex M * M.relIndex N = H'.relIndex N := by
      rw [Subgroup.relIndex_mul_relIndex (H' ⊓ N) M N le_sup_right hMN, Subgroup.inf_relIndex_right]
    have hrel_le_idx : H'.relIndex N ≤ H'.index := relIndex_le_index H' N
    have h363 : 121 * 3 ≤ (H' ⊓ N).relIndex M * M.relIndex N :=
      Nat.mul_le_mul hrel_le_M h3_le
    omega

/-- Every proper subgroup of `J₄` has index at least `256` (in fact at least `363`). -/
theorem index_ge_J4 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .J4) {H : Subgroup S} (hH : H ≠ ⊤) :
    256 ≤ H.index := by
  change S ≃* NativeSporadic.J4 at e
  have eJ : @MulEquiv S J _ (Subgroup.toGroup J).toMul :=
    @MulEquiv.trans S NativeSporadic.J4 J _ _ (Subgroup.toGroup J).toMul e (seedEquiv j4Facts.mat)
  let _ : Group J := Subgroup.toGroup J
  have hfinJ : Finite J := Finite.of_equiv S eJ.toEquiv
  exact le_index_of_injective_of_forall_not_le_index hH (f := eJ.symm.toMonoidHom) eJ.symm.injective
    (Subgroup.zpowers_ne_bot.mpr qz_ne_one) fun H' hg₀ =>
    index_ge_of_extraspecial_eleven Q11 isExtraspecial_Q11
      card_Q11 commutator_Q11 card_center_Q11 qz qz_mem center_Q11_eq pow_eleven_Q11
      (fun _ hq => qz_commute_of_mem hq) nrm₁ nrm₁_mem_normalizer nrm₁_qz
      (fun _ ht htZ => commutator_nrm1_ne_one ht htZ)
      (fun _ ht htZ => commutator_nrm1_sq_ne_one ht htZ) hg₀

/-- Maróti's bound for primitive almost simple groups with socle `J₄`. -/
theorem sporadicCase_J4 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .J4)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_J4
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 256) (c := 2) (by decide)
    (fun H hH => index_ge_J4 e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.J4, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
