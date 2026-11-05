module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Basic
import Maroti.MinDegree.Heisenberg
import CFSG.Sporadic.Fi24.Simple
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeC

/-!
# Sporadic Simple Group `Fi₂₄'`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Fischer's group `Fi₂₄'` (Maróti, *On the orders of
primitive groups*, J. Algebra 258 (2002), Theorem 1.1).

The minimum degree lower bound `512 ≤ H.index` uses the centralizer `fi24C` of a central
involution `fi24R2` in `Fi₂₄'` (`CFSG.EvenSporadicStandard.TwoFi22.DS81`), which has a normal
extraspecial subgroup `fi24QC` of order `2 ^ 13` on whose central quotient `commutator fi24C` acts
irreducibly while satisfying `⁅commutator fi24C, commutator fi24C⁆ = commutator fi24C`.
-/

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Maroti

open CFSG.Blueprint CFSG.Sporadic.Fi24
open CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.FischerOddCore
open scoped commutatorElement

private lemma perm_fin2_comm :
    ∀ σ τ : Equiv.Perm (Fin 2), ⁅σ, τ⁆ = 1 := by
  decide

private lemma perm_fin3_even_comm :
    ∀ σ τ : Equiv.Perm (Fin 3),
      Equiv.Perm.sign σ = 1 → Equiv.Perm.sign τ = 1 → ⁅σ, τ⁆ = 1 := by
  decide

private lemma commutator_eq_top_of_commutator_eq_self {C : Type*} [Group C] {D : Subgroup C}
    (hD : ⁅D, D⁆ = D) : commutator D = ⊤ := by
  apply Subgroup.map_injective D.subtype_injective
  rw [commutator_def, Subgroup.map_commutator]
  have htop : (⊤ : Subgroup D).map D.subtype = D := by
    ext x
    simp
  rw [htop, hD]

private def permCongrHom {α β : Type*} (e : α ≃ β) : Equiv.Perm α →* Equiv.Perm β where
  toFun σ := e.permCongr σ
  map_one' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp [Equiv.Perm.mul_apply]

private lemma four_le_relIndex_of_perfect {C : Type*} [Group C] [Finite C] {D N : Subgroup C}
    (hD : ⁅D, D⁆ = D) (hDN : ¬D ≤ N) :
    4 ≤ N.relIndex D := by
  let P : Subgroup D := N.subgroupOf D
  have hP_ne_top : P ≠ ⊤ := by
    intro htop
    apply hDN
    intro d hd
    have hmem : (⟨d, hd⟩ : D) ∈ P := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have hcomm_top : commutator D = ⊤ := commutator_eq_top_of_commutator_eq_self hD
  let φ : D →* Equiv.Perm (D ⧸ P) := MulAction.toPermHom D (D ⧸ P)
  have hker_le : φ.ker ≤ P := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have h1 : φ d (QuotientGroup.mk (1 : D)) = QuotientGroup.mk (1 : D) :=
      DFunLike.congr_fun hd (QuotientGroup.mk (1 : D))
    change (QuotientGroup.mk (d * 1) : D ⧸ P) = QuotientGroup.mk (1 : D) at h1
    have h2 : (d * 1)⁻¹ * 1 ∈ P := QuotientGroup.eq.mp h1
    rw [mul_one, inv_mem_iff, mul_one] at h2
    exact h2
  change 4 ≤ P.index
  by_contra! hlt
  have hpos : 0 < P.index := Nat.card_pos
  have hne1 : P.index ≠ 1 := fun h1 => hP_ne_top (Subgroup.index_eq_one.mp h1)
  have h23 : P.index = 2 ∨ P.index = 3 := by omega
  rcases h23 with h2 | h3
  · have e : (D ⧸ P) ≃ Fin 2 := Finite.equivFinOfCardEq h2
    let ψ : D →* Equiv.Perm (Fin 2) := (permCongrHom e).comp φ
    have hcomm_le : commutator D ≤ P := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      apply hker_le
      rw [MonoidHom.mem_ker]
      have h1 : ψ ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact perm_fin2_comm (ψ x) (ψ y)
      exact e.permCongr.injective (h1.trans (permCongrHom e).map_one.symm)
    rw [hcomm_top, top_le_iff] at hcomm_le
    exact hP_ne_top hcomm_le
  · have e : (D ⧸ P) ≃ Fin 3 := Finite.equivFinOfCardEq h3
    let ψ : D →* Equiv.Perm (Fin 3) := (permCongrHom e).comp φ
    let χ : D →* ℤˣ := Equiv.Perm.sign.comp ψ
    have hχ_top : commutator D ≤ χ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (χ x) (χ y))
    rw [hcomm_top] at hχ_top
    have hsign1 : ∀ d : D, Equiv.Perm.sign (ψ d) = 1 := fun d =>
      MonoidHom.mem_ker.mp (hχ_top (Subgroup.mem_top d))
    have hcomm_le : commutator D ≤ P := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      apply hker_le
      rw [MonoidHom.mem_ker]
      have h1 : ψ ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement]
        exact perm_fin3_even_comm (ψ x) (ψ y) (hsign1 x) (hsign1 y)
      exact e.permCongr.injective (h1.trans (permCongrHom e).map_one.symm)
    rw [hcomm_top, top_le_iff] at hcomm_le
    exact hP_ne_top hcomm_le

private lemma pow_eq_one_or_self_of_mul_self_eq_one {G : Type*} [Group G] {z : G}
    (hzz : z * z = 1) : ∀ n : ℕ, z ^ n = 1 ∨ z ^ n = z
  | 0 => Or.inl (pow_zero z)
  | n + 1 => by
    rcases pow_eq_one_or_self_of_mul_self_eq_one hzz n with h | h
    · right
      rw [pow_succ, h, one_mul]
    · left
      rw [pow_succ, h, hzz]

private lemma eq_one_or_eq_of_mem_zpowers_two {G : Type*} [Group G] {z g : G}
    (hzz : z * z = 1) (hg : g ∈ Subgroup.zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  cases k with
  | ofNat n =>
    change z ^ (n : ℤ) = 1 ∨ z ^ (n : ℤ) = z
    rw [zpow_natCast]
    exact pow_eq_one_or_self_of_mul_self_eq_one hzz n
  | negSucc n =>
    rw [zpow_negSucc]
    rcases pow_eq_one_or_self_of_mul_self_eq_one hzz (n + 1) with h | h
    · left
      rw [h, inv_one]
    · right
      rw [h, hz_inv]

private lemma index_ge_512_of_twoBModel {C S : Type*} [Group C] [Finite C] [Group S]
    {z : C} {ρ : C →* S} {K₀ N₀ : Subgroup S} (hm : TwoBModel z ρ K₀ N₀)
    (hQ_norm : (N₀.comap ρ).Normal) (hQ_card : Nat.card (N₀.comap ρ) = 2 ^ 13)
    (hQ_extra : CFSG.IsExtraspecial 2 ↥(N₀.comap ρ)) (hz1 : z ≠ 1)
    {H' : Subgroup C} (hzH' : ¬Subgroup.zpowers z ≤ H') :
    512 ≤ H'.index := by
  set Q : Subgroup C := N₀.comap ρ
  set Z : Subgroup C := Subgroup.zpowers z
  have hz_not_mem : z ∉ H' := fun h => hzH' (Subgroup.zpowers_le.mpr h)
  have hzz : z * z = 1 := by
    rcases (hm.ker (z * z)).1 (by rw [map_mul, hm.rho_z, one_mul]) with h | h
    · exact h
    · exact absurd (mul_left_cancel (a := z) (by rw [mul_one]; exact h)) hz1
  have hzQ : z ∈ Q := by
    show ρ z ∈ N₀
    rw [hm.rho_z]
    exact N₀.one_mem
  have hZ_le_Q : Z ≤ Q := Subgroup.zpowers_le.mpr hzQ
  have hQ_comm : ∀ q ∈ Q, ∀ r ∈ Q, ⁅q, r⁆ ∈ Z := by
    intro q hq r hr
    have h1 : ρ ⁅q, r⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm_of_mul_self hm.sq hq hr
    rcases (hm.ker ⁅q, r⁆).1 h1 with h | h
    · rw [h]
      exact Z.one_mem
    · rw [h]
      exact Subgroup.mem_zpowers z
  let zQ : Q := ⟨z, hzQ⟩
  have hzQ_ne1 : zQ ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzQ_zz : zQ * zQ = 1 := Subtype.ext hzz
  have hZ_Q_le : Subgroup.zpowers zQ ≤ Subgroup.center Q := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (hm.central q.1)
  have hord : orderOf zQ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq, hzQ_zz]) hzQ_ne1
  have hcenter_Q : Subgroup.center Q = Subgroup.zpowers zQ := by
    have : CFSG.IsExtraspecial 2 ↥Q := hQ_extra
    have hcard_c : Nat.card (Subgroup.center Q) = 2 :=
      CFSG.IsExtraspecial.center_order_p 2 ↥Q
    exact (Subgroup.eq_of_le_of_card_ge hZ_Q_le
      (by rw [hcard_c, Nat.card_zpowers, hord])).symm
  have hcomm_Q : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.zpowers zQ := by
    intro x y
    rcases eq_one_or_eq_of_mem_zpowers_two hzz (hQ_comm x.1 x.2 y.1 y.2) with h | h
    · have h' : ⁅x, y⁆ = 1 := Subtype.ext h
      rw [h']
      exact Subgroup.one_mem _
    · have h' : ⁅x, y⁆ = zQ := Subtype.ext h
      rw [h']
      exact Subgroup.mem_zpowers zQ
  have hexpZ_Q : ∀ w ∈ Subgroup.zpowers zQ, w ^ 2 = 1 := by
    intro w hw
    rcases eq_one_or_eq_of_mem_zpowers_two hzQ_zz hw with h | h
    · rw [h, one_pow]
    · rw [h, sq, hzQ_zz]
  have hexpQ_Q : ∀ x : Q, x ^ 2 ∈ Subgroup.zpowers zQ := by
    intro x
    have h1 : ρ (x.1 * x.1) = 1 := by
      rw [map_mul]
      exact hm.sq (ρ x.1) x.2
    rcases (hm.ker (x.1 * x.1)).1 h1 with h | h
    · have h' : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, sq, h]; rfl)
      rw [h']
      exact Subgroup.one_mem _
    · have h' : x ^ 2 = zQ := Subtype.ext (by rw [Subgroup.coe_pow, sq, h])
      rw [h']
      exact Subgroup.mem_zpowers zQ
  have hsurj_Q : ∀ x : Q, x ∉ Subgroup.zpowers zQ →
      ∀ w ∈ Subgroup.zpowers zQ, ∃ y : Q, ⁅x, y⁆ = w := by
    intro x hx w hw
    rcases eq_one_or_eq_of_mem_zpowers_two hzQ_zz hw with hw1 | hwz
    · exact ⟨1, by rw [hw1, commutatorElement_one_right]⟩
    · rw [hwz]
      have hx_nc : x ∉ Subgroup.center Q := hcenter_Q ▸ hx
      rw [Subgroup.mem_center_iff] at hx_nc
      push Not at hx_nc
      obtain ⟨y, hy⟩ := hx_nc
      have hne1 : ⁅x, y⁆ ≠ 1 := by
        intro h1
        exact hy (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      rcases eq_one_or_eq_of_mem_zpowers_two hzQ_zz (hcomm_Q x y) with h1 | hz
      · exact False.elim (hne1 h1)
      · exact ⟨y, hz⟩
  have hnot_Z_Q : ¬Subgroup.zpowers zQ ≤ H'.subgroupOf Q := by
    rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    exact hz_not_mem
  have hidx_Z_Q : 64 ^ 2 ≤ (Subgroup.zpowers zQ).index := by
    have hmul := Subgroup.index_mul_card (Subgroup.zpowers zQ)
    rw [Nat.card_zpowers, hord, hQ_card] at hmul
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h128 : 128 ≤ H'.relIndex Q :=
    mul_le_index_of_not_le hZ_Q_le hcomm_Q hexpZ_Q hexpQ_Q hsurj_Q hnot_Z_Q hidx_Z_Q
  have hH'_mul : H'.relIndex Q * (H' ⊔ Q).index ≤ H'.index := by
    rw [← Subgroup.relIndex_mul_index (le_sup_left : H' ≤ H' ⊔ Q)]
    exact Nat.mul_le_mul_right _ (relIndex_le_relIndex_of_le H' Q (H' ⊔ Q) le_sup_right)
  set K : Subgroup C := H' ⊓ Q
  set L : Subgroup C := K ⊔ Z
  have hLQ : L ≤ Q := sup_le inf_le_right hZ_le_Q
  have hL_cases : ∀ x ∈ L, x ∈ K ∨ x * z ∈ K := by
    let S_L : Subgroup C :=
      { carrier := {x : C | x ∈ K ∨ x * z ∈ K}
        one_mem' := Or.inl K.one_mem
        mul_mem' := fun {a b} ha hb => by
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (K.mul_mem ha hb)
          · right
            rw [mul_assoc]
            exact K.mul_mem ha hb
          · right
            have hbz : b * z = z * b := hm.central b
            have habz : a * b * z = a * z * b := by rw [mul_assoc, hbz, ← mul_assoc]
            rw [habz]
            exact K.mul_mem ha hb
          · left
            have hbz : z * (b * z) = b * (z * z) := by
              calc z * (b * z) = (z * b) * z := (mul_assoc z b z).symm
                _ = (b * z) * z := by rw [hm.central b]
                _ = b * (z * z) := mul_assoc b z z
            have hab : a * b = (a * z) * (b * z) := by
              calc a * b = a * (b * (z * z)) := by rw [hzz, mul_one]
                _ = a * (z * (b * z)) := by rw [← hbz]
                _ = (a * z) * (b * z) := (mul_assoc a z (b * z)).symm
            rw [hab]
            exact K.mul_mem ha hb
        inv_mem' := fun {a} ha => by
          rcases ha with ha | ha
          · exact Or.inl (K.inv_mem ha)
          · right
            have haz : a⁻¹ * z = (a * z)⁻¹ := by
              apply mul_left_cancel (a := a * z)
              rw [mul_inv_cancel]
              calc (a * z) * (a⁻¹ * z) = a * (z * a⁻¹) * z := by group
                _ = a * (a⁻¹ * z) * z := by rw [hm.central a⁻¹]
                _ = z * z := by group
                _ = 1 := hzz
            rw [haz]
            exact K.inv_mem ha }
    have hL_le : L ≤ S_L := by
      refine sup_le (fun k hk => Or.inl hk) ?_
      rw [Subgroup.zpowers_le]
      change z ∈ K ∨ z * z ∈ K
      right
      rw [hzz]
      exact K.one_mem
    exact fun x hx => hL_le hx
  have hL_ne_Q : L ≠ Q := by
    intro hLQ_eq
    obtain ⟨q₁, q₂, hq₁, hq₂, hne⟩ := hm.noncomm
    have hq₁L : q₁ ∈ L := hLQ_eq.symm ▸ hq₁
    have hq₂L : q₂ ∈ L := hLQ_eq.symm ▸ hq₂
    have hcomm_K : ∀ a b : C, (a ∈ K ∨ a * z ∈ K) → (b ∈ K ∨ b * z ∈ K) → ⁅a, b⁆ ∈ K := by
      intro a b ha hb
      have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
      have hcomm_z_right : ∀ x y : C, ⁅x, y * z⁆ = ⁅x, y⁆ := fun x y => by
        simp only [commutatorElement_def, mul_inv_rev, hz_inv]
        calc x * (y * z) * x⁻¹ * (z * y⁻¹)
            = x * y * (z * x⁻¹) * z * y⁻¹ := by group
          _ = x * y * (x⁻¹ * z) * z * y⁻¹ := by rw [hm.central x⁻¹]
          _ = x * y * x⁻¹ * (z * z) * y⁻¹ := by group
          _ = x * y * x⁻¹ * y⁻¹ := by rw [hzz, mul_one]
      have hcomm_z_left : ∀ x y : C, ⁅x * z, y⁆ = ⁅x, y⁆ := fun x y => by
        simp only [commutatorElement_def, mul_inv_rev, hz_inv]
        calc x * z * y * (z * x⁻¹) * y⁻¹
            = x * (z * y) * z * x⁻¹ * y⁻¹ := by group
          _ = x * (y * z) * z * x⁻¹ * y⁻¹ := by rw [hm.central y]
          _ = x * y * (z * z) * x⁻¹ * y⁻¹ := by group
          _ = x * y * x⁻¹ * y⁻¹ := by rw [hzz, mul_one]
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      · rw [← hcomm_z_right a b]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      · rw [← hcomm_z_left a b]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      · rw [← hcomm_z_left a b, ← hcomm_z_right (a * z) b]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    have hq_comm_K : ⁅q₁, q₂⁆ ∈ K := hcomm_K q₁ q₂ (hL_cases q₁ hq₁L) (hL_cases q₂ hq₂L)
    rcases eq_one_or_eq_of_mem_zpowers_two hzz (hQ_comm q₁ hq₁ q₂ hq₂) with h1 | hz
    · exact hne (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exact hz_not_mem (hz ▸ hq_comm_K.1)
  set N : Subgroup C := Subgroup.normalizer (L : Set C)
  have hZ_le_comap : ∀ c : C, Z ≤ L.comap (MulAut.conj c).toMonoidHom := by
    intro c
    rw [Subgroup.zpowers_le]
    change c * z * c⁻¹ ∈ L
    have hc : c * z * c⁻¹ = z := by rw [hm.central c, mul_inv_cancel_right]
    rw [hc]
    exact (le_sup_right : Z ≤ L) (Subgroup.mem_zpowers z)
  have hH'_le_N : H' ≤ N := by
    refine le_normalizer_of_conj_mem fun h hh => sup_le ?_ (hZ_le_comap h)
    intro k hk
    change h * k * h⁻¹ ∈ L
    exact (le_sup_left : K ≤ L)
      ⟨H'.mul_mem (H'.mul_mem hh hk.1) (H'.inv_mem hh), hQ_norm.conj_mem k hk.2 h⟩
  have hQ_le_N : Q ≤ N := by
    refine le_normalizer_of_conj_mem fun q hq => sup_le ?_ (hZ_le_comap q)
    intro k hk
    change q * k * q⁻¹ ∈ L
    have heq : q * k * q⁻¹ = ⁅q, k⁆ * k := by simp [commutatorElement_def]
    rw [heq]
    exact L.mul_mem ((le_sup_right : Z ≤ L) (hQ_comm q hq k hk.2)) ((le_sup_left : K ≤ L) hk)
  have hHQ_le_N : H' ⊔ Q ≤ N := sup_le hH'_le_N hQ_le_N
  have hN_le_HQ : N.index ≤ (H' ⊔ Q).index := index_le_of_le hHQ_le_N
  by_cases hDN : commutator C ≤ N
  · have hinv : ∀ p ∈ commutator C, ∀ y ∈ L, p * y * p⁻¹ ∈ L := fun p hp y hy =>
      (Subgroup.mem_normalizer_iff.mp (hDN hp) y).mp hy
    rcases (hm.irreducible L hLQ hinv) with hLZ | hLQ_eq
    · have hbot : H'.subgroupOf Q = ⊥ := by
        rw [eq_bot_iff]
        intro q hq
        have hqK : (q : C) ∈ K := ⟨hq, q.2⟩
        have hqZ : (q : C) ∈ Z := hLZ ((le_sup_left : K ≤ L) hqK)
        rcases eq_one_or_eq_of_mem_zpowers_two hzz hqZ with h1 | hz
        · exact Subgroup.mem_bot.mpr (Subtype.ext h1)
        · exact False.elim (hz_not_mem (hz ▸ hq))
      have hrel_card : H'.relIndex Q = 2 ^ 13 := by
        rw [Subgroup.relIndex, hbot, Subgroup.index_bot, hQ_card]
      have hle_idx : H'.relIndex Q ≤ H'.index := relIndex_le_index H' Q
      omega
    · exact False.elim (hL_ne_Q hLQ_eq)
  · have h4 : 4 ≤ N.relIndex (commutator C) :=
      four_le_relIndex_of_perfect hm.perfect' hDN
    have h4_N : N.relIndex (commutator C) ≤ N.index :=
      relIndex_le_index N (commutator C)
    have h512 : 128 * 4 ≤ H'.relIndex Q * (H' ⊔ Q).index :=
      Nat.mul_le_mul h128 (by omega)
    omega

/-- Every proper subgroup of `Fi₂₄'` has index at least `512`. -/
theorem index_ge_Fi24Prime {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Fi24Prime) {H : Subgroup S} (hH : H ≠ ⊤) :
    512 ≤ H.index := by
  have eJ : @MulEquiv S J _ (Subgroup.toGroup J).toMul :=
    @MulEquiv.trans S NativeSporadic.Fi24prime J _ Units.instGroup.toMul
      (Subgroup.toGroup J).toMul e fi24EquivJ
  have : Finite ↥fi24C := fi24C_finite
  have : fi24QC.Normal := fi24QC_normal
  let z₀ : ↥fi24C := ⟨fi24R2, fi24R2_mem_C⟩
  have hz₀1 : z₀ ≠ 1 := fun h => fi24R2_ne_one (congrArg Subtype.val h)
  let _ : Group J := Subgroup.toGroup J
  exact le_index_of_injective_of_forall_not_le_index hH
    (f := eJ.symm.toMonoidHom.comp fi24C.subtype)
    (eJ.symm.injective.comp fi24C.subtype_injective)
    (Subgroup.zpowers_ne_bot.mpr hz₀1)
    fun H' hzH' =>
      index_ge_512_of_twoBModel fi24C_twoBModel fi24QC_normal card_fi24QC fi24QC_extraspecial
        hz₀1 hzH'

/-- Maróti's bound for primitive almost simple groups with socle `Fi₂₄'`. -/
theorem sporadicCase_Fi24Prime {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Fi24Prime)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 1255205709190661721292800 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_Fi24prime
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 512) (c := 2) (by decide)
    (fun H hH => index_ge_Fi24Prime e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Fi24Prime, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
