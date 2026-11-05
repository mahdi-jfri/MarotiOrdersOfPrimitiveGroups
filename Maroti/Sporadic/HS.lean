module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Heisenberg
import CFSG.Sporadic.HS
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocalBase
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocalEq
import Certificates.Certificate19831
import all CFSG.Blueprint.NativeSporadic

/-!
# Sporadic Simple Group `HS`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to the Higman–Sims group `HS`.

Using `CFSG.AGLEmbeddingD2.hs_heisData_P` and `CFSG.AGLEmbeddingD2.heisLocalEq_of_heisDataEq`,
`HS` has an extraspecial Sylow `5`-subgroup `R` of order `5³ = 125` and exponent `5` normalized by
an element `t` moving every subgroup of index `5` in `R` containing `Z(R)`. This implies that every
proper subgroup of `HS` has index at least `2 * 5² = 50 ≥ 32`.
-/

@[expose] public section

namespace Maroti

open Subgroup CFSG.Blueprint CFSG.RankThree.Native CFSG.AGLEmbedding.MaxD2 CFSG.AGLEmbeddingD2
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem prime_le_of_ne_one_of_dvd_pow {p n k : ℕ} (hp : p.Prime) (hn0 : 0 < n)
    (hn1 : n ≠ 1) (hdvd : n ∣ p ^ k) : p ≤ n := by
  have hmin : n.minFac.Prime := Nat.minFac_prime hn1
  have hdvd_p : n.minFac ∣ p := hmin.dvd_of_dvd_pow (dvd_trans (Nat.minFac_dvd n) hdvd)
  have heq : n.minFac = p := (Nat.dvd_prime hp).mp hdvd_p |>.resolve_left hmin.ne_one
  exact Nat.le_of_dvd hn0 (heq ▸ Nat.minFac_dvd n)

private theorem two_mul_sq_le_index_of_heisLocalEq {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] {R : Subgroup X} (h : HeisLocalEq p R) {K : Subgroup X}
    (hZK : ¬ (R ⊓ centralizer (R : Set X)) ≤ K) :
    2 * p ^ 2 ≤ K.index := by
  have hp_pos : 0 < p := hp.out.pos
  have hp1 : 1 < p := hp.out.one_lt
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨hcard, -, hZcard, hcomm, hexp, -, t, htN, m, lam, e₀, hm, -, -, -, -, hline⟩ := h
  set Z : Subgroup X := R ⊓ centralizer (R : Set X)
  have hZR : Z.subgroupOf R = center R := by
    ext g
    rw [mem_subgroupOf, mem_inf, mem_centralizer_iff, mem_center_iff]
    refine ⟨fun ⟨_, hg⟩ r => Subtype.ext (hg r r.2), fun hg => ⟨g.2, fun r hr => ?_⟩⟩
    exact congrArg Subtype.val (hg ⟨r, hr⟩)
  have hcenter_card : Nat.card (center R) = p := by
    rw [← hZR, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : Z ≤ R)).toEquiv, hZcard]
  have hcomm_mem : ∀ x y : R, ⁅x, y⁆ ∈ center R := by
    intro x y
    rw [← hZR, mem_subgroupOf]
    have hcoe : ((⁅x, y⁆ : R) : X) = ⁅(x : X), (y : X)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe, ← hcomm]
    exact commutator_mem_commutator x.2 y.2
  have hexp_R : ∀ x : R, x ^ p = 1 := fun x => Subtype.ext (hexp x x.2)
  have hpow_Z : ∀ z ∈ center R, z ^ p = 1 := fun z _ => hexp_R z
  have hpow_mem : ∀ x : R, x ^ p ∈ center R := fun x => (hexp_R x).symm ▸ one_mem _
  have hexists_comm : ∀ x ∉ center R, ∀ z ∈ center R, ∃ y : R, ⁅x, y⁆ = z := by
    intro x hx z hz
    let φ : R →* center R :=
      { toFun := fun y => ⟨⁅x, y⁆, hcomm_mem x y⟩
        map_one' := Subtype.ext (commutatorElement_one_right x)
        map_mul' := fun y₁ y₂ =>
          Subtype.ext (commutatorElement_mul_right_of_le_center le_rfl hcomm_mem x y₁ y₂) }
    have hnot : ∃ y₀ : R, φ y₀ ≠ 1 := by
      by_contra! hall
      apply hx
      rw [mem_center_iff]
      intro y
      have hy := congrArg Subtype.val (hall y)
      exact (commutatorElement_eq_one_iff_mul_comm.mp hy).symm
    obtain ⟨y₀, hy₀⟩ := hnot
    have hdvd : Nat.card φ.range ∣ p := by
      rw [← hcenter_card]
      exact Subgroup.card_subgroup_dvd_card φ.range
    rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · exfalso
      have hsub : Subsingleton φ.range := Finite.card_le_one_iff_subsingleton.mp h1.le
      exact hy₀ (congrArg Subtype.val (Subsingleton.elim (⟨φ y₀, ⟨y₀, rfl⟩⟩ : φ.range) 1))
    · have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (hp'.trans hcenter_card.symm)
      have hmem : (⟨z, hz⟩ : center R) ∈ φ.range := htop ▸ mem_top _
      obtain ⟨y, hy⟩ := hmem
      exact ⟨y, congrArg Subtype.val hy⟩
  have hidx_Z : (center R).index = p ^ 2 := by
    have hmul := (center R).index_mul_card
    rw [hcenter_card, hcard, show p ^ 3 = p ^ 2 * p by ring] at hmul
    exact Nat.eq_of_mul_eq_mul_right hp_pos hmul
  set KR : Subgroup R := K.subgroupOf R
  have hKRZ : ¬ center R ≤ KR := by
    rw [← hZR]
    intro hle
    apply hZK
    intro z hz
    have hz' : (⟨z, hz.1⟩ : R) ∈ Z.subgroupOf R := hz
    exact hle hz'
  have hsq : p ^ 2 ≤ KR.index := by
    rw [sq]
    exact mul_le_index_of_not_le le_rfl hcomm_mem hpow_Z hpow_mem hexists_comm hKRZ hidx_Z.symm.le
  have hmul_card : KR.index * Nat.card KR = p ^ 3 := by
    rw [KR.index_mul_card, hcard]
  rcases eq_or_ne (Nat.card KR) 1 with hcard1 | hcard_ne1
  · have hidx_cube : KR.index = p ^ 3 := by
      rw [hcard1, mul_one] at hmul_card
      exact hmul_card
    have h2le : 2 * p ^ 2 ≤ KR.index := by
      rw [hidx_cube, show p ^ 3 = p * p ^ 2 by ring]
      exact Nat.mul_le_mul_right (p ^ 2) hp2
    let ι : R ⧸ KR → X ⧸ K :=
      Quotient.lift (fun q : R => ((q : X) : X ⧸ K)) fun q₁ q₂ hq => by
        have hq' : (QuotientGroup.mk q₁ : R ⧸ KR) = QuotientGroup.mk q₂ := Quotient.sound hq
        rw [QuotientGroup.eq, mem_subgroupOf] at hq'
        exact QuotientGroup.eq.mpr hq'
    have hι : Function.Injective ι := by
      intro a₁ a₂ ha
      induction a₁ using QuotientGroup.induction_on with | H q₁ =>
      induction a₂ using QuotientGroup.induction_on with | H q₂ =>
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact QuotientGroup.eq.mp ha
    exact h2le.trans (Nat.card_le_card_of_injective ι hι)
  · have hp_le_card : p ≤ Nat.card KR :=
      prime_le_of_ne_one_of_dvd_pow hp.out Nat.card_pos hcard_ne1
        ⟨KR.index, by rw [← hmul_card, mul_comm]⟩
    have hidx_sq : KR.index = p ^ 2 := by
      have h1 : p ^ 2 * p ≤ KR.index * p := Nat.mul_le_mul_right p hsq
      have h2 : KR.index * p ≤ KR.index * Nat.card KR := Nat.mul_le_mul_left KR.index hp_le_card
      rw [hmul_card, show p ^ 3 = p ^ 2 * p by ring] at h2
      exact Nat.eq_of_mul_eq_mul_right hp_pos (le_antisymm h2 h1)
    have hKR_card : Nat.card KR = p := by
      rw [hidx_sq, show p ^ 3 = p ^ 2 * p by ring] at hmul_card
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp_pos 2) hmul_card
    have hKR_ne_bot : KR ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hKR_card]
      exact hp1
    obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKR_ne_bot
    set u : R := u₀.1
    have huKR : u ∈ KR := u₀.2
    have hu1 : u ≠ 1 := fun h => hu₀1 (Subtype.ext h)
    have hu_not_Z : u ∉ center R := by
      intro huZ
      apply hKRZ
      have hZ_eq : zpowers u = center R := by
        apply eq_of_le_of_card_ge (zpowers_le.mpr huZ)
        rw [hcenter_card, Nat.card_zpowers, orderOf_eq_prime (hexp_R u) hu1]
      rw [← hZ_eq, zpowers_le]
      exact huKR
    have hKR_eq : zpowers u = KR := by
      apply eq_of_le_of_card_ge (zpowers_le.mpr huKR)
      rw [hKR_card, Nat.card_zpowers, orderOf_eq_prime (hexp_R u) hu1]
    set F : Subgroup X := Z ⊔ (K ⊓ R)
    have hZF : Z ≤ F := le_sup_left
    have hFR : F ≤ R := sup_le inf_le_left inf_le_right
    have hFR_sub : F.subgroupOf R = center R ⊔ KR := by
      have hKR_map : KR.map R.subtype = K ⊓ R := by
        ext x
        constructor
        · rintro ⟨⟨a, haR⟩, haK, rfl⟩
          exact ⟨haK, haR⟩
        · rintro ⟨hxK, hxR⟩
          exact ⟨⟨x, hxR⟩, hxK, rfl⟩
      rw [← hZR]
      apply Subgroup.map_injective R.subtype_injective
      rw [map_subgroupOf_eq_of_le hFR, Subgroup.map_sup,
        map_subgroupOf_eq_of_le inf_le_left, hKR_map]
    have hF_idx : F.relIndex R = p := by
      change (F.subgroupOf R).index = p
      rw [hFR_sub]
      set W : Subgroup R := center R ⊔ KR
      have hW_mul : W.index * Nat.card W = p ^ 3 := by
        rw [W.index_mul_card, hcard]
      have hW_le_cent : W ≤ centralizer ({u} : Set R) := by
        refine sup_le ?_ ?_
        · intro z hz
          rw [mem_centralizer_iff]
          rintro _ rfl
          exact mem_center_iff.mp hz u
        · rw [← hKR_eq, zpowers_le, mem_centralizer_iff]
          rintro _ rfl
          rfl
      have hW_ne_top : W ≠ ⊤ := by
        intro htop
        apply hu_not_Z
        rw [mem_center_iff]
        intro r
        have hr : r ∈ centralizer ({u} : Set R) := hW_le_cent (htop ▸ mem_top r)
        exact (mem_centralizer_iff.mp hr u rfl).symm
      have hW_idx_ne1 : W.index ≠ 1 := mt index_eq_one.mp hW_ne_top
      have hp_le_W_idx : p ≤ W.index :=
        prime_le_of_ne_one_of_dvd_pow hp.out Nat.card_pos hW_idx_ne1
          ⟨Nat.card W, by rw [← hW_mul]⟩
      have hZW : center R ≤ W := le_sup_left
      set ZW : Subgroup W := (center R).subgroupOf W
      have hZW_card : Nat.card ZW = p := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv, hcenter_card]
      have hZ_rel_mul : ZW.index * p = Nat.card W := by
        rw [← hZW_card, ZW.index_mul_card]
      have hZ_rel_ne1 : ZW.index ≠ 1 := by
        intro hrel1
        have hZW_top : ZW = ⊤ := index_eq_one.mp hrel1
        apply hu_not_Z
        have huW : (⟨u, mem_sup_right huKR⟩ : W) ∈ ZW := hZW_top ▸ mem_top _
        exact huW
      have hp_le_Z_rel : p ≤ ZW.index := by
        have hpos : 0 < ZW.index := Nat.card_pos
        have hdvd : ZW.index ∣ p ^ 3 :=
          ⟨W.index * p, by rw [← hW_mul, ← hZ_rel_mul]; ring⟩
        exact prime_le_of_ne_one_of_dvd_pow hp.out hpos hZ_rel_ne1 hdvd
      have hp2_le_W_card : p ^ 2 ≤ Nat.card W := by
        rw [sq, ← hZ_rel_mul]
        exact Nat.mul_le_mul_right p hp_le_Z_rel
      have h1 : W.index * p ^ 2 ≤ W.index * Nat.card W :=
        Nat.mul_le_mul_left W.index hp2_le_W_card
      have h2 : p * p ^ 2 ≤ W.index * p ^ 2 :=
        Nat.mul_le_mul_right (p ^ 2) hp_le_W_idx
      rw [hW_mul, show p ^ 3 = p * p ^ 2 by ring] at h1
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp_pos 2) (le_antisymm h1 h2)
    have hR_le_normF : R ≤ normalizer (F : Set X) := by
      intro r hr
      refine Subgroup.mem_normalizer_fintype fun f hf => ?_
      have hfR : f ∈ R := hFR hf
      have hcomm_rf : ⁅r, f⁆ ∈ F := hZF (hcomm ▸ commutator_mem_commutator hr hfR)
      have heq : r * f * r⁻¹ = ⁅r, f⁆ * f := by
        simp only [commutatorElement_def]; group
      rw [heq]
      exact F.mul_mem hcomm_rf hf
    have hnot_mem : ∀ q₀ : R, (q₀ : X) * t ∉ K := by
      intro q₀ hq₀t
      set g : X := (q₀ : X) * t
      have hgN : g ∈ normalizer (R : Set X) :=
        (normalizer (R : Set X)).mul_mem (le_normalizer q₀.2) htN
      have hgZ : g ∈ normalizer (Z : Set X) := mem_normalizer_inf_centralizer hgN
      have hgF : g ∈ normalizer (F : Set X) := by
        refine Subgroup.mem_normalizer_fintype fun x hx => ?_
        have hle_comap : F ≤ F.comap (MulAut.conj g).toMonoidHom := by
          refine sup_le ?_ ?_
          · intro z hz
            exact hZF ((mem_normalizer_iff.mp hgZ z).mp hz)
          · rintro y ⟨hyK, hyR⟩
            exact mem_sup_right ⟨K.mul_mem (K.mul_mem hq₀t hyK) (K.inv_mem hq₀t),
              (mem_normalizer_iff.mp hgN y).mp hyR⟩
        exact hle_comap hx
      have htF : t ^ 1 ∈ normalizer (F : Set X) := by
        rw [pow_one, show t = (q₀ : X)⁻¹ * g by simp [g]]
        exact (normalizer (F : Set X)).mul_mem
          ((normalizer (F : Set X)).inv_mem (hR_le_normF q₀.2)) hgF
      exact hline 1 (by decide) hm F hZF hFR hF_idx htF
    let Φ : Fin 2 × (R ⧸ KR) → X ⧸ K := fun s =>
      Quotient.liftOn s.2 (fun q : R => ((t ^ (s.1 : ℕ) * (q : X) : X) : X ⧸ K)) fun q₁ q₂ hq => by
        have hq' : (QuotientGroup.mk q₁ : R ⧸ KR) = QuotientGroup.mk q₂ := Quotient.sound hq
        rw [QuotientGroup.eq, mem_subgroupOf] at hq'
        apply QuotientGroup.eq.mpr
        have h1 : (t ^ (s.1 : ℕ) * (q₁ : X))⁻¹ * (t ^ (s.1 : ℕ) * (q₂ : X)) =
            (q₁ : X)⁻¹ * (q₂ : X) := by group
        rw [h1]
        exact hq'
    have hstep_lt : ∀ (s₁ s₂ : Fin 2) (q₁ q₂ : R),
        s₁ < s₂ → Φ (s₁, QuotientGroup.mk q₁) = Φ (s₂, QuotientGroup.mk q₂) → False := by
      intro s₁ s₂ q₁ q₂ hlt heq
      have hk : (t ^ (s₁ : ℕ) * (q₁ : X))⁻¹ * (t ^ (s₂ : ℕ) * (q₂ : X)) ∈ K :=
        QuotientGroup.eq.mp heq
      have hs₁ : (s₁ : ℕ) = 0 := by omega
      have hs₂ : (s₂ : ℕ) = 1 := by omega
      have hq₂1 : t * (q₂ : X) * t⁻¹ ∈ R := (mem_normalizer_iff.mp htN q₂.1).mp q₂.2
      let q₀ : R := q₁⁻¹ * ⟨t * (q₂ : X) * t⁻¹, hq₂1⟩
      have hq₀t : (q₀ : X) * t =
          (t ^ (s₁ : ℕ) * (q₁ : X))⁻¹ * (t ^ (s₂ : ℕ) * (q₂ : X)) := by
        simp only [q₀, Subgroup.coe_mul, Subgroup.coe_inv, hs₁, hs₂, pow_zero, pow_one]
        group
      exact hnot_mem q₀ (hq₀t.symm ▸ hk)
    have hΦ : Function.Injective Φ := by
      rintro ⟨s₁, a₁⟩ ⟨s₂, a₂⟩ heq
      induction a₁ using QuotientGroup.induction_on with | H q₁ =>
      induction a₂ using QuotientGroup.induction_on with | H q₂ =>
      rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
      · exact False.elim (hstep_lt s₁ s₂ q₁ q₂ hlt heq)
      · refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, mem_subgroupOf]
        have hk : (t ^ (s₁ : ℕ) * (q₁ : X))⁻¹ * (t ^ (s₁ : ℕ) * (q₂ : X)) ∈ K :=
          QuotientGroup.eq.mp heq
        have h1 : (t ^ (s₁ : ℕ) * (q₁ : X))⁻¹ * (t ^ (s₁ : ℕ) * (q₂ : X)) =
            (q₁ : X)⁻¹ * (q₂ : X) := by group
        rwa [h1] at hk
      · exact False.elim (hstep_lt s₂ s₁ q₂ q₁ hgt heq.symm)
    have hcard_dom : Nat.card (Fin 2 × (R ⧸ KR)) = 2 * p ^ 2 := by
      rw [Nat.card_prod, Nat.card_fin, ← Subgroup.index, hidx_sq]
    rw [Subgroup.index, ← hcard_dom]
    exact Nat.card_le_card_of_injective Φ hΦ

/-- Every proper subgroup of `HS` has index at least `50`. -/
theorem index_ge_HS {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .HS) {H : Subgroup S} (hH : H ≠ ⊤) :
    50 ≤ H.index := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hR₀ := Certificates.certificate19831.1
  have hloc : HeisLocalEq 5 (hsOR0.subgroupOf hs100P) :=
    heisLocalEq_of_heisDataEq hR₀ (le_refl 2) orderOf_three_zmod_five_hs (by norm_num)
  let e' : S ≃* hs100P := e.trans hs100Equiv
  set Z : Subgroup hs100P :=
    hsOR0.subgroupOf hs100P ⊓ centralizer ((hsOR0.subgroupOf hs100P : Subgroup hs100P) : Set hs100P)
  have hZne : Z ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hloc.2.2.1]
    decide
  exact le_index_of_injective_of_forall_not_le_index hH e'.symm.toMonoidHom e'.symm.injective hZne
    fun K hZK => two_mul_sq_le_index_of_heisLocalEq hloc hZK

/-- Maróti's bound for primitive almost simple groups with socle `HS`. -/
theorem sporadicCase_HS {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .HS)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcard : Nat.card S = 44352000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 50) (c := 2) (by decide)
    (fun H hH => index_ge_HS e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.HS, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
