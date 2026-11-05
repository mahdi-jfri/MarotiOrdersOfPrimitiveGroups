module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
public import Maroti.Sporadic.ExtraspecialCoord
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzGroup
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.LieType.Ree.SuzukiOrder

/-!
# Sporadic Simple Group `Ru`

This file proves Maróti's bound `Nat.card G ≤ bound (Nat.card α)` for primitive almost simple
groups `G` whose socle `S` is isomorphic to Rudvalis's group `Ru` (Maróti, *On the orders of
primitive groups*, J. Algebra 258 (2002), Theorem 1.1).

Using `CFSG.EvenSporadicStandard.Induction.RuSz`, `Ru` contains a subgroup `K0` isomorphic to
`Sz(8) = suzukiGroup 1 (GaloisField 2 3)`. Inside `Sz(8)`, the Borel subgroup `B = U ⋊ T` has
order `448 = 64 · 7` and index `65`, where `U` is the Sylow `2`-subgroup of order `64` with center
`Z` of order `8`, and `T` of order `7` acts transitively on `Z \ {1}`. Using the regular action of
`U` on the Suzuki ovoid `Ω \ {∞}`, we prove that every subgroup of `Sz(8)` not containing
`z₀ = suzukiSElt 1 K 0 1` has index at least `64`, and hence every proper subgroup of `Ru` has
index at least `64`.
-/

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Maroti

open Subgroup
open CFSG.Blueprint CFSG.LieType.Ree CFSG.Sporadic.RuSchreier
open CFSG.EvenSporadicStandard.Induction.RuSz

section SuzukiIndex

abbrev GF8 : Type := GaloisField 2 3

private theorem gf8_two_eq_zero : (2 : GF8) = 0 :=
  (suzuki_frob_data 1 card_GF).1

private theorem gf8_add_self (x : GF8) : x + x = 0 := by
  linear_combination x * gf8_two_eq_zero

private theorem gf8_pow5_bijective : Function.Bijective (fun s : GF8ˣ => s ^ (5 : ℕ)) := by
  have h := (suzuki_frobenius_exponents 1 GF8 card_GF).2.2.2.2.2.2.2.2.2.2.1
  convert h using 1
  ext s
  rfl

private theorem gf8_pow5_eq_zero {x : GF8} (h : x ^ 5 = 0) : x = 0 := by
  by_contra hx
  exact (Units.mk0 x hx ^ (5 : ℕ)).ne_zero h

private theorem gf8_pow5_inj {x y : GF8} (h : x ^ 5 = y ^ 5) : x = y := by
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by decide)] at h
    exact (gf8_pow5_eq_zero h.symm).symm
  · by_cases hy : y = 0
    · subst hy
      rw [zero_pow (by decide)] at h
      exact gf8_pow5_eq_zero h
    · have hu : Units.mk0 x hx ^ (5 : ℕ) = Units.mk0 y hy ^ (5 : ℕ) := by
        ext
        exact h
      exact congrArg Units.val (gf8_pow5_bijective.1 hu)

private theorem gf8_card_units : Nat.card GF8ˣ = 7 := by
  rw [Nat.card_units, card_GF]
  rfl

private theorem gf8_units_pow7 (l : GF8ˣ) : l ^ 7 = 1 := by
  rw [← gf8_card_units]
  exact pow_card_eq_one'

private theorem gf8_units_exists_pow {μ : GF8ˣ} (hμ : μ ≠ 1) (t : GF8ˣ) :
    ∃ i : ℕ, μ ^ i = t := by
  let P := Subgroup.zpowers μ
  have hP_mul : P.index * Nat.card P = 7 := by
    rw [Subgroup.index_mul_card, gf8_card_units]
  have hP_gt1 : 1 < Nat.card P := by
    have h1 : (1 : P) ≠ ⟨μ, Subgroup.mem_zpowers μ⟩ := by
      intro heq
      exact hμ (congrArg Subtype.val heq).symm
    have : Nontrivial P := ⟨⟨1, ⟨μ, Subgroup.mem_zpowers μ⟩, h1⟩⟩
    exact Finite.one_lt_card
  have hP_idx : P.index = 1 := by
    have hdvd : Nat.card P ∣ 7 := ⟨P.index, by linarith⟩
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdvd with h1 | h7
    · omega
    · rw [h7] at hP_mul
      omega
  have hP_top : P = ⊤ := Subgroup.index_eq_one.mp hP_idx
  have ht_mem : t ∈ P := hP_top ▸ Subgroup.mem_top t
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht_mem
  have hk7 : k = 7 * (k / 7) + k % 7 := by omega
  have hnonneg : 0 ≤ k % 7 := by omega
  refine ⟨(k % 7).toNat, ?_⟩
  have hi : ((k % 7).toNat : ℤ) = k % 7 := Int.toNat_of_nonneg hnonneg
  have hμ7 : μ ^ (7 : ℤ) = 1 := by exact_mod_cast gf8_units_pow7 μ
  calc μ ^ (k % 7).toNat = μ ^ ((k % 7).toNat : ℤ) := (zpow_natCast μ _).symm
    _ = (μ ^ (7 : ℤ)) ^ (k / 7) * μ ^ (k % 7) := by rw [hi, hμ7, one_zpow, one_mul]
    _ = μ ^ (7 * (k / 7) + k % 7) := by rw [← zpow_mul, ← zpow_add]
    _ = μ ^ k := by rw [← hk7]

private theorem suzukiSElt_sq (u v : GF8) :
    (suzukiSElt 1 GF8 u v) ^ 2 = suzukiSElt 1 GF8 0 (u ^ 5) :=
  suzukiSElt_ext ((suzuki_unipotent_product 1 card_GF).2.2.1 u v)

private theorem suzukiSElt_zero_sq (v : GF8) :
    suzukiSElt 1 GF8 0 v * suzukiSElt 1 GF8 0 v = 1 := by
  rw [← sq, suzukiSElt_sq, zero_pow (by decide), suzukiSElt_zero_zero card_GF]

private theorem suzukiSElt_pow4 (u v : GF8) :
    (suzukiSElt 1 GF8 u v) ^ 4 = 1 := by
  change (suzukiSElt 1 GF8 u v) ^ (2 + 2) = 1
  rw [pow_add, suzukiSElt_sq, suzukiSElt_zero_sq]

private theorem suzukiB_pow_decomp (u v : GF8) (l : GF8ˣ) (n : ℕ) :
    ∃ u' v' : GF8,
      (suzukiSElt 1 GF8 u v * suzukiDElt 1 GF8 l) ^ n =
        suzukiSElt 1 GF8 u' v' * suzukiDElt 1 GF8 (l ^ n) := by
  induction n with
  | zero =>
    exact ⟨0, 0, by rw [pow_zero, pow_zero, suzukiSElt_zero_zero card_GF, suzukiDElt_one, mul_one]⟩
  | succ n ih =>
    rcases ih with ⟨u', v', ih⟩
    have hconj := suzukiDElt_conj' card_GF (l ^ n) u v
    refine ⟨u' + ((l ^ n)⁻¹ : GF8ˣ) * u,
      v' + (((l ^ n)⁻¹ : GF8ˣ) : GF8) ^ (2 ^ (1 + 1) + 1) * v +
        u' ^ 2 ^ (1 + 1) * (((l ^ n)⁻¹ : GF8ˣ) * u), ?_⟩
    calc (suzukiSElt 1 GF8 u v * suzukiDElt 1 GF8 l) ^ (n + 1)
        = (suzukiSElt 1 GF8 u' v' * suzukiDElt 1 GF8 (l ^ n)) *
            (suzukiSElt 1 GF8 u v * suzukiDElt 1 GF8 l) := by rw [pow_succ, ih]
      _ = suzukiSElt 1 GF8 u' v' *
            (suzukiDElt 1 GF8 (l ^ n) * suzukiSElt 1 GF8 u v * (suzukiDElt 1 GF8 (l ^ n))⁻¹) *
            (suzukiDElt 1 GF8 (l ^ n) * suzukiDElt 1 GF8 l) := by group
      _ = suzukiSElt 1 GF8 _ _ * suzukiDElt 1 GF8 (l ^ (n + 1)) := by
            rw [hconj, suzukiSElt_mul card_GF, suzukiDElt_mul, ← pow_succ]

private theorem suzukiB_conj_zero (u₀ v₀ : GF8) (l : GF8ˣ) (v : GF8) :
    (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) * suzukiSElt 1 GF8 0 v *
      (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l)⁻¹ =
      suzukiSElt 1 GF8 0 ((((l⁻¹ : GF8ˣ) ^ (5 : ℕ) : GF8ˣ) : GF8) * v) := by
  have hd := suzukiDElt_conj' card_GF l 0 v
  simp only [mul_zero] at hd
  have hcomm := suzukiSElt_zero_commute card_GF
    ((((l⁻¹ : GF8ˣ) : GF8) ^ (2 ^ (1 + 1) + 1) * v)) u₀ v₀
  calc (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) * suzukiSElt 1 GF8 0 v *
        (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l)⁻¹
      = suzukiSElt 1 GF8 u₀ v₀ *
          (suzukiDElt 1 GF8 l * suzukiSElt 1 GF8 0 v * (suzukiDElt 1 GF8 l)⁻¹) *
          (suzukiSElt 1 GF8 u₀ v₀)⁻¹ := by group
    _ = suzukiSElt 1 GF8 u₀ v₀ *
          suzukiSElt 1 GF8 0 (((l⁻¹ : GF8ˣ) : GF8) ^ (2 ^ (1 + 1) + 1) * v) *
          (suzukiSElt 1 GF8 u₀ v₀)⁻¹ := by rw [hd]
    _ = suzukiSElt 1 GF8 0 (((l⁻¹ : GF8ˣ) : GF8) ^ (2 ^ (1 + 1) + 1) * v) := by
          rw [← hcomm, mul_inv_cancel_right]
    _ = suzukiSElt 1 GF8 0 ((((l⁻¹ : GF8ˣ) ^ (5 : ℕ) : GF8ˣ) : GF8) * v) := by
          rfl

private theorem suzukiB_pow_conj_zero (u₀ v₀ : GF8) (l : GF8ˣ) (i : ℕ) (v : GF8) :
    (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) ^ i * suzukiSElt 1 GF8 0 v *
      ((suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) ^ i)⁻¹ =
      suzukiSElt 1 GF8 0 (((((l⁻¹ : GF8ˣ) ^ (5 : ℕ)) ^ i : GF8ˣ) : GF8) * v) := by
  induction i generalizing v with
  | zero => simp
  | succ i ih =>
    calc (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) ^ (i + 1) * suzukiSElt 1 GF8 0 v *
          ((suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) ^ (i + 1))⁻¹
        = (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) ^ i *
            ((suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) * suzukiSElt 1 GF8 0 v *
              (suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l)⁻¹) *
            ((suzukiSElt 1 GF8 u₀ v₀ * suzukiDElt 1 GF8 l) ^ i)⁻¹ := by
          rw [pow_succ]; group
      _ = suzukiSElt 1 GF8 0
            (((((l⁻¹ : GF8ˣ) ^ (5 : ℕ)) ^ (i + 1) : GF8ˣ) : GF8) * v) := by
          rw [suzukiB_conj_zero, ih, ← mul_assoc, ← Units.val_mul, ← pow_succ]

private theorem mem_suzukiB_of_conj_mem_suzukiU {x g : SzB}
    (hxU : x ∈ suzukiU 1 GF8) (hx1 : x ≠ 1) (hgx : g * x * g⁻¹ ∈ suzukiU 1 GF8) :
    g ∈ suzukiB 1 GF8 := by
  rw [← (suzuki_ovoid_stabilizer card_GF).1, MulAction.mem_stabilizer_iff]
  by_contra hne
  have hp : g • suzukiInfty GF8 ∈ suzukiOmega 1 GF8 \ {suzukiInfty GF8} :=
    ⟨suzuki_smul_mem_suzukiOmega card_GF g (suzukiInfty_mem_suzukiOmega 1 GF8), hne⟩
  have hx_fix : x • suzukiInfty GF8 = suzukiInfty GF8 := by
    have hxB : x ∈ suzukiB 1 GF8 := suzukiU_le_suzukiB 1 GF8 hxU
    rwa [← (suzuki_ovoid_stabilizer card_GF).1, MulAction.mem_stabilizer_iff] at hxB
  have hgx_fix : (g * x * g⁻¹) • (g • suzukiInfty GF8) = g • suzukiInfty GF8 := by
    rw [mul_smul, mul_smul, inv_smul_smul, hx_fix]
  have h1_fix : ((1 : suzukiU 1 GF8) : SzB) • (g • suzukiInfty GF8) = g • suzukiInfty GF8 :=
    one_smul SzB _
  obtain ⟨u₀, -, hu₀_uniq⟩ :=
    (suzuki_ovoid_unipotent_action card_GF).2.2.2.2.2.1 _ hp _ hp
  have heq1 := hu₀_uniq ⟨g * x * g⁻¹, hgx⟩ hgx_fix
  have heq2 := hu₀_uniq 1 h1_fix
  have hgx1 : g * x * g⁻¹ = 1 := congrArg Subtype.val (heq1.trans heq2.symm)
  apply hx1
  calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = 1 := by rw [hgx1]; group

private theorem involution_mul_pow_conj {G : Type*} [Group G] {u z : G}
    (hu : u * u = 1) (hz : z * z = 1) (k : ℕ) :
    (u * z) ^ k * u * ((u * z) ^ k)⁻¹ = (u * z) ^ (2 * k + 1) * z := by
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h_uz_z : u * z * z = u := by rw [mul_assoc, hz, mul_one]
  have h_uz_inv : (u * z)⁻¹ = z * u := by rw [mul_inv_rev, hu_inv, hz_inv]
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one, Nat.mul_zero, zero_add, pow_one]
    exact h_uz_z.symm
  | succ k ih =>
    calc (u * z) ^ (k + 1) * u * ((u * z) ^ (k + 1))⁻¹
        = (u * z) * ((u * z) ^ k * u * ((u * z) ^ k)⁻¹) * (u * z)⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
      _ = (u * z) * ((u * z) ^ (2 * k + 1) * z) * (z * u) := by
          rw [ih, h_uz_inv]
      _ = ((u * z) * (u * z) ^ (2 * k + 1)) * (z * z) * u := by
          simp only [mul_assoc]
      _ = (u * z) ^ (2 * k + 1 + 1) * u := by
          rw [← pow_succ', hz, mul_one]
      _ = (u * z) ^ (2 * k + 2) * (u * z * z) := by
          rw [h_uz_z]
      _ = (u * z) ^ (2 * (k + 1) + 1) * z := by
          rw [← mul_assoc, ← pow_succ, show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by omega]

private theorem suzuki_card_U : Nat.card (suzukiU 1 GF8) = 64 := by
  rw [(suzuki_unipotent_structure card_GF).2.1]
  norm_num

private theorem suzuki_card_B : Nat.card (suzukiB 1 GF8) = 448 := by
  rw [(suzuki_borel_structure card_GF).2.2.2.2.2.2.2]
  norm_num

/-- Every subgroup `M` of `Sz(8)` not containing `suzukiSElt 1 GF8 0 1` has index at least `64`. -/
private theorem szB_sixty_four_le_index (M : Subgroup SzB)
    (hz₀ : suzukiSElt 1 GF8 0 1 ∉ M) :
    64 ≤ M.index := by
  have : Finite SzB := (suzuki_simple le_rfl card_GF).1
  set U := suzukiU 1 GF8
  set Z := suzukiZ0 1 GF8
  set B := suzukiB 1 GF8
  let W_B := M.subgroupOf B
  let W_U := M.subgroupOf U
  have hWB_le : W_B.index ≤ M.index := relIndex_le_index M B
  have hWU_le : W_U.index ≤ M.index := relIndex_le_index M U
  have hWB_mul : W_B.index * Nat.card W_B = 448 := by
    rw [Subgroup.index_mul_card, suzuki_card_B]
  have hWU_mul : W_U.index * Nat.card W_U = 64 := by
    rw [Subgroup.index_mul_card, suzuki_card_U]
  by_cases h7 : 7 ∣ Nat.card W_B
  · -- Case 1: 7 divides |M ∩ B|
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    have : Fintype W_B := Fintype.ofFinite W_B
    have h7' : 7 ∣ Fintype.card W_B := by rwa [← Nat.card_eq_fintype_card]
    obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card 7 h7'
    let xS : SzB := x.1.1
    have hxB : xS ∈ B := x.1.2
    have hxM : xS ∈ M := x.2
    obtain ⟨⟨⟨u₀, v₀⟩, l⟩, hx_eq, -⟩ := (suzuki_borel_structure card_GF).2.2.2.2.2.2.1 xS hxB
    dsimp only at hx_eq
    have hx_ord' : orderOf xS = 7 :=
      (Subgroup.orderOf_coe x.1).trans ((Subgroup.orderOf_coe x).trans hx_ord)
    have hl_ne1 : l ≠ 1 := by
      intro hl1
      subst hl1
      rw [suzukiDElt_one, mul_one] at hx_eq
      have hx4 : xS ^ 4 = 1 := by rw [hx_eq, suzukiSElt_pow4]
      have hdvd4 : orderOf xS ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
      rw [hx_ord'] at hdvd4
      exact absurd hdvd4 (by decide)
    have hlinv_ne1 : (l⁻¹ : GF8ˣ) ≠ 1 := inv_ne_one.mpr hl_ne1
    have hμ_ne1 : (l⁻¹ : GF8ˣ) ^ (5 : ℕ) ≠ 1 := by
      intro hμ
      apply hlinv_ne1
      exact gf8_pow5_bijective.1 (hμ.trans (one_pow 5).symm)
    have hMZ_triv : ∀ v : GF8, suzukiSElt 1 GF8 0 v ∈ M → v = 0 := by
      intro v hvM
      by_contra hv0
      obtain ⟨i, hi⟩ := gf8_units_exists_pow hμ_ne1 (Units.mk0 v hv0)⁻¹
      have hconj_mem : xS ^ i * suzukiSElt 1 GF8 0 v * (xS ^ i)⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem (M.pow_mem hxM i) hvM) (M.inv_mem (M.pow_mem hxM i))
      rw [hx_eq, suzukiB_pow_conj_zero, hi] at hconj_mem
      have hmul_one : (((Units.mk0 v hv0)⁻¹ : GF8ˣ) : GF8) * v = 1 :=
        inv_mul_cancel₀ hv0
      rw [hmul_one] at hconj_mem
      exact hz₀ hconj_mem
    have hWU_eq1 : ∀ g : W_U, g = 1 := by
      intro ⟨gU, hgM⟩
      have hgM' : (gU : SzB) ∈ M := hgM
      obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff card_GF).1 gU.2
      have hg_eq : (gU : SzB) = suzukiSElt 1 GF8 u v := huv.symm
      have hg2M : suzukiSElt 1 GF8 0 (u ^ 5) ∈ M := by
        rw [← suzukiSElt_sq u v, ← hg_eq]
        exact M.pow_mem hgM' 2
      have hu5 : u ^ 5 = 0 := hMZ_triv (u ^ 5) hg2M
      have hu0 : u = 0 := gf8_pow5_eq_zero hu5
      subst hu0
      rw [hg_eq] at hgM'
      have hv0 : v = 0 := hMZ_triv v hgM'
      subst hv0
      apply Subtype.ext
      apply Subtype.ext
      rw [hg_eq, suzukiSElt_zero_zero card_GF]
      rfl
    have hWU_one : Nat.card W_U = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hWU_eq1 a).trans (hWU_eq1 b).symm⟩, ⟨1⟩⟩
    rw [hWU_one, mul_one] at hWU_mul
    omega
  · -- Case 2: 7 does not divide |M ∩ B|
    have hcop : Nat.Coprime (Nat.card W_B) 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).2 h7).symm
    have hMB_le_U : ∀ g ∈ B, g ∈ M → g ∈ U := by
      intro g hgB hgM
      obtain ⟨⟨⟨u, v⟩, l⟩, hg_eq, -⟩ := (suzuki_borel_structure card_GF).2.2.2.2.2.2.1 g hgB
      dsimp only at hg_eq
      let w : W_B := ⟨⟨g, hgB⟩, hgM⟩
      have hw_pow : w ^ Nat.card W_B = 1 := pow_card_eq_one'
      have hg_pow : g ^ Nat.card W_B = 1 :=
        congrArg (fun x : W_B => (x.1 : SzB)) hw_pow
      obtain ⟨u', v', hdecomp⟩ := suzukiB_pow_decomp u v l (Nat.card W_B)
      rw [hg_eq] at hg_pow
      obtain ⟨p₀, -, hp₀_uniq⟩ := (suzuki_borel_structure card_GF).2.2.2.2.2.2.1 1 B.one_mem
      have hp1 := hp₀_uniq ⟨(u', v'), l ^ Nat.card W_B⟩ (by
        dsimp only
        rw [← hdecomp, hg_pow])
      have hp2 := hp₀_uniq ⟨(0, 0), 1⟩ (by
        dsimp only
        rw [suzukiSElt_zero_zero card_GF, suzukiDElt_one, mul_one])
      have hl_pow : l ^ Nat.card W_B = 1 := congrArg Prod.snd (hp1.trans hp2.symm)
      have hdvd1 : orderOf l ∣ Nat.card W_B := orderOf_dvd_of_pow_eq_one hl_pow
      have hdvd2 : orderOf l ∣ 7 := orderOf_dvd_of_pow_eq_one (gf8_units_pow7 l)
      have hdvd_gcd : orderOf l ∣ Nat.gcd (Nat.card W_B) 7 := Nat.dvd_gcd hdvd1 hdvd2
      rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd_gcd
      rw [hg_eq, hdvd_gcd, suzukiDElt_one, mul_one]
      exact suzukiSElt_mem_suzukiU 1 GF8 u v
    have hcard_WB_le_WU : Nat.card W_B ≤ Nat.card W_U := by
      let f : W_B → W_U := fun x => ⟨⟨x.1.1, hMB_le_U x.1.1 x.1.2 x.2⟩, x.2⟩
      have hf : Function.Injective f := by
        intro x y hxy
        exact Subtype.ext (Subtype.ext (congrArg (fun z : W_U => (z.1 : SzB)) hxy))
      exact Nat.card_le_card_of_injective f hf
    by_cases hz2 : ∃ z₁ ∈ M, ∃ z₂ ∈ M, z₁ ∈ Z ∧ z₁ ≠ 1 ∧ z₂ ∈ Z ∧ z₂ ≠ 1 ∧ z₁ ≠ z₂
    · -- Subcase 2a: M ∩ Z contains two distinct non-identity elements z₁ ≠ z₂
      rcases hz2 with ⟨z₁, hz₁M, z₂, hz₂M, hz₁Z, hz₁1, hz₂Z, hz₂1, hz12⟩
      by_cases hMB : M ≤ B
      · have hcardM_le : Nat.card M ≤ 448 := by
          rw [← suzuki_card_B]
          exact Subgroup.card_le_of_le hMB
        have hM_mul : M.index * Nat.card M = 29120 := by
          rw [Subgroup.index_mul_card, card_SzB]
        have h29120 : 29120 ≤ M.index * 448 :=
          hM_mul ▸ Nat.mul_le_mul_left M.index hcardM_le
        omega
      · exfalso
        have hy_ex : ∃ y ∈ M, y ∉ B := by
          by_contra! h
          exact hMB h
        rcases hy_ex with ⟨y, hyM, hyB⟩
        have hz₁U : z₁ ∈ U := suzukiZ0_le_suzukiU hz₁Z
        have hz₂U : z₂ ∈ U := suzukiZ0_le_suzukiU hz₂Z
        have hz₁_sq : z₁ * z₁ = 1 := by
          obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff card_GF).1 hz₁Z
          exact suzukiSElt_zero_sq v
        have hz₂_sq : z₂ * z₂ = 1 := by
          obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff card_GF).1 hz₂Z
          exact suzukiSElt_zero_sq v
        set u := y * z₁ * y⁻¹
        have huM : u ∈ M := M.mul_mem (M.mul_mem hyM hz₁M) (M.inv_mem hyM)
        have hu_sq : u * u = 1 := by
          dsimp only [u]
          calc (y * z₁ * y⁻¹) * (y * z₁ * y⁻¹) = y * (z₁ * z₁) * y⁻¹ := by group
            _ = 1 := by rw [hz₁_sq]; group
        set w := u * z₂
        have hwM : w ∈ M := M.mul_mem huM hz₂M
        have hw_pos : 0 < orderOf w := orderOf_pos w
        rcases Nat.even_or_odd (orderOf w) with ⟨m, hm⟩ | ⟨k, hk⟩
        · -- Even orderOf w = m + m
          have hm_pos : 0 < m := by omega
          have hm_lt : m < orderOf w := by omega
          set c := w ^ m
          have hcM : c ∈ M := M.pow_mem hwM m
          have hc_ne1 : c ≠ 1 := pow_ne_one_of_lt_orderOf hm_pos.ne' hm_lt
          have hc_sq : c * c = 1 := by
            change w ^ m * w ^ m = 1
            rw [← pow_add, ← hm, pow_orderOf_eq_one]
          have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc_sq
          have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu_sq
          have hz₂_inv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂_sq
          have hu_w : u * w * u⁻¹ = w⁻¹ := by
            change u * (u * z₂) * u⁻¹ = (u * z₂)⁻¹
            rw [mul_inv_rev u z₂, hu_inv, hz₂_inv, ← mul_assoc u u z₂, hu_sq, one_mul]
          have hz₂_w : z₂ * w * z₂⁻¹ = w⁻¹ := by
            change z₂ * (u * z₂) * z₂⁻¹ = (u * z₂)⁻¹
            rw [mul_inv_rev u z₂, hu_inv, hz₂_inv, ← mul_assoc z₂ u z₂,
              mul_assoc (z₂ * u) z₂ z₂, hz₂_sq, mul_one]
          have hu_c : u * c * u⁻¹ = c := by
            change MulAut.conj u (w ^ m) = c
            rw [map_pow, MulAut.conj_apply, hu_w, inv_pow, hc_inv]
          have hz₂_c : z₂ * c * z₂⁻¹ = c := by
            change MulAut.conj z₂ (w ^ m) = c
            rw [map_pow, MulAut.conj_apply, hz₂_w, inv_pow, hc_inv]
          have hc_z₂ : c * z₂ * c⁻¹ = z₂ := by
            calc c * z₂ * c⁻¹ = (z₂ * c * z₂⁻¹) * z₂ * c⁻¹ := by rw [hz₂_c]
              _ = z₂ := by group
          have hc_u : c * u * c⁻¹ = u := by
            calc c * u * c⁻¹ = (u * c * u⁻¹) * u * c⁻¹ := by rw [hu_c]
              _ = u := by group
          have hcB : c ∈ B :=
            mem_suzukiB_of_conj_mem_suzukiU hz₂U hz₂1 (hc_z₂.symm ▸ hz₂U)
          have hcU : c ∈ U := hMB_le_U c hcB hcM
          have hycy_z₁ : (y⁻¹ * c * y) * z₁ * (y⁻¹ * c * y)⁻¹ = z₁ := by
            calc (y⁻¹ * c * y) * z₁ * (y⁻¹ * c * y)⁻¹
                = y⁻¹ * (c * (y * z₁ * y⁻¹) * c⁻¹) * y := by group
              _ = y⁻¹ * (y * z₁ * y⁻¹) * y := by rw [hc_u]
              _ = z₁ := by group
          have hycyM : y⁻¹ * c * y ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hyM) hcM) hyM
          have hycyB : y⁻¹ * c * y ∈ B :=
            mem_suzukiB_of_conj_mem_suzukiU hz₁U hz₁1 (hycy_z₁.symm ▸ hz₁U)
          have hycyU : y⁻¹ * c * y ∈ U := hMB_le_U _ hycyB hycyM
          have hyinvB : y⁻¹ ∈ B := by
            refine mem_suzukiB_of_conj_mem_suzukiU hcU hc_ne1 ?_
            simpa only [inv_inv] using hycyU
          exact hyB (B.inv_mem_iff.mp hyinvB)
        · -- Odd orderOf w = 2 * k + 1
          have hw_conj : w ^ k * u * (w ^ k)⁻¹ = z₂ := by
            have h1 := involution_mul_pow_conj hu_sq hz₂_sq k
            change w ^ k * u * (w ^ k)⁻¹ = w ^ (2 * k + 1) * z₂ at h1
            rw [← hk, pow_orderOf_eq_one, one_mul] at h1
            exact h1
          set g := w ^ k * y
          have hgM : g ∈ M := M.mul_mem (M.pow_mem hwM k) hyM
          have hg_z₁ : g * z₁ * g⁻¹ = z₂ := by
            calc (w ^ k * y) * z₁ * (w ^ k * y)⁻¹
                = w ^ k * (y * z₁ * y⁻¹) * (w ^ k)⁻¹ := by group
              _ = z₂ := hw_conj
          have hgB : g ∈ B :=
            mem_suzukiB_of_conj_mem_suzukiU hz₁U hz₁1 (hg_z₁.symm ▸ hz₂U)
          have hgU : g ∈ U := hMB_le_U g hgB hgM
          have hcomm_z₁ : z₁ * g = g * z₁ :=
            (suzuki_unipotent_structure card_GF).2.2.2.2.2.1 z₁ hz₁Z g hgU
          have hg_z₁_eq : g * z₁ * g⁻¹ = z₁ := by
            rw [← hcomm_z₁, mul_inv_cancel_right]
          exact hz12 (hg_z₁_eq.symm.trans hg_z₁)
    · -- Subcase 2b: M ∩ Z has at most one non-identity element
      push Not at hz2
      classical
      let z₁ : W_U :=
        if h : ∃ z : W_U, (z.1 : SzB) ∈ Z ∧ z ≠ 1 then Classical.choose h else 1
      have hz_two : ∀ z : W_U, (z.1 : SzB) ∈ Z → z = 1 ∨ z = z₁ := by
        intro z hzZ
        by_cases hz1 : z = 1
        · exact Or.inl hz1
        · right
          have hex : ∃ z : W_U, (z.1 : SzB) ∈ Z ∧ z ≠ 1 := ⟨z, hzZ, hz1⟩
          dsimp only [z₁]
          rw [dite_eq_left_of_eq_true (eq_true hex)]
          have hspec := Classical.choose_spec hex
          have hz_ne1 : (z.1 : SzB) ≠ 1 := by
            intro h1
            exact hz1 (Subtype.ext (Subtype.ext h1))
          have hchoose_ne1 : ((Classical.choose hex).1 : SzB) ≠ 1 := by
            intro h1
            exact hspec.2 (Subtype.ext (Subtype.ext h1))
          have heq := hz2 (z.1 : SzB) z.2 ((Classical.choose hex).1 : SzB)
            (Classical.choose hex).2 hzZ hz_ne1 hspec.1 hchoose_ne1
          exact Subtype.ext (Subtype.ext heq)
      let s₁ : W_U :=
        if h : ∃ s : W_U, (s.1 : SzB) ∉ Z then Classical.choose h else 1
      have hs_two : ∀ g : W_U, (g.1 : SzB) ∈ Z ∨ (((s₁⁻¹ * g : W_U).1 : SzB) ∈ Z) := by
        intro g
        by_cases hgZ : (g.1 : SzB) ∈ Z
        · exact Or.inl hgZ
        · right
          have hex : ∃ s : W_U, (s.1 : SzB) ∉ Z := ⟨g, hgZ⟩
          have hs₁_notZ : (s₁.1 : SzB) ∉ Z := by
            dsimp only [s₁]
            rw [dite_eq_left_of_eq_true (eq_true hex)]
            exact Classical.choose_spec hex
          obtain ⟨u, v, huv⟩ := (mem_suzukiU_iff card_GF).1 g.1.2
          obtain ⟨u₁, v₁, huv₁⟩ := (mem_suzukiU_iff card_GF).1 s₁.1.2
          have hg_eq : (g.1 : SzB) = suzukiSElt 1 GF8 u v := huv.symm
          have hs₁_eq : (s₁.1 : SzB) = suzukiSElt 1 GF8 u₁ v₁ := huv₁.symm
          have hu0 : u ≠ 0 := by
            intro hu0
            subst hu0
            exact hgZ ((mem_suzukiZ0_iff card_GF).2 ⟨v, hg_eq.symm⟩)
          have hu₁0 : u₁ ≠ 0 := by
            intro hu₁0
            subst hu₁0
            exact hs₁_notZ ((mem_suzukiZ0_iff card_GF).2 ⟨v₁, hs₁_eq.symm⟩)
          have hg2M : suzukiSElt 1 GF8 0 (u ^ 5) ∈ M := by
            rw [← suzukiSElt_sq u v, ← hg_eq]
            exact M.pow_mem g.2 2
          have hs₁2M : suzukiSElt 1 GF8 0 (u₁ ^ 5) ∈ M := by
            rw [← suzukiSElt_sq u₁ v₁, ← hs₁_eq]
            exact M.pow_mem s₁.2 2
          have hg2Z : suzukiSElt 1 GF8 0 (u ^ 5) ∈ Z :=
            (mem_suzukiZ0_iff card_GF).2 ⟨u ^ 5, rfl⟩
          have hs₁2Z : suzukiSElt 1 GF8 0 (u₁ ^ 5) ∈ Z :=
            (mem_suzukiZ0_iff card_GF).2 ⟨u₁ ^ 5, rfl⟩
          have hg2_ne1 : suzukiSElt 1 GF8 0 (u ^ 5) ≠ 1 := by
            intro h1
            rw [← suzukiSElt_zero_zero card_GF, suzukiSElt_inj] at h1
            exact pow_ne_zero 5 hu0 h1.2
          have hs₁2_ne1 : suzukiSElt 1 GF8 0 (u₁ ^ 5) ≠ 1 := by
            intro h1
            rw [← suzukiSElt_zero_zero card_GF, suzukiSElt_inj] at h1
            exact pow_ne_zero 5 hu₁0 h1.2
          have hsq_eq := hz2 _ hg2M _ hs₁2M hg2Z hg2_ne1 hs₁2Z hs₁2_ne1
          have hu5_eq : u ^ 5 = u₁ ^ 5 := (suzukiSElt_inj.1 hsq_eq).2
          have hu_eq : u = u₁ := gf8_pow5_inj hu5_eq
          subst hu_eq
          change (s₁.1 : SzB)⁻¹ * (g.1 : SzB) ∈ Z
          rw [hs₁_eq, hg_eq, suzukiSElt_inv card_GF, suzukiSElt_mul card_GF, gf8_add_self]
          exact (mem_suzukiZ0_iff card_GF).2 ⟨_, rfl⟩
      have hWU_le4 : Nat.card W_U ≤ 4 := by
        let f : Fin 4 → W_U := ![1, z₁, s₁, s₁ * z₁]
        have hf : Function.Surjective f := by
          intro g
          rcases hs_two g with hgZ | hsgZ
          · rcases hz_two g hgZ with rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
          · rcases hz_two (s₁⁻¹ * g) hsgZ with h1 | h2
            · refine ⟨2, ?_⟩
              dsimp only [f]
              exact eq_of_inv_mul_eq_one h1
            · refine ⟨3, ?_⟩
              dsimp only [f]
              calc s₁ * z₁ = s₁ * (s₁⁻¹ * g) := by rw [h2]
                _ = g := mul_inv_cancel_left s₁ g
        simpa [Nat.card_fin] using
          Nat.card_le_card_of_injective (Function.surjInv hf) (Function.injective_surjInv hf)
      have h448 : 448 ≤ W_B.index * 4 :=
        hWB_mul ▸ Nat.mul_le_mul_left W_B.index (hcard_WB_le_WU.trans hWU_le4)
      omega

end SuzukiIndex

attribute [local irreducible] CFSG.Sporadic.Ru.Native.ruData

/-- Every proper subgroup of `Ru` has index at least `64`. -/
theorem index_ge_Ru {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .Ru) {H : Subgroup S} (hH : H ≠ ⊤) :
    64 ≤ H.index := by
  obtain ⟨eP⟩ : Nonempty (S ≃* ruP) := ⟨e.trans (ruSeedEquiv.trans ruJEquivP)⟩
  obtain ⟨eK⟩ := exists_mulEquiv_K0
  have hK0_le_P : K0 ≤ ruP := K0_le_L.trans ruL_le
  let ιP : K0 →* ruP := Subgroup.inclusion hK0_le_P
  let ι : SzB →* S := eP.symm.toMonoidHom.comp (ιP.comp eK.toMonoidHom)
  have hι_inj : Function.Injective ι :=
    eP.symm.injective.comp ((Subgroup.inclusion_injective hK0_le_P).comp eK.injective)
  set z₀ : SzB := suzukiSElt 1 GF8 0 1
  have hz₀_ne1 : z₀ ≠ 1 := by
    intro h1
    rw [← suzukiSElt_zero_zero card_GF, suzukiSElt_inj] at h1
    exact one_ne_zero h1.2
  have hιz₀_ne1 : ι z₀ ≠ 1 := by
    intro h1
    exact hz₀_ne1 (hι_inj (h1.trans (map_one ι).symm))
  have _ : FaithfulSMul S (S ⧸ H) := faithfulSMul_quotient_of_ne_top hH
  obtain ⟨q, hq⟩ := exists_stabilizer_not_le (α := S ⧸ H) (Subgroup.zpowers_ne_bot.mpr hιz₀_ne1)
  let K := MulAction.stabilizer S q
  let M : Subgroup SzB := K.comap ι
  have hz₀_not_M : z₀ ∉ M := fun hz0 => hq (Subgroup.zpowers_le.mpr hz0)
  have h64 : 64 ≤ M.index := szB_sixty_four_le_index M hz₀_not_M
  let φQ : SzB ⧸ M → S ⧸ K :=
    Quotient.lift (fun g => (ι g : S ⧸ K)) fun a b hab => by
      have hab' : (a : SzB ⧸ M) = b := Quotient.sound hab
      rw [QuotientGroup.eq] at hab'
      change ι (a⁻¹ * b) ∈ K at hab'
      rw [map_mul, map_inv] at hab'
      exact QuotientGroup.eq.mpr hab'
  have hφQ : Function.Injective φQ := by
    intro u v huv
    induction u using QuotientGroup.induction_on with | H a =>
    induction v using QuotientGroup.induction_on with | H b =>
    change (ι a : S ⧸ K) = (ι b : S ⧸ K) at huv
    rw [QuotientGroup.eq, ← map_inv, ← map_mul] at huv
    exact QuotientGroup.eq.mpr huv
  have hidx_le : M.index ≤ K.index := Nat.card_le_card_of_injective φQ hφQ
  exact (h64.trans hidx_le).trans (index_stabilizer_le_card q)

/-- Maróti's bound for primitive almost simple groups with socle `Ru`. -/
theorem sporadicCase_Ru {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type)
    [Group S] [MulAction.IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .Ru)) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  obtain ⟨eP⟩ : Nonempty (S ≃* ruP) := ⟨e.trans (ruSeedEquiv.trans ruJEquivP)⟩
  have hcard : Nat.card S = 145926144000 := by
    rw [Nat.card_congr eP.toEquiv]
    exact card_ruP
  refine hS.card_le_bound_of_outerAut_dvd (n₀ := 64) (c := 2) (by decide)
    (fun H hH => index_ge_Ru e hH)
    (card_outer_dvd_two_of_sporadicSocle ⟨.Ru, ⟨e⟩⟩) ?_
  rw [hcard]
  decide

end Maroti
