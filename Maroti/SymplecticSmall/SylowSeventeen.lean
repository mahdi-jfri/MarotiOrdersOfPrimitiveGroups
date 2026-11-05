module

public import Maroti.Interface
import CFSG.Open.StatedAPI
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

/-!
# Sylow `17` Arguments for `PSp(4, 4)` and `PSp(8, 2)`

This file proves two subgroup-index exclusions needed for the even-characteristic symplectic case of
Theorem 1.1 (Maróti, Section 2, Step 2, page 634):
* The theorem `Maroti.index_ne_twentyFour_pSp_four_four`: `PSp(4, 4)` has no subgroup of index `24`.
* The theorem `Maroti.not_index_mem_pSp_eight_two`: `PSp(8, 2)` has no subgroup `H` with
  `56 ≤ H.index ≤ 63`.

Both results use the action of a Sylow `17`-subgroup `P` of `S` on the coset space `S ⧸ H` when
`17 ∤ H.index`:
1. The number `f` of fixed points of `P` on `S ⧸ H` satisfies `f ≡ H.index [MOD 17]` and `0 < f`.
2. Since `S` is simple and `H ≠ ⊤`, `f < H.index` (otherwise `P` lies in the normal core of `H`).
3. By Witt's lemma, `N_S(P)` acts transitively on the fixed points of `P` in `S ⧸ H` with point
   stabilizer containing `P`, so `f` divides `[N_S(P) : P]` (and in particular `f ∣ |S|`).

For `PSp(4, 4)` (`|S| = 979200 = 2^8 · 3^2 · 5^2 · 17`), `H.index = 24` gives `f ≡ 7 [MOD 17]` and
`f < 24`, so `f = 7`, contradicting `7 ∤ 979200`.

For `PSp(8, 2) ≅ Sp(8, 2)` (`|S| = 47377612800 = 2^16 · 3^5 · 5^2 · 7 · 17`), an explicit element
`gSp ∈ StatedSp 4 (ZMod 2)` of order `17` has cyclic vector `Sum.inl 0` (the vectors `gSp^k e₀` for
`0 ≤ k < 8` form an invertible matrix `bMat`), so any matrix commuting with `gSp` is a linear
combination of `1, gSp, …, gSp^7`. Among the `256` such linear combinations, only the `17` powers of
`gSp` preserve the symplectic form, proving `C_S(P) = P` (`|C_S(P)| = 17`) and therefore
`[N_S(P) : P] ∣ 16`. None of the possible indices `m ∈ [56, 63]` dividing `|S|` (`56, 60, 63`) has a
positive residue modulo `17` (`5, 9, 12`) dividing `16`.
-/

@[expose] public section

namespace Maroti

open Matrix Subgroup CFSG.Open CFSG.Open.StatedAPI

namespace SymplecticSmall

/-! ### 1. General Sylow fixed-point lemma on cosets -/

/-- If `P` is a Sylow `r`-subgroup of a finite group `S`, and `x : S ⧸ H`
is fixed by `P`, then `P` is the image of a Sylow `r`-subgroup of `MulAction.stabilizer S x`. -/
private theorem exists_sylow_stabilizer_eq_of_mem_fixedPoints {S : Type*} [Group S] [Finite S]
    {r : ℕ} [Fact r.Prime] (P : Sylow r S) {H : Subgroup S}
    {x : S ⧸ H} (hx : x ∈ MulAction.fixedPoints (P : Subgroup S) (S ⧸ H)) :
    ∃ Q : Sylow r (MulAction.stabilizer S x),
      (Q : Subgroup (MulAction.stabilizer S x)).map (MulAction.stabilizer S x).subtype =
        (P : Subgroup S) := by
  let D := MulAction.stabilizer S x
  have hPD : (P : Subgroup S) ≤ D := by
    intro g hg
    exact MulAction.mem_stabilizer_iff.mpr (MulAction.mem_fixedPoints.mp hx ⟨g, hg⟩)
  let PD : Subgroup D := (P : Subgroup S).subgroupOf D
  have hPD_p : IsPGroup r PD :=
    P.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  have hPD_idx : ¬ r ∣ PD.index := by
    intro hdvd
    apply P.not_dvd_index
    have h1 : (PD.map D.subtype).index = PD.index * D.index := Subgroup.index_map_subtype PD
    rw [Subgroup.map_subgroupOf_eq_of_le hPD] at h1
    rw [h1]
    exact dvd_mul_of_dvd_left hdvd D.index
  let Q : Sylow r D := hPD_p.toSylow hPD_idx
  refine ⟨Q, ?_⟩
  have hQ_coe : (Q : Subgroup D) = PD := IsPGroup.toSylow_coe hPD_p hPD_idx
  rw [hQ_coe]
  exact Subgroup.map_subgroupOf_eq_of_le hPD

/-- Witt's transporter on `S ⧸ H`: if `P : Sylow r S` fixes `x, y : S ⧸ H`,
then some `n ∈ Subgroup.normalizer ((P : Subgroup S) : Set S)` satisfies `(n : S) • x = y`. -/
private theorem exists_normalizer_smul_eq_of_mem_fixedPoints {S : Type*} [Group S] [Finite S]
    {r : ℕ} [Fact r.Prime] (P : Sylow r S) {H : Subgroup S}
    {x y : S ⧸ H} (hx : x ∈ MulAction.fixedPoints (P : Subgroup S) (S ⧸ H))
    (hy : y ∈ MulAction.fixedPoints (P : Subgroup S) (S ⧸ H)) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup S) : Set S), n • x = y := by
  obtain ⟨g, hgx⟩ := MulAction.exists_smul_eq S x y
  let Dy := MulAction.stabilizer S y
  obtain ⟨Qy, hQy⟩ := exists_sylow_stabilizer_eq_of_mem_fixedPoints P hy
  have hx_conj : y ∈ MulAction.fixedPoints (g • P : Sylow r S) (S ⧸ H) := by
    rw [MulAction.mem_fixedPoints]
    rintro ⟨k, hk⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hk
    have hkx : (g⁻¹ * k * g) • x = x := MulAction.mem_fixedPoints.mp hx ⟨_, hk⟩
    calc k • y = k • (g • x) := by rw [← hgx]
      _ = g • ((g⁻¹ * k * g) • x) := by simp [mul_smul]
      _ = g • x := by rw [hkx]
      _ = y := hgx
  obtain ⟨Q', hQ'⟩ := exists_sylow_stabilizer_eq_of_mem_fixedPoints (g • P) hx_conj
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq Dy Q' Qy
  refine ⟨(d : S) * g, ?_, ?_⟩
  · change (d : S) * g ∈ Subgroup.normalizer (P : Set S)
    rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul]
    apply Sylow.ext
    rw [Sylow.coe_subgroup_smul, ← hQ', ← hQy, ← hd, Sylow.coe_subgroup_smul]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]
    constructor
    · rintro ⟨u, hu, hzu⟩
      refine ⟨d * u * d⁻¹, ?_, ?_⟩
      · convert hu using 1
        group
      · change (d : S) * (u : S) * (d : S)⁻¹ = z
        rw [hzu]
        group
    · rintro ⟨u, hu, rfl⟩
      exact ⟨d⁻¹ * u * d, hu, by simp [mul_assoc]⟩
  · rw [mul_smul, hgx, MulAction.mem_stabilizer_iff.mp d.2]

/-- In a finite group `S`, if `P : Sylow r S` and `H ≤ S` has `H.normalCore = ⊥` and
`¬ r ∣ H.index`, then the number `f` of fixed points of `P` on `S ⧸ H` satisfies
`f ≡ H.index [MOD r]`, `0 < f`, `f < H.index`, and
`f ∣ (P.subgroupOf (Subgroup.normalizer (P : Set S))).index`. -/
private theorem exists_fixedPoints_sylow_quotient {S : Type*} [Group S] [Finite S]
    {r : ℕ} [Fact r.Prime] (P : Sylow r S) {H : Subgroup S}
    (hcore : H.normalCore = ⊥) (hr : ¬ r ∣ H.index) (hP_ne_bot : (P : Subgroup S) ≠ ⊥) :
    ∃ f : ℕ, f ≡ H.index [MOD r] ∧ 0 < f ∧ f < H.index ∧
      f ∣ ((P : Subgroup S).subgroupOf (Subgroup.normalizer ((P : Subgroup S) : Set S))).index := by
  classical
  let FP := MulAction.fixedPoints (P : Subgroup S) (S ⧸ H)
  have hmod : Nat.card (S ⧸ H) ≡ Nat.card FP [MOD r] :=
    P.isPGroup'.card_modEq_card_fixedPoints (S ⧸ H)
  have hidx_eq : Nat.card (S ⧸ H) = H.index := rfl
  rw [hidx_eq] at hmod
  have hf_pos : 0 < Nat.card FP := by
    by_contra h0
    have hf0 : Nat.card FP = 0 := by omega
    rw [hf0] at hmod
    exact hr (Nat.modEq_zero_iff_dvd.mp hmod)
  have hFP_nonempty : Nonempty FP := (Nat.card_pos_iff.mp hf_pos).1
  obtain ⟨⟨x₀, hx₀⟩⟩ := hFP_nonempty
  have hf_lt : Nat.card FP < H.index := by
    have _ : Fintype (S ⧸ H) := Fintype.ofFinite (S ⧸ H)
    have _ : Fintype FP := Fintype.ofFinite FP
    have hle : Nat.card FP ≤ H.index := by
      rw [← hidx_eq]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hsurj : Function.Surjective (Subtype.val : FP → S ⧸ H) := by
        refine (Finite.injective_iff_surjective_of_equiv ?_).mp Subtype.val_injective
        exact Fintype.equivOfCardEq (by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, heq, hidx_eq])
      have hP_le_core : (P : Subgroup S) ≤ H.normalCore := by
        rw [Subgroup.normalCore_eq_ker]
        intro g hg
        rw [MonoidHom.mem_ker]
        ext y
        obtain ⟨⟨y', hy'⟩, rfl⟩ := hsurj y
        exact MulAction.mem_fixedPoints.mp hy' ⟨g, hg⟩
      rw [hcore, le_bot_iff] at hP_le_core
      exact hP_ne_bot hP_le_core
  set N := Subgroup.normalizer ((P : Subgroup S) : Set S)
  let _ : MulAction N FP :=
    { smul := fun n y => ⟨(n : S) • y.1, by
        rw [MulAction.mem_fixedPoints]
        rintro ⟨p, hp⟩
        have hp' : (n : S)⁻¹ * p * (n : S) ∈ (P : Subgroup S) :=
          (Subgroup.mem_normalizer_iff''.mp n.2 p).mp hp
        have hy' : ((n : S)⁻¹ * p * (n : S)) • y.1 = y.1 :=
          MulAction.mem_fixedPoints.mp y.2 ⟨_, hp'⟩
        calc p • ((n : S) • y.1) = (n : S) • (((n : S)⁻¹ * p * (n : S)) • y.1) := by
              simp [mul_smul]
          _ = (n : S) • y.1 := by rw [hy']⟩
      one_smul := fun y => Subtype.ext (one_smul S y.1)
      mul_smul := fun n₁ n₂ y => Subtype.ext (mul_smul (n₁ : S) (n₂ : S) y.1) }
  have htransN : MulAction.IsPretransitive N FP := by
    refine ⟨fun y₁ y₂ => ?_⟩
    obtain ⟨n, hn, hny⟩ := exists_normalizer_smul_eq_of_mem_fixedPoints P y₁.2 y₂.2
    exact ⟨⟨n, hn⟩, Subtype.ext hny⟩
  let S₀ := MulAction.stabilizer N (⟨x₀, hx₀⟩ : FP)
  have hFP_card : Nat.card FP = S₀.index := by
    have heq1 : MulAction.orbit N (⟨x₀, hx₀⟩ : FP) = Set.univ :=
      MulAction.orbit_eq_univ N (⟨x₀, hx₀⟩ : FP)
    have heq2 := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N (⟨x₀, hx₀⟩ : FP))
    rw [heq1, Nat.card_coe_set_eq, Set.ncard_univ] at heq2
    exact heq2
  let PN : Subgroup N := (P : Subgroup S).subgroupOf N
  have hPN_le_S₀ : PN ≤ S₀ := by
    intro n hn
    rw [MulAction.mem_stabilizer_iff]
    exact Subtype.ext (MulAction.mem_fixedPoints.mp hx₀ ⟨n.1, hn⟩)
  have hdvd : S₀.index ∣ PN.index := by
    rw [← Subgroup.relIndex_mul_index hPN_le_S₀]
    exact dvd_mul_left S₀.index (PN.relIndex S₀)
  exact ⟨Nat.card FP, hmod.symm, hf_pos, hf_lt, hFP_card ▸ hdvd⟩

/-! ### 2. The group `PSp(4, 4)` has no subgroup of index `24` -/

/-- No subgroup of `PSp(4, 4)` has index `24`. -/
theorem index_ne_twentyFour_pSp_four_four (S : Type) [Group S]
    (hS : CFSG.Open.StatedClassicalModel S .PSp 2 2 2) (H : Subgroup S) :
    H.index ≠ 24 := by
  intro h24
  have hsimple : IsSimpleGroup S :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp S 2 2 2 hS
  have hcard : Nat.card S = 979200 := by
    rw [(CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound S 2 2 2 hS).1]
    decide
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have hH_ne_top : H ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at h24
    omega
  have hcore : H.normalCore = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_unique (h ▸ H.normalCore_le)) hH_ne_top
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  obtain ⟨P⟩ : Nonempty (Sylow 17 S) := Sylow.nonempty
  have hP_card : Nat.card (P : Subgroup S) = 17 := by
    rw [Sylow.card_eq_multiplicity, hcard, show (979200 : ℕ) = 17 ^ 1 * 57600 by decide,
      Nat.factorization_mul_of_coprime (by decide), Nat.Prime.factorization_pow (by decide),
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 17 ∣ 57600)]
    decide
  have hP_ne_bot : (P : Subgroup S) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hP_card
    omega
  have hr : ¬ 17 ∣ H.index := by
    rw [h24]
    decide
  obtain ⟨f, hf_mod, hf_pos, hf_lt, hf_dvd⟩ :=
    exists_fixedPoints_sylow_quotient P hcore hr hP_ne_bot
  rw [h24] at hf_mod hf_lt
  have hf7 : f = 7 := by
    change f % 17 = 24 % 17 at hf_mod
    omega
  set N := Subgroup.normalizer ((P : Subgroup S) : Set S)
  let PN : Subgroup N := (P : Subgroup S).subgroupOf N
  have hPN_dvd_N : PN.index ∣ Nat.card N := ⟨Nat.card PN, (Subgroup.index_mul_card PN).symm⟩
  have hN_dvd_S : Nat.card N ∣ Nat.card S := Subgroup.card_subgroup_dvd_card N
  have hf_dvd_S : f ∣ 979200 := by
    rw [← hcard]
    exact (hf_dvd.trans hPN_dvd_N).trans hN_dvd_S
  rw [hf7] at hf_dvd_S
  exact (by decide : ¬ 7 ∣ 979200) hf_dvd_S

/-! ### 3. The group `PSp(8, 2)` has no subgroup of index in `[56, 63]` -/

namespace SylowSeventeen

/-- Decidable equality on `StatedSp 4 (ZMod 2)` induced by underlying `8 × 8` matrices. -/
local instance instDecidableEqStatedSpFourTwo : DecidableEq (StatedSp 4 (ZMod 2)) :=
  fun a b => decidable_of_iff
    (((a : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) =
     ((b : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)))
    ⟨fun h => Subtype.ext (Units.ext h),
     fun h => congrArg (fun g : StatedSp 4 (ZMod 2) =>
       ((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))) h⟩

/-- Helper constructor for elements of `StatedSp 4 (ZMod 2)` from explicit `8 × 8` matrices. -/
def mkSp82 (M Minv : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))
    (h1 : M * Minv = 1) (h2 : Minv * M = 1)
    (hJ : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0) :
    StatedSp 4 (ZMod 2) :=
  ⟨⟨M, Minv, h1, h2⟩, mem_statedSp_iff.mpr hJ⟩

/-- Matrix of an element `gSp` of order `17` in `StatedSp 4 (ZMod 2)`. -/
def gMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks
    !![1, 0, 0, 1; 0, 1, 1, 1; 1, 0, 1, 1; 0, 1, 1, 1]
    !![0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0; 1, 0, 0, 1]
    !![1, 0, 0, 1; 0, 0, 0, 1; 1, 0, 1, 1; 0, 0, 0, 1]
    !![1, 0, 1, 1; 0, 1, 1, 1; 1, 1, 1, 0; 0, 0, 1, 1]

/-- Inverse of `gMat`. -/
def gInvMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks
    !![1, 0, 1, 0; 0, 1, 1, 0; 1, 1, 1, 1; 1, 1, 0, 1]
    !![0, 0, 1, 1; 1, 1, 0, 0; 0, 0, 0, 0; 1, 0, 0, 1]
    !![1, 0, 1, 0; 0, 0, 0, 0; 0, 0, 1, 0; 1, 1, 1, 1]
    !![1, 0, 1, 0; 0, 1, 0, 1; 0, 1, 1, 1; 1, 1, 1, 1]

/-- Cyclic-basis matrix `bMat` whose columns are `gMat ^ k * e₀` (`0 ≤ k < 8`). -/
def bMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks
    !![1, 1, 1, 1; 0, 0, 1, 1; 0, 1, 1, 1; 0, 0, 0, 0]
    !![0, 0, 0, 1; 0, 0, 0, 0; 1, 0, 0, 0; 0, 1, 0, 1]
    !![0, 1, 1, 1; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 1]
    !![1, 1, 0, 0; 1, 1, 0, 0; 1, 0, 1, 1; 1, 0, 1, 0]

/-- Inverse of `bMat`. -/
def bInvMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  fromBlocks
    !![1, 0, 0, 0; 0, 1, 1, 1; 0, 0, 1, 1; 0, 1, 1, 1]
    !![0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 1, 1; 0, 1, 1, 1]
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 1]
    !![1, 0, 1, 1; 1, 0, 0, 0; 1, 0, 1, 0; 1, 0, 0, 0]

/-- Explicit element `gSp` of order `17` in `StatedSp 4 (ZMod 2)`. -/
def gSp : StatedSp 4 (ZMod 2) :=
  mkSp82 gMat gInvMat (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem gSp_pow_seventeen : gSp ^ 17 = 1 := by decide +kernel

private theorem gSp_ne_one : gSp ≠ 1 := by decide +kernel

private theorem orderOf_gSp : orderOf gSp = 17 := by
  have hdvd : orderOf gSp ∣ 17 := orderOf_dvd_of_pow_eq_one gSp_pow_seventeen
  rcases (Nat.dvd_prime (by decide : Nat.Prime 17)).mp hdvd with h1 | h17
  · exact absurd (orderOf_eq_one_iff.mp h1) gSp_ne_one
  · exact h17

/-- Exponent `0..7` associated to each coordinate in `Fin 4 ⊕ Fin 4`. -/
def colExp : Fin 4 ⊕ Fin 4 → ℕ
  | Sum.inl i => i.val
  | Sum.inr i => i.val + 4

private theorem bMat_mul_bInvMat : bMat * bInvMat = 1 := by decide +kernel

private theorem bMat_eq_gMat_pow :
    bMat = Matrix.of (fun i j => (gMat ^ colExp j) i (Sum.inl 0)) := by
  decide +kernel

private theorem bMat_entry (i j : Fin 4 ⊕ Fin 4) :
    bMat i j = (gMat ^ colExp j) i (Sum.inl 0) :=
  congrFun (congrFun bMat_eq_gMat_pow i) j

/-- The `8`-tuple of coefficients of `M * e₀` in the cyclic basis `bMat`. -/
def coeffOf (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) :
    (Fin 4 ⊕ Fin 4) → ZMod 2 :=
  fun k => (bInvMat * M) k (Sum.inl 0)

/-- Polynomial matrix `∑ k, c k • gMat ^ colExp k`. -/
def polyMat (c : (Fin 4 ⊕ Fin 4) → ZMod 2) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  ∑ k : Fin 4 ⊕ Fin 4, c k • gMat ^ colExp k

private theorem mul_bMat_eq_polyMat_mul_bMat
    {M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)} (hcomm : Commute M gMat) :
    M * bMat = polyMat (coeffOf M) * bMat := by
  have hMb : ∀ i j : Fin 4 ⊕ Fin 4,
      (M * bMat) i j = ((gMat ^ colExp j) * M) i (Sum.inl 0) := by
    intro i j
    have hpow : M * gMat ^ colExp j = gMat ^ colExp j * M := hcomm.pow_right (colExp j)
    calc (M * bMat) i j = ∑ r, M i r * bMat r j := Matrix.mul_apply
      _ = ∑ r, M i r * (gMat ^ colExp j) r (Sum.inl 0) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [bMat_entry]
      _ = (M * gMat ^ colExp j) i (Sum.inl 0) := Matrix.mul_apply.symm
      _ = (gMat ^ colExp j * M) i (Sum.inl 0) := by rw [hpow]
  have hid_M : M = bMat * (bInvMat * M) := by
    rw [← Matrix.mul_assoc, bMat_mul_bInvMat, Matrix.one_mul]
  ext i j
  rw [hMb i j]
  have h1 : (gMat ^ colExp j * M) i (Sum.inl 0) =
      ((gMat ^ colExp j * bMat) * (bInvMat * M)) i (Sum.inl 0) := by
    rw [Matrix.mul_assoc, ← hid_M]
  rw [h1, Matrix.mul_apply]
  have h2 : (polyMat (coeffOf M) * bMat) i j =
      ∑ k : Fin 4 ⊕ Fin 4, coeffOf M k * (gMat ^ colExp k * bMat) i j := by
    rw [polyMat, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcomm_gk : gMat ^ colExp j * gMat ^ colExp k = gMat ^ colExp k * gMat ^ colExp j := by
    rw [← pow_add, ← pow_add, add_comm]
  have hL : (gMat ^ colExp j * bMat) i k = (gMat ^ colExp j * gMat ^ colExp k) i (Sum.inl 0) := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => by rw [bMat_entry]
  have hR : (gMat ^ colExp k * bMat) i j = (gMat ^ colExp k * gMat ^ colExp j) i (Sum.inl 0) := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ => by rw [bMat_entry]
  change (gMat ^ colExp j * bMat) i k * coeffOf M k = coeffOf M k * (gMat ^ colExp k * bMat) i j
  rw [hL, hR, hcomm_gk, mul_comm]

private theorem eq_polyMat_of_commute
    {M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)} (hcomm : Commute M gMat) :
    M = polyMat (coeffOf M) := by
  calc M = M * (bMat * bInvMat) := by rw [bMat_mul_bInvMat, Matrix.mul_one]
    _ = (M * bMat) * bInvMat := (Matrix.mul_assoc M bMat bInvMat).symm
    _ = (polyMat (coeffOf M) * bMat) * bInvMat := by rw [mul_bMat_eq_polyMat_mul_bMat hcomm]
    _ = polyMat (coeffOf M) * (bMat * bInvMat) := Matrix.mul_assoc _ bMat bInvMat
    _ = polyMat (coeffOf M) := by rw [bMat_mul_bInvMat, Matrix.mul_one]

private theorem polyMat_symplectic_mem_powers :
    ∀ c : (Fin 4 ⊕ Fin 4) → ZMod 2,
      (polyMat c)ᵀ * fromBlocks 0 1 (-1) 0 * polyMat c = fromBlocks 0 1 (-1) 0 →
      ∃ m : Fin 17, polyMat c = gMat ^ (m : ℕ) := by
  decide +kernel

/-- The subgroup `P17` of `StatedSp 4 (ZMod 2)` generated by `gSp` of order `17`. -/
abbrev P17 : Subgroup (StatedSp 4 (ZMod 2)) := Subgroup.zpowers gSp

private theorem card_P17 : Nat.card P17 = 17 := by
  rw [Nat.card_zpowers, orderOf_gSp]

private theorem centralizer_P17_le_P17 :
    Subgroup.centralizer (P17 : Set (StatedSp 4 (ZMod 2))) ≤ P17 := by
  intro x hx
  have hcomm_x : gSp * x = x * gSp :=
    Subgroup.mem_centralizer_iff.mp hx gSp (Subgroup.mem_zpowers gSp)
  let M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) := (x : GL (Fin 4 ⊕ Fin 4) (ZMod 2))
  have hcomm_M : Commute M gMat := by
    change M * gMat = gMat * M
    have hval := congrArg (fun g : StatedSp 4 (ZMod 2) =>
      ((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))) hcomm_x
    exact hval.symm
  have hM_poly : M = polyMat (coeffOf M) := eq_polyMat_of_commute hcomm_M
  have hM_sp : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0 :=
    mem_statedSp_iff.mp x.2
  rw [hM_poly] at hM_sp
  obtain ⟨m, hm⟩ := polyMat_symplectic_mem_powers (coeffOf M) hM_sp
  have hx_eq : x = gSp ^ (m : ℕ) := by
    apply Subtype.ext
    apply Units.ext
    change M = ((gSp ^ (m : ℕ) : StatedSp 4 (ZMod 2)) : GL (Fin 4 ⊕ Fin 4) (ZMod 2))
    rw [hM_poly, hm]
    rfl
  rw [hx_eq]
  exact P17.pow_mem (Subgroup.mem_zpowers gSp) (m : ℕ)

private theorem card_centralizer_P17_dvd :
    Nat.card (Subgroup.centralizer (P17 : Set (StatedSp 4 (ZMod 2)))) ∣ 17 := by
  rw [← card_P17]
  exact Subgroup.card_dvd_of_le centralizer_P17_le_P17

/-- If `P ≤ G` has prime order `p`, then `|N_G(P)|` divides `|C_G(P)| * (p - 1)`. -/
private theorem card_normalizer_dvd_mul_totient_of_prime {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) {p : ℕ} [hp : Fact p.Prime] (hP : Nat.card P = p) :
    Nat.card (Subgroup.normalizer (P : Set G)) ∣
      Nat.card (Subgroup.centralizer (P : Set G)) * (p - 1) := by
  set N := Subgroup.normalizer (P : Set G)
  set C := Subgroup.centralizer (P : Set G)
  let φ : N →* MulAut P :=
    { toFun := fun n =>
        { toFun := fun x => ⟨n.1 * x.1 * n.1⁻¹, (n.2 x.1).mp x.2⟩
          invFun := fun x => ⟨n.1⁻¹ * x.1 * n.1, by
            have := ((N.inv_mem n.2) x.1).mp x.2
            simpa [mul_assoc] using this⟩
          left_inv := fun x => Subtype.ext (by group)
          right_inv := fun x => Subtype.ext (by group)
          map_mul' := fun x y => Subtype.ext (by simp) }
      map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun n₁ n₂ => MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc]) }
  have hker : φ.ker = C.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have hx' := congrArg Subtype.val (MulEquiv.ext_iff.mp h ⟨x, hx⟩)
      change n.1 * x * n.1⁻¹ = x at hx'
      calc x * n.1 = (n.1 * x * n.1⁻¹) * n.1 := by rw [hx']
        _ = n.1 * x := by group
    · intro h
      ext ⟨x, hx⟩
      change n.1 * x * n.1⁻¹ = x
      calc n.1 * x * n.1⁻¹ = (x * n.1) * n.1⁻¹ := by rw [h x hx]
        _ = x := by group
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (P : Set G)
  have hcard_ker : Nat.card φ.ker = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  have hcard_N : Nat.card N = Nat.card C * Nat.card φ.range := by
    have h1 := Subgroup.card_mul_index φ.ker
    have h2 : φ.ker.index = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [hcard_ker, h2] at h1
    exact h1.symm
  have : IsCyclic P := isCyclic_of_prime_card hP
  have hAut : Nat.card (MulAut P) = p - 1 := by
    rw [IsCyclic.card_mulAut, hP, Nat.totient_prime hp.out]
  have hdvd : Nat.card φ.range ∣ p - 1 := by
    rw [← hAut]
    exact Subgroup.card_subgroup_dvd_card φ.range
  rw [hcard_N]
  exact mul_dvd_mul_left (Nat.card C) hdvd

private theorem card_normalizer_P17_dvd :
    Nat.card (Subgroup.normalizer (P17 : Set (StatedSp 4 (ZMod 2)))) ∣ 17 * 16 := by
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  exact (card_normalizer_dvd_mul_totient_of_prime P17 card_P17).trans
    (mul_dvd_mul card_centralizer_P17_dvd (dvd_refl 16))

/-- No subgroup of `PSp(8, 2)` has index in `[56, 63]`. -/
theorem not_index_mem_pSp_eight_two (S : Type) [Group S]
    (hS : CFSG.Open.StatedClassicalModel S .PSp 4 2 1) (H : Subgroup S)
    (h56 : 56 ≤ H.index) (h63 : H.index ≤ 63) : False := by
  have hsimple : IsSimpleGroup S :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp S 4 2 1 hS
  have hcard : Nat.card S = 47377612800 := by
    rw [(CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound S 4 2 1 hS).1]
    decide
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ := hS
  have hfin : Finite S := Finite.of_equiv _ eS.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  let φK : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let mapSp : StatedSp 4 (ZMod 2) →* StatedSp 4 K :=
    { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map φK g.1, map_mem_statedSp φK g.2⟩
      map_one' := Subtype.ext (map_one (Matrix.GeneralLinearGroup.map φK))
      map_mul' := fun a b => Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map φK) a.1 b.1) }
  have hmapSp_inj : Function.Injective mapSp := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    ext i j
    have hmat : ((mapSp a : StatedSp 4 K).1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
        ((mapSp b : StatedSp 4 K).1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) :=
      congrArg (fun g : StatedSp 4 K =>
        ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)) hab
    exact φK.injective (congrFun (congrFun hmat i) j)
  let Nscal : Subgroup (StatedSp 4 K) :=
    (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedSp 4 K)
  have hN_bot : Nscal = ⊥ := statedScalars_subgroupOf_statedSp_eq_bot
  have hmk_inj : Function.Injective (QuotientGroup.mk' Nscal) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN_bot]
  let emb : StatedSp 4 (ZMod 2) →* S :=
    eS.symm.toMonoidHom.comp ((QuotientGroup.mk' Nscal).comp mapSp)
  have hemb_inj : Function.Injective emb :=
    eS.symm.injective.comp (hmk_inj.comp hmapSp_inj)
  have hcard_Sp82 : Nat.card (StatedSp 4 (ZMod 2)) = Nat.card S := by
    have h1 : Nat.card (StatedSp 4 (ZMod 2)) = Nat.card (StatedSp 4 K) := by
      refine Nat.card_congr (Equiv.ofBijective mapSp ⟨hmapSp_inj, ?_⟩)
      have hsurj : Function.Surjective φK := by
        refine (Finite.injective_iff_surjective_of_equiv ?_).mp φK.injective
        exact Fintype.equivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one])
      let φK_equiv : ZMod 2 ≃+* K := RingEquiv.ofBijective φK ⟨φK.injective, hsurj⟩
      intro g
      refine ⟨⟨Matrix.GeneralLinearGroup.map φK_equiv.symm.toRingHom g.1,
        map_mem_statedSp φK_equiv.symm.toRingHom g.2⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      ext i j
      exact φK_equiv.apply_symm_apply _
    have h2 : Nat.card (StatedSp 4 K) = Nat.card S := by
      have hidx := Subgroup.card_mul_index Nscal
      have hidx_eq : Nscal.index = Nat.card S := Nat.card_congr eS.symm.toEquiv
      rw [hidx_eq, hN_bot, Subgroup.card_bot, one_mul] at hidx
      exact hidx.symm
    exact h1.trans h2
  have hemb_surj : Function.Surjective emb := by
    have _ : Fintype (StatedSp 4 (ZMod 2)) := Fintype.ofFinite _
    have _ : Fintype S := Fintype.ofFinite S
    refine (Finite.injective_iff_surjective_of_equiv ?_).mp hemb_inj
    exact Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_Sp82])
  let eSp : StatedSp 4 (ZMod 2) ≃* S := MulEquiv.ofBijective emb ⟨hemb_inj, hemb_surj⟩
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  let PS : Subgroup S := P17.map eSp.toMonoidHom
  have hPS_card : Nat.card PS = 17 := by
    rw [Subgroup.card_map_of_injective eSp.injective, card_P17]
  have hPS_p : IsPGroup 17 PS := IsPGroup.of_card (n := 1) (by rw [hPS_card, pow_one])
  have hPS_idx : ¬ 17 ∣ PS.index := by
    intro hdvd
    have hmul := Subgroup.card_mul_index PS
    rw [hPS_card, hcard] at hmul
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hmul
    have h17_sq : 17 * 17 ∣ 47377612800 := ⟨k, by linarith⟩
    exact (by decide : ¬ 17 * 17 ∣ 47377612800) h17_sq
  let P : Sylow 17 S := hPS_p.toSylow hPS_idx
  have hP_coe : (P : Subgroup S) = PS := IsPGroup.toSylow_coe hPS_p hPS_idx
  have hP_ne_bot : (P : Subgroup S) ≠ ⊥ := by
    intro hbot
    rw [hP_coe] at hbot
    have : Nat.card PS = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hH_ne_top : H ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at h56
    omega
  have hcore : H.normalCore = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_unique (h ▸ H.normalCore_le)) hH_ne_top
  have hr : ¬ 17 ∣ H.index := by
    intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    omega
  obtain ⟨f, hf_mod, hf_pos, hf_lt, hf_dvd⟩ :=
    exists_fixedPoints_sylow_quotient P hcore hr hP_ne_bot
  set N := Subgroup.normalizer ((P : Subgroup S) : Set S)
  let PN : Subgroup N := (P : Subgroup S).subgroupOf N
  have hN_eq_map :
      N = (Subgroup.normalizer (P17 : Set (StatedSp 4 (ZMod 2)))).map eSp.toMonoidHom := by
    ext s
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_map]
    constructor
    · intro hs
      refine ⟨eSp.symm s, ?_, eSp.apply_symm_apply s⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hsx := hs (eSp x)
      rw [hP_coe, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at hsx
      simpa [map_mul, map_inv] using hsx
    · rintro ⟨x, hx, rfl⟩
      intro y
      rw [Subgroup.mem_normalizer_iff] at hx
      have hxy := hx (eSp.symm y)
      rw [hP_coe, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
      simpa [map_mul, map_inv] using hxy
  have hN_card_dvd : Nat.card N ∣ 17 * 16 := by
    rw [hN_eq_map, Subgroup.card_map_of_injective eSp.injective]
    exact card_normalizer_P17_dvd
  have hPN_card : Nat.card PN = 17 := by
    have hPN_le : (P : Subgroup S) ≤ N := Subgroup.le_normalizer
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN_le).toEquiv, hP_coe, hPS_card]
  have hPN_idx_dvd : PN.index ∣ 16 := by
    have hmul := Subgroup.card_mul_index PN
    rw [hPN_card] at hmul
    rw [← hmul] at hN_card_dvd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 17)).mp hN_card_dvd
  have hf_dvd_16 : f ∣ 16 := hf_dvd.trans hPN_idx_dvd
  have hf_le_16 : f ≤ 16 := Nat.le_of_dvd (by decide) hf_dvd_16
  have hm_dvd_S : H.index ∣ 47377612800 := by
    rw [← hcard]
    exact ⟨Nat.card H, (Subgroup.index_mul_card H).symm⟩
  have hf_eq : f = H.index % 17 := by
    have hmod' : f % 17 = H.index % 17 := hf_mod
    rwa [Nat.mod_eq_of_lt (by omega : f < 17)] at hmod'
  have hno : ∀ m ∈ Finset.Icc 56 63, m % 17 ∣ 16 → m ∣ 47377612800 → False := by decide
  exact hno H.index (Finset.mem_Icc.mpr ⟨h56, h63⟩) (hf_eq ▸ hf_dvd_16) hm_dvd_S

end SylowSeventeen

end SymplecticSmall

/-- No subgroup of `PSp(4, 4)` has index `24` (Maróti, Section 2, Step 2, page 634). -/
theorem index_ne_twentyFour_pSp_four_four (S : Type) [Group S]
    (hS : CFSG.Open.StatedClassicalModel S .PSp 2 2 2) (H : Subgroup S) :
    H.index ≠ 24 :=
  SymplecticSmall.index_ne_twentyFour_pSp_four_four S hS H

/-- No subgroup of `PSp(8, 2)` has index in `[56, 63]` (Maróti, Section 2, Step 2, page 634). -/
theorem not_index_mem_pSp_eight_two (S : Type) [Group S]
    (hS : CFSG.Open.StatedClassicalModel S .PSp 4 2 1) (H : Subgroup S)
    (h56 : 56 ≤ H.index) (h63 : H.index ≤ 63) : False :=
  SymplecticSmall.SylowSeventeen.not_index_mem_pSp_eight_two S hS H h56 h63

end Maroti
