module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
public import Maroti.Sporadic.MathieuM12M22
import Maroti.MinDegree.Basic
import Maroti.Sporadic.Mathieu
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Schreier.MathieuOddCoreM12
import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
import CFSG.Sporadic.Bridge.M12
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Mathieu Group `M₁₂`

This file proves `sporadicCase_M12`: every primitive almost simple group `G` on `α` with socle
`M₁₂` either has degree `12`, `G ≃* M₁₂`, and acts `4`-transitively on `α`, or satisfies
`Nat.card G ≤ bound (Nat.card α)`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint MulAction

namespace M12CaseProof

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native CFSG.Sporadic.Th CFSG.Perm.Native
open CFSG.Sporadic.Schreier CFSG.Certificates

/-! ### Pointwise stabilizer of `0, 1, 2, 3, 4` in `M₁₂` -/

private theorem eq_one_of_fix_five (g : NativeSporadic.M12)
    (h0 : (g : Equiv.Perm (Fin 12)) 0 = 0) (h1 : (g : Equiv.Perm (Fin 12)) 1 = 1)
    (h2 : (g : Equiv.Perm (Fin 12)) 2 = 2) (h3 : (g : Equiv.Perm (Fin 12)) 3 = 3)
    (h4 : (g : Equiv.Perm (Fin 12)) 4 = 4) : g = 1 := by
  have hC := chain m12_hyp
  have hl0 : g ∈ lvl (m12Data ()) m12a m12b 0 := by
    rw [lvl_zero m12_hyp]
    trivial
  have hstep : ∀ (i : ℕ) (hi : i < 5) (hlt : i < 12),
      (m12Data ()).base[i]! = i →
      (g : Equiv.Perm (Fin 12)) ⟨i, hlt⟩ = ⟨i, hlt⟩ →
      g ∈ lvl (m12Data ()) m12a m12b i →
      g ∈ lvl (m12Data ()) m12a m12b (i + 1) := by
    intro i hi hlt hbi hfix hgi
    have hib : i < (m12Data ()).base.size := by change i < 5; exact hi
    refine (hC.2.1 i hib g hgi).1 ?_
    rw [hbi, idx_of_lt g hlt]
    exact congrArg Fin.val hfix
  have hl1 := hstep 0 (by decide) (by decide) rfl h0 hl0
  have hl2 := hstep 1 (by decide) (by decide) rfl h1 hl1
  have hl3 := hstep 2 (by decide) (by decide) rfl h2 hl2
  have hl4 := hstep 3 (by decide) (by decide) rfl h3 hl3
  have hl5 := hstep 4 (by decide) (by decide) rfl h4 hl4
  have hcard5 : Nat.card (lvl (m12Data ()) m12a m12b 5) = 1 := by
    have := hC.2.2 5 (by decide)
    have hsz : (m12Data ()).base.size = 5 := rfl
    rw [hsz, Finset.Ico_self, Finset.prod_empty] at this
    exact this
  have hbot : lvl (m12Data ()) m12a m12b 5 = ⊥ := Subgroup.card_eq_one.mp hcard5
  rwa [hbot, Subgroup.mem_bot] at hl5

/-! ### Ruling out subgroups of index `15` in `M₁₂` -/

private abbrev x11Perm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8, 3, 1, 9, 6, 11, 4, 5, 2]

private abbrev m12x11 : NativeSporadic.M12 := m12a * m12b

private theorem m12x11_val : (m12x11 : Equiv.Perm (Fin 12)) = x11Perm := by decide +kernel

private theorem orderOf_m12x11 : orderOf m12x11 = 11 := by
  have hdvd : orderOf m12x11 ∣ 11 := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    change (m12x11 : Equiv.Perm (Fin 12)) ^ 11 = 1
    rw [m12x11_val]; decide +kernel)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp hdvd with h1 | h11
  · exfalso
    have hval : (m12x11 : Equiv.Perm (Fin 12)) = 1 :=
      congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
    rw [m12x11_val] at hval
    exact (by decide +kernel : x11Perm ≠ 1) hval
  · exact h11

private abbrev P11 : Subgroup NativeSporadic.M12 := Subgroup.zpowers m12x11

private theorem card_P11 : Nat.card P11 = 11 := by
  rw [Nat.card_zpowers, orderOf_m12x11]

private abbrev C11 : Subgroup NativeSporadic.M12 :=
  Subgroup.centralizer (P11 : Set NativeSporadic.M12)

private theorem comm_m12x11_pow (g : C11) (k : ℕ) (p : Fin 12) :
    (g.1 : Equiv.Perm (Fin 12)) ((x11Perm ^ k) p) =
      (x11Perm ^ k) ((g.1 : Equiv.Perm (Fin 12)) p) := by
  have hcomm : m12x11 * g.1 = g.1 * m12x11 :=
    Subgroup.mem_centralizer_iff.mp g.2 m12x11 (Subgroup.mem_zpowers m12x11)
  have hcomm' : Commute (g.1 : Equiv.Perm (Fin 12)) x11Perm := by
    rw [← m12x11_val]
    exact (congrArg Subtype.val hcomm).symm
  have hpow : (g.1 : Equiv.Perm (Fin 12)) * x11Perm ^ k =
      x11Perm ^ k * (g.1 : Equiv.Perm (Fin 12)) :=
    hcomm'.pow_right k
  exact Equiv.Perm.ext_iff.mp hpow p

private theorem m12x11_orb1 : (x11Perm ^ 4) 0 = 1 := by decide +kernel
private theorem m12x11_orb2 : (x11Perm ^ 10) 0 = 2 := by decide +kernel
private theorem m12x11_orb3 : (x11Perm ^ 3) 0 = 3 := by decide +kernel
private theorem m12x11_orb4 : (x11Perm ^ 8) 0 = 4 := by decide +kernel
private theorem m12x11_fix10 : (x11Perm ^ 3) 10 = 10 := by decide +kernel

private theorem stabilizer_C11_zero_eq_bot : stabilizer C11 (0 : Fin 12) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h0 : (g.1 : Equiv.Perm (Fin 12)) 0 = 0 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 12)) 1 = 1 := by
    rw [← m12x11_orb1, comm_m12x11_pow g 4 0, h0, m12x11_orb1]
  have h2 : (g.1 : Equiv.Perm (Fin 12)) 2 = 2 := by
    rw [← m12x11_orb2, comm_m12x11_pow g 10 0, h0, m12x11_orb2]
  have h3 : (g.1 : Equiv.Perm (Fin 12)) 3 = 3 := by
    rw [← m12x11_orb3, comm_m12x11_pow g 3 0, h0, m12x11_orb3]
  have h4 : (g.1 : Equiv.Perm (Fin 12)) 4 = 4 := by
    rw [← m12x11_orb4, comm_m12x11_pow g 8 0, h0, m12x11_orb4]
  exact Subtype.ext (eq_one_of_fix_five g.1 h0 h1 h2 h3 h4)

private theorem not_mem_orbit_C11_ten : (10 : Fin 12) ∉ orbit C11 (0 : Fin 12) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 12)) 0 = 10 := hg
  have h3 : (g.1 : Equiv.Perm (Fin 12)) 3 = 10 := by
    rw [← m12x11_orb3, comm_m12x11_pow g 3 0, h0, m12x11_fix10]
  have heq : (3 : Fin 12) = 0 := (g.1 : Equiv.Perm (Fin 12)).injective (h3.trans h0.symm)
  exact (by decide : (3 : Fin 12) ≠ 0) heq

private theorem card_C11_dvd : Nat.card C11 ∣ 11 := by
  have hstab : Nat.card (stabilizer C11 (0 : Fin 12)) = 1 := by
    rw [stabilizer_C11_zero_eq_bot, Subgroup.card_bot]
  have hcard_eq : Nat.card C11 = Nat.card (orbit C11 (0 : Fin 12)) := by
    have h := (stabilizer C11 (0 : Fin 12)).index_mul_card
    rw [hstab, mul_one, index_stabilizer C11 (0 : Fin 12), ← Nat.card_coe_set_eq] at h
    exact h.symm
  let emb : orbit C11 (0 : Fin 12) → {p : Fin 12 // p ≠ 10} :=
    fun x => ⟨x.1, fun h => not_mem_orbit_C11_ten (h ▸ x.2)⟩
  have hemb : Function.Injective emb :=
    fun x y h => Subtype.ext (congrArg (fun z : {p : Fin 12 // p ≠ 10} => z.1) h)
  have h11 : Nat.card {p : Fin 12 // p ≠ 10} = 11 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hle : Nat.card C11 ≤ 11 :=
    (hcard_eq.trans_le (Nat.card_le_card_of_injective emb hemb)).trans h11.le
  have hP_le_C : P11 ≤ C11 := by
    intro y hy z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    simp only [← zpow_add, add_comm]
  have hdvd11 : 11 ∣ Nat.card C11 := by
    rw [← card_P11]
    exact Subgroup.card_dvd_of_le hP_le_C
  have hpos : 0 < Nat.card C11 := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd11
  have hk1 : k = 1 := by omega
  subst hk1
  rw [hk]

private theorem card_normalizer_P11_dvd :
    Nat.card (Subgroup.normalizer (P11 : Set NativeSporadic.M12)) ∣ 110 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h1 := card_normalizer_dvd_mul_totient P11 card_P11
  have h2 : Nat.card C11 * (11 - 1) ∣ 11 * 10 :=
    mul_dvd_mul card_C11_dvd (dvd_refl 10)
  exact h1.trans h2

private theorem not_exists_subgroup_index_15 (H : Subgroup NativeSporadic.M12) :
    H.index ≠ 15 := by
  intro hidx
  have hcard_H : Nat.card H = 6336 := by
    have h := H.index_mul_card
    rw [hidx, card_M12] at h
    omega
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hval := hasValidSylowNormalizer_of_dvd P11 card_P11
    (by rw [card_M12]; decide) card_normalizer_P11_dvd (by decide)
    (H := H) (by rw [hcard_H]; decide)
  rw [hcard_H] at hval
  exact absurd hval (by decide)

/-! ### Strong generators of `m12Pairs` and outer automorphism swap -/

private theorem swap_mem_m12Pairs :
    ∀ p ∈ m12Pairs, p.swap ∈ m12Pairs := by
  have hmap : m12Pairs.map (MulEquiv.prodComm :
      Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12) ≃*
        Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)).toMonoidHom ≤ m12Pairs := by
    rw [m12Pairs, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro p (hp | hp)
    · change p = (m12gA, m12gA) at hp
      rw [hp]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · change p = (m12bp, m12gB) at hp
      rw [hp]
      have hconj : blockHom (m12bp, m12gB) = m12Sigma * m12B1 * m12Sigma⁻¹ := by
        decide +kernel
      have hmemD : blockHom (m12bp, m12gB) ∈ m12D.originalSubgroup := by
        rw [hconj]
        exact m12D_sigma_normalizes m12B1 (m12_gens_memD _ (by simp))
      rw [m12D_originalSubgroup] at hmemD
      obtain ⟨q, hq, hq_eq⟩ := hmemD
      have hqp : q = (m12bp, m12gB) := blockHom_injective hq_eq
      rw [← hqp]
      exact hq
  intro p hp
  exact hmap ⟨p, hp, rfl⟩

private def swapPairs : m12Pairs ≃* m12Pairs where
  toFun p := ⟨p.1.swap, swap_mem_m12Pairs p.1 p.2⟩
  invFun p := ⟨p.1.swap, swap_mem_m12Pairs p.1 p.2⟩
  left_inv p := Subtype.ext (Prod.swap_swap p.1)
  right_inv p := Subtype.ext (Prod.swap_swap p.1)
  map_mul' _ _ := rfl

private noncomputable def proj₁ : m12Pairs ≃* NativeSporadic.M12 :=
  MulEquiv.ofBijective m12Proj m12Proj_bijective

private noncomputable def proj₂ : m12Pairs ≃* NativeSporadic.M12 :=
  swapPairs.trans proj₁

private theorem proj₁_coe (p : m12Pairs) :
    (proj₁ p : Equiv.Perm (Fin 12)) = p.1.1 := rfl

private theorem proj₂_coe (p : m12Pairs) :
    (proj₂ p : Equiv.Perm (Fin 12)) = p.1.2 := rfl

private abbrev g0 : m12Pairs :=
  ⟨(m12gA, m12gA), Subgroup.subset_closure (Set.mem_insert _ _)⟩

private abbrev g1 : m12Pairs :=
  ⟨(m12gB, m12bp), Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

private def g2 : m12Pairs := g1⁻¹ * g0 * g1
private def g3 : m12Pairs := g0⁻¹ * g2 * g0
private def g4 : m12Pairs := g1⁻¹ * g2 * g1
private def g5 : m12Pairs := g1⁻¹ * g3 * g1
private def g6 : m12Pairs := g0⁻¹ * g1⁻¹ * g5 * g1 * g0
private def g7 : m12Pairs := g2⁻¹ * g1 * g6 * g1⁻¹
private def g8 : m12Pairs := g2⁻¹ * g6⁻¹ * g0⁻¹ * g7⁻¹ * g3 * g1⁻¹
private def g9 : m12Pairs := g6⁻¹ * g3⁻¹ * g0⁻¹ * g8⁻¹ * g1⁻¹ * g0
private def g10 : m12Pairs := g5⁻¹ * g9⁻¹ * g7⁻¹ * g0⁻¹ * g9⁻¹ * g8⁻¹ * g0
private def g11 : m12Pairs := g5⁻¹ * g7⁻¹ * g8 * g3⁻¹ * g5⁻¹ * g0⁻¹ * g9⁻¹ * g5 * g1

private abbrev g2Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 5] * List.formPerm [2, 8] * List.formPerm [4, 6] * List.formPerm [10, 11]
private abbrev g2Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 10] * List.formPerm [3, 5] * List.formPerm [6, 9] * List.formPerm [7, 8]

private abbrev g3Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 11] * List.formPerm [4, 5] * List.formPerm [6, 10] * List.formPerm [8, 9]
private abbrev g3Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 11] * List.formPerm [2, 6] * List.formPerm [3, 4] * List.formPerm [7, 8]

private abbrev g4Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 7] * List.formPerm [3, 6] * List.formPerm [4, 11] * List.formPerm [9, 10]
private abbrev g4Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 5] * List.formPerm [1, 4] * List.formPerm [3, 6] * List.formPerm [7, 11]

private abbrev g5Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [3, 4] * List.formPerm [5, 7] * List.formPerm [6, 10] * List.formPerm [9, 11]
private abbrev g5Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 4] * List.formPerm [3, 10] * List.formPerm [5, 9] * List.formPerm [8, 11]

private abbrev g6Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 5] * List.formPerm [3, 6] * List.formPerm [4, 9] * List.formPerm [10, 11]
private abbrev g6Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 4] * List.formPerm [2, 9] * List.formPerm [3, 7] * List.formPerm [6, 11]

private abbrev g7Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 8] * List.formPerm [3, 9] * List.formPerm [4, 11] * List.formPerm [6, 10]
private abbrev g7Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 6] * List.formPerm [1, 4] * List.formPerm [3, 5] * List.formPerm [9, 10]

private abbrev g8Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 10, 5, 3] * List.formPerm [4, 9, 8, 7]
private abbrev g8Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 4, 1, 8] * List.formPerm [2, 5, 3, 10] * List.formPerm [6, 11] *
    List.formPerm [7, 9]

private abbrev g9Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [3, 5, 7, 6] * List.formPerm [4, 9, 10, 8]
private abbrev g9Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 2, 11, 3] * List.formPerm [1, 7] * List.formPerm [4, 5, 6, 9] *
    List.formPerm [8, 10]

private abbrev g10Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [4, 10, 8, 5] * List.formPerm [6, 7, 9, 11]
private abbrev g10Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 6, 11, 1] * List.formPerm [2, 5] * List.formPerm [3, 7, 10, 9] *
    List.formPerm [4, 8]

private abbrev g11Perm1 : Equiv.Perm (Fin 12) :=
  List.formPerm [4, 7, 8, 11] * List.formPerm [5, 9, 10, 6]
private abbrev g11Perm2 : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 10, 11, 3] * List.formPerm [1, 9, 6, 7] * List.formPerm [2, 8] *
    List.formPerm [4, 5]

private theorem g0_val : (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (m12gA, m12gA) := rfl
private theorem g1_val : (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (m12gB, m12bp) := rfl

private theorem g2_val : (g2 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g2Perm1, g2Perm2) := by
  change (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g2Perm1, g2Perm2)
  rw [g0_val, g1_val]; decide +kernel

private theorem g3_val : (g3 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g3Perm1, g3Perm2) := by
  change (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g2 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g3Perm1, g3Perm2)
  rw [g0_val, g2_val]; decide +kernel

private theorem g4_val : (g4 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g4Perm1, g4Perm2) := by
  change (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g2 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g4Perm1, g4Perm2)
  rw [g1_val, g2_val]; decide +kernel

private theorem g5_val : (g5 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g5Perm1, g5Perm2) := by
  change (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g3 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g5Perm1, g5Perm2)
  rw [g1_val, g3_val]; decide +kernel

private theorem g6_val : (g6 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g6Perm1, g6Perm2) := by
  change (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g5 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g6Perm1, g6Perm2)
  rw [g0_val, g1_val, g5_val]; decide +kernel

private theorem g7_val : (g7 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g7Perm1, g7Perm2) := by
  change (g2 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g6 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ = (g7Perm1, g7Perm2)
  rw [g1_val, g2_val, g6_val]; decide +kernel

private theorem g8_val : (g8 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g8Perm1, g8Perm2) := by
  change (g2 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g6 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g7 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g3 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ = (g8Perm1, g8Perm2)
  rw [g0_val, g1_val, g2_val, g3_val, g6_val, g7_val]; decide +kernel

private theorem g9_val : (g9 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g9Perm1, g9Perm2) := by
  change (g6 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g3 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g8 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g9Perm1, g9Perm2)
  rw [g0_val, g1_val, g3_val, g6_val, g8_val]; decide +kernel

private theorem g10_val :
    (g10 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g10Perm1, g10Perm2) := by
  change (g5 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g9 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g7 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g9 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g8 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g10Perm1, g10Perm2)
  rw [g0_val, g5_val, g7_val, g8_val, g9_val]; decide +kernel

private theorem g11_val :
    (g11 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g11Perm1, g11Perm2) := by
  change (g5 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g7 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g8 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g3 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g5 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g9 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g5 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (g11Perm1, g11Perm2)
  rw [g0_val, g1_val, g3_val, g5_val, g7_val, g8_val, g9_val]; decide +kernel

/-! ### Normalizer of `M₁₂` in `Equiv.Perm (Fin 12)` -/

private noncomputable def wC : NativeSporadic.M12 := proj₁ g5
private noncomputable def wB : NativeSporadic.M12 := proj₁ (g7 * g3 * g7)
private noncomputable def wD : NativeSporadic.M12 := proj₁ (g0 * g5 * g6 * g0)

private abbrev wBPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 4] * List.formPerm [2, 3] * List.formPerm [5, 11] * List.formPerm [6, 10]

private abbrev wDPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 4, 2] * List.formPerm [5, 6, 10] * List.formPerm [7, 11, 9]

private theorem wC_val : (wC : Equiv.Perm (Fin 12)) = g5Perm1 :=
  congrArg Prod.fst g5_val

private theorem wB_val : (wB : Equiv.Perm (Fin 12)) = wBPerm := by
  have h : (g7 * g3 * g7 : m12Pairs).1 = (wBPerm, g7Perm2 * g3Perm2 * g7Perm2) := by
    change (g7 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
      (g3 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
      (g7 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = _
    rw [g3_val, g7_val]; decide +kernel
  exact congrArg Prod.fst h

private theorem wD_val : (wD : Equiv.Perm (Fin 12)) = wDPerm := by
  have h : (g0 * g5 * g6 * g0 : m12Pairs).1 =
      (wDPerm, m12gA * g5Perm2 * g6Perm2 * m12gA) := by
    change (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
      (g5 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
      (g6 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
      (g0 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = _
    rw [g0_val, g5_val, g6_val]; decide +kernel
  exact congrArg Prod.fst h

private theorem comm_of_norm_fix_five
    (σ : Subgroup.normalizer (NativeSporadic.M12 : Set (Equiv.Perm (Fin 12))))
    (h0 : (σ : Equiv.Perm (Fin 12)) 0 = 0) (h1 : (σ : Equiv.Perm (Fin 12)) 1 = 1)
    (h2 : (σ : Equiv.Perm (Fin 12)) 2 = 2) (h3 : (σ : Equiv.Perm (Fin 12)) 3 = 3)
    (h4 : (σ : Equiv.Perm (Fin 12)) 4 = 4)
    (w : NativeSporadic.M12) {wPerm : Equiv.Perm (Fin 12)} (hw : (w : Equiv.Perm (Fin 12)) = wPerm)
    (hpres : ∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 4] : List (Fin 12)) →
      wPerm i ∈ ([0, 1, 2, 3, 4] : List (Fin 12))) :
    ∀ p : Fin 12, (σ : Equiv.Perm (Fin 12)) (wPerm p) = wPerm ((σ : Equiv.Perm (Fin 12)) p) := by
  have hfix : ∀ q : Fin 12, q ∈ ([0, 1, 2, 3, 4] : List (Fin 12)) →
      (σ : Equiv.Perm (Fin 12)) q = q := by
    rintro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hfix_inv : ∀ q : Fin 12, q ∈ ([0, 1, 2, 3, 4] : List (Fin 12)) →
      (σ : Equiv.Perm (Fin 12))⁻¹ q = q := by
    intro q hq
    apply (σ : Equiv.Perm (Fin 12)).injective
    simp [hfix q hq]
  let c : NativeSporadic.M12 :=
    ⟨(σ : Equiv.Perm (Fin 12)) * (w : Equiv.Perm (Fin 12)) * (σ : Equiv.Perm (Fin 12))⁻¹,
      (σ.2 w.1).mp w.2⟩
  let u : NativeSporadic.M12 := w⁻¹ * c
  have hu_fix : ∀ q : Fin 12, q ∈ ([0, 1, 2, 3, 4] : List (Fin 12)) →
      (u : Equiv.Perm (Fin 12)) q = q := by
    intro q hq
    change (w : Equiv.Perm (Fin 12))⁻¹
      ((σ : Equiv.Perm (Fin 12)) ((w : Equiv.Perm (Fin 12)) ((σ : Equiv.Perm (Fin 12))⁻¹ q))) = q
    rw [hfix_inv q hq, hw, hfix (wPerm q) (hpres q hq), ← hw]
    exact (w : Equiv.Perm (Fin 12)).symm_apply_apply q
  have hu1 : u = 1 := eq_one_of_fix_five u
    (hu_fix 0 (by decide)) (hu_fix 1 (by decide)) (hu_fix 2 (by decide))
    (hu_fix 3 (by decide)) (hu_fix 4 (by decide))
  have hcw : c = w := (inv_mul_eq_one.mp hu1).symm
  have hval : (σ : Equiv.Perm (Fin 12)) * wPerm * (σ : Equiv.Perm (Fin 12))⁻¹ = wPerm := by
    rw [← hw]
    exact congrArg Subtype.val hcw
  intro p
  have := Equiv.Perm.ext_iff.mp hval ((σ : Equiv.Perm (Fin 12)) p)
  simpa [Equiv.Perm.mul_apply] using this

private theorem eq_eight_of_fix_g5 :
    ∀ q : Fin 12, g5Perm1 q = q → q ≠ 0 → q ≠ 1 → q ≠ 2 → q = 8 := by decide

private theorem eq_nine_of_fix_wB_wD :
    ∀ q : Fin 12, wBPerm q = q → wBPerm (wDPerm q) = wDPerm q → q ≠ 0 → q ≠ 8 → q = 9 := by
  decide

private theorem eq_one_of_norm_fix_five
    (σ : Subgroup.normalizer (NativeSporadic.M12 : Set (Equiv.Perm (Fin 12))))
    (h0 : (σ : Equiv.Perm (Fin 12)) 0 = 0) (h1 : (σ : Equiv.Perm (Fin 12)) 1 = 1)
    (h2 : (σ : Equiv.Perm (Fin 12)) 2 = 2) (h3 : (σ : Equiv.Perm (Fin 12)) 3 = 3)
    (h4 : (σ : Equiv.Perm (Fin 12)) 4 = 4) : σ = 1 := by
  have hcC := comm_of_norm_fix_five σ h0 h1 h2 h3 h4 wC wC_val (by decide)
  have hcB := comm_of_norm_fix_five σ h0 h1 h2 h3 h4 wB wB_val (by decide)
  have hcD := comm_of_norm_fix_five σ h0 h1 h2 h3 h4 wD wD_val (by decide)
  have h8 : (σ : Equiv.Perm (Fin 12)) 8 = 8 := by
    apply eq_eight_of_fix_g5 ((σ : Equiv.Perm (Fin 12)) 8)
    · rw [← hcC 8]; congr 1
    · intro h
      exact (by decide : (8 : Fin 12) ≠ 0)
        ((σ : Equiv.Perm (Fin 12)).injective (h.trans h0.symm))
    · intro h
      exact (by decide : (8 : Fin 12) ≠ 1)
        ((σ : Equiv.Perm (Fin 12)).injective (h.trans h1.symm))
    · intro h
      exact (by decide : (8 : Fin 12) ≠ 2)
        ((σ : Equiv.Perm (Fin 12)).injective (h.trans h2.symm))
  have h9 : (σ : Equiv.Perm (Fin 12)) 9 = 9 := by
    apply eq_nine_of_fix_wB_wD ((σ : Equiv.Perm (Fin 12)) 9)
    · rw [← hcB 9]; congr 1
    · rw [← hcD 9, ← hcB (wDPerm 9)]; congr 1
    · intro h
      exact (by decide : (9 : Fin 12) ≠ 0)
        ((σ : Equiv.Perm (Fin 12)).injective (h.trans h0.symm))
    · intro h
      exact (by decide : (9 : Fin 12) ≠ 8)
        ((σ : Equiv.Perm (Fin 12)).injective (h.trans h8.symm))
  have h7 : (σ : Equiv.Perm (Fin 12)) 7 = 7 := by
    have hd : wDPerm 9 = 7 := by decide
    rw [← hd, hcD 9, h9, hd]
  have h11 : (σ : Equiv.Perm (Fin 12)) 11 = 11 := by
    have hd : wDPerm 7 = 11 := by decide
    rw [← hd, hcD 7, h7, hd]
  have h5 : (σ : Equiv.Perm (Fin 12)) 5 = 5 := by
    have hd : g5Perm1 7 = 5 := by decide
    rw [← hd, hcC 7, h7, hd]
  have h6 : (σ : Equiv.Perm (Fin 12)) 6 = 6 := by
    have hd : wDPerm 5 = 6 := by decide
    rw [← hd, hcD 5, h5, hd]
  have h10 : (σ : Equiv.Perm (Fin 12)) 10 = 10 := by
    have hd : wDPerm 6 = 10 := by decide
    rw [← hd, hcD 6, h6, hd]
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11

private theorem card_normalizer_M12_le :
    Nat.card (Subgroup.normalizer (NativeSporadic.M12 : Set (Equiv.Perm (Fin 12)))) ≤ 95040 := by
  set N := Subgroup.normalizer (NativeSporadic.M12 : Set (Equiv.Perm (Fin 12)))
  let emb5 : Fin 5 ↪ Fin 12 := Fin.castLEEmb (by decide)
  let toEmb : N → (Fin 5 ↪ Fin 12) := fun σ =>
    emb5.trans (σ : Equiv.Perm (Fin 12)).toEmbedding
  have hinj : Function.Injective toEmb := by
    intro σ₁ σ₂ h
    have hpt : ∀ i : Fin 5,
        (σ₁ : Equiv.Perm (Fin 12)) (emb5 i) =
          (σ₂ : Equiv.Perm (Fin 12)) (emb5 i) :=
      fun i => DFunLike.congr_fun h i
    have hinv_fix : ∀ i : Fin 5,
        ((σ₁⁻¹ * σ₂ : N) : Equiv.Perm (Fin 12)) (emb5 i) = emb5 i := by
      intro i
      change (σ₁ : Equiv.Perm (Fin 12))⁻¹
        ((σ₂ : Equiv.Perm (Fin 12)) (emb5 i)) = emb5 i
      rw [← hpt i]
      exact (σ₁ : Equiv.Perm (Fin 12)).symm_apply_apply (emb5 i)
    have h1 := eq_one_of_norm_fix_five (σ₁⁻¹ * σ₂)
      (hinv_fix 0) (hinv_fix 1) (hinv_fix 2) (hinv_fix 3) (hinv_fix 4)
    exact inv_mul_eq_one.mp h1
  have hcard_emb : Nat.card (Fin 5 ↪ Fin 12) = 95040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    rfl
  exact (Nat.card_le_card_of_injective toEmb hinj).trans hcard_emb.le

/-! ### Enumerating `S₃` and ruling out doubly transitive index-`12` subgroups of `m12Pairs` -/

private instance isMultiplyPretransitive_M12_four :
    IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 4 := by
  rw [isMultiplyPretransitive_iff]
  intro e f
  have hex : ∀ x : Fin 4 ↪ Fin 12, ∃ g : NativeSporadic.M12,
      ∀ i : Fin 4, g • (⟨i.val, by omega⟩ : Fin 12) = x i := by
    intro x
    obtain ⟨g, hg⟩ := maps m12_hyp 4 le_rfl
      (fun j => if h : j < 4 then x ⟨j, h⟩ else 0) (by
        intro i hi j hj hij
        rw [dite_eq_left hi, dite_eq_left (lt_trans hj hi)] at hij
        have heq : (⟨i, hi⟩ : Fin 4) = ⟨j, lt_trans hj hi⟩ := x.injective hij
        have : i = j := congrArg Fin.val heq
        omega)
    refine ⟨g, fun i => ?_⟩
    have hgi := hg i.val i.isLt ⟨i.val, by omega⟩ rfl
    rw [dite_eq_left i.isLt] at hgi
    exact hgi
  obtain ⟨ge, hge⟩ := hex e
  obtain ⟨gf, hgf⟩ := hex f
  refine ⟨gf * ge⁻¹, ?_⟩
  apply DFunLike.ext
  intro i
  change gf • (ge⁻¹ • e i) = f i
  rw [inv_smul_eq_iff.mpr (hge i).symm, hgf i]

private theorem mem_lvl_three_of_fix_three (g : NativeSporadic.M12)
    (h0 : (g : Equiv.Perm (Fin 12)) 0 = 0) (h1 : (g : Equiv.Perm (Fin 12)) 1 = 1)
    (h2 : (g : Equiv.Perm (Fin 12)) 2 = 2) :
    g ∈ lvl (m12Data ()) m12a m12b 3 := by
  have hC := chain m12_hyp
  have hl0 : g ∈ lvl (m12Data ()) m12a m12b 0 := by
    rw [lvl_zero m12_hyp]
    trivial
  have hstep : ∀ (i : ℕ) (hi : i < 5) (hlt : i < 12),
      (m12Data ()).base[i]! = i →
      (g : Equiv.Perm (Fin 12)) ⟨i, hlt⟩ = ⟨i, hlt⟩ →
      g ∈ lvl (m12Data ()) m12a m12b i →
      g ∈ lvl (m12Data ()) m12a m12b (i + 1) := by
    intro i hi hlt hbi hfix hgi
    have hib : i < (m12Data ()).base.size := by change i < 5; exact hi
    refine (hC.2.1 i hib g hgi).1 ?_
    rw [hbi, idx_of_lt g hlt]
    exact congrArg Fin.val hfix
  have hl1 := hstep 0 (by decide) (by decide) rfl h0 hl0
  have hl2 := hstep 1 (by decide) (by decide) rfl h1 hl1
  exact hstep 2 (by decide) (by decide) rfl h2 hl2

private theorem card_lvl_3 : Nat.card (lvl (m12Data ()) m12a m12b 3) = 72 := by
  have hC := (chain m12_hyp).2.2 3 (by decide)
  have hsz : (m12Data ()).base.size = 5 := rfl
  have hIco : Finset.Ico 3 5 = {3, 4} := rfl
  rw [hsz, hIco, Finset.prod_pair (by decide)] at hC
  have h3 : (trees 12 (m12Data ()))[3]!.pts.size = 9 := by
    have h2 := congrArg (fun L : List ℕ => L[3]?) (checkFacts m12_hyp.cert).sizes
    simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList] at h2
    have hv : (m12Data ()).sizes[3]? = some 9 := rfl
    rw [hv] at h2
    have hl : 3 < (trees 12 (m12Data ())).size := by
      by_contra hc
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h2
      simp at h2
    rw [Array.getElem?_eq_getElem hl] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    rw [getElem!_pos (trees 12 (m12Data ())) 3 hl]
    exact h2
  have h4 : (trees 12 (m12Data ()))[4]!.pts.size = 8 := by
    have h2 := congrArg (fun L : List ℕ => L[4]?) (checkFacts m12_hyp.cert).sizes
    simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList] at h2
    have hv : (m12Data ()).sizes[4]? = some 8 := rfl
    rw [hv] at h2
    have hl : 4 < (trees 12 (m12Data ())).size := by
      by_contra hc
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h2
      simp at h2
    rw [Array.getElem?_eq_getElem hl] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    rw [getElem!_pos (trees 12 (m12Data ())) 4 hl]
    exact h2
  rw [hC, h3, h4]
  rfl

private abbrev L₁ : Subgroup NativeSporadic.M12 := stabilizer NativeSporadic.M12 (0 : Fin 12)
private abbrev L₂ : Subgroup NativeSporadic.M12 := L₁ ⊓ stabilizer NativeSporadic.M12 (1 : Fin 12)
private abbrev L₃ : Subgroup NativeSporadic.M12 := L₂ ⊓ stabilizer NativeSporadic.M12 (2 : Fin 12)

private noncomputable abbrev S₁ : Subgroup m12Pairs := L₁.comap proj₁.toMonoidHom
private noncomputable abbrev S₃ : Subgroup m12Pairs := L₃.comap proj₁.toMonoidHom

private theorem mem_S₁_iff (p : m12Pairs) : p ∈ S₁ ↔ p.1.1 0 = 0 := Iff.rfl

private theorem mem_S₃_iff (p : m12Pairs) :
    p ∈ S₃ ↔ (p.1.1 0 = 0 ∧ p.1.1 1 = 1) ∧ p.1.1 2 = 2 := Iff.rfl

private def q1 : m12Pairs := g9 * g11
private def q2 : m12Pairs := g9⁻¹ * g11⁻¹

private abbrev q1Perm1 : Equiv.Perm (Fin 12) := g9Perm1 * g11Perm1
private abbrev q1Perm2 : Equiv.Perm (Fin 12) := g9Perm2 * g11Perm2
private abbrev q2Perm1 : Equiv.Perm (Fin 12) := g9Perm1⁻¹ * g11Perm1⁻¹
private abbrev q2Perm2 : Equiv.Perm (Fin 12) := g9Perm2⁻¹ * g11Perm2⁻¹

private theorem q1_val : (q1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (q1Perm1, q1Perm2) := by
  change (g9 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) *
    (g11 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (q1Perm1, q1Perm2)
  rw [g9_val, g11_val]; rfl

private theorem q2_val : (q2 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (q2Perm1, q2Perm2) := by
  change (g9 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ *
    (g11 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12))⁻¹ = (q2Perm1, q2Perm2)
  rw [g9_val, g11_val]; rfl

private noncomputable def q1S : S₃ :=
  ⟨q1, by rw [mem_S₃_iff, q1_val]; decide +kernel⟩

private noncomputable def q2S : S₃ :=
  ⟨q2, by rw [mem_S₃_iff, q2_val]; decide +kernel⟩

private noncomputable def g10S : S₃ :=
  ⟨g10, by rw [mem_S₃_iff, g10_val]; decide +kernel⟩

private noncomputable def g11S : S₃ :=
  ⟨g11, by rw [mem_S₃_iff, g11_val]; decide +kernel⟩

private theorem q1S_val :
    ((q1S : m12Pairs) : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (q1Perm1, q1Perm2) := q1_val

private theorem q2S_val :
    ((q2S : m12Pairs) : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) = (q2Perm1, q2Perm2) := q2_val

private theorem g10S_val :
    ((g10S : m12Pairs) : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) =
      (g10Perm1, g10Perm2) := g10_val

private theorem g11S_val :
    ((g11S : m12Pairs) : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) =
      (g11Perm1, g11Perm2) := g11_val

private abbrev idx72Perm1 (m : Fin 72) : Equiv.Perm (Fin 12) :=
  q1Perm1 ^ (m.val / 24) * q2Perm1 ^ ((m.val / 8) % 3) *
    g10Perm1 ^ ((m.val / 2) % 4) * g11Perm1 ^ (m.val % 2)

private abbrev idx72Perm2 (m : Fin 72) : Equiv.Perm (Fin 12) :=
  q1Perm2 ^ (m.val / 24) * q2Perm2 ^ ((m.val / 8) % 3) *
    g10Perm2 ^ ((m.val / 2) % 4) * g11Perm2 ^ (m.val % 2)

private noncomputable def idx72 (m : Fin 72) : S₃ :=
  q1S ^ (m.val / 24) * q2S ^ ((m.val / 8) % 3) *
    g10S ^ ((m.val / 2) % 4) * g11S ^ (m.val % 2)

private theorem idx72_val (m : Fin 72) :
    ((idx72 m : m12Pairs) : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) =
      (idx72Perm1 m, idx72Perm2 m) := by
  unfold idx72
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, q1S_val, q2S_val, g10S_val, g11S_val]
  rfl

private theorem idx72_inj_check :
    ∀ i j : Fin 72, idx72Perm1 i 3 = idx72Perm1 j 3 →
      idx72Perm1 i 4 = idx72Perm1 j 4 → i = j := by
  decide +kernel

private theorem idx72_injective : Function.Injective idx72 := by
  intro i j hij
  have hval :=
    congrArg (fun z : S₃ => ((z : m12Pairs) : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)).1) hij
  rw [congrArg Prod.fst (idx72_val i), congrArg Prod.fst (idx72_val j)] at hval
  exact idx72_inj_check i j (congrArg (· 3) hval) (congrArg (· 4) hval)

private theorem card_S₃_and_L₃ : Nat.card S₃ = 72 ∧ Nat.card L₃ = 72 := by
  let eS₃ : S₃ ≃ L₃ :=
    { toFun := fun p => ⟨proj₁ p.1, p.2⟩
      invFun := fun q => ⟨proj₁.symm q.1, by
        change proj₁ (proj₁.symm q.1) ∈ L₃
        rw [proj₁.apply_symm_apply]
        exact q.2⟩
      left_inv := fun p => Subtype.ext (proj₁.symm_apply_apply p.1)
      right_inv := fun q => Subtype.ext (proj₁.apply_symm_apply q.1) }
  have hL₃_le : L₃ ≤ lvl (m12Data ()) m12a m12b 3 := fun g hg =>
    mem_lvl_three_of_fix_three g hg.1.1 hg.1.2 hg.2
  have hL₃_le_72 : Nat.card L₃ ≤ 72 :=
    (Subgroup.card_le_of_le hL₃_le).trans card_lvl_3.le
  have hS₃_eq_L₃ : Nat.card S₃ = Nat.card L₃ := Nat.card_congr eS₃
  have h72_le_S₃ : 72 ≤ Nat.card S₃ := by
    rw [← Nat.card_fin 72]
    exact Nat.card_le_card_of_injective idx72 idx72_injective
  omega

private theorem idx72_surjective : Function.Surjective idx72 :=
  (idx72_injective.bijective_of_nat_card_le (by rw [card_S₃_and_L₃.1, Nat.card_fin])).2

private theorem card_L₁_L₂_L₃ :
    Nat.card L₁ = 7920 ∧ Nat.card L₂ = 720 ∧ Nat.card L₃ = 72 := by
  have hcard12 : Nat.card (Fin 12) = 12 := Nat.card_fin 12
  have h4 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 4 :=
    isMultiplyPretransitive_M12_four
  have h1 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 1 :=
    isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard12]; decide)
  have : IsPretransitive NativeSporadic.M12 (Fin 12) := is_one_pretransitive_iff.mp h1
  have hL₁_idx : L₁.index = 12 := by rw [index_stabilizer_of_transitive, hcard12]
  have hL₁ : Nat.card L₁ = 7920 := by
    have h := L₁.index_mul_card
    rw [hL₁_idx, card_M12] at h; omega
  set X₀ := SubMulAction.ofStabilizer NativeSporadic.M12 (0 : Fin 12)
  have hX₀_card : Nat.card X₀ = 11 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq, hcard12]
  have h3_X₀ : IsMultiplyPretransitive L₁ X₀ 3 := by
    have : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) (3 + 1) := h4
    exact SubMulAction.ofStabilizer.isMultiplyPretransitive.mp this
  have h1_X₀ : IsMultiplyPretransitive L₁ X₀ 1 :=
    isMultiplyPretransitive_of_le (m := 1) (n := 3) (by decide) (by rw [hX₀_card]; decide)
  have : IsPretransitive L₁ X₀ := is_one_pretransitive_iff.mp h1_X₀
  let p₁ : X₀ := ⟨1, (by decide : (1 : Fin 12) ≠ 0)⟩
  set L₁_1 := stabilizer L₁ p₁
  have hL₁_1_idx : L₁_1.index = 11 := by
    rw [index_stabilizer_of_transitive, hX₀_card]
  let eL₂ : L₁_1 ≃ L₂ :=
    { toFun := fun g => ⟨g.1.1, ⟨g.1.2, congrArg Subtype.val g.2⟩⟩
      invFun := fun h => ⟨⟨h.1, h.2.1⟩, Subtype.ext h.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmul₁ := L₁_1.index_mul_card
  rw [hL₁_1_idx, hL₁, Nat.card_congr eL₂] at hmul₁
  have hL₂ : Nat.card L₂ = 720 := by omega
  exact ⟨hL₁, hL₂, card_S₃_and_L₃.2⟩

private theorem card_inf_of_index_12_not_le_stabilizer (H : Subgroup NativeSporadic.M12)
    (hH_idx : H.index = 12) (hnot : ∀ y : Fin 12, ¬ H ≤ stabilizer NativeSporadic.M12 y) :
    (∀ y : Fin 12, Nat.card ↑(H ⊓ stabilizer NativeSporadic.M12 y) = 660) ∧
      (Nat.card ↑(H ⊓ L₃) = 6 ∨ Nat.card ↑(H ⊓ L₃) = 12) := by
  have hcard12 : Nat.card (Fin 12) = 12 := Nat.card_fin 12
  have h4 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 4 :=
    isMultiplyPretransitive_M12_four
  have h1 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 1 :=
    isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard12]; decide)
  have : IsPretransitive NativeSporadic.M12 (Fin 12) := is_one_pretransitive_iff.mp h1
  have : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) (3 + 1) := h4
  have hH_card : Nat.card H = 7920 := by
    have h := H.index_mul_card
    rw [hH_idx, card_M12] at h; omega
  have horb_exists : ∃ x₀ : Fin 12, Nat.card (orbit H x₀) = 12 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy⟩ := exists_le_stabilizer_of_orbit_one_or_sub_one
      (by rw [hcard12]; decide) H fun x => by
        have hmem := mem_validOrbits (Γ := NativeSporadic.M12) (X := Fin 12) 3
          (by rw [hcard12]; decide) H x
        rw [hH_idx, hcard12, card_M12] at hmem
        have hvo : validOrbits 3 12 95040 12 = [1, 11, 12] := by decide
        rw [hvo, List.mem_cons, List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with h1 | h11 | h12
        · exact Or.inl h1
        · exact Or.inr (by rw [hcard12]; exact h11)
        · exact absurd h12 (hall x)
    exact hnot y hy
  obtain ⟨x₀, hx₀⟩ := horb_exists
  have horb_univ : orbit H x₀ = Set.univ := by
    classical
    have : Fintype (Fin 12) := inferInstance
    have hsum : Nat.card (orbit H x₀) + Nat.card {z : Fin 12 // z ∉ orbit H x₀} = 12 := by
      rw [← Nat.card_sum]
      exact (Nat.card_congr (Equiv.sumCompl (· ∈ orbit H x₀))).trans hcard12
    have hzero : Nat.card {z : Fin 12 // z ∉ orbit H x₀} = 0 := by omega
    have hempty : IsEmpty {z : Fin 12 // z ∉ orbit H x₀} :=
      (Nat.card_eq_zero.mp hzero).resolve_right (not_infinite_iff_finite.mpr inferInstance)
    ext y
    simp only [Set.mem_univ, iff_true]
    by_contra hy
    exact hempty.false ⟨y, hy⟩
  have horb_all : ∀ y : Fin 12, Nat.card (orbit H y) = 12 := by
    intro y
    have hy : y ∈ orbit H x₀ := horb_univ.symm ▸ Set.mem_univ y
    rw [orbit_eq_iff.mpr hy]
    exact hx₀
  have h660 : ∀ y : Fin 12, Nat.card ↑(H ⊓ stabilizer NativeSporadic.M12 y) = 660 := by
    intro y
    have hmul := (stabilizer H y).index_mul_card
    rw [index_stabilizer H y, ← Nat.card_coe_set_eq, horb_all y, hH_card] at hmul
    let eStab : stabilizer H y ≃ ↑(H ⊓ stabilizer NativeSporadic.M12 y) :=
      { toFun := fun g => ⟨g.1.1, ⟨g.1.2, g.2⟩⟩
        invFun := fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eStab] at hmul
    omega
  set X₀ := SubMulAction.ofStabilizer NativeSporadic.M12 (0 : Fin 12)
  have hX₀_card : Nat.card X₀ = 11 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq, hcard12]
  have h3_X₀ : IsMultiplyPretransitive L₁ X₀ (2 + 1) := by
    have : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) ((2 + 1) + 1) := h4
    exact SubMulAction.ofStabilizer.isMultiplyPretransitive.mp this
  set H₀ := H.subgroupOf L₁
  have hH₀_card : Nat.card H₀ = 660 := by
    have heq : (H ⊓ L₁).subgroupOf L₁ = H₀ := by ext x; simp [H₀, Subgroup.mem_subgroupOf]
    rw [← heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact h660 0
  have hH₀_idx : H₀.index = 12 := by
    have h := H₀.index_mul_card
    rw [hH₀_card, card_L₁_L₂_L₃.1] at h; omega
  let p₁ : X₀ := ⟨1, (by decide : (1 : Fin 12) ≠ 0)⟩
  have horb₁ : Nat.card (orbit H₀ p₁) = 11 := by
    have hmem := mem_validOrbits (Γ := L₁) (X := X₀) 2 (by rw [hX₀_card]; decide) H₀ p₁
    rw [hH₀_idx, hX₀_card, card_L₁_L₂_L₃.1] at hmem
    have hvo : validOrbits 2 11 7920 12 = [11] := by decide
    rwa [hvo, List.mem_singleton] at hmem
  let eStab₁ : stabilizer H₀ p₁ ≃ ↑(H ⊓ L₂) :=
    { toFun := fun g => ⟨g.1.1.1, ⟨g.1.2, ⟨g.1.1.2, congrArg Subtype.val g.2⟩⟩⟩
      invFun := fun h => ⟨⟨⟨h.1, h.2.2.1⟩, h.2.1⟩, Subtype.ext h.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmul₁ := (stabilizer H₀ p₁).index_mul_card
  rw [index_stabilizer H₀ p₁, ← Nat.card_coe_set_eq, horb₁, hH₀_card,
    Nat.card_congr eStab₁] at hmul₁
  have h60 : Nat.card ↑(H ⊓ L₂) = 60 := by omega
  set A := H.subgroupOf L₂
  set B := L₃.subgroupOf L₂
  have hA_card : Nat.card A = 60 := by
    have heq : (H ⊓ L₂).subgroupOf L₂ = A := by ext x; simp [A, Subgroup.mem_subgroupOf]
    rw [← heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact h60
  have hB_card : Nat.card B = 72 := by
    have heq : (L₂ ⊓ L₃).subgroupOf L₂ = B := by ext x; simp [B]
    have hle : L₃ ≤ L₂ := inf_le_left
    rw [← heq, inf_of_le_right hle, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact card_L₁_L₂_L₃.2.2
  have hA_idx : A.index = 12 := by
    have h := A.index_mul_card
    rw [hA_card, card_L₁_L₂_L₃.2.1] at h; omega
  let eAB : A.subgroupOf B ≃ ↑(H ⊓ L₃) :=
    { toFun := fun g => ⟨g.1.1.1, ⟨g.2, g.1.2⟩⟩
      invFun := fun h => ⟨⟨⟨h.1, h.2.2.1⟩, h.2.2⟩, h.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eBA : B.subgroupOf A ≃ ↑(H ⊓ L₃) :=
    { toFun := fun g => ⟨g.1.1.1, ⟨g.1.2, g.2⟩⟩
      invFun := fun h => ⟨⟨⟨h.1, h.2.2.1⟩, h.2.1⟩, h.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmulA := (B.subgroupOf A).index_mul_card
  rw [Nat.card_congr eBA, hA_card] at hmulA
  have hmulB := (A.subgroupOf B).index_mul_card
  rw [Nat.card_congr eAB, hB_card] at hmulB
  have hrel_le : (A.subgroupOf B).index ≤ 12 := by
    have hle := Subgroup.relIndex_le_of_le_right (H := A) (le_top : B ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right, hA_idx]; decide)
    rwa [Subgroup.relIndex_top_right, hA_idx] at hle
  set c := Nat.card ↑(H ⊓ L₃)
  have hdvd60 : c ∣ 60 := ⟨(B.subgroupOf A).index, by rw [← hmulA, mul_comm]⟩
  have hdvd72 : c ∣ 72 := ⟨(A.subgroupOf B).index, by rw [← hmulB, mul_comm]⟩
  have hdvd12 : c ∣ 12 := Nat.dvd_gcd hdvd60 hdvd72
  have hle12 : c ≤ 12 := Nat.le_of_dvd (by decide) hdvd12
  have h72_le : 72 ≤ 12 * c := by
    rw [← hmulB]
    exact Nat.mul_le_mul_right c hrel_le
  have hge6 : 6 ≤ c := by omega
  refine ⟨h660, ?_⟩
  rcases (by omega : c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12) with
    h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact Or.inl h6
  · exfalso; rw [h7] at hdvd12; exact absurd hdvd12 (by decide)
  · exfalso; rw [h8] at hdvd12; exact absurd hdvd12 (by decide)
  · exfalso; rw [h9] at hdvd12; exact absurd hdvd12 (by decide)
  · exfalso; rw [h10] at hdvd12; exact absurd hdvd12 (by decide)
  · exfalso; rw [h11] at hdvd12; exact absurd hdvd12 (by decide)
  · exact Or.inr h12

private theorem exists_fixed_of_ord2_S₃ :
    ∀ m : Fin 72, idx72Perm1 m ≠ 1 → idx72Perm1 m ^ 2 = 1 →
      ∃ b₀ : Fin 12, idx72Perm2 m b₀ = b₀ := by
  decide +kernel

private theorem not_both_fix_two_of_ord2_ord3 :
    ∀ m₂ m₃ : Fin 72,
      idx72Perm1 m₂ ≠ 1 → idx72Perm1 m₂ ^ 2 = 1 →
      idx72Perm1 m₃ ≠ 1 → idx72Perm1 m₃ ^ 3 = 1 →
      ∀ c₀ c₁ : Fin 12, c₀ ≠ c₁ →
        idx72Perm2 m₂ c₀ = c₀ → idx72Perm2 m₂ c₁ = c₁ →
        idx72Perm2 m₃ c₀ = c₀ → idx72Perm2 m₃ c₁ = c₁ → False := by
  decide +kernel

private theorem exists_le_stabilizer_of_card_660 (H : Subgroup NativeSporadic.M12)
    (hcard : Nat.card H = 660) {b₀ : Fin 12} (hb₀ : 2 ∣ Nat.card (stabilizer H b₀)) :
    ∃ c₀ : Fin 12, H ≤ stabilizer NativeSporadic.M12 c₀ := by
  have hcard12 : Nat.card (Fin 12) = 12 := Nat.card_fin 12
  obtain ⟨_⟩ : Nonempty (Fintype H) := ⟨Fintype.ofFinite H⟩
  have hdvd11 : 11 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, hcard]; decide
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card 11 hdvd11
  have hg_ne1 : (g.1 : Equiv.Perm (Fin 12)) ≠ 1 := by
    intro h1
    have hg1 : g = 1 := Subtype.ext (Subtype.ext h1)
    rw [hg1, orderOf_one] at hg_ord
    exact (by decide : 1 ≠ 11) hg_ord
  have hex_move : ∃ x₀ : Fin 12, (g.1 : Equiv.Perm (Fin 12)) x₀ ≠ x₀ := by
    by_contra hall
    push Not at hall
    exact hg_ne1 (Equiv.ext hall)
  obtain ⟨x₀, hx₀⟩ := hex_move
  set P := Subgroup.zpowers g
  have hP_card : Nat.card P = 11 := by rw [Nat.card_zpowers, hg_ord]
  have horbP_dvd : Nat.card (orbit P x₀) ∣ 11 := by
    rw [← hP_card, Nat.card_coe_set_eq, ← index_stabilizer P x₀]
    exact Subgroup.index_dvd_card (stabilizer P x₀)
  have horbP_ne1 : Nat.card (orbit P x₀) ≠ 1 := by
    intro h1
    have : Subsingleton (orbit P x₀) := Finite.card_le_one_iff_subsingleton.mp h1.le
    let a : orbit P x₀ := ⟨(⟨g, Subgroup.mem_zpowers g⟩ : P) • x₀, mem_orbit x₀ _⟩
    let b : orbit P x₀ := ⟨x₀, mem_orbit_self x₀⟩
    exact hx₀ (congrArg Subtype.val (Subsingleton.elim a b))
  have horbP_11 : Nat.card (orbit P x₀) = 11 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 11)).mp horbP_dvd).resolve_left horbP_ne1
  have hsub_orb : orbit P x₀ ⊆ orbit H x₀ := by
    rintro y ⟨⟨h, hh⟩, rfl⟩
    exact ⟨h, rfl⟩
  have hle11 : 11 ≤ Nat.card (orbit H x₀) := by
    rw [← horbP_11]
    exact Nat.card_le_card_of_injective (Set.inclusion hsub_orb) (Set.inclusion_injective hsub_orb)
  have hle12 : Nat.card (orbit H x₀) ≤ 12 :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.coe_injective).trans hcard12.le
  have horb_b₀_ne12 : Nat.card (orbit H b₀) ≠ 12 := by
    intro h12
    have hmul := (stabilizer H b₀).index_mul_card
    rw [index_stabilizer H b₀, ← Nat.card_coe_set_eq, h12, hcard] at hmul
    have h55 : Nat.card (stabilizer H b₀) = 55 := by omega
    rw [h55] at hb₀
    exact absurd hb₀ (by decide)
  have horb_x₀_11 : Nat.card (orbit H x₀) = 11 := by
    rcases (by omega : Nat.card (orbit H x₀) = 11 ∨ Nat.card (orbit H x₀) = 12) with h11 | h12
    · exact h11
    · exfalso
      classical
      have hsum : Nat.card (orbit H x₀) + Nat.card {z : Fin 12 // z ∉ orbit H x₀} = 12 := by
        rw [← Nat.card_sum]
        exact (Nat.card_congr (Equiv.sumCompl (· ∈ orbit H x₀))).trans hcard12
      have hzero : Nat.card {z : Fin 12 // z ∉ orbit H x₀} = 0 := by omega
      have hempty : IsEmpty {z : Fin 12 // z ∉ orbit H x₀} :=
        (Nat.card_eq_zero.mp hzero).resolve_right (not_infinite_iff_finite.mpr inferInstance)
      have hb₀_mem : b₀ ∈ orbit H x₀ := by
        by_contra hnot
        exact hempty.false ⟨b₀, hnot⟩
      rw [← orbit_eq_iff.mpr hb₀_mem] at h12
      exact horb_b₀_ne12 h12
  classical
  have hsum : Nat.card (orbit H x₀) + Nat.card {z : Fin 12 // z ∉ orbit H x₀} = 12 := by
    rw [← Nat.card_sum]
    exact (Nat.card_congr (Equiv.sumCompl (· ∈ orbit H x₀))).trans hcard12
  have hcompl1 : Nat.card {z : Fin 12 // z ∉ orbit H x₀} = 1 := by omega
  have hne : Nonempty {z : Fin 12 // z ∉ orbit H x₀} :=
    (Nat.card_pos_iff.mp (by omega : 0 < Nat.card {z : Fin 12 // z ∉ orbit H x₀})).1
  have hsub : Subsingleton {z : Fin 12 // z ∉ orbit H x₀} :=
    Finite.card_le_one_iff_subsingleton.mp hcompl1.le
  obtain ⟨⟨c₀, hc₀⟩⟩ := hne
  refine ⟨c₀, fun h hh => ?_⟩
  rw [mem_stabilizer_iff]
  have hnot_smul : (⟨h, hh⟩ : H) • c₀ ∉ orbit H x₀ := by
    rintro ⟨k, hk⟩
    apply hc₀
    have hk' : k • x₀ = (⟨h, hh⟩ : H) • c₀ := hk
    refine ⟨(⟨h, hh⟩ : H)⁻¹ * k, ?_⟩
    change (⟨h, hh⟩ : H)⁻¹ • (k • x₀) = c₀
    rw [hk', inv_smul_smul]
  exact congrArg Subtype.val
    (@Subsingleton.elim {z : Fin 12 // z ∉ orbit H x₀} hsub
      ⟨(⟨h, hh⟩ : H) • c₀, hnot_smul⟩ ⟨c₀, hc₀⟩)

private theorem exists_le_stabilizer_m12Pairs (K : Subgroup m12Pairs) (hK_idx : K.index = 12) :
    (∃ y₀ : Fin 12, K.map proj₁.toMonoidHom ≤ stabilizer NativeSporadic.M12 y₀) ∨
      (∃ y₀ : Fin 12, K.map proj₂.toMonoidHom ≤ stabilizer NativeSporadic.M12 y₀) := by
  by_contra hnot
  push Not at hnot
  obtain ⟨hnot₁, hnot₂⟩ := hnot
  set K₁ := K.map proj₁.toMonoidHom
  set K₂ := K.map proj₂.toMonoidHom
  have hK₁_idx : K₁.index = 12 := (Subgroup.index_map_equiv K proj₁).trans hK_idx
  have hK₂_idx : K₂.index = 12 := (Subgroup.index_map_equiv K proj₂).trans hK_idx
  obtain ⟨hK₁_660, hK₁_6⟩ := card_inf_of_index_12_not_le_stabilizer K₁ hK₁_idx hnot₁
  obtain ⟨hK₂_660, -⟩ := card_inf_of_index_12_not_le_stabilizer K₂ hK₂_idx hnot₂
  have hKS₁_card : Nat.card ↑(K ⊓ S₁) = 660 := by
    have heq : (K ⊓ S₁).map proj₁.toMonoidHom = K₁ ⊓ L₁ := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨p, ⟨hpK, hpL⟩, rfl⟩
        exact ⟨⟨p, hpK, rfl⟩, hpL⟩
      · rintro ⟨⟨p, hpK, rfl⟩, hpL⟩
        exact ⟨p, ⟨hpK, hpL⟩, rfl⟩
    have hcongr := Nat.card_congr
      (Subgroup.equivMapOfInjective (K ⊓ S₁) proj₁.toMonoidHom proj₁.injective).toEquiv
    rw [heq] at hcongr
    exact hcongr.trans (hK₁_660 0)
  have hKS₃_card : Nat.card ↑(K ⊓ S₃) = 6 ∨ Nat.card ↑(K ⊓ S₃) = 12 := by
    have heq : (K ⊓ S₃).map proj₁.toMonoidHom = K₁ ⊓ L₃ := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨p, ⟨hpK, hpL⟩, rfl⟩
        exact ⟨⟨p, hpK, rfl⟩, hpL⟩
      · rintro ⟨⟨p, hpK, rfl⟩, hpL⟩
        exact ⟨p, ⟨hpK, hpL⟩, rfl⟩
    have hcongr := Nat.card_congr
      (Subgroup.equivMapOfInjective (K ⊓ S₃) proj₁.toMonoidHom proj₁.injective).toEquiv
    rw [heq] at hcongr
    rwa [hcongr]
  set U := K ⊓ S₃
  obtain ⟨_⟩ : Nonempty (Fintype U) := ⟨Fintype.ofFinite U⟩
  have hdvd2 : 2 ∣ Fintype.card U := by
    rw [← Nat.card_eq_fintype_card]
    rcases hKS₃_card with h6 | h12 <;> [rw [h6]; rw [h12]] <;> decide
  have hdvd3 : 3 ∣ Fintype.card U := by
    rw [← Nat.card_eq_fintype_card]
    rcases hKS₃_card with h6 | h12 <;> [rw [h6]; rw [h12]] <;> decide
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨u, hu_ord⟩ := exists_prime_orderOf_dvd_card 2 hdvd2
  obtain ⟨v, hv_ord⟩ := exists_prime_orderOf_dvd_card 3 hdvd3
  obtain ⟨m₂, hm₂⟩ := idx72_surjective ⟨u.1, u.2.2⟩
  obtain ⟨m₃, hm₃⟩ := idx72_surjective ⟨v.1, v.2.2⟩
  have hu_pair : (u.1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) =
      (idx72Perm1 m₂, idx72Perm2 m₂) := by
    rw [← idx72_val m₂, hm₂]
  have hv_pair : (v.1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)) =
      (idx72Perm1 m₃, idx72Perm2 m₃) := by
    rw [← idx72_val m₃, hm₃]
  have hm₂_ne1 : idx72Perm1 m₂ ≠ 1 := by
    intro h1
    have hproj1 : proj₁ u.1 = 1 := Subtype.ext ((congrArg Prod.fst hu_pair).trans h1)
    have hu1 : u = 1 := Subtype.ext (proj₁.injective (hproj1.trans (map_one proj₁).symm))
    rw [hu1, orderOf_one] at hu_ord
    exact (by decide : 1 ≠ 2) hu_ord
  have hm₂_sq1 : idx72Perm1 m₂ ^ 2 = 1 := by
    have h1 : u ^ 2 = 1 := by rw [← hu_ord, pow_orderOf_eq_one]
    have h2 : ((u.1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)).1) ^ 2 = 1 :=
      congrArg (fun z : U => ((z.1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)).1)) h1
    rwa [congrArg Prod.fst hu_pair] at h2
  have hm₃_ne1 : idx72Perm1 m₃ ≠ 1 := by
    intro h1
    have hproj1 : proj₁ v.1 = 1 := Subtype.ext ((congrArg Prod.fst hv_pair).trans h1)
    have hv1 : v = 1 := Subtype.ext (proj₁.injective (hproj1.trans (map_one proj₁).symm))
    rw [hv1, orderOf_one] at hv_ord
    exact (by decide : 1 ≠ 3) hv_ord
  have hm₃_cube1 : idx72Perm1 m₃ ^ 3 = 1 := by
    have h1 : v ^ 3 = 1 := by rw [← hv_ord, pow_orderOf_eq_one]
    have h2 : ((v.1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)).1) ^ 3 = 1 :=
      congrArg (fun z : U => ((z.1 : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)).1)) h1
    rwa [congrArg Prod.fst hv_pair] at h2
  obtain ⟨b₀, hb₀_fix⟩ := exists_fixed_of_ord2_S₃ m₂ hm₂_ne1 hm₂_sq1
  set H := (K ⊓ S₁).map proj₂.toMonoidHom
  have hH_card : Nat.card H = 660 :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective (K ⊓ S₁) proj₂.toMonoidHom proj₂.injective).toEquiv).symm.trans
      hKS₁_card
  have hu_mem_KS₁ : u.1 ∈ K ⊓ S₁ := ⟨u.2.1, u.2.2.1.1⟩
  let uH : stabilizer H b₀ :=
    ⟨⟨proj₂ u.1, ⟨u.1, hu_mem_KS₁, rfl⟩⟩, by
      change (proj₂ u.1 : Equiv.Perm (Fin 12)) b₀ = b₀
      rw [proj₂_coe, congrArg Prod.snd hu_pair]
      exact hb₀_fix⟩
  have huH_ord : orderOf uH = 2 := by
    calc orderOf uH = orderOf (uH : H) := (Subgroup.orderOf_coe uH).symm
      _ = orderOf (proj₂ u.1 : NativeSporadic.M12) := (Subgroup.orderOf_coe (uH : H)).symm
      _ = orderOf u.1 := MulEquiv.orderOf_eq proj₂ u.1
      _ = orderOf u := Subgroup.orderOf_coe u
      _ = 2 := hu_ord
  have hb₀_dvd2 : 2 ∣ Nat.card (stabilizer H b₀) := by
    rw [← huH_ord]
    exact orderOf_dvd_natCard uH
  obtain ⟨c₀, hc₀⟩ := exists_le_stabilizer_of_card_660 H hH_card hb₀_dvd2
  have hH_le_K₂c₀ : H ≤ K₂ ⊓ stabilizer NativeSporadic.M12 c₀ := by
    refine le_inf ?_ hc₀
    exact Subgroup.map_mono inf_le_left
  have hH_eq_K₂c₀ : H = K₂ ⊓ stabilizer NativeSporadic.M12 c₀ := by
    have hrel : H.relIndex (K₂ ⊓ stabilizer NativeSporadic.M12 c₀) = 1 := by
      have hmul := (H.subgroupOf (K₂ ⊓ stabilizer NativeSporadic.M12 c₀)).index_mul_card
      change H.relIndex (K₂ ⊓ stabilizer NativeSporadic.M12 c₀) *
        Nat.card (H.subgroupOf (K₂ ⊓ stabilizer NativeSporadic.M12 c₀)) =
        Nat.card ↑(K₂ ⊓ stabilizer NativeSporadic.M12 c₀) at hmul
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le_K₂c₀).toEquiv,
        hH_card, hK₂_660 c₀] at hmul
      omega
    exact le_antisymm hH_le_K₂c₀ (Subgroup.relIndex_eq_one.mp hrel)
  have hiff_c₀ : ∀ p ∈ K, p.1.1 0 = 0 ↔ p.1.2 c₀ = c₀ := by
    intro p hp
    constructor
    · intro hp0
      have hmem : proj₂ p ∈ H := ⟨p, ⟨hp, hp0⟩, rfl⟩
      exact hc₀ hmem
    · intro hpc₀
      have hmem : proj₂ p ∈ K₂ ⊓ stabilizer NativeSporadic.M12 c₀ :=
        ⟨⟨p, hp, rfl⟩, hpc₀⟩
      rw [← hH_eq_K₂c₀] at hmem
      obtain ⟨q, ⟨hqK, hq0⟩, hqp⟩ := hmem
      have hpq : q = p := proj₂.injective hqp
      exact hpq ▸ hq0
  -- Find `k ∈ K` with `k.1.1 1 = 0` (since `K₁` has stabilizer at `1` of order `660 < 7920`)
  have hex_k : ∃ k ∈ K, k.1.1 1 = 0 := by
    have h1 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 1 :=
      isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide)
        (by rw [Nat.card_fin]; decide)
    have : IsPretransitive NativeSporadic.M12 (Fin 12) := is_one_pretransitive_iff.mp h1
    have horb_K₁ : (0 : Fin 12) ∈ orbit K₁ (1 : Fin 12) := by
      have hmul := (stabilizer K₁ (1 : Fin 12)).index_mul_card
      let eStab : stabilizer K₁ (1 : Fin 12) ≃ ↑(K₁ ⊓ stabilizer NativeSporadic.M12 (1 : Fin 12)) :=
        { toFun := fun g => ⟨g.1.1, ⟨g.1.2, g.2⟩⟩
          invFun := fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hK₁_card : Nat.card K₁ = 7920 := by
        have h := K₁.index_mul_card
        rw [hK₁_idx, card_M12] at h; omega
      rw [index_stabilizer K₁ (1 : Fin 12), ← Nat.card_coe_set_eq, Nat.card_congr eStab,
        hK₁_660 (1 : Fin 12), hK₁_card] at hmul
      have horb12 : Nat.card (orbit K₁ (1 : Fin 12)) = 12 := by omega
      classical
      have hsum : Nat.card (orbit K₁ (1 : Fin 12)) +
          Nat.card {z : Fin 12 // z ∉ orbit K₁ (1 : Fin 12)} = 12 := by
        rw [← Nat.card_sum]
        exact (Nat.card_congr (Equiv.sumCompl (· ∈ orbit K₁ (1 : Fin 12)))).trans (Nat.card_fin 12)
      have hzero : Nat.card {z : Fin 12 // z ∉ orbit K₁ (1 : Fin 12)} = 0 := by omega
      have hempty : IsEmpty {z : Fin 12 // z ∉ orbit K₁ (1 : Fin 12)} :=
        (Nat.card_eq_zero.mp hzero).resolve_right (not_infinite_iff_finite.mpr inferInstance)
      by_contra hnot0
      exact hempty.false ⟨0, hnot0⟩
    obtain ⟨⟨g, ⟨k, hkK, rfl⟩⟩, hgk⟩ := horb_K₁
    exact ⟨k, hkK, hgk⟩
  obtain ⟨k, hkK, hk1⟩ := hex_k
  let c₁ : Fin 12 := k.1.2⁻¹ c₀
  have hc₀_ne_c₁ : c₀ ≠ c₁ := by
    intro heq
    have hkc₀ : k.1.2 c₀ = c₀ := by
      have := congrArg k.1.2 heq
      dsimp only [c₁] at this
      simpa using this
    have hk0 : k.1.1 0 = 0 := (hiff_c₀ k hkK).mpr hkc₀
    have h01 : (0 : Fin 12) = 1 := k.1.1.injective (hk0.trans hk1.symm)
    exact (by decide : (0 : Fin 12) ≠ 1) h01
  have hfix_c₀_c₁ : ∀ p ∈ U, p.1.2 c₀ = c₀ ∧ p.1.2 c₁ = c₁ := by
    intro p ⟨hpK, hpS₃⟩
    have hp0 : p.1.1 0 = 0 := hpS₃.1.1
    have hp1 : p.1.1 1 = 1 := hpS₃.1.2
    have hpc₀ : p.1.2 c₀ = c₀ := (hiff_c₀ p hpK).mp hp0
    have hconj_K : k * p * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hkK hpK) (K.inv_mem hkK)
    have hconj_0 : (k * p * k⁻¹).1.1 0 = 0 := by
      change k.1.1 (p.1.1 (k.1.1⁻¹ 0)) = 0
      have hk1_inv : k.1.1⁻¹ 0 = 1 := by
        rw [← hk1]
        simp
      rw [hk1_inv, hp1, hk1]
    have hconj_c₀ : (k * p * k⁻¹).1.2 c₀ = c₀ := (hiff_c₀ (k * p * k⁻¹) hconj_K).mp hconj_0
    have hpc₁ : p.1.2 c₁ = c₁ := by
      apply k.1.2.injective
      calc k.1.2 (p.1.2 c₁) = (k * p * k⁻¹).1.2 c₀ := rfl
        _ = c₀ := hconj_c₀
        _ = k.1.2 c₁ := by simp [c₁]
    exact ⟨hpc₀, hpc₁⟩
  obtain ⟨hu_c₀, hu_c₁⟩ := hfix_c₀_c₁ u.1 u.2
  obtain ⟨hv_c₀, hv_c₁⟩ := hfix_c₀_c₁ v.1 v.2
  rw [congrArg Prod.snd hu_pair] at hu_c₀ hu_c₁
  rw [congrArg Prod.snd hv_pair] at hv_c₀ hv_c₁
  exact not_both_fix_two_of_ord2_ord3 m₂ m₃ hm₂_ne1 hm₂_sq1 hm₃_ne1 hm₃_cube1
    c₀ c₁ hc₀_ne_c₁ hu_c₀ hu_c₁ hv_c₀ hv_c₁

/-! ### Equivariant bijection and normalizer bound for degree `12` -/

private theorem mathieu_action_of_le_stabilizer {α : Type} [Finite α]
    (G T : Subgroup (Equiv.Perm α)) [IsPretransitive T α]
    (hTG : T ≤ G) (hTnorm : ∀ g ∈ G, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hcardα : Nat.card α = 12) (x₀ : α) (ψ : NativeSporadic.M12 ≃* T)
    {y₀ : Fin 12} (hy₀ : (stabilizer T x₀).comap ψ.toMonoidHom ≤ stabilizer NativeSporadic.M12 y₀) :
    IsMultiplyPretransitive G α 4 ∧ Nat.card G ≤ 95040 := by
  have hcard12 : Nat.card (Fin 12) = 12 := Nat.card_fin 12
  have h4 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 4 :=
    isMultiplyPretransitive_M12_four
  have h1 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 1 :=
    isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard12]; decide)
  have : IsPretransitive NativeSporadic.M12 (Fin 12) := is_one_pretransitive_iff.mp h1
  set H : Subgroup NativeSporadic.M12 := (stabilizer T x₀).comap ψ.toMonoidHom
  have hH_idx : H.index = 12 := by
    rw [Subgroup.index_comap_of_surjective _ ψ.surjective,
      index_stabilizer_of_transitive T x₀, hcardα]
  have hSy_idx : (stabilizer NativeSporadic.M12 y₀).index = 12 := by
    rw [index_stabilizer_of_transitive NativeSporadic.M12 y₀, hcard12]
  have hrel : H.relIndex (stabilizer NativeSporadic.M12 y₀) = 1 := by
    have h := Subgroup.relIndex_mul_index hy₀
    change H.relIndex (stabilizer NativeSporadic.M12 y₀) *
      (stabilizer NativeSporadic.M12 y₀).index = H.index at h
    rw [hH_idx, hSy_idx] at h
    omega
  have hH_eq : H = stabilizer NativeSporadic.M12 y₀ :=
    le_antisymm hy₀ (Subgroup.relIndex_eq_one.mp hrel)
  have horbX : orbit NativeSporadic.M12 y₀ = Set.univ := orbit_eq_univ NativeSporadic.M12 y₀
  have horbα : orbit T x₀ = Set.univ := orbit_eq_univ T x₀
  let eX₀ : Fin 12 ≃ orbit NativeSporadic.M12 y₀ :=
    { toFun := fun x => ⟨x, horbX.symm ▸ Set.mem_univ x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  let eX : Fin 12 ≃ NativeSporadic.M12 ⧸ stabilizer NativeSporadic.M12 y₀ :=
    eX₀.trans (orbitEquivQuotientStabilizer NativeSporadic.M12 y₀)
  let eQ : NativeSporadic.M12 ⧸ stabilizer NativeSporadic.M12 y₀ ≃ T ⧸ stabilizer T x₀ :=
    { toFun := Quotient.map' ψ fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        rw [← hH_eq, Subgroup.mem_comap, map_mul, map_inv] at hab
        exact hab
      invFun := Quotient.map' ψ.symm fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        rw [← hH_eq, Subgroup.mem_comap]
        simpa using hab
      left_inv := by
        rintro ⟨g⟩
        exact congrArg Quotient.mk'' (ψ.symm_apply_apply g)
      right_inv := by
        rintro ⟨g⟩
        exact congrArg Quotient.mk'' (ψ.apply_symm_apply g) }
  let eα₀ : α ≃ orbit T x₀ :=
    { toFun := fun x => ⟨x, horbα.symm ▸ Set.mem_univ x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  let eα : α ≃ T ⧸ stabilizer T x₀ := eα₀.trans (orbitEquivQuotientStabilizer T x₀)
  let f : Fin 12 →ₑ[ψ.toMonoidHom] α :=
    { toFun := eα.symm ∘ eQ ∘ eX
      map_smul' := fun g x => by
        obtain ⟨k, rfl⟩ := exists_smul_eq NativeSporadic.M12 y₀ x
        have heX : ∀ m : NativeSporadic.M12,
            eX (m • y₀) = (m : NativeSporadic.M12 ⧸ stabilizer NativeSporadic.M12 y₀) :=
          fun m => eX.apply_symm_apply (m : NativeSporadic.M12 ⧸ stabilizer NativeSporadic.M12 y₀)
        have heα : ∀ m : T, eα.symm (m : T ⧸ stabilizer T x₀) = m • x₀ := fun _ => rfl
        change eα.symm (eQ (eX (g • (k • y₀)))) = ψ g • eα.symm (eQ (eX (k • y₀)))
        rw [← mul_smul, heX, heX]
        change eα.symm (ψ (g * k) : T ⧸ stabilizer T x₀) =
          ψ g • eα.symm (ψ k : T ⧸ stabilizer T x₀)
        rw [heα, heα, map_mul, mul_smul] }
  have hf : Function.Bijective f := eα.symm.bijective.comp (eQ.bijective.comp eX.bijective)
  have hT4 : IsMultiplyPretransitive T α 4 :=
    (IsPretransitive.of_embedding_congr ψ.surjective hf).mp h4
  have hG4 : IsMultiplyPretransitive G α 4 := by
    rw [isMultiplyPretransitive_iff] at hT4 ⊢
    intro u v
    obtain ⟨t, ht⟩ := hT4 u v
    exact ⟨⟨t.1, hTG t.2⟩, ht⟩
  let φ : Fin 12 ≃ α := Equiv.ofBijective f hf
  let cHom : Equiv.Perm α ≃* Equiv.Perm (Fin 12) :=
    { toFun := fun p => φ.trans (p.trans φ.symm)
      invFun := fun q => φ.symm.trans (q.trans φ)
      left_inv := fun p => by ext x; simp
      right_inv := fun q => by ext x; simp
      map_mul' := fun p₁ p₂ => by ext x; simp }
  have hcHom_ψ :
      ∀ m : NativeSporadic.M12, cHom (ψ m : Equiv.Perm α) = (m : Equiv.Perm (Fin 12)) := by
    intro m
    apply Equiv.Perm.ext
    intro x
    change φ.symm ((ψ m : Equiv.Perm α) (φ x)) = (m : Equiv.Perm (Fin 12)) x
    have hsmul : (ψ m : Equiv.Perm α) (φ x) = φ (m • x) := (f.map_smul' m x).symm
    rw [hsmul, φ.symm_apply_apply]
    rfl
  have hcHom_T : ∀ p : Equiv.Perm α, p ∈ T ↔ cHom p ∈ NativeSporadic.M12 := by
    intro p
    constructor
    · intro hp
      have h := hcHom_ψ (ψ.symm ⟨p, hp⟩)
      have hp_eq : (ψ (ψ.symm ⟨p, hp⟩) : Equiv.Perm α) = p :=
        congrArg Subtype.val (ψ.apply_symm_apply ⟨p, hp⟩)
      rw [hp_eq] at h
      rw [h]
      exact (ψ.symm ⟨p, hp⟩).2
    · intro hcp
      have h := hcHom_ψ ⟨cHom p, hcp⟩
      have hp_eq : p = (ψ ⟨cHom p, hcp⟩ : Equiv.Perm α) :=
        cHom.injective h.symm
      rw [hp_eq]
      exact (ψ ⟨cHom p, hcp⟩).2
  let toNorm : G → Subgroup.normalizer (NativeSporadic.M12 : Set (Equiv.Perm (Fin 12))) :=
    fun g => ⟨cHom g.1, fun m => by
      obtain ⟨p, rfl⟩ := cHom.surjective m
      simp only [SetLike.mem_coe]
      rw [← map_inv, ← map_mul, ← map_mul, ← hcHom_T, ← hcHom_T]
      exact ⟨fun hp => hTnorm g.1 g.2 p hp, fun hconj => by
        have := hTnorm g.1⁻¹ (G.inv_mem g.2) (g.1 * p * g.1⁻¹) hconj
        simpa [mul_assoc] using this⟩⟩
  have htoNorm_inj : Function.Injective toNorm := by
    intro g₁ g₂ h
    exact Subtype.ext (cHom.injective (congrArg Subtype.val h))
  have hG_le : Nat.card G ≤ 95040 :=
    (Nat.card_le_card_of_injective toNorm htoNorm_inj).trans card_normalizer_M12_le
  exact ⟨hG4, hG_le⟩

end M12CaseProof

/-- Maróti's theorem for primitive almost simple groups with socle `M₁₂`. -/
theorem sporadicCase_M12 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .M12)) :
    AlmostSimpleConclusion G := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  let eM12 : S ≃* NativeSporadic.M12 := e
  have hcardS : Nat.card S = 95040 := by
    rw [Nat.card_congr eM12.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have hAut : Nat.card (MulAut S) ≤ 2 * 95040 := by
    rw [Nat.card_congr (MulAut.congr eM12).toEquiv]
    exact CFSG.Sporadic.Schreier.m12_mulAut_card.trans
      (Nat.mul_le_mul_left 2 CFSG.Sporadic.Mathieu.card_M12.le)
  have hG_le : Nat.card G ≤ 190080 := hS.card_le_card_mulAut.trans hAut
  obtain ⟨H, hH_ne, hH_idx⟩ := hS.exists_proper_subgroup_index_eq
  have hn12 : 12 ≤ Nat.card α := hH_idx ▸ index_ge_M12 e hH_ne
  rcases le_or_gt 16 (Nat.card α) with hn16 | hn16
  · right; right
    exact hG_le.trans ((by decide : 190080 ≤ bound 16).trans (bound_mono hn16))
  · have hdvd : Nat.card α ∣ 95040 := by
      rw [← hcardS, ← hH_idx]
      exact Subgroup.index_dvd_card H
    rcases (by omega :
        Nat.card α = 12 ∨ Nat.card α = 13 ∨ Nat.card α = 14 ∨ Nat.card α = 15) with
      hn_eq | hn13 | hn14 | hn15
    · have hS' := hS
      obtain ⟨T, hTG, hTnorm, hSimpleT, _, _, ⟨eTS⟩⟩ := hS'
      have : IsPretransitive T α := isPretransitive_socle hTG hTnorm
      have hα_pos : 0 < Nat.card α := by omega
      obtain ⟨x₀⟩ : Nonempty α := (Nat.card_pos_iff.mp hα_pos).1
      let ePairsT : CFSG.Sporadic.Schreier.m12Pairs ≃* T :=
        M12CaseProof.proj₁.trans (eM12.symm.trans eTS.symm)
      let K : Subgroup CFSG.Sporadic.Schreier.m12Pairs :=
        (stabilizer T x₀).comap ePairsT.toMonoidHom
      have hK_idx : K.index = 12 := by
        rw [Subgroup.index_comap_of_surjective _ ePairsT.surjective,
          index_stabilizer_of_transitive T x₀, hn_eq]
      have hex_ψ : ∃ (ψ : NativeSporadic.M12 ≃* T) (y₀ : Fin 12),
          (stabilizer T x₀).comap ψ.toMonoidHom ≤ stabilizer NativeSporadic.M12 y₀ := by
        rcases M12CaseProof.exists_le_stabilizer_m12Pairs K hK_idx with
          ⟨y₀, hy₀⟩ | ⟨y₀, hy₀⟩
        · refine ⟨M12CaseProof.proj₁.symm.trans ePairsT, y₀, ?_⟩
          intro m hm
          apply hy₀
          exact ⟨M12CaseProof.proj₁.symm m, hm, M12CaseProof.proj₁.apply_symm_apply m⟩
        · refine ⟨M12CaseProof.proj₂.symm.trans ePairsT, y₀, ?_⟩
          intro m hm
          apply hy₀
          exact ⟨M12CaseProof.proj₂.symm m, hm, M12CaseProof.proj₂.apply_symm_apply m⟩
      obtain ⟨ψ, y₀, hy₀⟩ := hex_ψ
      obtain ⟨hG4, hG_95040⟩ :=
        M12CaseProof.mathieu_action_of_le_stabilizer G T hTG hTnorm hn_eq x₀ ψ hy₀
      obtain ⟨eGS⟩ := mulEquiv_of_card_le hS (hG_95040.trans hcardS.symm.le)
      obtain ⟨eBridge⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
      right; left
      exact ⟨(.M12, 12), by simp [fourTransitiveMathieu], hn_eq, hG4,
        ⟨(eGS.trans eM12).trans eBridge⟩⟩
    · exfalso; rw [hn13] at hdvd; exact absurd hdvd (by decide)
    · exfalso; rw [hn14] at hdvd; exact absurd hdvd (by decide)
    · exfalso
      have hH'_idx : (H.map (eM12 : S →* NativeSporadic.M12)).index = 15 := by
        rw [Subgroup.index_map_equiv, hH_idx, hn15]
      exact M12CaseProof.not_exists_subgroup_index_15 _ hH'_idx

end Maroti
