module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Basic
import Maroti.Sporadic.Mathieu
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.Schreier.MathieuOddCoreM22
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Schreier.MathieuOddCoreM12
import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
import CFSG.Sporadic.Bridge.M12

/-!
# Mathieu Groups `M₁₂` and `M₂₂`

This file proves `sporadicCase_M22` and `sporadicCase_M12`, together with `index_ge_M22` (`≥ 19`)
and `index_ge_M12` (`≥ 12`).
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint MulAction

/-! ### `M₂₂` -/

namespace M22Proof

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native CFSG.Sporadic.Th CFSG.Perm.Native

private theorem mem_lvl_four_of_fix_four (g : NativeSporadic.M22)
    (h0 : (g : Equiv.Perm (Fin 22)) 0 = 0) (h1 : (g : Equiv.Perm (Fin 22)) 1 = 1)
    (h2 : (g : Equiv.Perm (Fin 22)) 2 = 2) (h3 : (g : Equiv.Perm (Fin 22)) 3 = 3) :
    g ∈ lvl (m22Data ()) m22a m22b 4 := by
  have hC := chain m22_hyp
  have hl0 : g ∈ lvl (m22Data ()) m22a m22b 0 := by
    rw [lvl_zero m22_hyp]
    trivial
  have hstep : ∀ (i : ℕ) (hi : i < 5) (hlt : i < 22),
      (m22Data ()).base[i]! = i →
      (g : Equiv.Perm (Fin 22)) ⟨i, hlt⟩ = ⟨i, hlt⟩ →
      g ∈ lvl (m22Data ()) m22a m22b i →
      g ∈ lvl (m22Data ()) m22a m22b (i + 1) := by
    intro i hi hlt hbi hfix hgi
    have hib : i < (m22Data ()).base.size := by change i < 5; exact hi
    refine (hC.2.1 i hib g hgi).1 ?_
    rw [hbi, idx_of_lt g hlt]
    exact congrArg Fin.val hfix
  have hl1 := hstep 0 (by decide) (by decide) rfl h0 hl0
  have hl2 := hstep 1 (by decide) (by decide) rfl h1 hl1
  have hl3 := hstep 2 (by decide) (by decide) rfl h2 hl2
  exact hstep 3 (by decide) (by decide) rfl h3 hl3

private theorem eq_one_of_fix_five (g : NativeSporadic.M22)
    (h0 : (g : Equiv.Perm (Fin 22)) 0 = 0) (h1 : (g : Equiv.Perm (Fin 22)) 1 = 1)
    (h2 : (g : Equiv.Perm (Fin 22)) 2 = 2) (h3 : (g : Equiv.Perm (Fin 22)) 3 = 3)
    (h4 : (g : Equiv.Perm (Fin 22)) 4 = 4) : g = 1 := by
  have hC := chain m22_hyp
  have hl4 := mem_lvl_four_of_fix_four g h0 h1 h2 h3
  have hib : 4 < (m22Data ()).base.size := by decide
  have hl5 : g ∈ lvl (m22Data ()) m22a m22b 5 := by
    refine (hC.2.1 4 hib g hl4).1 ?_
    have hbi : (m22Data ()).base[4]! = 4 := rfl
    rw [hbi, idx_of_lt g (by decide)]
    exact congrArg Fin.val h4
  have hcard5 : Nat.card (lvl (m22Data ()) m22a m22b 5) = 1 := by
    have := hC.2.2 5 (by decide)
    have hsz : (m22Data ()).base.size = 5 := rfl
    rw [hsz, Finset.Ico_self, Finset.prod_empty] at this
    exact this
  have hbot : lvl (m22Data ()) m22a m22b 5 = ⊥ := Subgroup.card_eq_one.mp hcard5
  rwa [hbot, Subgroup.mem_bot] at hl5

private theorem card_lvl_4 : Nat.card (lvl (m22Data ()) m22a m22b 4) = 3 := by
  have hC := (chain m22_hyp).2.2 4 (by decide)
  have hsz : (m22Data ()).base.size = 5 := rfl
  have hIco : Finset.Ico 4 5 = {4} := rfl
  rw [hsz, hIco, Finset.prod_singleton] at hC
  have h2 := congrArg (fun L : List ℕ => L[4]?) (checkFacts m22_hyp.cert).sizes
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList] at h2
  have hv : (m22Data ()).sizes[4]? = some 3 := rfl
  rw [hv] at h2
  have hl : 4 < (trees 22 (m22Data ())).size := by
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h2
    simp at h2
  rw [Array.getElem?_eq_getElem hl] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  rw [hC, getElem!_pos (trees 22 (m22Data ())) 4 hl]
  exact h2

private abbrev gA : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

private abbrev gB : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

private abbrev a22 : NativeSporadic.M22 :=
  ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

private abbrev b22 : NativeSporadic.M22 :=
  ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

private abbrev g0 : NativeSporadic.M22 := a22
private abbrev g1 : NativeSporadic.M22 := b22 * a22 * b22
private abbrev g2 : NativeSporadic.M22 :=
  g0⁻¹ * g1⁻¹ * g1⁻¹ * g0⁻¹ * g1⁻¹ * g0 * g1 * g1 * g0 * g1⁻¹
private abbrev g3 : NativeSporadic.M22 :=
  g0⁻¹ * g1⁻¹ * g2 * g0⁻¹ * g1 * g0 * g2⁻¹ * g1
private abbrev g4 : NativeSporadic.M22 := g3⁻¹ * g3⁻¹
private abbrev g5 : NativeSporadic.M22 :=
  g3⁻¹ * g2⁻¹ * g3 * g3 * g2 * g3 * g2
private abbrev g6 : NativeSporadic.M22 := g5 * g4 * g5⁻¹
private abbrev g7 : NativeSporadic.M22 := g4⁻¹ * g6 * g5⁻¹
private abbrev g8 : NativeSporadic.M22 := g2 * g7⁻¹ * g3 * g2 * g3 * g2
private abbrev g9 : NativeSporadic.M22 := g6⁻¹ * g8 * g6 * g7 * g8

private abbrev g1Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 10, 18, 14, 2] * List.formPerm [1, 3, 21, 15, 20] *
    List.formPerm [4, 12, 13, 9, 17] * List.formPerm [5, 19, 8, 7, 6]

private abbrev g2Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 20, 14] * List.formPerm [2, 8, 5] * List.formPerm [4, 11, 13] *
    List.formPerm [7, 10, 16] * List.formPerm [9, 12, 17] * List.formPerm [18, 21, 19]

private abbrev g3Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 7] * List.formPerm [2, 6, 10, 4] * List.formPerm [3, 20, 5, 13] *
    List.formPerm [8, 21] * List.formPerm [9, 17, 11, 15] * List.formPerm [12, 14, 19, 18]

private abbrev g4Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [2, 10] * List.formPerm [3, 5] * List.formPerm [4, 6] * List.formPerm [9, 11] *
    List.formPerm [12, 19] * List.formPerm [13, 20] * List.formPerm [14, 18] *
    List.formPerm [15, 17]

private abbrev g5Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [2, 15, 8] * List.formPerm [3, 14, 20] * List.formPerm [4, 18, 13] *
    List.formPerm [7, 9, 12] * List.formPerm [10, 16, 17] * List.formPerm [11, 21, 19]

private abbrev g6Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [3, 4] * List.formPerm [5, 14] * List.formPerm [6, 18] * List.formPerm [7, 11] *
    List.formPerm [8, 10] * List.formPerm [12, 21] * List.formPerm [13, 20] *
    List.formPerm [15, 16]

private abbrev g7Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [3, 20] * List.formPerm [4, 13] * List.formPerm [5, 18] * List.formPerm [6, 14] *
    List.formPerm [7, 21] * List.formPerm [8, 16] * List.formPerm [10, 15] *
    List.formPerm [11, 12]

private abbrev g8Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [3, 18, 11] * List.formPerm [4, 12, 14] * List.formPerm [5, 15, 6] *
    List.formPerm [7, 16, 21] * List.formPerm [9, 19, 17] * List.formPerm [10, 20, 13]

private abbrev g9Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [4, 15, 16] * List.formPerm [5, 10, 21] * List.formPerm [6, 14, 20] *
    List.formPerm [7, 13, 12] * List.formPerm [8, 18, 11] * List.formPerm [9, 17, 19]

private theorem g0_val : (g0 : Equiv.Perm (Fin 22)) = gA := rfl
private theorem g1_val : (g1 : Equiv.Perm (Fin 22)) = g1Perm := by decide +kernel
private theorem g2_val : (g2 : Equiv.Perm (Fin 22)) = g2Perm := by
  change (g0 : Equiv.Perm (Fin 22))⁻¹ * (g1 : Equiv.Perm (Fin 22))⁻¹ *
    (g1 : Equiv.Perm (Fin 22))⁻¹ * (g0 : Equiv.Perm (Fin 22))⁻¹ *
    (g1 : Equiv.Perm (Fin 22))⁻¹ * (g0 : Equiv.Perm (Fin 22)) *
    (g1 : Equiv.Perm (Fin 22)) * (g1 : Equiv.Perm (Fin 22)) *
    (g0 : Equiv.Perm (Fin 22)) * (g1 : Equiv.Perm (Fin 22))⁻¹ = g2Perm
  rw [g0_val, g1_val]; decide +kernel
private theorem g3_val : (g3 : Equiv.Perm (Fin 22)) = g3Perm := by
  change (g0 : Equiv.Perm (Fin 22))⁻¹ * (g1 : Equiv.Perm (Fin 22))⁻¹ *
    (g2 : Equiv.Perm (Fin 22)) * (g0 : Equiv.Perm (Fin 22))⁻¹ *
    (g1 : Equiv.Perm (Fin 22)) * (g0 : Equiv.Perm (Fin 22)) *
    (g2 : Equiv.Perm (Fin 22))⁻¹ * (g1 : Equiv.Perm (Fin 22)) = g3Perm
  rw [g0_val, g1_val, g2_val]; decide +kernel
private theorem g4_val : (g4 : Equiv.Perm (Fin 22)) = g4Perm := by
  change (g3 : Equiv.Perm (Fin 22))⁻¹ * (g3 : Equiv.Perm (Fin 22))⁻¹ = g4Perm
  rw [g3_val]; decide +kernel
private theorem g5_val : (g5 : Equiv.Perm (Fin 22)) = g5Perm := by
  change (g3 : Equiv.Perm (Fin 22))⁻¹ * (g2 : Equiv.Perm (Fin 22))⁻¹ *
    (g3 : Equiv.Perm (Fin 22)) * (g3 : Equiv.Perm (Fin 22)) *
    (g2 : Equiv.Perm (Fin 22)) * (g3 : Equiv.Perm (Fin 22)) *
    (g2 : Equiv.Perm (Fin 22)) = g5Perm
  rw [g2_val, g3_val]; decide +kernel
private theorem g6_val : (g6 : Equiv.Perm (Fin 22)) = g6Perm := by
  change (g5 : Equiv.Perm (Fin 22)) * (g4 : Equiv.Perm (Fin 22)) *
    (g5 : Equiv.Perm (Fin 22))⁻¹ = g6Perm
  rw [g4_val, g5_val]; decide +kernel
private theorem g7_val : (g7 : Equiv.Perm (Fin 22)) = g7Perm := by
  change (g4 : Equiv.Perm (Fin 22))⁻¹ * (g6 : Equiv.Perm (Fin 22)) *
    (g5 : Equiv.Perm (Fin 22))⁻¹ = g7Perm
  rw [g4_val, g5_val, g6_val]; decide +kernel
private theorem g8_val : (g8 : Equiv.Perm (Fin 22)) = g8Perm := by
  change (g2 : Equiv.Perm (Fin 22)) * (g7 : Equiv.Perm (Fin 22))⁻¹ *
    (g3 : Equiv.Perm (Fin 22)) * (g2 : Equiv.Perm (Fin 22)) *
    (g3 : Equiv.Perm (Fin 22)) * (g2 : Equiv.Perm (Fin 22)) = g8Perm
  rw [g2_val, g3_val, g7_val]; decide +kernel
private theorem g9_val : (g9 : Equiv.Perm (Fin 22)) = g9Perm := by
  change (g6 : Equiv.Perm (Fin 22))⁻¹ * (g8 : Equiv.Perm (Fin 22)) *
    (g6 : Equiv.Perm (Fin 22)) * (g7 : Equiv.Perm (Fin 22)) *
    (g8 : Equiv.Perm (Fin 22)) = g9Perm
  rw [g6_val, g7_val, g8_val]; decide +kernel

private theorem g9_mem_lvl_4 : g9 ∈ lvl (m22Data ()) m22a m22b 4 :=
  mem_lvl_four_of_fix_four g9
    (by rw [g9_val]; decide) (by rw [g9_val]; decide)
    (by rw [g9_val]; decide) (by rw [g9_val]; decide)

private theorem img_four_of_fix_four (w : NativeSporadic.M22)
    (h0 : (w : Equiv.Perm (Fin 22)) 0 = 0) (h1 : (w : Equiv.Perm (Fin 22)) 1 = 1)
    (h2 : (w : Equiv.Perm (Fin 22)) 2 = 2) (h3 : (w : Equiv.Perm (Fin 22)) 3 = 3) :
    (w : Equiv.Perm (Fin 22)) 4 = 4 ∨ (w : Equiv.Perm (Fin 22)) 4 = 15 ∨
      (w : Equiv.Perm (Fin 22)) 4 = 16 := by
  let g9L : lvl (m22Data ()) m22a m22b 4 := ⟨g9, g9_mem_lvl_4⟩
  let f : Fin 3 → lvl (m22Data ()) m22a m22b 4 := fun k => g9L ^ k.val
  have hf_val :
      ∀ k : Fin 3, ((f k : NativeSporadic.M22) : Equiv.Perm (Fin 22)) = g9Perm ^ k.val := by
    intro k
    change ((g9 ^ k.val : NativeSporadic.M22) : Equiv.Perm (Fin 22)) = g9Perm ^ k.val
    rw [Subgroup.coe_pow, g9_val]
  have hinj : Function.Injective f := by
    intro i j hij
    have h4 : ((f i : NativeSporadic.M22) : Equiv.Perm (Fin 22)) 4 =
        ((f j : NativeSporadic.M22) : Equiv.Perm (Fin 22)) 4 :=
      congrArg
        (fun z : lvl (m22Data ()) m22a m22b 4 => ((z : NativeSporadic.M22) : Equiv.Perm (Fin 22)) 4)
        hij
    rw [hf_val i, hf_val j] at h4
    revert h4
    fin_cases i <;> fin_cases j <;> decide
  have hsurj : Function.Surjective f :=
    (hinj.bijective_of_nat_card_le (by rw [card_lvl_4, Nat.card_fin])).2
  obtain ⟨k, hk⟩ := hsurj ⟨w, mem_lvl_four_of_fix_four w h0 h1 h2 h3⟩
  have hw4 : (w : Equiv.Perm (Fin 22)) 4 = (g9Perm ^ k.val) 4 := by
    rw [← hf_val k, hk]
  rw [hw4]
  fin_cases k
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (by decide))

/-! #### Sylow `11`-normalizer in `M₂₂` -/

private abbrev x11Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 2, 7, 8, 1, 4, 3, 10, 21, 12, 11] *
    List.formPerm [5, 18, 6, 15, 20, 13, 9, 16, 14, 19, 17]

private abbrev m22x11 : NativeSporadic.M22 := a22 * b22 * a22 * b22 * b22

private theorem m22x11_val : (m22x11 : Equiv.Perm (Fin 22)) = x11Perm := by decide +kernel

private theorem orderOf_m22x11 : orderOf m22x11 = 11 := by
  have hdvd : orderOf m22x11 ∣ 11 := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    change (m22x11 : Equiv.Perm (Fin 22)) ^ 11 = 1
    rw [m22x11_val]; decide +kernel)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp hdvd with h1 | h11
  · exfalso
    have hval : (m22x11 : Equiv.Perm (Fin 22)) = 1 :=
      congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
    rw [m22x11_val] at hval
    exact (by decide +kernel : x11Perm ≠ 1) hval
  · exact h11

private abbrev P11 : Subgroup NativeSporadic.M22 := Subgroup.zpowers m22x11

private theorem card_P11 : Nat.card P11 = 11 := by
  rw [Nat.card_zpowers, orderOf_m22x11]

private abbrev C11 : Subgroup NativeSporadic.M22 :=
  Subgroup.centralizer (P11 : Set NativeSporadic.M22)

private theorem comm_m22x11_pow (g : C11) (k : ℕ) (p : Fin 22) :
    (g.1 : Equiv.Perm (Fin 22)) ((x11Perm ^ k) p) =
      (x11Perm ^ k) ((g.1 : Equiv.Perm (Fin 22)) p) := by
  have hcomm : m22x11 * g.1 = g.1 * m22x11 :=
    Subgroup.mem_centralizer_iff.mp g.2 m22x11 (Subgroup.mem_zpowers m22x11)
  have hcomm' : Commute (g.1 : Equiv.Perm (Fin 22)) x11Perm := by
    rw [← m22x11_val]
    exact (congrArg Subtype.val hcomm).symm
  have hpow : (g.1 : Equiv.Perm (Fin 22)) * x11Perm ^ k =
      x11Perm ^ k * (g.1 : Equiv.Perm (Fin 22)) :=
    hcomm'.pow_right k
  exact Equiv.Perm.ext_iff.mp hpow p

private theorem m22x11_orb1 : (x11Perm ^ 4) 0 = 1 := by decide +kernel
private theorem m22x11_orb2 : (x11Perm ^ 1) 0 = 2 := by decide +kernel
private theorem m22x11_orb3 : (x11Perm ^ 6) 0 = 3 := by decide +kernel
private theorem m22x11_orb4 : (x11Perm ^ 5) 0 = 4 := by decide +kernel

private theorem stabilizer_C11_zero_eq_bot : stabilizer C11 (0 : Fin 22) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h0 : (g.1 : Equiv.Perm (Fin 22)) 0 = 0 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 22)) 1 = 1 := by
    rw [← m22x11_orb1, comm_m22x11_pow g 4 0, h0, m22x11_orb1]
  have h2 : (g.1 : Equiv.Perm (Fin 22)) 2 = 2 := by
    rw [← m22x11_orb2, comm_m22x11_pow g 1 0, h0, m22x11_orb2]
  have h3 : (g.1 : Equiv.Perm (Fin 22)) 3 = 3 := by
    rw [← m22x11_orb3, comm_m22x11_pow g 6 0, h0, m22x11_orb3]
  have h4 : (g.1 : Equiv.Perm (Fin 22)) 4 = 4 := by
    rw [← m22x11_orb4, comm_m22x11_pow g 5 0, h0, m22x11_orb4]
  exact Subtype.ext (eq_one_of_fix_five g.1 h0 h1 h2 h3 h4)

private abbrev v11 : NativeSporadic.M22 :=
  g8 * g7 * g5⁻¹ * g9 * g2⁻¹ * g3⁻¹ * g2⁻¹ * g1 * g2

private abbrev v11Perm : Equiv.Perm (Fin 22) :=
  g8Perm * g7Perm * g5Perm⁻¹ * g9Perm * g2Perm⁻¹ * g3Perm⁻¹ * g2Perm⁻¹ * g1Perm * g2Perm

private theorem v11_val : (v11 : Equiv.Perm (Fin 22)) = v11Perm := by
  change (g8 : Equiv.Perm (Fin 22)) * (g7 : Equiv.Perm (Fin 22)) *
    (g5 : Equiv.Perm (Fin 22))⁻¹ * (g9 : Equiv.Perm (Fin 22)) *
    (g2 : Equiv.Perm (Fin 22))⁻¹ * (g3 : Equiv.Perm (Fin 22))⁻¹ *
    (g2 : Equiv.Perm (Fin 22))⁻¹ * (g1 : Equiv.Perm (Fin 22)) *
    (g2 : Equiv.Perm (Fin 22)) = v11Perm
  rw [g1_val, g2_val, g3_val, g5_val, g7_val, g8_val, g9_val]

private theorem not_mem_orbit_C11_five : (5 : Fin 22) ∉ orbit C11 (0 : Fin 22) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 22)) 0 = 5 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 22)) 1 = 20 := by
    rw [← m22x11_orb1, comm_m22x11_pow g 4 0, h0]; decide +kernel
  have h2 : (g.1 : Equiv.Perm (Fin 22)) 2 = 18 := by
    rw [← m22x11_orb2, comm_m22x11_pow g 1 0, h0]; decide +kernel
  have h3 : (g.1 : Equiv.Perm (Fin 22)) 3 = 9 := by
    rw [← m22x11_orb3, comm_m22x11_pow g 6 0, h0]; decide +kernel
  have h4 : (g.1 : Equiv.Perm (Fin 22)) 4 = 13 := by
    rw [← m22x11_orb4, comm_m22x11_pow g 5 0, h0]; decide +kernel
  obtain ⟨w, hw_def⟩ : ∃ w : NativeSporadic.M22, w = v11 * g.1 := ⟨_, rfl⟩
  have hw_apply : ∀ p : Fin 22,
      (w : Equiv.Perm (Fin 22)) p = v11Perm ((g.1 : Equiv.Perm (Fin 22)) p) := by
    intro p
    rw [hw_def, Subgroup.coe_mul, v11_val, Equiv.Perm.mul_apply]
  have hw0 : (w : Equiv.Perm (Fin 22)) 0 = 0 := by
    rw [hw_apply, h0]; decide +kernel
  have hw1 : (w : Equiv.Perm (Fin 22)) 1 = 1 := by
    rw [hw_apply, h1]; decide +kernel
  have hw2 : (w : Equiv.Perm (Fin 22)) 2 = 2 := by
    rw [hw_apply, h2]; decide +kernel
  have hw3 : (w : Equiv.Perm (Fin 22)) 3 = 3 := by
    rw [hw_apply, h3]; decide +kernel
  have hw4 : (w : Equiv.Perm (Fin 22)) 4 = 6 := by
    rw [hw_apply, h4]; decide +kernel
  have himg := img_four_of_fix_four w hw0 hw1 hw2 hw3
  rw [hw4] at himg
  rcases himg with h | h | h <;> exact absurd h (by decide)

private theorem card_C11_dvd : Nat.card C11 ∣ 11 := by
  have hstab : Nat.card (stabilizer C11 (0 : Fin 22)) = 1 := by
    rw [stabilizer_C11_zero_eq_bot, Subgroup.card_bot]
  have hcard_eq : Nat.card C11 = Nat.card (orbit C11 (0 : Fin 22)) := by
    have h := (stabilizer C11 (0 : Fin 22)).index_mul_card
    rw [hstab, mul_one, index_stabilizer C11 (0 : Fin 22), ← Nat.card_coe_set_eq] at h
    exact h.symm
  let emb : orbit C11 (0 : Fin 22) → {p : Fin 22 // p ≠ 5} :=
    fun x => ⟨x.1, fun h => not_mem_orbit_C11_five (h ▸ x.2)⟩
  have hemb : Function.Injective emb :=
    fun x y h => Subtype.ext (congrArg (fun z : {p : Fin 22 // p ≠ 5} => z.1) h)
  have h21 : Nat.card {p : Fin 22 // p ≠ 5} = 21 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hle : Nat.card C11 ≤ 21 :=
    (hcard_eq.trans_le (Nat.card_le_card_of_injective emb hemb)).trans h21.le
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
    Nat.card (Subgroup.normalizer (P11 : Set NativeSporadic.M22)) ∣ 110 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h1 := card_normalizer_dvd_mul_totient P11 card_P11
  have h2 : Nat.card C11 * (11 - 1) ∣ 11 * 10 :=
    mul_dvd_mul card_C11_dvd (dvd_refl 10)
  exact h1.trans h2

private theorem not_exists_subgroup_of_sylow11 (H : Subgroup NativeSporadic.M22)
    {c : ℕ} (hcard : Nat.card H = c) (hdvd : 11 ∣ c)
    (hno : hasValidSylowNormalizer 11 110 c = false) : False := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hval := hasValidSylowNormalizer_of_dvd P11 card_P11
    (by rw [card_M22]; decide) card_normalizer_P11_dvd (by decide)
    (H := H) (by rwa [hcard])
  rw [hcard, hno] at hval
  exact Bool.noConfusion hval

/-! #### Sylow `7`-normalizer in `M₂₂` -/

private abbrev x7Perm : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 3, 16, 1, 15, 4, 2] * List.formPerm [5, 17, 19, 21, 13, 11, 12] *
    List.formPerm [6, 10, 20, 7, 9, 18, 14]

private abbrev m22x7 : NativeSporadic.M22 := g3 * g8⁻¹ * g1

private theorem m22x7_val : (m22x7 : Equiv.Perm (Fin 22)) = x7Perm := by
  change (g3 : Equiv.Perm (Fin 22)) * (g8 : Equiv.Perm (Fin 22))⁻¹ *
    (g1 : Equiv.Perm (Fin 22)) = x7Perm
  rw [g1_val, g3_val, g8_val]; decide +kernel

private theorem orderOf_m22x7 : orderOf m22x7 = 7 := by
  have hdvd : orderOf m22x7 ∣ 7 := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    change (m22x7 : Equiv.Perm (Fin 22)) ^ 7 = 1
    rw [m22x7_val]; decide +kernel)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdvd with h1 | h7
  · exfalso
    have hval : (m22x7 : Equiv.Perm (Fin 22)) = 1 :=
      congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
    rw [m22x7_val] at hval
    exact (by decide +kernel : x7Perm ≠ 1) hval
  · exact h7

private abbrev P7 : Subgroup NativeSporadic.M22 := Subgroup.zpowers m22x7

private theorem card_P7 : Nat.card P7 = 7 := by
  rw [Nat.card_zpowers, orderOf_m22x7]

private abbrev C7 : Subgroup NativeSporadic.M22 :=
  Subgroup.centralizer (P7 : Set NativeSporadic.M22)

private theorem comm_m22x7_pow (g : C7) (k : ℕ) (p : Fin 22) :
    (g.1 : Equiv.Perm (Fin 22)) ((x7Perm ^ k) p) =
      (x7Perm ^ k) ((g.1 : Equiv.Perm (Fin 22)) p) := by
  have hcomm : m22x7 * g.1 = g.1 * m22x7 :=
    Subgroup.mem_centralizer_iff.mp g.2 m22x7 (Subgroup.mem_zpowers m22x7)
  have hcomm' : Commute (g.1 : Equiv.Perm (Fin 22)) x7Perm := by
    rw [← m22x7_val]
    exact (congrArg Subtype.val hcomm).symm
  have hpow : (g.1 : Equiv.Perm (Fin 22)) * x7Perm ^ k =
      x7Perm ^ k * (g.1 : Equiv.Perm (Fin 22)) :=
    hcomm'.pow_right k
  exact Equiv.Perm.ext_iff.mp hpow p

private theorem m22x7_orb1 : (x7Perm ^ 3) 0 = 1 := by decide +kernel
private theorem m22x7_orb2 : (x7Perm ^ 6) 0 = 2 := by decide +kernel
private theorem m22x7_orb3 : (x7Perm ^ 1) 0 = 3 := by decide +kernel
private theorem m22x7_orb4 : (x7Perm ^ 5) 0 = 4 := by decide +kernel
private theorem m22x7_fix8 : (x7Perm ^ 1) 8 = 8 := by decide +kernel

private theorem stabilizer_C7_zero_eq_bot : stabilizer C7 (0 : Fin 22) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have h0 : (g.1 : Equiv.Perm (Fin 22)) 0 = 0 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 22)) 1 = 1 := by
    rw [← m22x7_orb1, comm_m22x7_pow g 3 0, h0, m22x7_orb1]
  have h2 : (g.1 : Equiv.Perm (Fin 22)) 2 = 2 := by
    rw [← m22x7_orb2, comm_m22x7_pow g 6 0, h0, m22x7_orb2]
  have h3 : (g.1 : Equiv.Perm (Fin 22)) 3 = 3 := by
    rw [← m22x7_orb3, comm_m22x7_pow g 1 0, h0, m22x7_orb3]
  have h4 : (g.1 : Equiv.Perm (Fin 22)) 4 = 4 := by
    rw [← m22x7_orb4, comm_m22x7_pow g 5 0, h0, m22x7_orb4]
  exact Subtype.ext (eq_one_of_fix_five g.1 h0 h1 h2 h3 h4)

private theorem not_mem_orbit_C7_eight : (8 : Fin 22) ∉ orbit C7 (0 : Fin 22) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 22)) 0 = 8 := hg
  have h3 : (g.1 : Equiv.Perm (Fin 22)) 3 = 8 := by
    rw [← m22x7_orb3, comm_m22x7_pow g 1 0, h0, m22x7_fix8]
  have heq : (3 : Fin 22) = 0 := (g.1 : Equiv.Perm (Fin 22)).injective (h3.trans h0.symm)
  exact (by decide : (3 : Fin 22) ≠ 0) heq

private abbrev v7_5 : NativeSporadic.M22 :=
  g6 * g9⁻¹ * g4 * g9⁻¹ * g6 * g2⁻¹ * g3⁻¹ * g2 * g1 * g2

private abbrev v7_5Perm : Equiv.Perm (Fin 22) :=
  g6Perm * g9Perm⁻¹ * g4Perm * g9Perm⁻¹ * g6Perm * g2Perm⁻¹ * g3Perm⁻¹ * g2Perm * g1Perm * g2Perm

private theorem v7_5_val : (v7_5 : Equiv.Perm (Fin 22)) = v7_5Perm := by
  change (g6 : Equiv.Perm (Fin 22)) * (g9 : Equiv.Perm (Fin 22))⁻¹ *
    (g4 : Equiv.Perm (Fin 22)) * (g9 : Equiv.Perm (Fin 22))⁻¹ *
    (g6 : Equiv.Perm (Fin 22)) * (g2 : Equiv.Perm (Fin 22))⁻¹ *
    (g3 : Equiv.Perm (Fin 22))⁻¹ * (g2 : Equiv.Perm (Fin 22)) *
    (g1 : Equiv.Perm (Fin 22)) * (g2 : Equiv.Perm (Fin 22)) = v7_5Perm
  rw [g1_val, g2_val, g3_val, g4_val, g6_val, g9_val]

private theorem not_mem_orbit_C7_five : (5 : Fin 22) ∉ orbit C7 (0 : Fin 22) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 22)) 0 = 5 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 22)) 1 = 21 := by
    rw [← m22x7_orb1, comm_m22x7_pow g 3 0, h0]; decide +kernel
  have h2 : (g.1 : Equiv.Perm (Fin 22)) 2 = 12 := by
    rw [← m22x7_orb2, comm_m22x7_pow g 6 0, h0]; decide +kernel
  have h3 : (g.1 : Equiv.Perm (Fin 22)) 3 = 17 := by
    rw [← m22x7_orb3, comm_m22x7_pow g 1 0, h0]; decide +kernel
  have h4 : (g.1 : Equiv.Perm (Fin 22)) 4 = 11 := by
    rw [← m22x7_orb4, comm_m22x7_pow g 5 0, h0]; decide +kernel
  obtain ⟨w, hw_def⟩ : ∃ w : NativeSporadic.M22, w = v7_5 * g.1 * g6 := ⟨_, rfl⟩
  have hw_apply : ∀ p : Fin 22,
      (w : Equiv.Perm (Fin 22)) p = v7_5Perm ((g.1 : Equiv.Perm (Fin 22)) (g6Perm p)) := by
    intro p
    rw [hw_def, Subgroup.coe_mul, Subgroup.coe_mul, v7_5_val, g6_val, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply]
  have hw0 : (w : Equiv.Perm (Fin 22)) 0 = 0 := by
    have hg6 : g6Perm 0 = 0 := by decide +kernel
    rw [hw_apply, hg6, h0]; decide +kernel
  have hw1 : (w : Equiv.Perm (Fin 22)) 1 = 1 := by
    have hg6 : g6Perm 1 = 1 := by decide +kernel
    rw [hw_apply, hg6, h1]; decide +kernel
  have hw2 : (w : Equiv.Perm (Fin 22)) 2 = 2 := by
    have hg6 : g6Perm 2 = 2 := by decide +kernel
    rw [hw_apply, hg6, h2]; decide +kernel
  have hw3 : (w : Equiv.Perm (Fin 22)) 3 = 3 := by
    have hg6 : g6Perm 3 = 4 := by decide +kernel
    rw [hw_apply, hg6, h4]; decide +kernel
  have hw4 : (w : Equiv.Perm (Fin 22)) 4 = 9 := by
    have hg6 : g6Perm 4 = 3 := by decide +kernel
    rw [hw_apply, hg6, h3]; decide +kernel
  have himg := img_four_of_fix_four w hw0 hw1 hw2 hw3
  rw [hw4] at himg
  rcases himg with h | h | h <;> exact absurd h (by decide)

private abbrev v7_6 : NativeSporadic.M22 :=
  g8 * g6 * g5 * g2⁻¹ * g1⁻¹ * g3

private abbrev v7_6Perm : Equiv.Perm (Fin 22) :=
  g8Perm * g6Perm * g5Perm * g2Perm⁻¹ * g1Perm⁻¹ * g3Perm

private theorem v7_6_val : (v7_6 : Equiv.Perm (Fin 22)) = v7_6Perm := by
  change (g8 : Equiv.Perm (Fin 22)) * (g6 : Equiv.Perm (Fin 22)) *
    (g5 : Equiv.Perm (Fin 22)) * (g2 : Equiv.Perm (Fin 22))⁻¹ *
    (g1 : Equiv.Perm (Fin 22))⁻¹ * (g3 : Equiv.Perm (Fin 22)) = v7_6Perm
  rw [g1_val, g2_val, g3_val, g5_val, g6_val, g8_val]

private theorem not_mem_orbit_C7_six : (6 : Fin 22) ∉ orbit C7 (0 : Fin 22) := by
  rintro ⟨g, hg⟩
  have h0 : (g.1 : Equiv.Perm (Fin 22)) 0 = 6 := hg
  have h1 : (g.1 : Equiv.Perm (Fin 22)) 1 = 7 := by
    rw [← m22x7_orb1, comm_m22x7_pow g 3 0, h0]; decide +kernel
  have h2 : (g.1 : Equiv.Perm (Fin 22)) 2 = 14 := by
    rw [← m22x7_orb2, comm_m22x7_pow g 6 0, h0]; decide +kernel
  have h3 : (g.1 : Equiv.Perm (Fin 22)) 3 = 10 := by
    rw [← m22x7_orb3, comm_m22x7_pow g 1 0, h0]; decide +kernel
  have h4 : (g.1 : Equiv.Perm (Fin 22)) 4 = 18 := by
    rw [← m22x7_orb4, comm_m22x7_pow g 5 0, h0]; decide +kernel
  obtain ⟨w, hw_def⟩ : ∃ w : NativeSporadic.M22, w = v7_6 * g.1 := ⟨_, rfl⟩
  have hw_apply : ∀ p : Fin 22,
      (w : Equiv.Perm (Fin 22)) p = v7_6Perm ((g.1 : Equiv.Perm (Fin 22)) p) := by
    intro p
    rw [hw_def, Subgroup.coe_mul, v7_6_val, Equiv.Perm.mul_apply]
  have hw0 : (w : Equiv.Perm (Fin 22)) 0 = 0 := by
    rw [hw_apply, h0]; decide +kernel
  have hw1 : (w : Equiv.Perm (Fin 22)) 1 = 1 := by
    rw [hw_apply, h1]; decide +kernel
  have hw2 : (w : Equiv.Perm (Fin 22)) 2 = 2 := by
    rw [hw_apply, h2]; decide +kernel
  have hw3 : (w : Equiv.Perm (Fin 22)) 3 = 3 := by
    rw [hw_apply, h3]; decide +kernel
  have hw4 : (w : Equiv.Perm (Fin 22)) 4 = 18 := by
    rw [hw_apply, h4]; decide +kernel
  have himg := img_four_of_fix_four w hw0 hw1 hw2 hw3
  rw [hw4] at himg
  rcases himg with h | h | h <;> exact absurd h (by decide)

private theorem mem_x7_pow_of_mem_C7 (k : ℕ) {p : Fin 22} (hp : p ∈ orbit C7 (0 : Fin 22)) :
    (x7Perm ^ k) p ∈ orbit C7 (0 : Fin 22) := by
  obtain ⟨g, hg⟩ := hp
  have h0 : (g.1 : Equiv.Perm (Fin 22)) 0 = p := hg
  have hx_C7 : m22x7 ^ k ∈ C7 := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.refl m22x7).zpow_left m |>.pow_right k
  refine ⟨⟨m22x7 ^ k, hx_C7⟩ * g, ?_⟩
  change ((m22x7 ^ k : NativeSporadic.M22) : Equiv.Perm (Fin 22)) ((g.1 : Equiv.Perm (Fin 22)) 0) =
    (x7Perm ^ k) p
  rw [Subgroup.coe_pow, m22x7_val, h0]

private theorem mem_orb0_of_mem_orbit_C7 {p : Fin 22} (hp : p ∈ orbit C7 (0 : Fin 22)) :
    p ∈ ([0, 3, 16, 1, 15, 4, 2] : List (Fin 22)) := by
  by_contra hnot
  have hpow : ∃ k : Fin 7, (x7Perm ^ k.val) p = 5 ∨ (x7Perm ^ k.val) p = 6 ∨
      (x7Perm ^ k.val) p = 8 := by
    revert hnot
    fin_cases p <;> decide
  obtain ⟨k, h5 | h6 | h8⟩ := hpow
  · exact not_mem_orbit_C7_five (h5 ▸ mem_x7_pow_of_mem_C7 k.val hp)
  · exact not_mem_orbit_C7_six (h6 ▸ mem_x7_pow_of_mem_C7 k.val hp)
  · exact not_mem_orbit_C7_eight (h8 ▸ mem_x7_pow_of_mem_C7 k.val hp)

private theorem card_C7_eq : Nat.card C7 = 7 := by
  have hstab : Nat.card (stabilizer C7 (0 : Fin 22)) = 1 := by
    rw [stabilizer_C7_zero_eq_bot, Subgroup.card_bot]
  have hcard_eq : Nat.card C7 = Nat.card (orbit C7 (0 : Fin 22)) := by
    have h := (stabilizer C7 (0 : Fin 22)).index_mul_card
    rw [hstab, mul_one, index_stabilizer C7 (0 : Fin 22), ← Nat.card_coe_set_eq] at h
    exact h.symm
  let emb : orbit C7 (0 : Fin 22) → {p : Fin 22 // p ∈ ([0, 3, 16, 1, 15, 4, 2] : List (Fin 22))} :=
    fun x => ⟨x.1, mem_orb0_of_mem_orbit_C7 x.2⟩
  have hemb : Function.Injective emb :=
    fun x y h => Subtype.ext (congrArg
      (fun z : {p : Fin 22 // p ∈ ([0, 3, 16, 1, 15, 4, 2] : List (Fin 22))} => z.1) h)
  have h7 : Nat.card {p : Fin 22 // p ∈ ([0, 3, 16, 1, 15, 4, 2] : List (Fin 22))} = 7 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hle : Nat.card C7 ≤ 7 :=
    (hcard_eq.trans_le (Nat.card_le_card_of_injective emb hemb)).trans h7.le
  have hP_le_C : P7 ≤ C7 := by
    intro y hy z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    simp only [← zpow_add, add_comm]
  have hdvd7 : 7 ∣ Nat.card C7 := by
    rw [← card_P7]
    exact Subgroup.card_dvd_of_le hP_le_C
  have hpos : 0 < Nat.card C7 := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd7
  have hk1 : k = 1 := by omega
  subst hk1
  omega

private abbrev u7_0 : NativeSporadic.M22 :=
  g9 * g6 * g2⁻¹ * g9⁻¹ * g8 * g2

private abbrev u7_0Perm : Equiv.Perm (Fin 22) :=
  g9Perm * g6Perm * g2Perm⁻¹ * g9Perm⁻¹ * g8Perm * g2Perm

private theorem u7_0_val : (u7_0 : Equiv.Perm (Fin 22)) = u7_0Perm := by
  change (g9 : Equiv.Perm (Fin 22)) * (g6 : Equiv.Perm (Fin 22)) *
    (g2 : Equiv.Perm (Fin 22))⁻¹ * (g9 : Equiv.Perm (Fin 22))⁻¹ *
    (g8 : Equiv.Perm (Fin 22)) * (g2 : Equiv.Perm (Fin 22)) = u7_0Perm
  rw [g2_val, g6_val, g8_val, g9_val]

private abbrev vN_5 : NativeSporadic.M22 :=
  g8⁻¹ * g9 * g4 * g8 * g2 * g3 * g1 * g2

private abbrev vN_5Perm : Equiv.Perm (Fin 22) :=
  g8Perm⁻¹ * g9Perm * g4Perm * g8Perm * g2Perm * g3Perm * g1Perm * g2Perm

private theorem vN_5_val : (vN_5 : Equiv.Perm (Fin 22)) = vN_5Perm := by
  change (g8 : Equiv.Perm (Fin 22))⁻¹ * (g9 : Equiv.Perm (Fin 22)) *
    (g4 : Equiv.Perm (Fin 22)) * (g8 : Equiv.Perm (Fin 22)) *
    (g2 : Equiv.Perm (Fin 22)) * (g3 : Equiv.Perm (Fin 22)) *
    (g1 : Equiv.Perm (Fin 22)) * (g2 : Equiv.Perm (Fin 22)) = vN_5Perm
  rw [g1_val, g2_val, g3_val, g4_val, g8_val, g9_val]

private abbrev vN_6 : NativeSporadic.M22 :=
  g6 * g8 * g4 * g5⁻¹ * g3 * g5⁻¹ * g1⁻¹ * g3

private abbrev vN_6Perm : Equiv.Perm (Fin 22) :=
  g6Perm * g8Perm * g4Perm * g5Perm⁻¹ * g3Perm * g5Perm⁻¹ * g1Perm⁻¹ * g3Perm

private theorem vN_6_val : (vN_6 : Equiv.Perm (Fin 22)) = vN_6Perm := by
  change (g6 : Equiv.Perm (Fin 22)) * (g8 : Equiv.Perm (Fin 22)) *
    (g4 : Equiv.Perm (Fin 22)) * (g5 : Equiv.Perm (Fin 22))⁻¹ *
    (g3 : Equiv.Perm (Fin 22)) * (g5 : Equiv.Perm (Fin 22))⁻¹ *
    (g1 : Equiv.Perm (Fin 22))⁻¹ * (g3 : Equiv.Perm (Fin 22)) = vN_6Perm
  rw [g1_val, g3_val, g4_val, g5_val, g6_val, g8_val]

private theorem not_exists_inv_conj_m22x7 (h : NativeSporadic.M22)
    (hconj : (h : Equiv.Perm (Fin 22)) * x7Perm = x7Perm ^ 6 * (h : Equiv.Perm (Fin 22))) :
    False := by
  have hpow : ∀ k : ℕ, (h : Equiv.Perm (Fin 22)) * x7Perm ^ k =
      (x7Perm ^ 6) ^ k * (h : Equiv.Perm (Fin 22)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hconj, ← mul_assoc, ← pow_succ]
  have hpow_pt : ∀ (k : ℕ) (p : Fin 22),
      (h : Equiv.Perm (Fin 22)) ((x7Perm ^ k) p) =
        (x7Perm ^ (6 * k)) ((h : Equiv.Perm (Fin 22)) p) := by
    intro k p
    rw [pow_mul]
    exact Equiv.Perm.ext_iff.mp (hpow k) p
  have hex_k : ∃ k : Fin 7, (x7Perm ^ k.val) ((h : Equiv.Perm (Fin 22)) 0) = 8 ∨
      (x7Perm ^ k.val) ((h : Equiv.Perm (Fin 22)) 0) = 0 ∨
      (x7Perm ^ k.val) ((h : Equiv.Perm (Fin 22)) 0) = 5 ∨
      (x7Perm ^ k.val) ((h : Equiv.Perm (Fin 22)) 0) = 6 := by
    generalize (h : Equiv.Perm (Fin 22)) 0 = q
    fin_cases q <;> decide
  obtain ⟨k, hk⟩ := hex_k
  obtain ⟨h', hh'_def⟩ : ∃ h' : NativeSporadic.M22, h' = m22x7 ^ k.val * h := ⟨_, rfl⟩
  have hh'_val : (h' : Equiv.Perm (Fin 22)) = x7Perm ^ k.val * (h : Equiv.Perm (Fin 22)) := by
    rw [hh'_def, Subgroup.coe_mul, Subgroup.coe_pow, m22x7_val]
  have hh'_pt : ∀ (m : ℕ) (p : Fin 22),
      (h' : Equiv.Perm (Fin 22)) ((x7Perm ^ m) p) =
        (x7Perm ^ (6 * m)) ((h' : Equiv.Perm (Fin 22)) p) := by
    intro m p
    rw [hh'_val, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hpow_pt m p]
    exact Equiv.Perm.ext_iff.mp ((Commute.refl x7Perm).pow_left k.val |>.pow_right (6 * m)) _
  have hh'0_eq : (x7Perm ^ k.val) ((h : Equiv.Perm (Fin 22)) 0) = (h' : Equiv.Perm (Fin 22)) 0 := by
    rw [hh'_val, Equiv.Perm.mul_apply]
  rcases hk with h8 | h0 | h5 | h6
  · rw [hh'0_eq] at h8
    have h3 : (h' : Equiv.Perm (Fin 22)) 3 = 8 := by
      rw [← m22x7_orb3, hh'_pt 1 0, h8]; decide +kernel
    have heq : (3 : Fin 22) = 0 := (h' : Equiv.Perm (Fin 22)).injective (h3.trans h8.symm)
    exact (by decide : (3 : Fin 22) ≠ 0) heq
  · rw [hh'0_eq] at h0
    have h1 : (h' : Equiv.Perm (Fin 22)) 1 = 15 := by
      rw [← m22x7_orb1, hh'_pt 3 0, h0]; decide +kernel
    have h2 : (h' : Equiv.Perm (Fin 22)) 2 = 3 := by
      rw [← m22x7_orb2, hh'_pt 6 0, h0]; decide +kernel
    have h3 : (h' : Equiv.Perm (Fin 22)) 3 = 2 := by
      rw [← m22x7_orb3, hh'_pt 1 0, h0]; decide +kernel
    have h4 : (h' : Equiv.Perm (Fin 22)) 4 = 16 := by
      rw [← m22x7_orb4, hh'_pt 5 0, h0]; decide +kernel
    obtain ⟨w, hw_def⟩ : ∃ w : NativeSporadic.M22, w = u7_0 * h' := ⟨_, rfl⟩
    have hw_apply : ∀ p : Fin 22,
        (w : Equiv.Perm (Fin 22)) p = u7_0Perm ((h' : Equiv.Perm (Fin 22)) p) := by
      intro p
      rw [hw_def, Subgroup.coe_mul, u7_0_val, Equiv.Perm.mul_apply]
    have hw0 : (w : Equiv.Perm (Fin 22)) 0 = 0 := by
      rw [hw_apply, h0]; decide +kernel
    have hw1 : (w : Equiv.Perm (Fin 22)) 1 = 1 := by
      rw [hw_apply, h1]; decide +kernel
    have hw2 : (w : Equiv.Perm (Fin 22)) 2 = 2 := by
      rw [hw_apply, h2]; decide +kernel
    have hw3 : (w : Equiv.Perm (Fin 22)) 3 = 3 := by
      rw [hw_apply, h3]; decide +kernel
    have hw4 : (w : Equiv.Perm (Fin 22)) 4 = 4 := by
      rw [hw_apply, h4]; decide +kernel
    have hw_one : w = 1 := eq_one_of_fix_five w hw0 hw1 hw2 hw3 hw4
    have hw8 : u7_0Perm ((h' : Equiv.Perm (Fin 22)) 8) = 8 := by
      rw [← hw_apply 8, hw_one]; rfl
    have hu10 : u7_0Perm 10 = 8 := by decide +kernel
    have hh'8 : (h' : Equiv.Perm (Fin 22)) 8 = 10 :=
      u7_0Perm.injective (hw8.trans hu10.symm)
    have hpt8 := hh'_pt 1 8
    rw [m22x7_fix8, hh'8] at hpt8
    exact (by decide +kernel : (10 : Fin 22) ≠ (x7Perm ^ (6 * 1)) 10) hpt8
  · rw [hh'0_eq] at h5
    have h1 : (h' : Equiv.Perm (Fin 22)) 1 = 13 := by
      rw [← m22x7_orb1, hh'_pt 3 0, h5]; decide +kernel
    have h2 : (h' : Equiv.Perm (Fin 22)) 2 = 17 := by
      rw [← m22x7_orb2, hh'_pt 6 0, h5]; decide +kernel
    have h3 : (h' : Equiv.Perm (Fin 22)) 3 = 12 := by
      rw [← m22x7_orb3, hh'_pt 1 0, h5]; decide +kernel
    have h4 : (h' : Equiv.Perm (Fin 22)) 4 = 19 := by
      rw [← m22x7_orb4, hh'_pt 5 0, h5]; decide +kernel
    obtain ⟨w, hw_def⟩ : ∃ w : NativeSporadic.M22, w = vN_5 * h' := ⟨_, rfl⟩
    have hw_apply : ∀ p : Fin 22,
        (w : Equiv.Perm (Fin 22)) p = vN_5Perm ((h' : Equiv.Perm (Fin 22)) p) := by
      intro p
      rw [hw_def, Subgroup.coe_mul, vN_5_val, Equiv.Perm.mul_apply]
    have hw0 : (w : Equiv.Perm (Fin 22)) 0 = 0 := by
      rw [hw_apply, h5]; decide +kernel
    have hw1 : (w : Equiv.Perm (Fin 22)) 1 = 1 := by
      rw [hw_apply, h1]; decide +kernel
    have hw2 : (w : Equiv.Perm (Fin 22)) 2 = 2 := by
      rw [hw_apply, h2]; decide +kernel
    have hw3 : (w : Equiv.Perm (Fin 22)) 3 = 3 := by
      rw [hw_apply, h3]; decide +kernel
    have hw4 : (w : Equiv.Perm (Fin 22)) 4 = 19 := by
      rw [hw_apply, h4]; decide +kernel
    have himg := img_four_of_fix_four w hw0 hw1 hw2 hw3
    rw [hw4] at himg
    rcases himg with h | h | h <;> exact absurd h (by decide)
  · rw [hh'0_eq] at h6
    have h1 : (h' : Equiv.Perm (Fin 22)) 1 = 9 := by
      rw [← m22x7_orb1, hh'_pt 3 0, h6]; decide +kernel
    have h2 : (h' : Equiv.Perm (Fin 22)) 2 = 10 := by
      rw [← m22x7_orb2, hh'_pt 6 0, h6]; decide +kernel
    have h3 : (h' : Equiv.Perm (Fin 22)) 3 = 14 := by
      rw [← m22x7_orb3, hh'_pt 1 0, h6]; decide +kernel
    have h4 : (h' : Equiv.Perm (Fin 22)) 4 = 20 := by
      rw [← m22x7_orb4, hh'_pt 5 0, h6]; decide +kernel
    obtain ⟨w, hw_def⟩ : ∃ w : NativeSporadic.M22, w = vN_6 * h' := ⟨_, rfl⟩
    have hw_apply : ∀ p : Fin 22,
        (w : Equiv.Perm (Fin 22)) p = vN_6Perm ((h' : Equiv.Perm (Fin 22)) p) := by
      intro p
      rw [hw_def, Subgroup.coe_mul, vN_6_val, Equiv.Perm.mul_apply]
    have hw0 : (w : Equiv.Perm (Fin 22)) 0 = 0 := by
      rw [hw_apply, h6]; decide +kernel
    have hw1 : (w : Equiv.Perm (Fin 22)) 1 = 1 := by
      rw [hw_apply, h1]; decide +kernel
    have hw2 : (w : Equiv.Perm (Fin 22)) 2 = 2 := by
      rw [hw_apply, h2]; decide +kernel
    have hw3 : (w : Equiv.Perm (Fin 22)) 3 = 3 := by
      rw [hw_apply, h3]; decide +kernel
    have hw4 : (w : Equiv.Perm (Fin 22)) 4 = 18 := by
      rw [hw_apply, h4]; decide +kernel
    have himg := img_four_of_fix_four w hw0 hw1 hw2 hw3
    rw [hw4] at himg
    rcases himg with h | h | h <;> exact absurd h (by decide)

private theorem conj_pow_eq_self_of_sq_eq_one {G : Type*} [Group G] {g x : G} {r : ℕ}
    (hg : g ^ 2 = 1) (hc : g * x * g⁻¹ = x ^ r) : x = x ^ (r * r) := by
  have hmap := map_pow (MulAut.conj g) x r
  change g * x ^ r * g⁻¹ = (g * x * g⁻¹) ^ r at hmap
  have hgg : g * g = 1 := by rw [← sq, hg]
  have hginv : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hgg, inv_one]
  calc x = 1 * x * 1 := by rw [one_mul, mul_one]
    _ = (g * g) * x * (g⁻¹ * g⁻¹) := by rw [hgg, hginv]
    _ = g * (g * x * g⁻¹) * g⁻¹ := by simp only [mul_assoc]
    _ = g * x ^ r * g⁻¹ := by rw [hc]
    _ = (x ^ r) ^ r := by rw [hmap, hc]
    _ = x ^ (r * r) := (pow_mul x r r).symm

private theorem comm_of_conj_eq_self {G : Type*} [Group G] {g x : G}
    (hc : g * x * g⁻¹ = x) : x * g = g * x := by
  calc x * g = (g * x * g⁻¹) * g := by rw [hc]
    _ = g * x := by group

private theorem mul_eq_of_conj_eq {G : Type*} [Group G] {g x y : G}
    (hc : g * x * g⁻¹ = y) : g * x = y * g := by
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = y * g := by rw [hc]

private theorem exists_fin_pow_of_mem_zpowers {G : Type*} [Group G] {x y : G} {n : ℕ}
    (hn : 0 < n) (hord : orderOf x = n) (hy : y ∈ Subgroup.zpowers x) :
    ∃ r : Fin n, y = x ^ r.val := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hnonneg : 0 ≤ m % (n : ℤ) := Int.emod_nonneg m (by omega)
  have hlt : (m % (n : ℤ)).toNat < n := by
    have := Int.emod_lt_of_pos m (by omega : (0 : ℤ) < n)
    omega
  refine ⟨⟨(m % (n : ℤ)).toNat, hlt⟩, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg, ← hord, zpow_mod_orderOf]

private theorem rFin_eq_one_or_six : ∀ rFin : Fin 7,
    x7Perm 0 = (x7Perm ^ (rFin.val * rFin.val)) 0 → rFin = 1 ∨ rFin = 6 := by
  decide +kernel

private theorem dvd_21_of_dvd_42_of_not_two_dvd {d : ℕ} (h42 : d ∣ 42) (h2 : ¬ 2 ∣ d) :
    d ∣ 21 := by
  have hle : d ≤ 42 := Nat.le_of_dvd (by decide) h42
  have hcheck : ∀ n : Fin 43, n.val ∣ 42 → ¬ 2 ∣ n.val → n.val ∣ 21 := by decide
  exact hcheck ⟨d, by omega⟩ h42 h2

private theorem card_normalizer_P7_dvd :
    Nat.card (Subgroup.normalizer (P7 : Set NativeSporadic.M22)) ∣ 21 := by
  set N7 := Subgroup.normalizer (P7 : Set NativeSporadic.M22)
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h42 : Nat.card N7 ∣ 42 := by
    have h1 := card_normalizer_dvd_mul_totient P7 card_P7
    rw [card_C7_eq] at h1
    exact h1
  have hnot2 : ¬ 2 ∣ Nat.card N7 := by
    intro hdvd2
    obtain ⟨_⟩ : Nonempty (Fintype N7) := ⟨Fintype.ofFinite N7⟩
    have hdvd2' : 2 ∣ Fintype.card N7 := by rwa [← Nat.card_eq_fintype_card]
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card 2 hdvd2'
    have hg_sq : g.1 ^ 2 = 1 := by
      have h1 : g ^ 2 = 1 := by rw [← hg_ord, pow_orderOf_eq_one]
      exact congrArg Subtype.val h1
    have hconj_mem : g.1 * m22x7 * g.1⁻¹ ∈ P7 :=
      (g.2 m22x7).mp (Subgroup.mem_zpowers m22x7)
    obtain ⟨rFin, hconj_r⟩ :=
      exists_fin_pow_of_mem_zpowers (by decide) orderOf_m22x7 hconj_mem
    have hconj_perm : (g.1 : Equiv.Perm (Fin 22)) * x7Perm * (g.1 : Equiv.Perm (Fin 22))⁻¹ =
        x7Perm ^ rFin.val := by
      have := congrArg Subtype.val hconj_r
      change (g.1 : Equiv.Perm (Fin 22)) * (m22x7 : Equiv.Perm (Fin 22)) *
        (g.1 : Equiv.Perm (Fin 22))⁻¹ = (m22x7 : Equiv.Perm (Fin 22)) ^ rFin.val at this
      rwa [m22x7_val] at this
    have hg_sq_perm : (g.1 : Equiv.Perm (Fin 22)) ^ 2 = 1 := congrArg Subtype.val hg_sq
    have hconj2 : x7Perm = x7Perm ^ (rFin.val * rFin.val) :=
      conj_pow_eq_self_of_sq_eq_one hg_sq_perm hconj_perm
    have hpt0 : x7Perm 0 = (x7Perm ^ (rFin.val * rFin.val)) 0 :=
      congrArg (fun p : Equiv.Perm (Fin 22) => p 0) hconj2
    rcases rFin_eq_one_or_six rFin hpt0 with hr1 | hr6
    · have hr1_val : rFin.val = 1 := congrArg Fin.val hr1
      rw [hr1_val, pow_one] at hconj_r
      have hcomm_x7 : m22x7 * g.1 = g.1 * m22x7 := comm_of_conj_eq_self hconj_r
      have hg_C7 : g.1 ∈ C7 := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left hcomm_x7 n).eq
      let gC : C7 := ⟨g.1, hg_C7⟩
      have hord_gC : orderOf gC = 2 := by
        calc orderOf gC = orderOf (gC : NativeSporadic.M22) := (Subgroup.orderOf_coe gC).symm
          _ = orderOf (g : NativeSporadic.M22) := rfl
          _ = orderOf g := Subgroup.orderOf_coe g
          _ = 2 := hg_ord
      have hdvd_C7 : 2 ∣ Nat.card C7 := by
        rw [← hord_gC]
        exact orderOf_dvd_natCard gC
      rw [card_C7_eq] at hdvd_C7
      exact absurd hdvd_C7 (by decide)
    · apply not_exists_inv_conj_m22x7 g.1
      have hr6_val : rFin.val = 6 := congrArg Fin.val hr6
      rw [hr6_val] at hconj_perm
      exact mul_eq_of_conj_eq hconj_perm
  exact dvd_21_of_dvd_42_of_not_two_dvd h42 hnot2

private theorem not_exists_subgroup_of_sylow7 (H : Subgroup NativeSporadic.M22)
    {c : ℕ} (hcard : Nat.card H = c) (hdvd : 7 ∣ c)
    (hno : hasValidSylowNormalizer 7 21 c = false) : False := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hval := hasValidSylowNormalizer_of_dvd P7 card_P7
    (by rw [card_M22]; decide) card_normalizer_P7_dvd (by decide)
    (H := H) (by rwa [hcard])
  rw [hcard, hno] at hval
  exact Bool.noConfusion hval

private theorem not_exists_subgroup_index_11 (H : Subgroup NativeSporadic.M22) :
    H.index ≠ 11 := by
  intro hH_idx
  have hcard22 : Nat.card (Fin 22) = 22 := Nat.card_fin 22
  have : IsMultiplyPretransitive NativeSporadic.M22 (Fin 22) (1 + 1) :=
    isMultiplyPretransitive_two m22_hyp (by decide) (by decide)
  have hmem := mem_validOrbits (Γ := NativeSporadic.M22) (X := Fin 22) 1
    (by rw [hcard22]; decide) H (0 : Fin 22)
  rw [hH_idx, hcard22, card_M22] at hmem
  have hvo : validOrbits 1 22 443520 11 = [] := by decide
  rw [hvo] at hmem
  exact List.not_mem_nil hmem

end M22Proof

/-- Every proper subgroup of `M₂₂` has index at least `19`. -/
theorem index_ge_M22 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .M22) {H : Subgroup S} (hH : H ≠ ⊤) :
    19 ≤ H.index := by
  let e' : S ≃* NativeSporadic.M22 := e
  have hcard : Nat.card S = 443520 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  have h11 : 11 ≤ H.index :=
    prime_le_index_of_ne_top hH (by decide : Nat.Prime 11) (by rw [hcard]; decide)
  by_contra hlt19
  push Not at hlt19
  have hdvd : H.index ∣ 443520 := by
    rw [← hcard]
    exact Subgroup.index_dvd_card H
  set K := H.map (e' : S →* NativeSporadic.M22)
  have hK_idx : K.index = H.index := Subgroup.index_map_equiv H e'
  have hK_mul : K.index * Nat.card K = 443520 := by
    rw [← CFSG.Sporadic.Mathieu.card_M22]
    exact K.index_mul_card
  rcases (by omega :
      H.index = 11 ∨ H.index = 12 ∨ H.index = 13 ∨ H.index = 14 ∨
      H.index = 15 ∨ H.index = 16 ∨ H.index = 17 ∨ H.index = 18) with
    h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18
  · exact M22Proof.not_exists_subgroup_index_11 K (hK_idx.trans h11)
  · rw [hK_idx, h12] at hK_mul
    exact M22Proof.not_exists_subgroup_of_sylow7 K (c := 36960) (by omega) (by decide) (by decide)
  · rw [h13] at hdvd; exact absurd hdvd (by decide)
  · rw [hK_idx, h14] at hK_mul
    exact M22Proof.not_exists_subgroup_of_sylow11 K (c := 31680) (by omega) (by decide) (by decide)
  · rw [hK_idx, h15] at hK_mul
    exact M22Proof.not_exists_subgroup_of_sylow11 K (c := 29568) (by omega) (by decide) (by decide)
  · rw [hK_idx, h16] at hK_mul
    exact M22Proof.not_exists_subgroup_of_sylow7 K (c := 27720) (by omega) (by decide) (by decide)
  · rw [h17] at hdvd; exact absurd hdvd (by decide)
  · rw [hK_idx, h18] at hK_mul
    exact M22Proof.not_exists_subgroup_of_sylow11 K (c := 24640) (by omega) (by decide) (by decide)

/-- Maróti's theorem for primitive almost simple groups with socle `M₂₂`. -/
theorem sporadicCase_M22 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .M22)) :
    AlmostSimpleConclusion G := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hAut : Nat.card (MulAut S) ≤ 2 * 443520 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.Sporadic.Schreier.m22_mulAut_card.trans
      (Nat.mul_le_mul_left 2 CFSG.Sporadic.Mathieu.card_M22.le)
  have hG_le : Nat.card G ≤ 887040 := hS.card_le_card_mulAut.trans hAut
  obtain ⟨H, hH_ne, hH_idx⟩ := hS.exists_proper_subgroup_index_eq
  have hn19 : 19 ≤ Nat.card α := hH_idx ▸ index_ge_M22 e hH_ne
  right; right
  exact hG_le.trans ((by decide : 887040 ≤ bound 19).trans (bound_mono hn19))

/-! ### `M₁₂` -/

namespace M12Proof

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native CFSG.Sporadic.Th

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

private theorem not_exists_subgroup_index_11 (H : Subgroup NativeSporadic.M12) :
    H.index ≠ 11 := by
  intro hH_idx
  have hcard12 : Nat.card (Fin 12) = 12 := Nat.card_fin 12
  have : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) (3 + 1) :=
    isMultiplyPretransitive_M12_four
  have hmem0 := mem_validOrbits (Γ := NativeSporadic.M12) (X := Fin 12) 3
    (by rw [hcard12]; decide) H (0 : Fin 12)
  rw [hH_idx, hcard12, card_M12] at hmem0
  have hvo0 : validOrbits 3 12 95040 11 = [12] := by decide
  rw [hvo0, List.mem_singleton] at hmem0
  set S₀ := stabilizer NativeSporadic.M12 (0 : Fin 12)
  set X₀ := SubMulAction.ofStabilizer NativeSporadic.M12 (0 : Fin 12)
  set H₀ := H.subgroupOf S₀
  have hX₀_card : Nat.card X₀ = 11 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq, hcard12]
  have h1 : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) 1 :=
    isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard12]; decide)
  have : IsPretransitive NativeSporadic.M12 (Fin 12) := is_one_pretransitive_iff.mp h1
  have hS₀_idx : S₀.index = 12 := by
    rw [index_stabilizer_of_transitive, hcard12]
  have hS₀_card : Nat.card S₀ = 7920 := by
    have h := S₀.index_mul_card
    rw [hS₀_idx, card_M12] at h
    omega
  have hrel_S₀ : S₀.relIndex H = 12 := by
    change (stabilizer H (0 : Fin 12)).index = 12
    rw [index_stabilizer H (0 : Fin 12), ← Nat.card_coe_set_eq, hmem0]
  have hH₀_idx : H₀.index = 11 := by
    change H.relIndex S₀ = 11
    have hinf : H.relIndex S₀ * S₀.index = S₀.relIndex H * H.index := by
      rw [← Subgroup.index_inf, ← Subgroup.index_inf, inf_comm]
    rw [hS₀_idx, hrel_S₀, hH_idx] at hinf
    omega
  have : IsMultiplyPretransitive S₀ X₀ (2 + 1) := by
    have : IsMultiplyPretransitive NativeSporadic.M12 (Fin 12) ((2 + 1) + 1) :=
      isMultiplyPretransitive_M12_four
    exact SubMulAction.ofStabilizer.isMultiplyPretransitive.mp this
  refine not_exists_subgroup_index_sub_one (Γ := NativeSporadic.M12) (X := Fin 12)
    (by rw [hcard12]; decide) H (by rw [hH_idx, hcard12]) (0 : Fin 12)
    (by rw [hmem0, hcard12]) ?_
  intro z
  have hmem1 := mem_validOrbits (Γ := S₀) (X := X₀) 2 (by rw [hX₀_card]; decide) H₀ z
  rw [hH₀_idx, hX₀_card, hS₀_card] at hmem1
  have hvo1 : validOrbits 2 11 7920 11 = [1, 10] := by decide
  rw [hvo1, List.mem_cons, List.mem_singleton] at hmem1
  simpa [hcard12] using hmem1

end M12Proof

/-- Every proper subgroup of `M₁₂` has index at least `12`. -/
theorem index_ge_M12 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .M12) {H : Subgroup S} (hH : H ≠ ⊤) :
    12 ≤ H.index := by
  have hcard : Nat.card S = 95040 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have h11 : 11 ≤ H.index :=
    prime_le_index_of_ne_top hH (by decide : Nat.Prime 11) (by rw [hcard]; decide)
  rcases eq_or_lt_of_le h11 with h11_eq | h12
  · exfalso
    let e' : S ≃* NativeSporadic.M12 := e
    have hH'_idx : (H.map (e' : S →* NativeSporadic.M12)).index = 11 := by
      rw [Subgroup.index_map_equiv, ← h11_eq]
    exact M12Proof.not_exists_subgroup_index_11 _ hH'_idx
  · omega

end Maroti
