module

public import Maroti.AlmostSimple.Basic
public import Maroti.Sporadic.AutBound
import Maroti.MinDegree.Basic
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Schreier.MathieuOddCoreM11
import CFSG.Sporadic.Bridge.M11
import CFSG.Certificates.Kernel.M11Local.Group

/-!
# Mathieu Groups: Orbit-Stabilizer Descent and `M₁₁`

This file develops the recursive orbit-stabilizer filter `validOrbits` for subgroups of a
multiply transitive permutation group and applies it to prove `sporadicCase_M11`.
-/

@[expose] public section

namespace Maroti

open CFSG.Blueprint MulAction

/-- Check whether a set of size `target` can have an orbit of size in `opts` (and, if that orbit
is smaller than `target`, a second disjoint orbit of size in `opts`). -/
def canPair (target : ℕ) (opts : List ℕ) : Bool :=
  target == 0 || opts.any fun s => s == target || (s < target && opts.any fun s2 => s + s2 ≤ target)

/-- Necessary arithmetic and sub-orbit conditions on the size `r` of an `H`-orbit on `X`, where
`Γ` of order `order` acts `(k + 1)`-transitively on `X` of size `m`, and `H ≤ Γ` has index `n`. -/
def validOrbits : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, m, order, n =>
    let cand := (List.range' 1 m).filter fun r => (order / n) % r == 0 && (r * n) % m == 0
    cand.filter fun r => r == m || cand.any fun r2 => r + r2 ≤ m
  | k + 1, m, order, n =>
    let cand := (List.range' 1 m).filter fun r =>
      (order / n) % r == 0 && (r * n) % m == 0 &&
      let sub := validOrbits k (m - 1) (order / m) ((r * n) / m)
      canPair (r - 1) sub && canPair (m - r) sub
    cand.filter fun r => r == m || cand.any fun r2 => r + r2 ≤ m

/-- If `P : Y → Prop` is invariant under `K`, any `K`-orbit of a point in `{y // P y}` has size
at most `Nat.card {y // P y}`, and if strictly smaller, there is a second disjoint `K`-orbit
inside `{y // P y}`. -/
private theorem canPair_of_invariant {K Y : Type*} [Group K] [Finite Y] [MulAction K Y]
    (P : Y → Prop) (hinv : ∀ (g : K) {y : Y}, P y → P (g • y))
    {opts : List ℕ} (hopts : ∀ y : Y, P y → Nat.card (orbit K y) ∈ opts) :
    canPair (Nat.card {y : Y // P y}) opts = true := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  unfold canPair
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases Nat.eq_zero_or_pos (Nat.card {y : Y // P y}) with h0 | hpos
  · exact Or.inl h0
  · right
    have hne : Nonempty {y : Y // P y} := (Nat.card_pos_iff.mp hpos).1
    obtain ⟨⟨y, hy⟩⟩ := hne
    have hsub : ∀ z ∈ orbit K y, P z := by
      rintro z ⟨g, rfl⟩
      exact hinv g hy
    let emb1 : orbit K y → {z : Y // P z} := fun z => ⟨z.1, hsub z.1 z.2⟩
    have hemb1 : Function.Injective emb1 :=
      fun a b h => Subtype.ext (congrArg (Subtype.val : {z : Y // P z} → Y) h)
    have hle : Nat.card (orbit K y) ≤ Nat.card {z : Y // P z} :=
      Nat.card_le_card_of_injective emb1 hemb1
    refine ⟨Nat.card (orbit K y), hopts y hy, ?_⟩
    rcases lt_or_eq_of_le hle with hlt | heq
    · right
      refine ⟨hlt, ?_⟩
      have hnot_surj : ¬ Function.Surjective emb1 := fun hsurj =>
        not_le_of_gt hlt (Nat.card_le_card_of_surjective emb1 hsurj)
      rw [Function.Surjective] at hnot_surj
      push Not at hnot_surj
      obtain ⟨⟨w, hw⟩, hnw⟩ := hnot_surj
      have hw_not_mem : w ∉ orbit K y := fun h => hnw ⟨w, h⟩ rfl
      have hdisj : Disjoint (orbit K y) (orbit K w) := by
        rw [Set.disjoint_left]
        intro z hzy hzw
        apply hw_not_mem
        rw [← orbit_eq_iff.mpr hzy, orbit_eq_iff.mpr hzw]
        exact mem_orbit_self w
      have hsubw : ∀ z ∈ orbit K w, P z := by
        rintro z ⟨g, rfl⟩
        exact hinv g hw
      let emb2 : orbit K y ⊕ orbit K w → {z : Y // P z} :=
        Sum.elim (fun z => ⟨z.1, hsub z.1 z.2⟩) (fun z => ⟨z.1, hsubw z.1 z.2⟩)
      have hemb2 : Function.Injective emb2 := by
        rintro (a | a) (b | b) h
        · exact congrArg Sum.inl (Subtype.ext (congrArg (Subtype.val : {z : Y // P z} → Y) h))
        · exfalso
          have hval : a.1 = b.1 := congrArg (Subtype.val : {z : Y // P z} → Y) h
          exact Set.disjoint_left.mp hdisj a.2 (hval ▸ b.2)
        · exfalso
          have hval : a.1 = b.1 := congrArg (Subtype.val : {z : Y // P z} → Y) h
          exact Set.disjoint_left.mp hdisj b.2 (hval.symm ▸ a.2)
        · exact congrArg Sum.inr (Subtype.ext (congrArg (Subtype.val : {z : Y // P z} → Y) h))
      have hsum := Nat.card_le_card_of_injective emb2 hemb2
      rw [Nat.card_sum] at hsum
      exact ⟨Nat.card (orbit K w), hopts w hw, hsum⟩
    · exact Or.inl heq

/-- Every orbit size of a subgroup `H ≤ Γ` in a `(k + 1)`-transitive action of `Γ` on `X` lies in
`validOrbits k (Nat.card X) (Nat.card Γ) H.index`. -/
theorem mem_validOrbits {Γ X : Type*} [Group Γ] [Finite Γ] [Finite X] [MulAction Γ X]
    (k : ℕ) [IsMultiplyPretransitive Γ X (k + 1)] (hk : k + 1 ≤ Nat.card X)
    (H : Subgroup Γ) (x : X) :
    Nat.card (orbit H x) ∈ validOrbits k (Nat.card X) (Nat.card Γ) H.index := by
  induction k generalizing Γ X with
  | zero =>
    have h1 : IsMultiplyPretransitive Γ X 1 := inferInstance
    have htr : IsPretransitive Γ X := is_one_pretransitive_iff.mp h1
    have hcand : ∀ y : X, Nat.card (orbit H y) ∈
        (List.range' 1 (Nat.card X)).filter fun r =>
          (Nat.card Γ / H.index) % r == 0 && (r * H.index) % Nat.card X == 0 := by
      intro y
      set r := Nat.card (orbit H y)
      have : Nonempty (orbit H y) := ⟨⟨y, mem_orbit_self y⟩⟩
      have hr_pos : 1 ≤ r := Nat.card_pos
      have hr_le : r ≤ Nat.card X :=
        Nat.card_le_card_of_injective Subtype.val Subtype.coe_injective
      have hr_eq : (stabilizer Γ y).relIndex H = r := by
        change (stabilizer H y).index = Nat.card (orbit H y)
        rw [index_stabilizer H y, Nat.card_coe_set_eq]
      have hH_idx_pos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hH_card : Nat.card Γ / H.index = Nat.card H :=
        Nat.div_eq_of_eq_mul_right hH_idx_pos H.index_mul_card.symm
      have hr_dvd : r ∣ Nat.card H := by
        rw [← hr_eq]
        exact Subgroup.relIndex_dvd_card (stabilizer Γ y) H
      have hidx_S : (stabilizer Γ y).index = Nat.card X :=
        index_stabilizer_of_transitive Γ y
      have hrel : r * H.index = Nat.card X * H.relIndex (stabilizer Γ y) := by
        rw [← hr_eq, ← hidx_S, ← Subgroup.index_inf, mul_comm (stabilizer Γ y).index,
          ← Subgroup.index_inf, inf_comm]
      rw [List.mem_filter, List.mem_range'_1]
      refine ⟨⟨hr_pos, by omega⟩, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, hH_card]
      exact ⟨Nat.mod_eq_zero_of_dvd hr_dvd, Nat.mod_eq_zero_of_dvd ⟨_, hrel⟩⟩
    have hpair := canPair_of_invariant (K := H) (Y := X) (fun _ => True) (fun _ _ _ => trivial)
      (fun y _ => hcand y)
    have hcard_true : Nat.card {y : X // True} = Nat.card X :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    rw [hcard_true] at hpair
    unfold validOrbits
    rw [List.mem_filter]
    refine ⟨hcand x, ?_⟩
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq]
    rcases eq_or_lt_of_le (Nat.card_le_card_of_injective (α := orbit H x) Subtype.val
      Subtype.coe_injective) with heq | hlt
    · exact Or.inl heq
    · right
      have hpair' := canPair_of_invariant (K := H) (Y := X) (fun z => z ∉ orbit H x)
        (fun g z hz hmem => hz (by
          obtain ⟨h, hh⟩ := hmem
          exact ⟨g⁻¹ * h, by simp [mul_smul, hh]⟩))
        (fun y _ => hcand y)
      have hcard_compl : Nat.card {z : X // z ∉ orbit H x} = Nat.card X - Nat.card (orbit H x) := by
        classical
        have : Fintype X := Fintype.ofFinite X
        have hsum : Nat.card (orbit H x) + Nat.card {z : X // z ∉ orbit H x} = Nat.card X := by
          rw [← Nat.card_sum]
          exact Nat.card_congr (Equiv.sumCompl (· ∈ orbit H x))
        omega
      rw [hcard_compl] at hpair'
      unfold canPair at hpair'
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hpair'
      rcases hpair' with h0 | ⟨s, ⟨hs, hrest⟩⟩
      · omega
      · refine ⟨s, hs, ?_⟩
        rcases hrest with rfl | ⟨_, s2, _, hs2⟩ <;> omega
  | succ k ih =>
    have h1 : IsMultiplyPretransitive Γ X 1 :=
      isMultiplyPretransitive_of_le (m := 1) (n := k + 2) (by omega) hk
    have htr : IsPretransitive Γ X := is_one_pretransitive_iff.mp h1
    have hcand : ∀ y : X, Nat.card (orbit H y) ∈
        (List.range' 1 (Nat.card X)).filter fun r =>
          (Nat.card Γ / H.index) % r == 0 && (r * H.index) % Nat.card X == 0 &&
          let sub := validOrbits k (Nat.card X - 1) (Nat.card Γ / Nat.card X)
            ((r * H.index) / Nat.card X)
          canPair (r - 1) sub && canPair (Nat.card X - r) sub := by
      intro y
      set r := Nat.card (orbit H y)
      have : Nonempty (orbit H y) := ⟨⟨y, mem_orbit_self y⟩⟩
      have hr_pos : 1 ≤ r := Nat.card_pos
      have hr_le : r ≤ Nat.card X :=
        Nat.card_le_card_of_injective Subtype.val Subtype.coe_injective
      set S_y := stabilizer Γ y
      set X_y := SubMulAction.ofStabilizer Γ y
      set H_y := H.subgroupOf S_y
      have hr_eq : S_y.relIndex H = r := by
        change (stabilizer H y).index = Nat.card (orbit H y)
        rw [index_stabilizer H y, Nat.card_coe_set_eq]
      have hH_idx_pos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hH_card : Nat.card Γ / H.index = Nat.card H :=
        Nat.div_eq_of_eq_mul_right hH_idx_pos H.index_mul_card.symm
      have hr_dvd : r ∣ Nat.card H := by
        rw [← hr_eq]
        exact Subgroup.relIndex_dvd_card S_y H
      have hidx_S : S_y.index = Nat.card X := index_stabilizer_of_transitive Γ y
      have hX_pos : 0 < Nat.card X := by omega
      have hS_card : Nat.card Γ / Nat.card X = Nat.card S_y := by
        have := S_y.index_mul_card
        rw [hidx_S] at this
        exact Nat.div_eq_of_eq_mul_right hX_pos this.symm
      have hrel : r * H.index = Nat.card X * H_y.index := by
        change r * H.index = Nat.card X * H.relIndex S_y
        rw [← hr_eq, ← hidx_S, ← Subgroup.index_inf, mul_comm S_y.index,
          ← Subgroup.index_inf, inf_comm]
      have hHy_idx : (r * H.index) / Nat.card X = H_y.index :=
        Nat.div_eq_of_eq_mul_right hX_pos hrel
      have hXy_card : Nat.card X_y = Nat.card X - 1 :=
        SubMulAction.nat_card_ofStabilizer_eq Γ y
      have hk' : k + 1 ≤ Nat.card X_y := by omega
      have : IsMultiplyPretransitive S_y X_y (k + 1) :=
        SubMulAction.ofStabilizer.isMultiplyPretransitive.mp inferInstance
      have hsub : ∀ z : X_y, Nat.card (orbit H_y z) ∈
          validOrbits k (Nat.card X - 1) (Nat.card Γ / Nat.card X)
            ((r * H.index) / Nat.card X) := by
        intro z
        rw [← hXy_card, hS_card, hHy_idx]
        exact ih hk' H_y z
      have hin_inv :
          ∀ (g : H_y) {z : X_y}, (z : X) ∈ orbit H y → ((g • z : X_y) : X) ∈ orbit H y := by
        rintro g z ⟨h, hh⟩
        refine ⟨⟨(g : Γ), g.2⟩ * h, ?_⟩
        change ((⟨(g : Γ), g.2⟩ * h : H) : Γ) • y = (g : Γ) • (z : X)
        have hh' : (h : Γ) • y = (z : X) := hh
        rw [Subgroup.coe_mul, mul_smul, hh']
      have hout_inv :
          ∀ (g : H_y) {z : X_y}, (z : X) ∉ orbit H y → ((g • z : X_y) : X) ∉ orbit H y := by
        rintro g z hz ⟨h, hh⟩
        apply hz
        refine ⟨⟨(g : Γ), g.2⟩⁻¹ * h, ?_⟩
        change ((⟨(g : Γ), g.2⟩⁻¹ * h : H) : Γ) • y = (z : X)
        have hh' : (h : Γ) • y = (g : Γ) • (z : X) := hh
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hh', inv_smul_smul]
      classical
      have hcard_in : Nat.card {z : X_y // (z : X) ∈ orbit H y} = r - 1 := by
        let e : {z : X_y // (z : X) ∈ orbit H y} ⊕ Unit ≃ orbit H y :=
          { toFun := Sum.elim (fun z => ⟨z.1.1, z.2⟩) (fun _ => ⟨y, mem_orbit_self y⟩)
            invFun := fun z =>
              if h : z.1 = y then Sum.inr () else Sum.inl ⟨⟨z.1, h⟩, z.2⟩
            left_inv := by
              rintro (⟨⟨z, hz⟩, hmem⟩ | ⟨⟩)
              · have hne : z ≠ y := hz
                simp [hne]
              · simp
            right_inv := by
              rintro ⟨z, hmem⟩
              by_cases hz : z = y <;> simp [hz] }
        have hsum := Nat.card_congr e
        have hunit : Nat.card Unit = 1 := Nat.card_unique
        rw [Nat.card_sum, hunit] at hsum
        have hr_def : Nat.card (orbit H y) = r := rfl
        omega
      have hcard_out : Nat.card {z : X_y // (z : X) ∉ orbit H y} = Nat.card X - r := by
        let e : orbit H y ⊕ {z : X_y // (z : X) ∉ orbit H y} ≃ X :=
          { toFun := Sum.elim Subtype.val (fun z => z.1.1)
            invFun := fun z =>
              if h : z ∈ orbit H y then Sum.inl ⟨z, h⟩
              else Sum.inr ⟨⟨z, fun hzy => h (hzy.symm ▸ mem_orbit_self y)⟩, h⟩
            left_inv := by
              rintro (⟨z, hz⟩ | ⟨⟨z, hne⟩, hz⟩) <;> simp [hz]
            right_inv := fun z => by
              by_cases hz : z ∈ orbit H y <;> simp [hz] }
        have hsum := Nat.card_congr e
        rw [Nat.card_sum] at hsum
        have hr_def : Nat.card (orbit H y) = r := rfl
        omega
      have hp_in := canPair_of_invariant (K := H_y) (Y := X_y) (fun z => (z : X) ∈ orbit H y)
        hin_inv (fun z _ => hsub z)
      rw [hcard_in] at hp_in
      have hp_out := canPair_of_invariant (K := H_y) (Y := X_y) (fun z => (z : X) ∉ orbit H y)
        hout_inv (fun z _ => hsub z)
      rw [hcard_out] at hp_out
      rw [List.mem_filter, List.mem_range'_1]
      refine ⟨⟨hr_pos, by omega⟩, ?_⟩
      dsimp only
      simp only [Bool.and_eq_true, beq_iff_eq, hH_card]
      exact ⟨⟨Nat.mod_eq_zero_of_dvd hr_dvd, Nat.mod_eq_zero_of_dvd ⟨_, hrel⟩⟩, hp_in, hp_out⟩
    unfold validOrbits
    rw [List.mem_filter]
    refine ⟨hcand x, ?_⟩
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq]
    rcases eq_or_lt_of_le (Nat.card_le_card_of_injective (α := orbit H x) Subtype.val
      Subtype.coe_injective) with heq | hlt
    · exact Or.inl heq
    · right
      have hpair' := canPair_of_invariant (K := H) (Y := X) (fun z => z ∉ orbit H x)
        (fun g z hz hmem => hz (by
          obtain ⟨h, hh⟩ := hmem
          exact ⟨g⁻¹ * h, by simp [mul_smul, hh]⟩))
        (fun y _ => hcand y)
      have hcard_compl : Nat.card {z : X // z ∉ orbit H x} = Nat.card X - Nat.card (orbit H x) := by
        classical
        have : Fintype X := Fintype.ofFinite X
        have hsum : Nat.card (orbit H x) + Nat.card {z : X // z ∉ orbit H x} = Nat.card X := by
          rw [← Nat.card_sum]
          exact Nat.card_congr (Equiv.sumCompl (· ∈ orbit H x))
        omega
      rw [hcard_compl] at hpair'
      unfold canPair at hpair'
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hpair'
      rcases hpair' with h0 | ⟨s, ⟨hs, hrest⟩⟩
      · omega
      · refine ⟨s, hs, ?_⟩
        rcases hrest with rfl | ⟨_, s2, _, hs2⟩ <;> omega

/-- If every `H`-orbit on `X` (`3 ≤ Nat.card X`) has size `1` or `Nat.card X - 1`, then `H` fixes
a point of `X`. -/
theorem exists_le_stabilizer_of_orbit_one_or_sub_one {Γ X : Type*} [Group Γ] [Finite X]
    [MulAction Γ X] (hX : 3 ≤ Nat.card X) (H : Subgroup Γ)
    (horb : ∀ x : X, Nat.card (orbit H x) = 1 ∨ Nat.card (orbit H x) = Nat.card X - 1) :
    ∃ y : X, H ≤ stabilizer Γ y := by
  have hX_pos : 0 < Nat.card X := by omega
  have hne : Nonempty X := (Nat.card_pos_iff.mp hX_pos).1
  obtain ⟨x⟩ := hne
  have hfix_of_one : ∀ y : X, Nat.card (orbit H y) = 1 → H ≤ stabilizer Γ y := by
    intro y hy1 g hg
    rw [mem_stabilizer_iff]
    have : Subsingleton (orbit H y) := Finite.card_le_one_iff_subsingleton.mp (by omega)
    let a : orbit H y := ⟨(⟨g, hg⟩ : H) • y, mem_orbit y (⟨g, hg⟩ : H)⟩
    let b : orbit H y := ⟨y, mem_orbit_self y⟩
    exact congrArg Subtype.val (Subsingleton.elim a b)
  rcases horb x with h1 | hsub
  · exact ⟨x, hfix_of_one x h1⟩
  · let emb : orbit H x → X := Subtype.val
    have hnot_surj : ¬ Function.Surjective emb := fun hsurj => by
      have := Nat.card_le_card_of_surjective emb hsurj
      omega
    rw [Function.Surjective] at hnot_surj
    push Not at hnot_surj
    obtain ⟨y, hy⟩ := hnot_surj
    have hy_not_mem : y ∉ orbit H x := fun h => hy ⟨y, h⟩ rfl
    have hdisj : Disjoint (orbit H x) (orbit H y) := by
      rw [Set.disjoint_left]
      intro z hzx hzy
      apply hy_not_mem
      rw [← orbit_eq_iff.mpr hzx, orbit_eq_iff.mpr hzy]
      exact mem_orbit_self y
    let emb2 : orbit H x ⊕ orbit H y → X := Sum.elim Subtype.val Subtype.val
    have hemb2 : Function.Injective emb2 := by
      rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · have hval : a.1 = b.1 := h
        exact absurd (hval ▸ b.2) (Set.disjoint_left.mp hdisj a.2)
      · have hval : a.1 = b.1 := h
        exact absurd (hval.symm ▸ a.2) (Set.disjoint_left.mp hdisj b.2)
      · exact congrArg Sum.inr (Subtype.ext h)
    have hsum := Nat.card_le_card_of_injective emb2 hemb2
    rw [Nat.card_sum, hsub] at hsum
    have hy1 : Nat.card (orbit H y) = 1 := by
      rcases horb y with h1 | h1 <;> omega
    exact ⟨y, hfix_of_one y hy1⟩

/-- If every subgroup `H ≤ Γ` of index `Nat.card X` fixes a point of `X`, then any transitive
action of `G ≃* Γ` on `α` (`Nat.card α = Nat.card X`) inherits `k`-transitivity from `X`. -/
theorem isMultiplyPretransitive_of_le_stabilizer {Γ X α : Type*} [Group Γ] [Finite Γ]
    [Finite X] [Nonempty X] [Finite α] [MulAction Γ X] [IsPretransitive Γ X]
    {G : Subgroup (Equiv.Perm α)} [IsPretransitive G α] (e : Γ ≃* G)
    (hcard : Nat.card α = Nat.card X)
    (hstab : ∀ H : Subgroup Γ, H.index = Nat.card X → ∃ y : X, H ≤ stabilizer Γ y)
    {k : ℕ} [IsMultiplyPretransitive Γ X k] :
    IsMultiplyPretransitive G α k := by
  have hX_pos : 0 < Nat.card X := Nat.card_pos
  have hα_pos : 0 < Nat.card α := by omega
  obtain ⟨x₀⟩ : Nonempty α := (Nat.card_pos_iff.mp hα_pos).1
  let H : Subgroup Γ := (stabilizer G x₀).comap e.toMonoidHom
  have hH_idx : H.index = Nat.card X := by
    rw [Subgroup.index_comap_of_surjective _ e.surjective, index_stabilizer_of_transitive G x₀,
      hcard]
  obtain ⟨y₀, hy₀⟩ := hstab H hH_idx
  have hSy_idx : (stabilizer Γ y₀).index = Nat.card X := index_stabilizer_of_transitive Γ y₀
  have hrel : H.relIndex (stabilizer Γ y₀) = 1 := by
    have h := Subgroup.relIndex_mul_index hy₀
    rw [hH_idx, hSy_idx] at h
    exact Nat.eq_of_mul_eq_mul_right hX_pos (h.trans (one_mul _).symm)
  have hH_eq : H = stabilizer Γ y₀ :=
    le_antisymm hy₀ (Subgroup.relIndex_eq_one.mp hrel)
  -- Construct an equivariant bijection `X ≃ α` along `e : Γ → G`
  have horbX : orbit Γ y₀ = Set.univ := orbit_eq_univ Γ y₀
  have horbα : orbit G x₀ = Set.univ := orbit_eq_univ G x₀
  let eX₀ : X ≃ orbit Γ y₀ :=
    { toFun := fun x => ⟨x, horbX.symm ▸ Set.mem_univ x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  let eX : X ≃ Γ ⧸ stabilizer Γ y₀ := eX₀.trans (orbitEquivQuotientStabilizer Γ y₀)
  let eQ : Γ ⧸ stabilizer Γ y₀ ≃ G ⧸ stabilizer G x₀ :=
    { toFun := Quotient.map' e fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        rw [← hH_eq, Subgroup.mem_comap, map_mul, map_inv] at hab
        exact hab
      invFun := Quotient.map' e.symm fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        rw [← hH_eq, Subgroup.mem_comap]
        simpa using hab
      left_inv := by
        rintro ⟨g⟩
        exact congrArg Quotient.mk'' (e.symm_apply_apply g)
      right_inv := by
        rintro ⟨g⟩
        exact congrArg Quotient.mk'' (e.apply_symm_apply g) }
  let eα₀ : α ≃ orbit G x₀ :=
    { toFun := fun x => ⟨x, horbα.symm ▸ Set.mem_univ x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  let eα : α ≃ G ⧸ stabilizer G x₀ := eα₀.trans (orbitEquivQuotientStabilizer G x₀)
  let f : X →ₑ[e.toMonoidHom] α :=
    { toFun := eα.symm ∘ eQ ∘ eX
      map_smul' := fun g x => by
        obtain ⟨k, rfl⟩ := exists_smul_eq Γ y₀ x
        have heX : ∀ m : Γ, eX (m • y₀) = (m : Γ ⧸ stabilizer Γ y₀) :=
          fun m => eX.apply_symm_apply (m : Γ ⧸ stabilizer Γ y₀)
        have heα : ∀ m : G, eα.symm (m : G ⧸ stabilizer G x₀) = m • x₀ := fun _ => rfl
        change eα.symm (eQ (eX (g • (k • y₀)))) = e g • eα.symm (eQ (eX (k • y₀)))
        rw [← mul_smul, heX, heX]
        change eα.symm (e (g * k) : G ⧸ stabilizer G x₀) =
          e g • eα.symm (e k : G ⧸ stabilizer G x₀)
        rw [heα, heα, map_mul, mul_smul] }
  have hf : Function.Bijective f := eα.symm.bijective.comp (eQ.bijective.comp eX.bijective)
  exact (IsPretransitive.of_embedding_congr e.surjective hf).mp inferInstance

/-- If `G` is almost simple with socle `S` and `Nat.card G ≤ Nat.card S`, then `G ≃* S`. -/
theorem mulEquiv_of_card_le {α : Type*} [Finite α] {G : Subgroup (Equiv.Perm α)} {S : Type*}
    [Group S] (hS : IsAlmostSimpleWith G S) (hle : Nat.card G ≤ Nat.card S) :
    Nonempty (G ≃* S) := by
  have : Finite S := hS.finite
  obtain ⟨T, hTG, -, -, -, -, ⟨eT⟩⟩ := hS
  have hcard_eq : Nat.card (T.subgroupOf G) = Nat.card S :=
    Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hTG).trans eT).toEquiv
  have hS_pos : 0 < Nat.card S := Nat.card_pos
  have hle' : Nat.card (T.subgroupOf G) ≤ Nat.card G :=
    Nat.card_le_card_of_injective Subtype.val Subtype.coe_injective
  have hG_eq : Nat.card G = Nat.card S := le_antisymm hle (hcard_eq ▸ hle')
  have hidx : (T.subgroupOf G).index = 1 := by
    have h := (T.subgroupOf G).index_mul_card
    rw [hcard_eq, hG_eq] at h
    exact Nat.eq_of_mul_eq_mul_right hS_pos (h.trans (one_mul _).symm)
  have heq : T.subgroupOf G = ⊤ := Subgroup.index_eq_one.mp hidx
  exact ⟨Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr heq.symm).trans ((Subgroup.subgroupOfEquivOfLe hTG).trans eT))⟩

/-- If `P ≤ G` has prime order `p`, then `|N_G(P)|` divides `|C_G(P)| * (p - 1)`. -/
theorem card_normalizer_dvd_mul_totient {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    {p : ℕ} [hp : Fact p.Prime] (hP : Nat.card P = p) :
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

/-- Check whether `hCard` has a divisor `d` divisible by `p` that divides `m` and satisfies
`(hCard / d) % p = 1`. -/
def hasValidSylowNormalizer (p m hCard : ℕ) : Bool :=
  (List.range' 1 m).any fun d =>
    d % p == 0 && m % d == 0 && hCard % d == 0 && (hCard / d) % p == 1

/-- If `P ≤ G` has prime order `p`, `p^2 ∤ |G|`, and `|N_G(P)| ∣ m`, then any subgroup `H ≤ G`
with `p ∣ |H|` satisfies `hasValidSylowNormalizer p m (Nat.card H) = true`. -/
theorem hasValidSylowNormalizer_of_dvd {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    {p m : ℕ} [hp : Fact p.Prime] (hP : Nat.card P = p) (hp2 : ¬ p ^ 2 ∣ Nat.card G)
    (hN : Nat.card (Subgroup.normalizer (P : Set G)) ∣ m) (hm_pos : 0 < m)
    {H : Subgroup G} (hpH : p ∣ Nat.card H) :
    hasValidSylowNormalizer p m (Nat.card H) = true := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have hp_gt1 : 1 < p := hp.out.one_lt
  have hle_eq :
      ∀ (R : Subgroup G) (S : Sylow p G), Nat.card R = p → R ≤ S → (S : Subgroup G) = R := by
    intro R S hR hRS
    obtain ⟨k, hk⟩ := S.2.exists_card_eq
    have hdvd0 : Nat.card R ∣ Nat.card (S : Subgroup G) := Subgroup.card_dvd_of_le hRS
    have hdvd1 : p ∣ p ^ k := by rwa [hR, hk] at hdvd0
    have hdvd2 : p ^ k ∣ Nat.card G := by
      rw [← hk]
      exact Subgroup.card_subgroup_dvd_card (S : Subgroup G)
    have hk_le : k ≤ 1 := by
      by_contra hlt
      push Not at hlt
      apply hp2
      exact (pow_dvd_pow p hlt).trans hdvd2
    have hk_pos : 1 ≤ k := by
      rcases k with _ | k
      · rw [pow_zero] at hdvd1
        exact absurd (Nat.le_of_dvd zero_lt_one hdvd1) (by omega)
      · omega
    have hk1 : k = 1 := le_antisymm hk_le hk_pos
    have hS_card : Nat.card (S : Subgroup G) = Nat.card R := by rw [hk, hk1, pow_one, hR]
    exact (Subgroup.eq_of_le_of_card_ge hRS hS_card.le).symm
  have hP_pgroup : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  obtain ⟨P_G, hP_le⟩ := hP_pgroup.exists_le_sylow
  have hPG_eq : (P_G : Subgroup G) = P := hle_eq P P_G hP hP_le
  have hpH' : p ∣ Fintype.card H := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hpH'
  let Q₀ : Subgroup G := Subgroup.zpowers (x : G)
  have hQ0_le_H : Q₀ ≤ H := by
    rw [Subgroup.zpowers_le]
    exact x.2
  have hQ0_card : Nat.card Q₀ = p := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_mk x.1 x.2, hx]
  have hQ0_pgroup : IsPGroup p Q₀ := IsPGroup.of_card (n := 1) (by rw [hQ0_card, pow_one])
  obtain ⟨P', hQ0_le⟩ := hQ0_pgroup.exists_le_sylow
  have hP'_eq : (P' : Subgroup G) = Q₀ := hle_eq Q₀ P' hQ0_card hQ0_le
  have hP'_le_H : (P' : Subgroup G) ≤ H := hP'_eq.symm ▸ hQ0_le_H
  let Q : Sylow p H := P'.subtype hP'_le_H
  have hnorm_Q : Subgroup.normalizer (Q : Set H) =
      (Subgroup.normalizer (P' : Set G)).subgroupOf H := by
    ext h
    rw [Subgroup.mem_subgroupOf, ← Sylow.smul_eq_iff_mem_normalizer,
      ← Sylow.smul_eq_iff_mem_normalizer]
    change h • P'.subtype hP'_le_H = P'.subtype hP'_le_H ↔ (h : G) • P' = P'
    rw [Sylow.smul_subtype]
    exact ⟨Sylow.subtype_injective, fun h' => by
      ext y
      change (y : G) ∈ ((h : G) • P' : Sylow p G) ↔ (y : G) ∈ P'
      rw [h']⟩
  obtain ⟨g, hg⟩ := exists_smul_eq G P' P_G
  have hnorm_conj : Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.normalizer (P' : Set G)) ≤
      Subgroup.normalizer (P : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← hPG_eq]
    change g * n * g⁻¹ ∈ Subgroup.normalizer (P_G : Set G)
    rw [← Sylow.smul_eq_iff_mem_normalizer, ← hg]
    have hn' : n • P' = P' := Sylow.smul_eq_iff_mem_normalizer.mpr hn
    change (g * n * g⁻¹) • g • P' = g • P'
    rw [mul_smul, mul_smul, inv_smul_smul, hn']
  set d := Nat.card (Subgroup.normalizer (Q : Set H))
  have hd_pos : 0 < d := Nat.card_pos
  have hp_dvd_d : p ∣ d := by
    have hQ_card : Nat.card (Q : Subgroup H) = p := by
      have : (Q : Subgroup H) = Q₀.subgroupOf H := by
        change (P' : Subgroup G).subgroupOf H = Q₀.subgroupOf H
        rw [hP'_eq]
      rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le_H).toEquiv, hQ0_card]
    rw [← hQ_card]
    exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have hd_dvd_N : d ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
    let f : (Subgroup.normalizer (P' : Set G)).subgroupOf H →* Subgroup.normalizer (P' : Set G) :=
      { toFun := fun n => ⟨n.1.1, n.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (Subtype.val : Subgroup.normalizer (P' : Set G) → G) h))
    have hd1 : d ∣ Nat.card (Subgroup.normalizer (P' : Set G)) := by
      change Nat.card (Subgroup.normalizer (Q : Set H)) ∣ _
      rw [Nat.card_congr (MulEquiv.subgroupCongr hnorm_Q).toEquiv]
      exact Subgroup.card_dvd_of_injective f hf
    have hd2 : Nat.card (Subgroup.normalizer (P' : Set G)) ∣
        Nat.card (Subgroup.normalizer (P : Set G)) := by
      have heq := Nat.card_congr
        ((Subgroup.normalizer (P' : Set G)).equivMapOfInjective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toEquiv
      rw [heq]
      exact Subgroup.card_dvd_of_le hnorm_conj
    exact hd1.trans hd2
  have hd_dvd_m : d ∣ m := hd_dvd_N.trans hN
  have hd_le_m : d ≤ m := Nat.le_of_dvd hm_pos hd_dvd_m
  have hd_dvd_H : d ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  have hmod : (Nat.card H / d) % p = 1 := by
    have hidx : Nat.card H / d = (Subgroup.normalizer (Q : Set H)).index := by
      have h := (Subgroup.normalizer (Q : Set H)).index_mul_card
      exact Nat.div_eq_of_eq_mul_left hd_pos h.symm
    rw [hidx, ← Q.card_eq_index_normalizer]
    have hsylow := card_sylow_modEq_one p H
    rw [Nat.ModEq, Nat.mod_eq_of_lt hp_gt1] at hsylow
    exact hsylow
  unfold hasValidSylowNormalizer
  rw [List.any_eq_true]
  refine ⟨d, ?_, ?_⟩
  · rw [List.mem_range'_1]
    omega
  · simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨Nat.mod_eq_zero_of_dvd hp_dvd_d, Nat.mod_eq_zero_of_dvd hd_dvd_m⟩,
      Nat.mod_eq_zero_of_dvd hd_dvd_H⟩, hmod⟩

private def emb4 {X : Type*} {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Fin 4 ↪ X :=
  ⟨![a, b, c, d], fun i j hij => by
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)⟩

/-- If `Γ` acts 4-transitively on `X` (`5 ≤ Nat.card X`), no subgroup `H ≤ Γ` of index
`Nat.card X - 1` can be transitive on `X` while having its point-stabilizer orbits on the
remaining `Nat.card X - 1` points be of size `1` or `Nat.card X - 2`. -/
theorem not_exists_subgroup_index_sub_one {Γ X : Type*} [Group Γ] [Finite Γ] [Finite X]
    [MulAction Γ X] [IsMultiplyPretransitive Γ X 4] (hX : 5 ≤ Nat.card X)
    (H : Subgroup Γ) (hH_idx : H.index = Nat.card X - 1) (x₀ : X)
    (horb₀ : Nat.card (orbit H x₀) = Nat.card X)
    (horb₁ : ∀ z : SubMulAction.ofStabilizer Γ x₀,
      Nat.card (orbit (H.subgroupOf (stabilizer Γ x₀)) z) = 1 ∨
      Nat.card (orbit (H.subgroupOf (stabilizer Γ x₀)) z) = Nat.card X - 2) :
    False := by
  classical
  have : Fintype X := Fintype.ofFinite X
  set S₀ := stabilizer Γ x₀
  set X₀ := SubMulAction.ofStabilizer Γ x₀
  set H₀ := H.subgroupOf S₀
  have hX₀_card : Nat.card X₀ = Nat.card X - 1 := SubMulAction.nat_card_ofStabilizer_eq Γ x₀
  obtain ⟨y₀, hy₀⟩ := exists_le_stabilizer_of_orbit_one_or_sub_one (X := X₀) (by omega) H₀ (by
    intro z
    rw [hX₀_card]
    exact horb₁ z)
  have h1 : IsMultiplyPretransitive Γ X 1 :=
    isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by omega)
  have htr : IsPretransitive Γ X := is_one_pretransitive_iff.mp h1
  have hS₀_idx : S₀.index = Nat.card X := index_stabilizer_of_transitive Γ x₀
  have hrel_S₀ : S₀.relIndex H = Nat.card X := by
    change (stabilizer H x₀).index = Nat.card X
    rw [index_stabilizer H x₀, ← Nat.card_coe_set_eq, horb₀]
  have hH₀_idx : H₀.index = Nat.card X - 1 := by
    change H.relIndex S₀ = Nat.card X - 1
    have hinf : H.relIndex S₀ * S₀.index = S₀.relIndex H * H.index := by
      rw [← Subgroup.index_inf, ← Subgroup.index_inf, inf_comm]
    rw [hS₀_idx, hrel_S₀, hH_idx, mul_comm (Nat.card X)] at hinf
    exact Nat.eq_of_mul_eq_mul_right (by omega) hinf
  have : IsMultiplyPretransitive S₀ X₀ 3 := by
    have : IsMultiplyPretransitive Γ X (3 + 1) := inferInstance
    exact SubMulAction.ofStabilizer.isMultiplyPretransitive.mp this
  have : IsPretransitive S₀ X₀ :=
    is_one_pretransitive_iff.mp
      (isMultiplyPretransitive_of_le (m := 1) (n := 3) (by decide) (by omega))
  have hSy₀_idx : (stabilizer S₀ y₀).index = Nat.card X - 1 := by
    rw [index_stabilizer_of_transitive S₀ y₀, hX₀_card]
  have hrel_y₀ : H₀.relIndex (stabilizer S₀ y₀) = 1 := by
    have h := Subgroup.relIndex_mul_index hy₀
    rw [hH₀_idx, hSy₀_idx] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) (h.trans (one_mul _).symm)
  have hH₀_eq : H₀ = stabilizer S₀ y₀ :=
    le_antisymm hy₀ (Subgroup.relIndex_eq_one.mp hrel_y₀)
  have hmem_H_iff : ∀ g : Γ, g • x₀ = x₀ → (g ∈ H ↔ g • y₀.1 = y₀.1) := by
    intro g hg
    have hgS : g ∈ S₀ := hg
    change (⟨g, hgS⟩ : S₀) ∈ H₀ ↔ _
    rw [hH₀_eq, mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  have horbH_univ : orbit H x₀ = Set.univ := by
    have hcard_univ : (Set.univ : Set X).ncard = Nat.card X := Set.ncard_univ X
    have hcard_orb : (orbit H x₀).ncard = Nat.card X := by
      rw [← Nat.card_coe_set_eq, horb₀]
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by omega)
  have hex_not_mem : ∀ s : Finset X, s.card < Nat.card X → ∃ q : X, q ∉ s := by
    intro s hs
    by_contra hall
    push Not at hall
    have hcard := Finset.card_le_card (fun q (_ : q ∈ Finset.univ) => hall q)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcard
    omega
  obtain ⟨u, hu⟩ := hex_not_mem {x₀, y₀.1} (Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨hux₀, huy₀⟩ := hu
  have hu_orb : u ∈ orbit H x₀ := horbH_univ.symm ▸ Set.mem_univ u
  obtain ⟨h, hh⟩ := hu_orb
  set v : X := (h : Γ) • y₀.1
  have hvu : v ≠ u := by
    intro heq
    have hh' : (h : Γ) • x₀ = u := hh
    exact y₀.2 (smul_left_cancel (h : Γ) (heq.trans hh'.symm))
  obtain ⟨z₀, hz₀⟩ := hex_not_mem {x₀, y₀.1, u} (Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz₀
  obtain ⟨hz₀x₀, hz₀y₀, hz₀u⟩ := hz₀
  let z : X := if v ≠ x₀ ∧ v ≠ y₀.1 then v else z₀
  have hzx₀ : z ≠ x₀ := by
    dsimp [z]; split_ifs with hv
    · exact hv.1
    · exact hz₀x₀
  have hzy₀ : z ≠ y₀.1 := by
    dsimp [z]; split_ifs with hv
    · exact hv.2
    · exact hz₀y₀
  have hzu : z ≠ u := by
    dsimp [z]; split_ifs with hv
    · exact hvu
    · exact hz₀u
  have hv_cases : v = z ∨ v = x₀ ∨ v = y₀.1 := by
    dsimp [z]
    split_ifs with hv
    · exact Or.inl rfl
    · rw [not_and_or, not_ne_iff, not_ne_iff] at hv
      exact Or.inr hv
  obtain ⟨w, hw⟩ := hex_not_mem {x₀, y₀.1, z, u} (Finset.card_le_four.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨hwx₀, hwy₀, hwz, hwu⟩ := hw
  let e₁ : Fin 4 ↪ X := emb4 (Ne.symm y₀.2) (Ne.symm hzx₀) (Ne.symm hux₀)
    (Ne.symm hzy₀) (Ne.symm huy₀) hzu
  let e₂ : Fin 4 ↪ X := emb4 (Ne.symm y₀.2) (Ne.symm hzx₀) (Ne.symm hwx₀)
    (Ne.symm hzy₀) (Ne.symm hwy₀) (Ne.symm hwz)
  obtain ⟨g, hg⟩ := (inferInstance : IsMultiplyPretransitive Γ X 4).exists_smul_eq e₁ e₂
  have hg_at : ∀ i : Fin 4, g • e₁ i = e₂ i := fun i =>
    congrArg (fun f : Fin 4 ↪ X => f i) hg
  have hgx₀ : g • x₀ = x₀ := hg_at 0
  have hgy₀ : g • y₀.1 = y₀.1 := hg_at 1
  have hgz : g • z = z := hg_at 2
  have hgu : g • u = w := hg_at 3
  have hgv : g • v = v := by
    rcases hv_cases with h | h | h <;> rw [h]
    · exact hgz
    · exact hgx₀
    · exact hgy₀
  have hgH : g ∈ H := (hmem_H_iff g hgx₀).mpr hgy₀
  have hconj_H : (h : Γ)⁻¹ * g * (h : Γ) ∈ H := H.mul_mem (H.mul_mem (H.inv_mem h.2) hgH) h.2
  have hstab_le : stabilizer H x₀ ≤ stabilizer H y₀.1 := by
    intro k hk
    rw [mem_stabilizer_iff] at hk ⊢
    exact (hmem_H_iff k.1 hk).mp k.2
  have hstab_x₀_idx : (stabilizer H x₀).index = Nat.card X := by
    rw [index_stabilizer H x₀, ← Nat.card_coe_set_eq, horb₀]
  have hstab_y₀_idx : (stabilizer H y₀.1).index = Nat.card X := by
    rw [index_stabilizer H y₀.1, ← Nat.card_coe_set_eq]
    have hy₀_orb : y₀.1 ∈ orbit H x₀ := horbH_univ.symm ▸ Set.mem_univ y₀.1
    rw [orbit_eq_iff.mpr hy₀_orb, horb₀]
  have hstab_rel : (stabilizer H x₀).relIndex (stabilizer H y₀.1) = 1 := by
    have hrel := Subgroup.relIndex_mul_index hstab_le
    rw [hstab_x₀_idx, hstab_y₀_idx] at hrel
    exact Nat.eq_of_mul_eq_mul_right (by omega) (hrel.trans (one_mul _).symm)
  have hstab_eq : stabilizer H x₀ = stabilizer H y₀.1 :=
    le_antisymm hstab_le (Subgroup.relIndex_eq_one.mp hstab_rel)
  have hconj_fix_y₀ : (⟨(h : Γ)⁻¹ * g * (h : Γ), hconj_H⟩ : H) ∈ stabilizer H y₀.1 := by
    rw [mem_stabilizer_iff]
    change ((h : Γ)⁻¹ * g * (h : Γ)) • y₀.1 = y₀.1
    rw [mul_smul, mul_smul]
    change (h : Γ)⁻¹ • (g • v) = y₀.1
    rw [hgv, inv_smul_smul]
  have hconj_fix_x₀ : (⟨(h : Γ)⁻¹ * g * (h : Γ), hconj_H⟩ : H) ∈ stabilizer H x₀ := by
    rwa [hstab_eq]
  rw [mem_stabilizer_iff] at hconj_fix_x₀
  change ((h : Γ)⁻¹ * g * (h : Γ)) • x₀ = x₀ at hconj_fix_x₀
  have hh' : (h : Γ) • x₀ = u := hh
  rw [mul_smul, mul_smul, hh', hgu] at hconj_fix_x₀
  have hwu' : w = u := by
    have h1 := congrArg ((h : Γ) • ·) hconj_fix_x₀
    rw [smul_inv_smul, hh'] at h1
    exact h1
  exact hwu hwu'

/-- The group `NativeSporadic.M11` acts 4-transitively on `Fin 11`. -/
instance isMultiplyPretransitive_M11 : IsMultiplyPretransitive NativeSporadic.M11 (Fin 11) 4 := by
  rw [isMultiplyPretransitive_iff]
  intro x y
  have hx : ∀ i j : Fin 4, i ≠ j → x i ≠ x j := fun i j hij => x.injective.ne hij
  have hy : ∀ i j : Fin 4, i ≠ j → y i ≠ y j := fun i j hij => y.injective.ne hij
  obtain ⟨gx, hgx0, hgx1, hgx2, hgx3⟩ := CFSG.KC.M11L.m11_four (x 0) (x 1) (x 2) (x 3)
    (hx 0 1 (by decide)) (hx 0 2 (by decide)) (hx 0 3 (by decide))
    (hx 1 2 (by decide)) (hx 1 3 (by decide)) (hx 2 3 (by decide))
  obtain ⟨gy, hgy0, hgy1, hgy2, hgy3⟩ := CFSG.KC.M11L.m11_four (y 0) (y 1) (y 2) (y 3)
    (hy 0 1 (by decide)) (hy 0 2 (by decide)) (hy 0 3 (by decide))
    (hy 1 2 (by decide)) (hy 1 3 (by decide)) (hy 2 3 (by decide))
  refine ⟨gy * gx⁻¹, ?_⟩
  apply DFunLike.ext
  intro i
  change gy • (gx⁻¹ • x i) = y i
  fin_cases i
  · change gy • (gx⁻¹ • x 0) = y 0
    rw [inv_smul_eq_iff.mpr hgx0.symm, hgy0]
  · change gy • (gx⁻¹ • x 1) = y 1
    rw [inv_smul_eq_iff.mpr hgx1.symm, hgy1]
  · change gy • (gx⁻¹ • x 2) = y 2
    rw [inv_smul_eq_iff.mpr hgx2.symm, hgy2]
  · change gy • (gx⁻¹ • x 3) = y 3
    rw [inv_smul_eq_iff.mpr hgx3.symm, hgy3]

/-- Every proper subgroup of `M₁₁` has index at least `11`. -/
theorem index_ge_M11 {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .M11) {H : Subgroup S} (hH : H ≠ ⊤) :
    11 ≤ H.index := by
  have hcard : Nat.card S = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  exact prime_le_index_of_ne_top hH (by decide : Nat.Prime 11) (by rw [hcard]; decide)

/-- Maróti's theorem for primitive almost simple groups with socle `M₁₁`. -/
theorem sporadicCase_M11 {α : Type} [Finite α] (G : Subgroup (Equiv.Perm α)) (S : Type) [Group S]
    [IsPreprimitive G α] (hS : IsAlmostSimpleWith G S)
    (he : Nonempty (S ≃* NativeSporadic.Carrier .M11)) :
    AlmostSimpleConclusion G := by
  have : Finite S := hS.finite
  have : IsSimpleGroup S := hS.isSimpleGroup
  obtain ⟨e⟩ := he
  have hcardS : Nat.card S = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  have hAut : Nat.card (MulAut S) ≤ 7920 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact CFSG.Sporadic.Schreier.m11_mulAut_card.trans (by rw [CFSG.Sporadic.Mathieu.card_M11])
  have hG_le : Nat.card G ≤ 7920 := hS.card_le_card_mulAut.trans hAut
  obtain ⟨H, hH_ne, hH_idx⟩ := hS.exists_proper_subgroup_index_eq
  have hn11 : 11 ≤ Nat.card α := hH_idx ▸ index_ge_M11 e hH_ne
  rcases le_or_gt 12 (Nat.card α) with hn12 | hn12
  · right; right
    exact hG_le.trans ((by decide : 7920 ≤ bound 12).trans (bound_mono hn12))
  · have hn_eq : Nat.card α = 11 := by omega
    obtain ⟨eGS⟩ := mulEquiv_of_card_le hS (hG_le.trans hcardS.symm.le)
    let eGM : G ≃* NativeSporadic.M11 := eGS.trans e
    obtain ⟨eBridge⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
    right; left
    refine ⟨(.M11, 11), by simp [fourTransitiveMathieu], hn_eq, ?_, ⟨eGM.trans eBridge⟩⟩
    have hcard11 : Nat.card (Fin 11) = 11 := Nat.card_fin 11
    have : IsMultiplyPretransitive NativeSporadic.M11 (Fin 11) (3 + 1) :=
      isMultiplyPretransitive_M11
    have : IsPretransitive NativeSporadic.M11 (Fin 11) :=
      is_one_pretransitive_iff.mp
        (isMultiplyPretransitive_of_le (m := 1) (n := 4) (by decide) (by rw [hcard11]; decide))
    apply isMultiplyPretransitive_of_le_stabilizer eGM.symm (hn_eq.trans hcard11.symm)
    intro K hK
    apply exists_le_stabilizer_of_orbit_one_or_sub_one (by rw [hcard11]; decide) K
    intro x
    have hmem := mem_validOrbits (Γ := NativeSporadic.M11) (X := Fin 11) 3
      (by rw [hcard11]; decide) K x
    rw [hK, hcard11, CFSG.Sporadic.Mathieu.card_M11] at hmem
    have hvo : validOrbits 3 11 7920 11 = [1, 10] := by decide
    rw [hvo, List.mem_cons, List.mem_singleton] at hmem
    simpa [hcard11] using hmem

end Maroti
