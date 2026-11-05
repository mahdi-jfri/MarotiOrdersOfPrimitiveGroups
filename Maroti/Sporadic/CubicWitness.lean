module

public import Maroti.MinDegree.Heisenberg
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

/-!
# Minimum degree and index bounds from cubic local witnesses

Given elements `x, y` of a group `G` and a prime `r` such that `x ^ r = 1`, `y ^ r = 1`,
`z = ⁅x, y⁆ ≠ 1`, `Commute z x`, `Commute z y`, and `Nat.card (Subgroup.closure {x, y}) = r ^ 3`,
the subgroup `Q = Subgroup.closure {x, y}` is an extraspecial group of order `r ^ 3` and exponent
`r`. Using `Maroti/MinDegree/Heisenberg.lean`, we show:

* The lemma `Maroti.CubicWitness.sq_le_index_of_not_le`: every subgroup `K ≤ Q` not containing
  `Z = ⟨z⟩` has index at least `r ^ 2` (hence `K.index = r ^ 2` or `r ^ 3`).
* The lemma `Maroti.CubicWitness.sq_le_index_of_ne_top`: if `G` is isomorphic to a finite simple
  group `S`, every proper subgroup `H ≠ ⊤` of `S` has index at least `r ^ 2`.
* The lemma `Maroti.CubicWitness.twentySeven_le_index_of_ne_top`: when `r = 3` and an element
  `h : G` normalizes `Q` and acts on `Q / Z ≅ (ZMod 3)²` with no invariant line under `h` and
  `h²`, every proper subgroup `H ≠ ⊤` of `S` has index at least `27`.
* The lemma `Maroti.CubicWitness.two_mul_sq_le_index_of_ne_top`: for any prime `r`, when an
  element `h : G` normalizes `Q` and acts on `Q / Z ≅ (ZMod r)²` with no invariant line, every
  proper subgroup `H ≠ ⊤` of `S` has index at least `2 * r ^ 2`.
-/

@[expose] public section

namespace Maroti.CubicWitness

open Subgroup CFSG.SectionRank.LocalWitness
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- If `g ^ r = 1` with `0 < r`, any integer power `g ^ n` equals the natural power
`g ^ Int.toNat (n % r)`. -/
theorem zpow_eq_pow_mod_toNat {H : Type*} [Group H] {g : H} {r : ℕ} (hr : 0 < r)
    (hg : g ^ r = 1) (n : ℤ) :
    g ^ n = g ^ Int.toNat (n % r) := by
  have hr0 : (r : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hpos : 0 ≤ n % (r : ℤ) := Int.emod_nonneg n hr0
  have hdiv := (Int.emod_add_mul_ediv n r).symm
  calc g ^ n = g ^ (n % r + r * (n / r)) := by rw [← hdiv]
    _ = g ^ (n % r) * (g ^ (r : ℤ)) ^ (n / r) := by rw [zpow_add, zpow_mul]
    _ = g ^ (n % r) := by rw [zpow_natCast, hg, one_zpow, mul_one]
    _ = g ^ (Int.toNat (n % r) : ℤ) := by rw [Int.toNat_of_nonneg hpos]
    _ = g ^ Int.toNat (n % r) := zpow_natCast g _

/-- In a cubic witness, `⁅x, y⁆ ^ r = 1`. -/
theorem commutator_pow_eq_one {x y : G} {r : ℕ} (hx : x ^ r = 1) (hzx : Commute ⁅x, y⁆ x) :
    ⁅x, y⁆ ^ r = 1 := by
  rw [commutator_pow_eq hzx, hx, commutatorElement_one_left]

/-- An element commuting with `x` and `y` commutes with every element of
`Subgroup.closure {x, y}`. -/
theorem commute_of_mem_closure_pair {x y z : G} (hzx : Commute z x) (hzy : Commute z y)
    {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : Commute z g := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl
    · exact hzx
    · exact hzy
  | one => exact Commute.one_right z
  | mul a b _ _ iha ihb => exact iha.mul_right ihb
  | inv a _ iha => exact iha.inv_right

/-- Reordering `y ^ j * x ^ i` into normal form `x ^ i * y ^ j * ⁅x, y⁆ ^ ((r - 1) * i * j)`. -/
theorem y_pow_mul_x_pow {x y : G} {r : ℕ} (hr : 0 < r) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hz : ⁅x, y⁆ ^ r = 1) (j i : ℕ) :
    y ^ j * x ^ i = x ^ i * y ^ j * ⁅x, y⁆ ^ ((r - 1) * i * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc y ^ (j + 1) * x ^ i = y ^ j * (y * x ^ i) := by rw [pow_succ, mul_assoc]
      _ = y ^ j * (x ^ i * y * ⁅x, y⁆ ^ ((r - 1) * i)) := by
        rw [y_mul_x_pow hr hzx hzy hz]
      _ = (y ^ j * x ^ i) * y * ⁅x, y⁆ ^ ((r - 1) * i) := by group
      _ = x ^ i * y ^ j * (⁅x, y⁆ ^ ((r - 1) * i * j) * y) * ⁅x, y⁆ ^ ((r - 1) * i) := by
        rw [ih]; group
      _ = x ^ i * (y ^ j * y) * (⁅x, y⁆ ^ ((r - 1) * i * j) * ⁅x, y⁆ ^ ((r - 1) * i)) := by
        rw [(hzy.pow_left ((r - 1) * i * j)).eq]; group
      _ = x ^ i * y ^ (j + 1) * ⁅x, y⁆ ^ ((r - 1) * i * (j + 1)) := by
        rw [← pow_succ, ← pow_add,
          show (r - 1) * i * j + (r - 1) * i = (r - 1) * i * (j + 1) by ring]

/-- Multiplication of two normal-form words `x ^ i * y ^ j * ⁅x, y⁆ ^ k`. -/
theorem normalForm_mul {x y : G} {r : ℕ} (hr : 0 < r) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hz : ⁅x, y⁆ ^ r = 1) (i₁ j₁ k₁ i₂ j₂ k₂ : ℕ) :
    (x ^ i₁ * y ^ j₁ * ⁅x, y⁆ ^ k₁) * (x ^ i₂ * y ^ j₂ * ⁅x, y⁆ ^ k₂) =
      x ^ (i₁ + i₂) * y ^ (j₁ + j₂) * ⁅x, y⁆ ^ (k₁ + k₂ + (r - 1) * i₂ * j₁) := by
  have hc1 : Commute (⁅x, y⁆ ^ k₁) (x ^ i₂ * y ^ j₂) :=
    ((hzx.pow_left _).pow_right _).mul_right ((hzy.pow_left _).pow_right _)
  have hc2 : Commute (⁅x, y⁆ ^ ((r - 1) * i₂ * j₁)) (y ^ j₂) :=
    (hzy.pow_left _).pow_right _
  calc (x ^ i₁ * y ^ j₁ * ⁅x, y⁆ ^ k₁) * (x ^ i₂ * y ^ j₂ * ⁅x, y⁆ ^ k₂)
      = x ^ i₁ * y ^ j₁ * (⁅x, y⁆ ^ k₁ * (x ^ i₂ * y ^ j₂)) * ⁅x, y⁆ ^ k₂ := by group
    _ = x ^ i₁ * (y ^ j₁ * x ^ i₂) * y ^ j₂ * (⁅x, y⁆ ^ k₁ * ⁅x, y⁆ ^ k₂) := by
      rw [hc1.eq]; group
    _ = x ^ i₁ * (x ^ i₂ * y ^ j₁ * ⁅x, y⁆ ^ ((r - 1) * i₂ * j₁)) * y ^ j₂ *
        (⁅x, y⁆ ^ k₁ * ⁅x, y⁆ ^ k₂) := by
      rw [y_pow_mul_x_pow hr hzx hzy hz]
    _ = (x ^ i₁ * x ^ i₂) * y ^ j₁ * (⁅x, y⁆ ^ ((r - 1) * i₂ * j₁) * y ^ j₂) *
        (⁅x, y⁆ ^ k₁ * ⁅x, y⁆ ^ k₂) := by group
    _ = (x ^ i₁ * x ^ i₂) * (y ^ j₁ * y ^ j₂) *
        (⁅x, y⁆ ^ ((r - 1) * i₂ * j₁) * (⁅x, y⁆ ^ k₁ * ⁅x, y⁆ ^ k₂)) := by
      rw [hc2.eq]; group
    _ = x ^ (i₁ + i₂) * y ^ (j₁ + j₂) * ⁅x, y⁆ ^ (k₁ + k₂ + (r - 1) * i₂ * j₁) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add,
        show (r - 1) * i₂ * j₁ + (k₁ + k₂) = k₁ + k₂ + (r - 1) * i₂ * j₁ by ring]

/-- Powers of a normal-form word `x ^ i * y ^ j * ⁅x, y⁆ ^ k`. -/
theorem normalForm_pow {x y : G} {r : ℕ} (hr : 0 < r) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hz : ⁅x, y⁆ ^ r = 1) (i j k n : ℕ) :
    ∃ m : ℕ, (x ^ i * y ^ j * ⁅x, y⁆ ^ k) ^ n = x ^ (n * i) * y ^ (n * j) * ⁅x, y⁆ ^ m := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + k + (r - 1) * i * (n * j), ?_⟩
    rw [pow_succ, hm, normalForm_mul hr hzx hzy hz]
    congr 2
    · rw [show n * i + i = (n + 1) * i by ring]
    · rw [show n * j + j = (n + 1) * j by ring]

/-- In a cubic witness, `⁅x, y⁆` belongs to `Subgroup.closure {x, y}`. -/
theorem commutator_mem_closure_pair (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.closure ({x, y} : Set G) := by
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hxQ hyQ) (inv_mem hxQ)) (inv_mem hyQ)

section HeisenbergInstance

variable {x y : G} {r : ℕ} [hp : Fact r.Prime]
  (hx : x ^ r = 1) (hy : y ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1)
  (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
  (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 3)

/-- The central element `z₀ = ⟨⁅x, y⁆, _⟩` in `Subgroup.closure {x, y}`. -/
def centerGen (x y : G) : Subgroup.closure ({x, y} : Set G) :=
  ⟨⁅x, y⁆, commutator_mem_closure_pair x y⟩

/-- The central subgroup `Z = Subgroup.zpowers (centerGen x y)` of `Subgroup.closure {x, y}`. -/
def centerSubgroup (x y : G) : Subgroup (Subgroup.closure ({x, y} : Set G)) :=
  Subgroup.zpowers (centerGen x y)

include hz1 in
theorem centerGen_ne_one : centerGen x y ≠ 1 :=
  fun h => hz1 (congrArg Subtype.val h)

include hz1 in
theorem centerSubgroup_ne_bot : centerSubgroup x y ≠ ⊥ :=
  Subgroup.zpowers_ne_bot.mpr (centerGen_ne_one hz1)

omit hp in
include hx hzx in
theorem centerGen_pow_eq_one : (centerGen x y) ^ r = 1 :=
  Subtype.ext (commutator_pow_eq_one hx hzx)

include hp hx hz1 hzx in
theorem card_centerSubgroup : Nat.card (centerSubgroup x y) = r := by
  rw [centerSubgroup, Nat.card_zpowers,
    orderOf_eq_prime (centerGen_pow_eq_one hx hzx) (centerGen_ne_one hz1)]

include hp hx hz1 hzx hcard in
theorem index_centerSubgroup : (centerSubgroup x y).index = r ^ 2 := by
  have hr : 0 < r := hp.out.pos
  have hmul := (centerSubgroup x y).index_mul_card
  rw [card_centerSubgroup hx hz1 hzx, hcard, show r ^ 3 = r ^ 2 * r by ring] at hmul
  exact Nat.eq_of_mul_eq_mul_right hr hmul

include hzx hzy in
theorem centerSubgroup_le_center :
    centerSubgroup x y ≤ Subgroup.center (Subgroup.closure ({x, y} : Set G)) := by
  rw [centerSubgroup, Subgroup.zpowers_le, Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (commute_of_mem_closure_pair hzx hzy g.2).symm

include hp hx hy hzx hzy in
theorem commutator_mem_centerSubgroup (u v : Subgroup.closure ({x, y} : Set G)) :
    ⁅u, v⁆ ∈ centerSubgroup x y := by
  have hr : 0 < r := hp.out.pos
  have hz : ⁅x, y⁆ ^ r = 1 := commutator_pow_eq_one hx hzx
  obtain ⟨i₁, j₁, k₁, -, -, -, hu⟩ := mem_closure_normalForm hr hx hy hzx hzy u.2
  obtain ⟨i₂, j₂, k₂, -, -, -, hv⟩ := mem_closure_normalForm hr hx hy hzx hzy v.2
  set a : G := x ^ (i₁ + i₂) * y ^ (j₁ + j₂)
  set m₁ : ℕ := k₁ + k₂ + (r - 1) * i₂ * j₁
  set m₂ : ℕ := k₂ + k₁ + (r - 1) * i₁ * j₂
  have huv : (u : G) * (v : G) = a * ⁅x, y⁆ ^ m₁ := by
    rw [hu, hv, normalForm_mul hr hzx hzy hz]
  have hvu : (v : G) * (u : G) = a * ⁅x, y⁆ ^ m₂ := by
    rw [hv, hu, normalForm_mul hr hzx hzy hz, Nat.add_comm i₂ i₁, Nat.add_comm j₂ j₁]
  have hca1 : Commute (⁅x, y⁆ ^ m₁) a :=
    ((hzx.pow_left _).pow_right _).mul_right ((hzy.pow_left _).pow_right _)
  have hca2 : Commute (⁅x, y⁆ ^ m₂) a :=
    ((hzx.pow_left _).pow_right _).mul_right ((hzy.pow_left _).pow_right _)
  have hcomm_eq : ((⁅u, v⁆ : Subgroup.closure ({x, y} : Set G)) : G) =
      ⁅x, y⁆ ^ m₁ * (⁅x, y⁆ ^ m₂)⁻¹ := by
    calc ((⁅u, v⁆ : Subgroup.closure ({x, y} : Set G)) : G)
        = ((u : G) * (v : G)) * ((v : G) * (u : G))⁻¹ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (a * ⁅x, y⁆ ^ m₁) * (a * ⁅x, y⁆ ^ m₂)⁻¹ := by rw [huv, hvu]
      _ = (a * ⁅x, y⁆ ^ m₁) * (⁅x, y⁆ ^ m₂ * a)⁻¹ := by rw [hca2.eq]
      _ = a * (⁅x, y⁆ ^ m₁ * a⁻¹) * (⁅x, y⁆ ^ m₂)⁻¹ := by group
      _ = ⁅x, y⁆ ^ m₁ * (⁅x, y⁆ ^ m₂)⁻¹ := by rw [hca1.inv_right.eq]; group
  have hmem : ⁅u, v⁆ = (centerGen x y) ^ m₁ * ((centerGen x y) ^ m₂)⁻¹ :=
    Subtype.ext hcomm_eq
  rw [hmem]
  exact mul_mem (pow_mem (Subgroup.mem_zpowers _) _) (inv_mem (pow_mem (Subgroup.mem_zpowers _) _))

omit hp in
include hx hzx in
theorem pow_eq_one_of_mem_centerSubgroup (w : Subgroup.closure ({x, y} : Set G))
    (hw : w ∈ centerSubgroup x y) : w ^ r = 1 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    centerGen_pow_eq_one hx hzx, one_zpow]

include hp hx hy hzx hzy in
theorem pow_mem_centerSubgroup (u : Subgroup.closure ({x, y} : Set G)) :
    u ^ r ∈ centerSubgroup x y := by
  have hr : 0 < r := hp.out.pos
  have hz : ⁅x, y⁆ ^ r = 1 := commutator_pow_eq_one hx hzx
  obtain ⟨i, j, k, -, -, -, hu⟩ := mem_closure_normalForm hr hx hy hzx hzy u.2
  obtain ⟨m, hm⟩ := normalForm_pow hr hzx hzy hz i j k r
  have hur : (u : G) ^ r = ⁅x, y⁆ ^ m := by
    rw [hu, hm, pow_mul, hx, one_pow, one_mul, pow_mul, hy, one_pow, one_mul]
  have hmem : u ^ r = (centerGen x y) ^ m := Subtype.ext hur
  rw [hmem]
  exact pow_mem (Subgroup.mem_zpowers _) m

include hp hx hy hz1 hzx hzy in
theorem exists_commutator_eq_of_not_mem_centerSubgroup
    (u : Subgroup.closure ({x, y} : Set G)) (huZ : u ∉ centerSubgroup x y)
    (w : Subgroup.closure ({x, y} : Set G)) (hwZ : w ∈ centerSubgroup x y) :
    ∃ v : Subgroup.closure ({x, y} : Set G), ⁅u, v⁆ = w := by
  have hr : 0 < r := hp.out.pos
  have hz : ⁅x, y⁆ ^ r = 1 := commutator_pow_eq_one hx hzx
  have : Finite (centerSubgroup x y) :=
    Nat.finite_of_card_ne_zero (by rw [card_centerSubgroup hx hz1 hzx]; exact hr.ne')
  obtain ⟨i, j, k, hi, hj, -, hu⟩ := mem_closure_normalForm hr hx hy hzx hzy u.2
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  suffices hgen : ∃ v₀ : Subgroup.closure ({x, y} : Set G),
      ∃ c : ℕ, 0 < c ∧ c < r ∧ ⁅u, v₀⁆ = (centerGen x y) ^ c by
    obtain ⟨v₀, c, hc0, hcr, hv₀⟩ := hgen
    have hzc_ne : (centerGen x y) ^ c ≠ 1 := by
      intro h1
      have hord : orderOf (centerGen x y) = r :=
        orderOf_eq_prime (centerGen_pow_eq_one hx hzx) (centerGen_ne_one hz1)
      have hdvd : r ∣ c := hord ▸ orderOf_dvd_of_pow_eq_one h1
      exact Nat.not_lt.mpr (Nat.le_of_dvd hc0 hdvd) hcr
    have hzc_pow : ((centerGen x y) ^ c) ^ r = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, centerGen_pow_eq_one hx hzx, one_pow]
    have hsub : Subgroup.zpowers ((centerGen x y) ^ c) = centerSubgroup x y := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]
        exact pow_mem (Subgroup.mem_zpowers _) c
      · rw [Nat.card_zpowers, orderOf_eq_prime hzc_pow hzc_ne, card_centerSubgroup hx hz1 hzx]
    rw [← hsub] at hwZ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwZ
    set m := Int.toNat (n % r)
    rw [zpow_eq_pow_mod_toNat hr hzc_pow n]
    refine ⟨v₀ ^ m, ?_⟩
    have hmul_right := commutatorElement_mul_right_of_le_center
      (centerSubgroup_le_center hzx hzy) (commutator_mem_centerSubgroup hx hy hzx hzy)
    have hpow : ∀ t : ℕ, ⁅u, v₀ ^ t⁆ = ⁅u, v₀⁆ ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t iht => rw [pow_succ, hmul_right, iht, pow_succ]
    rw [hpow, hv₀]
  rcases eq_or_ne i 0 with rfl | hi0
  · have hj0 : j ≠ 0 := by
      intro hj0
      apply huZ
      have hu' : u = (centerGen x y) ^ k := by
        apply Subtype.ext
        change (u : G) = ⁅x, y⁆ ^ k
        rw [hu, hj0, pow_zero, pow_zero, one_mul, one_mul]
      rw [hu']
      exact pow_mem (Subgroup.mem_zpowers _) k
    refine ⟨⟨x ^ (r - 1), pow_mem hxQ _⟩, j, Nat.pos_of_ne_zero hj0, hj, Subtype.ext ?_⟩
    change (u : G) * x ^ (r - 1) * (u : G)⁻¹ * (x ^ (r - 1))⁻¹ = ⁅x, y⁆ ^ j
    rw [pow_zero, one_mul] at hu
    have hcx : Commute (⁅x, y⁆ ^ k) (x ^ (r - 1)) := (hzx.pow_left k).pow_right (r - 1)
    have hcz : Commute (⁅x, y⁆ ^ ((r - 1) * (r - 1) * j)) (y ^ j) :=
      (hzy.pow_left _).pow_right j
    have hczx : Commute (⁅x, y⁆ ^ ((r - 1) * (r - 1) * j)) (x ^ (r - 1)) :=
      (hzx.pow_left _).pow_right (r - 1)
    have hrmod : ((r - 1) * (r - 1) * j) % r = j % r := by
      have hr1 : 1 ≤ r := hp.out.one_lt.le
      have h1 : (r - 1) * (r - 1) * j = j + r * ((r - 2) * j) := by
        rcases Nat.lt_or_ge r 2 with hlt | hge
        · omega
        · zify [hr1, hge]; ring
      rw [h1, Nat.add_mul_mod_self_left]
    calc (u : G) * x ^ (r - 1) * (u : G)⁻¹ * (x ^ (r - 1))⁻¹
        = y ^ j * (⁅x, y⁆ ^ k * x ^ (r - 1)) *
          (⁅x, y⁆ ^ k)⁻¹ * (y ^ j)⁻¹ * (x ^ (r - 1))⁻¹ := by
          rw [hu]; group
      _ = (y ^ j * x ^ (r - 1)) * (y ^ j)⁻¹ * (x ^ (r - 1))⁻¹ := by
          rw [hcx.eq]; group
      _ = (x ^ (r - 1) * y ^ j * ⁅x, y⁆ ^ ((r - 1) * (r - 1) * j)) *
          (y ^ j)⁻¹ * (x ^ (r - 1))⁻¹ := by
          rw [y_pow_mul_x_pow hr hzx hzy hz]
      _ = x ^ (r - 1) * (y ^ j * (⁅x, y⁆ ^ ((r - 1) * (r - 1) * j) * (y ^ j)⁻¹)) *
          (x ^ (r - 1))⁻¹ := by group
      _ = x ^ (r - 1) * (⁅x, y⁆ ^ ((r - 1) * (r - 1) * j) * (x ^ (r - 1))⁻¹) := by
          rw [hcz.inv_right.eq]; group
      _ = ⁅x, y⁆ ^ ((r - 1) * (r - 1) * j) := by
          rw [hczx.inv_right.eq]; group
      _ = ⁅x, y⁆ ^ j := by
          rw [pow_eq_pow_mod _ hz, hrmod, ← pow_eq_pow_mod _ hz]
  · refine ⟨⟨y, hyQ⟩, i, Nat.pos_of_ne_zero hi0, hi, Subtype.ext ?_⟩
    change (u : G) * y * (u : G)⁻¹ * y⁻¹ = ⁅x, y⁆ ^ i
    have hcy : Commute (y ^ j * ⁅x, y⁆ ^ k) y :=
      (Commute.pow_self y j).mul_left (hzy.pow_left k)
    calc (u : G) * y * (u : G)⁻¹ * y⁻¹
        = x ^ i * ((y ^ j * ⁅x, y⁆ ^ k) * y) * (y ^ j * ⁅x, y⁆ ^ k)⁻¹ * (x ^ i)⁻¹ * y⁻¹ := by
          rw [hu]; group
      _ = x ^ i * (y * (y ^ j * ⁅x, y⁆ ^ k)) * (y ^ j * ⁅x, y⁆ ^ k)⁻¹ * (x ^ i)⁻¹ * y⁻¹ := by
          rw [hcy.eq]
      _ = ⁅x ^ i, y⁆ := by simp only [commutatorElement_def]; group
      _ = ⁅x, y⁆ ^ i := (commutator_pow_eq hzx i).symm

include hp hx hy hz1 hzx hzy hcard in
/-- Every subgroup `K` of `Q = Subgroup.closure {x, y}` not containing `centerSubgroup x y` has
index at least `r ^ 2`. -/
theorem sq_le_index_of_not_le {K : Subgroup (Subgroup.closure ({x, y} : Set G))}
    (hKZ : ¬ centerSubgroup x y ≤ K) :
    r ^ 2 ≤ K.index := by
  have hr : 0 < r := hp.out.pos
  have : Finite (Subgroup.closure ({x, y} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hr.ne')
  have h := mul_le_index_of_not_le (p := r)
    (centerSubgroup_le_center hzx hzy)
    (commutator_mem_centerSubgroup hx hy hzx hzy)
    (pow_eq_one_of_mem_centerSubgroup hx hzx)
    (pow_mem_centerSubgroup hx hy hzx hzy)
    (exists_commutator_eq_of_not_mem_centerSubgroup hx hy hz1 hzx hzy)
    hKZ (m := r) (by rw [index_centerSubgroup hx hz1 hzx hcard])
  rwa [sq]

include hp hx hy hz1 hzx hzy hcard in
/-- If `G` embeds into a finite simple group `S`, every proper subgroup `H ≠ ⊤` of `S` has index at
least `r ^ 2`. -/
theorem sq_le_index_of_ne_top {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* G) {H : Subgroup S} (hH : H ≠ ⊤) :
    r ^ 2 ≤ H.index := by
  let f : Subgroup.closure ({x, y} : Set G) →* S :=
    e.symm.toMonoidHom.comp (Subgroup.closure ({x, y} : Set G)).subtype
  have hf : Function.Injective f := e.symm.injective.comp Subtype.coe_injective
  exact le_index_of_injective_of_forall_not_le_index hH f hf (centerSubgroup_ne_bot hz1)
    fun K hKZ => sq_le_index_of_not_le hx hy hz1 hzx hzy hcard hKZ

include hp hx hy hzx hzy hcard in
/-- Uniqueness of normal-form exponents modulo `r` when
`Nat.card (Subgroup.closure {x, y}) = r ^ 3`. -/
theorem eq_zmod_of_normalForm_eq {i₁ j₁ k₁ i₂ j₂ k₂ : ℕ}
    (heq : x ^ i₁ * y ^ j₁ * ⁅x, y⁆ ^ k₁ = x ^ i₂ * y ^ j₂ * ⁅x, y⁆ ^ k₂) :
    (i₁ : ZMod r) = (i₂ : ZMod r) ∧ (j₁ : ZMod r) = (j₂ : ZMod r) := by
  classical
  have hr : 0 < r := hp.out.pos
  have hz : ⁅x, y⁆ ^ r = 1 := commutator_pow_eq_one hx hzx
  set Q := Subgroup.closure ({x, y} : Set G)
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hr.ne')
  cases nonempty_fintype Q
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hzQ : ⁅x, y⁆ ∈ Q := commutator_mem_closure_pair x y
  let F : Fin r × Fin r × Fin r → Q := fun t =>
    ⟨x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ),
      Q.mul_mem (Q.mul_mem (Q.pow_mem hxQ _) (Q.pow_mem hyQ _)) (Q.pow_mem hzQ _)⟩
  have hsurj : Function.Surjective F := fun g => by
    obtain ⟨i, j, k, hi, hj, hk, hg⟩ := mem_closure_normalForm hr hx hy hzx hzy g.2
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), Subtype.ext hg.symm⟩
  have hcard_eq : Fintype.card (Fin r × Fin r × Fin r) = Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      Nat.card_prod, Nat.card_prod, Nat.card_fin]
    ring
  have hbij : Function.Bijective F :=
    (Fintype.bijective_iff_surjective_and_card F).mpr ⟨hsurj, hcard_eq⟩
  have heq' : F (⟨i₁ % r, Nat.mod_lt _ hr⟩, ⟨j₁ % r, Nat.mod_lt _ hr⟩, ⟨k₁ % r, Nat.mod_lt _ hr⟩) =
      F (⟨i₂ % r, Nat.mod_lt _ hr⟩, ⟨j₂ % r, Nat.mod_lt _ hr⟩, ⟨k₂ % r, Nat.mod_lt _ hr⟩) := by
    apply Subtype.ext
    dsimp [F]
    rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, ← pow_eq_pow_mod _ hz,
      ← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, ← pow_eq_pow_mod _ hz, heq]
  have hinj := hbij.1 heq'
  have hi_eq : i₁ % r = i₂ % r := congrArg (fun t : Fin r × Fin r × Fin r => (t.1 : ℕ)) hinj
  have hj_eq : j₁ % r = j₂ % r := congrArg (fun t : Fin r × Fin r × Fin r => (t.2.1 : ℕ)) hinj
  exact ⟨(ZMod.natCast_eq_natCast_iff' i₁ i₂ r).mpr hi_eq,
    (ZMod.natCast_eq_natCast_iff' j₁ j₂ r).mpr hj_eq⟩

end HeisenbergInstance

section IrreducibleNormalizer

variable {x y h : G} {r a b c d k₀ l₀ μ : ℕ} [hp : Fact r.Prime]
  (hx : x ^ r = 1) (hy : y ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1)
  (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
  (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 3)
  (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k₀)
  (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l₀)
  (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)

include hp hx hzx hzy hhx hhy hhz in
/-- Conjugation of a normal-form word by `h`. -/
theorem conj_normalForm (i j k : ℕ) :
    ∃ m : ℕ, h * (x ^ i * y ^ j * ⁅x, y⁆ ^ k) * h⁻¹ =
      x ^ (a * i + c * j) * y ^ (b * i + d * j) * ⁅x, y⁆ ^ m := by
  have hr : 0 < r := hp.out.pos
  have hz : ⁅x, y⁆ ^ r = 1 := commutator_pow_eq_one hx hzx
  let φ : G →* G := MulAut.conj h
  have hφ : ∀ g : G, φ g = h * g * h⁻¹ := fun _ => rfl
  have h1 : h * (x ^ i * y ^ j * ⁅x, y⁆ ^ k) * h⁻¹ =
      (x ^ a * y ^ b * ⁅x, y⁆ ^ k₀) ^ i * (x ^ c * y ^ d * ⁅x, y⁆ ^ l₀) ^ j *
        (⁅x, y⁆ ^ μ) ^ k := by
    rw [← hφ, map_mul, map_mul, map_pow, map_pow, map_pow, hφ, hφ, hφ, hhx, hhy, hhz]
  obtain ⟨m₁, hm₁⟩ := normalForm_pow hr hzx hzy hz a b k₀ i
  obtain ⟨m₂, hm₂⟩ := normalForm_pow hr hzx hzy hz c d l₀ j
  rw [h1, hm₁, hm₂, ← pow_mul]
  rw [normalForm_mul hr hzx hzy hz]
  refine ⟨m₁ + m₂ + (r - 1) * (j * c) * (i * b) + μ * k, ?_⟩
  rw [mul_assoc, ← pow_add]
  congr 2
  · rw [show i * a + j * c = a * i + c * j by ring]
  · rw [show i * b + j * d = b * i + d * j by ring]

include hp hx hy hzx hzy hhx hhy hhz in
/-- Conjugation by `h ^ s` maps `Subgroup.closure {x, y}` into itself. -/
theorem conj_pow_mem_closure_pair (s : ℕ) {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) :
    h ^ s * g * (h ^ s)⁻¹ ∈ Subgroup.closure ({x, y} : Set G) := by
  have hr : 0 < r := hp.out.pos
  induction s with
  | zero => simpa using hg
  | succ s ih =>
    obtain ⟨i, j, k, -, -, -, hgs⟩ := mem_closure_normalForm hr hx hy hzx hzy ih
    obtain ⟨m, hm⟩ := conj_normalForm hx hzx hzy hhx hhy hhz i j k
    have hstep : h ^ (s + 1) * g * (h ^ (s + 1))⁻¹ =
        h * (h ^ s * g * (h ^ s)⁻¹) * h⁻¹ := by
      rw [pow_succ']; group
    rw [hstep, hgs, hm]
    have hxQ : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
    have hyQ : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
    have hzQ : ⁅x, y⁆ ∈ Subgroup.closure ({x, y} : Set G) := commutator_mem_closure_pair x y
    exact mul_mem (mul_mem (pow_mem hxQ _) (pow_mem hyQ _)) (pow_mem hzQ _)

end IrreducibleNormalizer

section CubicThree

variable {x y h : G} {a b c d k₀ l₀ μ : ℕ}
  (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz1 : ⁅x, y⁆ ≠ 1)
  (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
  (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = 3 ^ 3)
  (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k₀)
  (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l₀)
  (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
  (hirr : ∀ i j : ZMod 3, (i ≠ 0 ∨ j ≠ 0) →
    (∀ m : ZMod 3, (a * i + c * j : ZMod 3) ≠ m * i ∨ (b * i + d * j : ZMod 3) ≠ m * j) ∧
    (∀ m : ZMod 3,
      (a * (a * i + c * j) + c * (b * i + d * j) : ZMod 3) ≠ m * i ∨
      (b * (a * i + c * j) + d * (b * i + d * j) : ZMod 3) ≠ m * j))

include hx hy hz1 hzx hzy hcard hhx hhy hhz hirr in
/-- If `r = 3` and `h` acts on `Q / Z` with no invariant line under `h` and `h²`, every subgroup
`K ≤ G` not containing `⁅x, y⁆` has index at least `27`. -/
theorem twentySeven_le_index_of_not_mem [Finite G] {K : Subgroup G} (hzK : ⁅x, y⁆ ∉ K) :
    27 ≤ K.index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : ⁅x, y⁆ ^ 3 = 1 := commutator_pow_eq_one hx hzx
  set Q := Subgroup.closure ({x, y} : Set G)
  set KQ : Subgroup Q := K.subgroupOf Q
  have hKZ : ¬ centerSubgroup x y ≤ KQ := by
    intro hle
    exact hzK (hle (Subgroup.mem_zpowers (centerGen x y)))
  have h9 : 9 ≤ KQ.index := sq_le_index_of_not_le hx hy hz1 hzx hzy hcard hKZ
  rcases Nat.lt_or_ge KQ.index 27 with hlt27 | hge27
  · have hKQ_card : Nat.card KQ = 3 := by
      have hmul := KQ.index_mul_card
      rw [hcard] at hmul
      obtain ⟨t, ht⟩ : ∃ t, Nat.card KQ = t := ⟨_, rfl⟩
      rw [ht] at hmul ⊢
      have h9t : 9 * t ≤ KQ.index * t := Nat.mul_le_mul_right t h9
      rcases t with _ | _ | _ | _ | t <;> omega
    have hidx9 : KQ.index = 9 := by
      have hmul := KQ.index_mul_card
      rw [hcard, hKQ_card] at hmul
      omega
    have hKQ_ne_bot : KQ ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hKQ_card]
      decide
    obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKQ_ne_bot
    set u : Q := u₀.1
    have huKQ : u ∈ KQ := u₀.2
    have hu1 : u ≠ 1 := fun h => hu₀1 (Subtype.ext h)
    have hu_not_Z : u ∉ centerSubgroup x y := by
      intro huZ
      apply hKZ
      have hZ_eq : Subgroup.zpowers u = centerSubgroup x y := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huZ)
        rw [card_centerSubgroup (r := 3) hx hz1 hzx, Nat.card_zpowers,
          orderOf_eq_prime (pow_eq_one_of_mem_centerSubgroup hx hzx u huZ) hu1]
      rw [← hZ_eq, Subgroup.zpowers_le]
      exact huKQ
    have hu3 : u₀ ^ 3 = 1 := by
      rw [← hKQ_card]
      exact pow_card_eq_one'
    have hKQ_eq : Subgroup.zpowers u₀ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hKQ_card, Nat.card_zpowers, orderOf_eq_prime hu3 hu₀1]
    have hnot_mem : ∀ s : ℕ, (s = 1 ∨ s = 2) → ∀ q₀ : Q, (q₀ : G) * h ^ s ∉ K := by
      intro s hs q₀ hqh
      have hus_mem : h ^ s * (u : G) * (h ^ s)⁻¹ ∈ Q :=
        conj_pow_mem_closure_pair hx hy hzx hzy hhx hhy hhz s u.2
      let us : Q := ⟨h ^ s * (u : G) * (h ^ s)⁻¹, hus_mem⟩
      have hconjK : (q₀ * us * q₀⁻¹ : Q) ∈ KQ := by
        rw [mem_subgroupOf]
        have h1 : ((q₀ * us * q₀⁻¹ : Q) : G) =
            ((q₀ : G) * h ^ s) * (u : G) * ((q₀ : G) * h ^ s)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, us]; group
        rw [h1]
        exact K.mul_mem (K.mul_mem hqh huKQ) (K.inv_mem hqh)
      have hmem_zpow : (⟨q₀ * us * q₀⁻¹, hconjK⟩ : KQ) ∈ Subgroup.zpowers u₀ := by
        rw [hKQ_eq]
        exact Subgroup.mem_top _
      obtain ⟨n₁, hn₁⟩ := Subgroup.mem_zpowers_iff.mp hmem_zpow
      set m := Int.toNat (n₁ % 3)
      have hm_eq : u₀ ^ n₁ = u₀ ^ m := zpow_eq_pow_mod_toNat (by decide) hu3 n₁
      have hqu_eq : q₀ * us * q₀⁻¹ = u ^ m :=
        congrArg Subtype.val (hn₁.symm.trans hm_eq)
      have hcommZ : ⁅q₀, us⁆⁻¹ ∈ centerSubgroup x y :=
        inv_mem (commutator_mem_centerSubgroup hx hy hzx hzy q₀ us)
      obtain ⟨n₂, hn₂⟩ := Subgroup.mem_zpowers_iff.mp hcommZ
      set n := Int.toNat (n₂ % 3)
      have hn_eq : (centerGen x y) ^ n₂ = (centerGen x y) ^ n :=
        zpow_eq_pow_mod_toNat (by decide) (centerGen_pow_eq_one hx hzx) n₂
      have hcomm_eq : ⁅q₀, us⁆⁻¹ = (centerGen x y) ^ n := hn₂.symm.trans hn_eq
      have hus_eq : us = u ^ m * (centerGen x y) ^ n := by
        have hc := (Subgroup.mem_center_iff.mp (centerSubgroup_le_center hzx hzy hcommZ)
          (q₀ * us * q₀⁻¹)).symm
        calc us = ⁅q₀, us⁆⁻¹ * (q₀ * us * q₀⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = (q₀ * us * q₀⁻¹) * ⁅q₀, us⁆⁻¹ := hc
          _ = u ^ m * (centerGen x y) ^ n := by rw [hqu_eq, hcomm_eq]
      have hus_G : h ^ s * (u : G) * (h ^ s)⁻¹ = (u : G) ^ m * ⁅x, y⁆ ^ n :=
        congrArg Subtype.val hus_eq
      obtain ⟨i, j, k, hi, hj, -, hu_nf⟩ := mem_closure_normalForm (by decide) hx hy hzx hzy u.2
      have hij : (i : ZMod 3) ≠ 0 ∨ (j : ZMod 3) ≠ 0 := by
        by_contra! h0
        apply hu_not_Z
        have hi0 : i = 0 := by
          have := congrArg ZMod.val h0.1
          rwa [ZMod.val_natCast_of_lt hi, ZMod.val_zero] at this
        have hj0 : j = 0 := by
          have := congrArg ZMod.val h0.2
          rwa [ZMod.val_natCast_of_lt hj, ZMod.val_zero] at this
        have hu' : u = (centerGen x y) ^ k := by
          apply Subtype.ext
          change (u : G) = ⁅x, y⁆ ^ k
          rw [hu_nf, hi0, hj0, pow_zero, pow_zero, one_mul, one_mul]
        rw [hu']
        exact pow_mem (Subgroup.mem_zpowers _) k
      obtain ⟨m₀, hm₀⟩ := normalForm_pow (by decide) hzx hzy hz i j k m
      have hrhs : (u : G) ^ m * ⁅x, y⁆ ^ n =
          x ^ (m * i) * y ^ (m * j) * ⁅x, y⁆ ^ (m₀ + n) := by
        rw [hu_nf, hm₀, mul_assoc, ← pow_add]
      obtain ⟨m₁, hm₁⟩ := conj_normalForm hx hzx hzy hhx hhy hhz i j k
      rcases hs with rfl | rfl
      · have hlhs : h ^ 1 * (u : G) * (h ^ 1)⁻¹ =
            x ^ (a * i + c * j) * y ^ (b * i + d * j) * ⁅x, y⁆ ^ m₁ := by
          rw [pow_one, hu_nf, hm₁]
        have heq_nf := hlhs.symm.trans (hus_G.trans hrhs)
        obtain ⟨hi_eq, hj_eq⟩ := eq_zmod_of_normalForm_eq hx hy hzx hzy hcard heq_nf
        push_cast at hi_eq hj_eq
        rcases (hirr (i : ZMod 3) (j : ZMod 3) hij).1 (m : ZMod 3) with hne | hne
        · exact hne hi_eq
        · exact hne hj_eq
      · obtain ⟨m₂, hm₂⟩ :=
          conj_normalForm hx hzx hzy hhx hhy hhz (a * i + c * j) (b * i + d * j) m₁
        have hlhs : h ^ 2 * (u : G) * (h ^ 2)⁻¹ =
            x ^ (a * (a * i + c * j) + c * (b * i + d * j)) *
              y ^ (b * (a * i + c * j) + d * (b * i + d * j)) * ⁅x, y⁆ ^ m₂ := by
          have hsq : h ^ 2 * (u : G) * (h ^ 2)⁻¹ = h * (h * (u : G) * h⁻¹) * h⁻¹ := by
            rw [sq]; group
          rw [hsq, hu_nf, hm₁, hm₂]
        have heq_nf := hlhs.symm.trans (hus_G.trans hrhs)
        obtain ⟨hi_eq, hj_eq⟩ := eq_zmod_of_normalForm_eq hx hy hzx hzy hcard heq_nf
        push_cast at hi_eq hj_eq
        rcases (hirr (i : ZMod 3) (j : ZMod 3) hij).2 (m : ZMod 3) with hne | hne
        · exact hne hi_eq
        · exact hne hj_eq
    let Φ : Fin 3 × (Q ⧸ KQ) → G ⧸ K := fun p =>
      Quotient.liftOn p.2 (fun q : Q => ((h ^ (p.1 : ℕ) * (q : G) : G) : G ⧸ K)) fun q₁ q₂ hq => by
        have hq' : (QuotientGroup.mk q₁ : Q ⧸ KQ) = QuotientGroup.mk q₂ := Quotient.sound hq
        rw [QuotientGroup.eq, mem_subgroupOf] at hq'
        apply QuotientGroup.eq.mpr
        have h1 : (h ^ (p.1 : ℕ) * (q₁ : G))⁻¹ * (h ^ (p.1 : ℕ) * (q₂ : G)) =
            (q₁ : G)⁻¹ * (q₂ : G) := by group
        rw [h1]
        exact hq'
    have hstep_lt : ∀ (s₁ s₂ : Fin 3) (q₁ q₂ : Q),
        s₁ < s₂ → Φ (s₁, QuotientGroup.mk q₁) = Φ (s₂, QuotientGroup.mk q₂) → False := by
      intro s₁ s₂ q₁ q₂ hlt heq
      have hk : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₂ : ℕ) * (q₂ : G)) ∈ K :=
        QuotientGroup.eq.mp heq
      set s := (s₂ : ℕ) - (s₁ : ℕ)
      have hs12 : s = 1 ∨ s = 2 := by omega
      have hs_add : (s₂ : ℕ) = (s₁ : ℕ) + s := by omega
      have hq₂s : h ^ s * (q₂ : G) * (h ^ s)⁻¹ ∈ Q :=
        conj_pow_mem_closure_pair hx hy hzx hzy hhx hhy hhz s q₂.2
      let q₀ : Q := q₁⁻¹ * ⟨h ^ s * (q₂ : G) * (h ^ s)⁻¹, hq₂s⟩
      have hq₀h : (q₀ : G) * h ^ s =
          (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₂ : ℕ) * (q₂ : G)) := by
        simp only [q₀, Subgroup.coe_mul, Subgroup.coe_inv, hs_add, pow_add]
        group
      exact hnot_mem s hs12 q₀ (hq₀h.symm ▸ hk)
    have hΦ : Function.Injective Φ := by
      rintro ⟨s₁, a₁⟩ ⟨s₂, a₂⟩ heq
      induction a₁ using QuotientGroup.induction_on with | H q₁ =>
      induction a₂ using QuotientGroup.induction_on with | H q₂ =>
      rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
      · exact False.elim (hstep_lt s₁ s₂ q₁ q₂ hlt heq)
      · refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, mem_subgroupOf]
        have hk : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₁ : ℕ) * (q₂ : G)) ∈ K :=
          QuotientGroup.eq.mp heq
        have h1 : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₁ : ℕ) * (q₂ : G)) =
            (q₁ : G)⁻¹ * (q₂ : G) := by group
        rwa [h1] at hk
      · exact False.elim (hstep_lt s₂ s₁ q₂ q₁ hgt heq.symm)
    have hcard_dom : Nat.card (Fin 3 × (Q ⧸ KQ)) = 27 := by
      rw [Nat.card_prod, Nat.card_fin, ← Subgroup.index, hidx9]
    rw [Subgroup.index, ← hcard_dom]
    exact Nat.card_le_card_of_injective Φ hΦ
  · let ι : Q ⧸ KQ → G ⧸ K :=
      Quotient.lift (fun q : Q => ((q : G) : G ⧸ K)) fun q₁ q₂ hq => by
        have hq' : (QuotientGroup.mk q₁ : Q ⧸ KQ) = QuotientGroup.mk q₂ := Quotient.sound hq
        rw [QuotientGroup.eq, mem_subgroupOf] at hq'
        exact QuotientGroup.eq.mpr hq'
    have hι : Function.Injective ι := by
      intro a₁ a₂ ha
      induction a₁ using QuotientGroup.induction_on with | H q₁ =>
      induction a₂ using QuotientGroup.induction_on with | H q₂ =>
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact QuotientGroup.eq.mp ha
    exact hge27.trans (Nat.card_le_card_of_injective ι hι)

include hx hy hz1 hzx hzy hcard hhx hhy hhz hirr in
/-- If `r = 3`, `h` acts on `Q / Z` with no invariant line under `h` and `h²`, and `G` is
isomorphic to a finite simple group `S`, then every proper subgroup `H ≠ ⊤` of `S` has index at
least `27`. -/
theorem twentySeven_le_index_of_ne_top {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* G) {H : Subgroup S} (hH : H ≠ ⊤) :
    27 ≤ H.index := by
  have : Finite G := Finite.of_equiv S e.toEquiv
  have hZne : Subgroup.zpowers ⁅x, y⁆ ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
  exact le_index_of_injective_of_forall_not_le_index hH e.symm.toMonoidHom e.symm.injective hZne
    fun K hZK =>
      twentySeven_le_index_of_not_mem hx hy hz1 hzx hzy hcard hhx hhy hhz hirr
        (fun hzK => hZK (Subgroup.zpowers_le.mpr hzK))

end CubicThree

section CubicTwoMulSq

variable {x y h : G} {r a b c d k₀ l₀ μ : ℕ} [hp : Fact r.Prime]
  (hx : x ^ r = 1) (hy : y ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1)
  (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
  (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 3)
  (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k₀)
  (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l₀)
  (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
  (hirr : ∀ i j : ZMod r, (i ≠ 0 ∨ j ≠ 0) →
    ∀ m : ZMod r, (a * i + c * j : ZMod r) ≠ m * i ∨ (b * i + d * j : ZMod r) ≠ m * j)

include hp hx hy hzx hzy hcard hhx hhy hhz in
private theorem two_mul_sq_le_index_of_not_eig [Finite G] {K : Subgroup G}
    (hidx_sq : (K.subgroupOf (Subgroup.closure ({x, y} : Set G))).index = r ^ 2)
    {u₀ : K.subgroupOf (Subgroup.closure ({x, y} : Set G))}
    (hur : u₀ ^ r = 1) (hKQ_eq : Subgroup.zpowers u₀ = ⊤)
    {i j k : ℕ} (hu_nf : (u₀.1 : G) = x ^ i * y ^ j * ⁅x, y⁆ ^ k)
    (hne_eig : ∀ m : ZMod r,
      (a * (i : ZMod r) + c * (j : ZMod r) : ZMod r) ≠ m * (i : ZMod r) ∨
      (b * (i : ZMod r) + d * (j : ZMod r) : ZMod r) ≠ m * (j : ZMod r)) :
    2 * r ^ 2 ≤ K.index := by
  have hr : 0 < r := hp.out.pos
  have hz : ⁅x, y⁆ ^ r = 1 := commutator_pow_eq_one hx hzx
  let Q := Subgroup.closure ({x, y} : Set G)
  let KQ : Subgroup Q := K.subgroupOf Q
  let u : Q := u₀.1
  have huKQ : u ∈ KQ := u₀.2
  have hnot_mem : ∀ q₀ : Q, (q₀ : G) * h ∉ K := by
    intro q₀ hqh
    have hu1_mem : h * (u : G) * h⁻¹ ∈ Q := by
      simpa using conj_pow_mem_closure_pair hx hy hzx hzy hhx hhy hhz 1 u.2
    let u1 : Q := ⟨h * (u : G) * h⁻¹, hu1_mem⟩
    have hconjK : (q₀ * u1 * q₀⁻¹ : Q) ∈ KQ := by
      rw [mem_subgroupOf]
      have h1 : ((q₀ * u1 * q₀⁻¹ : Q) : G) =
          ((q₀ : G) * h) * (u : G) * ((q₀ : G) * h)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, u1]; group
      rw [h1]
      exact K.mul_mem (K.mul_mem hqh huKQ) (K.inv_mem hqh)
    have hmem_zpow : (⟨q₀ * u1 * q₀⁻¹, hconjK⟩ : KQ) ∈ Subgroup.zpowers u₀ := by
      rw [hKQ_eq]
      exact Subgroup.mem_top _
    obtain ⟨n₁, hn₁⟩ := Subgroup.mem_zpowers_iff.mp hmem_zpow
    set m := Int.toNat (n₁ % r)
    have hm_eq : u₀ ^ n₁ = u₀ ^ m := zpow_eq_pow_mod_toNat hr hur n₁
    have hqu_eq : q₀ * u1 * q₀⁻¹ = u ^ m :=
      congrArg Subtype.val (hn₁.symm.trans hm_eq)
    have hcommZ : ⁅q₀, u1⁆⁻¹ ∈ centerSubgroup x y :=
      inv_mem (commutator_mem_centerSubgroup hx hy hzx hzy q₀ u1)
    obtain ⟨n₂, hn₂⟩ := Subgroup.mem_zpowers_iff.mp hcommZ
    set n := Int.toNat (n₂ % r)
    have hn_eq : (centerGen x y) ^ n₂ = (centerGen x y) ^ n :=
      zpow_eq_pow_mod_toNat hr (centerGen_pow_eq_one hx hzx) n₂
    have hcomm_eq : ⁅q₀, u1⁆⁻¹ = (centerGen x y) ^ n := hn₂.symm.trans hn_eq
    have hu1_eq : u1 = u ^ m * (centerGen x y) ^ n := by
      have hc := (Subgroup.mem_center_iff.mp (centerSubgroup_le_center hzx hzy hcommZ)
        (q₀ * u1 * q₀⁻¹)).symm
      calc u1 = ⁅q₀, u1⁆⁻¹ * (q₀ * u1 * q₀⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = (q₀ * u1 * q₀⁻¹) * ⁅q₀, u1⁆⁻¹ := hc
        _ = u ^ m * (centerGen x y) ^ n := by rw [hqu_eq, hcomm_eq]
    have hu1_G : h * (u : G) * h⁻¹ = (u : G) ^ m * ⁅x, y⁆ ^ n :=
      congrArg Subtype.val hu1_eq
    obtain ⟨m₀, hm₀⟩ := normalForm_pow hr hzx hzy hz i j k m
    have hrhs : (u : G) ^ m * ⁅x, y⁆ ^ n =
        x ^ (m * i) * y ^ (m * j) * ⁅x, y⁆ ^ (m₀ + n) := by
      rw [hu_nf, hm₀, mul_assoc, ← pow_add]
    obtain ⟨m₁, hm₁⟩ := conj_normalForm hx hzx hzy hhx hhy hhz i j k
    have hlhs : h * (u : G) * h⁻¹ =
        x ^ (a * i + c * j) * y ^ (b * i + d * j) * ⁅x, y⁆ ^ m₁ := by
      rw [hu_nf, hm₁]
    have heq_nf := hlhs.symm.trans (hu1_G.trans hrhs)
    obtain ⟨hi_eq, hj_eq⟩ := eq_zmod_of_normalForm_eq hx hy hzx hzy hcard heq_nf
    push_cast at hi_eq hj_eq
    rcases hne_eig (m : ZMod r) with hne | hne
    · exact hne hi_eq
    · exact hne hj_eq
  let Φ : Fin 2 × (Q ⧸ KQ) → G ⧸ K := fun p =>
    Quotient.liftOn p.2 (fun q : Q => ((h ^ (p.1 : ℕ) * (q : G) : G) : G ⧸ K)) fun q₁ q₂ hq => by
      have hq' : (QuotientGroup.mk q₁ : Q ⧸ KQ) = QuotientGroup.mk q₂ := Quotient.sound hq
      rw [QuotientGroup.eq, mem_subgroupOf] at hq'
      apply QuotientGroup.eq.mpr
      have h1 : (h ^ (p.1 : ℕ) * (q₁ : G))⁻¹ * (h ^ (p.1 : ℕ) * (q₂ : G)) =
          (q₁ : G)⁻¹ * (q₂ : G) := by group
      rw [h1]
      exact hq'
  have hstep_lt : ∀ (s₁ s₂ : Fin 2) (q₁ q₂ : Q),
      s₁ < s₂ → Φ (s₁, QuotientGroup.mk q₁) = Φ (s₂, QuotientGroup.mk q₂) → False := by
    intro s₁ s₂ q₁ q₂ hlt heq
    have hk : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₂ : ℕ) * (q₂ : G)) ∈ K :=
      QuotientGroup.eq.mp heq
    have hs₁ : (s₁ : ℕ) = 0 := by omega
    have hs₂ : (s₂ : ℕ) = 1 := by omega
    have hq₂1 : h * (q₂ : G) * h⁻¹ ∈ Q := by
      simpa using conj_pow_mem_closure_pair hx hy hzx hzy hhx hhy hhz 1 q₂.2
    let q₀ : Q := q₁⁻¹ * ⟨h * (q₂ : G) * h⁻¹, hq₂1⟩
    have hq₀h : (q₀ : G) * h =
        (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₂ : ℕ) * (q₂ : G)) := by
      simp only [q₀, Subgroup.coe_mul, Subgroup.coe_inv, hs₁, hs₂, pow_zero, pow_one]
      group
    exact hnot_mem q₀ (hq₀h.symm ▸ hk)
  have hΦ : Function.Injective Φ := by
    rintro ⟨s₁, a₁⟩ ⟨s₂, a₂⟩ heq
    induction a₁ using QuotientGroup.induction_on with | H q₁ =>
    induction a₂ using QuotientGroup.induction_on with | H q₂ =>
    rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
    · exact False.elim (hstep_lt s₁ s₂ q₁ q₂ hlt heq)
    · refine Prod.ext rfl ?_
      rw [QuotientGroup.eq, mem_subgroupOf]
      have hk : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₁ : ℕ) * (q₂ : G)) ∈ K :=
        QuotientGroup.eq.mp heq
      have h1 : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₁ : ℕ) * (q₂ : G)) =
          (q₁ : G)⁻¹ * (q₂ : G) := by group
      rwa [h1] at hk
    · exact False.elim (hstep_lt s₂ s₁ q₂ q₁ hgt heq.symm)
  have hcard_dom : Nat.card (Fin 2 × (Q ⧸ KQ)) = 2 * r ^ 2 := by
    rw [Nat.card_prod, Nat.card_fin, ← Subgroup.index, hidx_sq]
  rw [Subgroup.index, ← hcard_dom]
  exact Nat.card_le_card_of_injective Φ hΦ

include hp hx hy hz1 hzx hzy hcard in
/-- If `h₁, h₂` normalize `Q = Subgroup.closure {x, y}` and act on `Q / Z ≅ (ZMod r)²` with no
common invariant line, every subgroup `K ≤ G` not containing `⁅x, y⁆` has index at least
`2 * r ^ 2`. -/
theorem two_mul_sq_le_index_of_pair_of_not_mem [Finite G]
    {h₂ : G} {a₂ b₂ c₂ d₂ k₂ l₂ μ₂ : ℕ}
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k₀)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l₀)
    (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hh₂x : h₂ * x * h₂⁻¹ = x ^ a₂ * y ^ b₂ * ⁅x, y⁆ ^ k₂)
    (hh₂y : h₂ * y * h₂⁻¹ = x ^ c₂ * y ^ d₂ * ⁅x, y⁆ ^ l₂)
    (hh₂z : h₂ * ⁅x, y⁆ * h₂⁻¹ = ⁅x, y⁆ ^ μ₂)
    (hirr₂ : ∀ i j : ZMod r, (i ≠ 0 ∨ j ≠ 0) →
      (∀ m : ZMod r, (a * i + c * j : ZMod r) ≠ m * i ∨ (b * i + d * j : ZMod r) ≠ m * j) ∨
      (∀ m : ZMod r, (a₂ * i + c₂ * j : ZMod r) ≠ m * i ∨ (b₂ * i + d₂ * j : ZMod r) ≠ m * j))
    {K : Subgroup G} (hzK : ⁅x, y⁆ ∉ K) :
    2 * r ^ 2 ≤ K.index := by
  have hr : 0 < r := hp.out.pos
  have hr1 : 1 < r := hp.out.one_lt
  have hr2 : 2 ≤ r := hp.out.two_le
  set Q := Subgroup.closure ({x, y} : Set G)
  set KQ : Subgroup Q := K.subgroupOf Q
  have hKZ : ¬ centerSubgroup x y ≤ KQ := by
    intro hle
    exact hzK (hle (Subgroup.mem_zpowers (centerGen x y)))
  have hsq : r ^ 2 ≤ KQ.index := sq_le_index_of_not_le hx hy hz1 hzx hzy hcard hKZ
  have hmul_card : KQ.index * Nat.card KQ = r ^ 3 := by
    rw [KQ.index_mul_card, hcard]
  rcases eq_or_ne (Nat.card KQ) 1 with hcard1 | hcard_ne1
  · have hidx_cube : KQ.index = r ^ 3 := by
      rw [hcard1, mul_one] at hmul_card
      exact hmul_card
    have h2le : 2 * r ^ 2 ≤ KQ.index := by
      rw [hidx_cube, show r ^ 3 = r * r ^ 2 by ring]
      exact Nat.mul_le_mul_right (r ^ 2) hr2
    let ι : Q ⧸ KQ → G ⧸ K :=
      Quotient.lift (fun q : Q => ((q : G) : G ⧸ K)) fun q₁ q₂ hq => by
        have hq' : (QuotientGroup.mk q₁ : Q ⧸ KQ) = QuotientGroup.mk q₂ := Quotient.sound hq
        rw [QuotientGroup.eq, mem_subgroupOf] at hq'
        exact QuotientGroup.eq.mpr hq'
    have hι : Function.Injective ι := by
      intro a₁ a₂ ha
      induction a₁ using QuotientGroup.induction_on with | H q₁ =>
      induction a₂ using QuotientGroup.induction_on with | H q₂ =>
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact QuotientGroup.eq.mp ha
    exact h2le.trans (Nat.card_le_card_of_injective ι hι)
  · have hcard_pos : 0 < Nat.card KQ := Nat.card_pos
    have hmin_prime : (Nat.card KQ).minFac.Prime := Nat.minFac_prime hcard_ne1
    have hdvd_r3 : (Nat.card KQ).minFac ∣ r ^ 3 :=
      dvd_trans (Nat.minFac_dvd _) ⟨KQ.index, by rw [← hmul_card, mul_comm]⟩
    have hdvd_r : (Nat.card KQ).minFac ∣ r := hmin_prime.dvd_of_dvd_pow hdvd_r3
    have hmin_eq : (Nat.card KQ).minFac = r :=
      (Nat.dvd_prime hp.out).mp hdvd_r |>.resolve_left hmin_prime.ne_one
    have hr_le_card : r ≤ Nat.card KQ :=
      Nat.le_of_dvd hcard_pos (hmin_eq ▸ Nat.minFac_dvd _)
    have hidx_sq : KQ.index = r ^ 2 := by
      have h1 : r ^ 2 * r ≤ KQ.index * r := Nat.mul_le_mul_right r hsq
      have h2 : KQ.index * r ≤ KQ.index * Nat.card KQ := Nat.mul_le_mul_left KQ.index hr_le_card
      rw [hmul_card, show r ^ 3 = r ^ 2 * r by ring] at h2
      exact Nat.eq_of_mul_eq_mul_right hr (le_antisymm h2 h1)
    have hKQ_card : Nat.card KQ = r := by
      rw [hidx_sq, show r ^ 3 = r ^ 2 * r by ring] at hmul_card
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hr 2) hmul_card
    have hKQ_ne_bot : KQ ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hKQ_card]
      exact hr1
    obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKQ_ne_bot
    set u : Q := u₀.1
    have huKQ : u ∈ KQ := u₀.2
    have hu1 : u ≠ 1 := fun h => hu₀1 (Subtype.ext h)
    have hu_not_Z : u ∉ centerSubgroup x y := by
      intro huZ
      apply hKZ
      have hZ_eq : Subgroup.zpowers u = centerSubgroup x y := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huZ)
        rw [card_centerSubgroup hx hz1 hzx, Nat.card_zpowers,
          orderOf_eq_prime (pow_eq_one_of_mem_centerSubgroup hx hzx u huZ) hu1]
      rw [← hZ_eq, Subgroup.zpowers_le]
      exact huKQ
    have hur : u₀ ^ r = 1 := by
      rw [← hKQ_card]
      exact pow_card_eq_one'
    have hKQ_eq : Subgroup.zpowers u₀ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hKQ_card, Nat.card_zpowers, orderOf_eq_prime hur hu₀1]
    obtain ⟨i, j, k, hi, hj, -, hu_nf⟩ := mem_closure_normalForm hr hx hy hzx hzy u.2
    have hij : (i : ZMod r) ≠ 0 ∨ (j : ZMod r) ≠ 0 := by
      by_contra! h0
      apply hu_not_Z
      have hi0 : i = 0 := by
        have := congrArg ZMod.val h0.1
        rwa [ZMod.val_natCast_of_lt hi, ZMod.val_zero] at this
      have hj0 : j = 0 := by
        have := congrArg ZMod.val h0.2
        rwa [ZMod.val_natCast_of_lt hj, ZMod.val_zero] at this
      have hu' : u = (centerGen x y) ^ k := by
        apply Subtype.ext
        change (u : G) = ⁅x, y⁆ ^ k
        rw [hu_nf, hi0, hj0, pow_zero, pow_zero, one_mul, one_mul]
      rw [hu']
      exact pow_mem (Subgroup.mem_zpowers _) k
    rcases hirr₂ (i : ZMod r) (j : ZMod r) hij with h₁_eig | h₂_eig
    · exact two_mul_sq_le_index_of_not_eig hx hy hzx hzy hcard hhx hhy hhz
        hidx_sq hur hKQ_eq hu_nf h₁_eig
    · exact two_mul_sq_le_index_of_not_eig hx hy hzx hzy hcard hh₂x hh₂y hh₂z
        hidx_sq hur hKQ_eq hu_nf h₂_eig

include hp hx hy hz1 hzx hzy hcard in
/-- If `h, h₂` normalize `Q = Subgroup.closure {x, y}` and act on `Q / Z ≅ (ZMod r)²` with no
common invariant line, and `G` is isomorphic to a finite simple group `S`, then every proper
subgroup `H ≠ ⊤` of `S` has index at least `2 * r ^ 2`. -/
theorem two_mul_sq_le_index_of_pair_of_ne_top
    {h₂ : G} {a₂ b₂ c₂ d₂ k₂ l₂ μ₂ : ℕ}
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k₀)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l₀)
    (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
    (hh₂x : h₂ * x * h₂⁻¹ = x ^ a₂ * y ^ b₂ * ⁅x, y⁆ ^ k₂)
    (hh₂y : h₂ * y * h₂⁻¹ = x ^ c₂ * y ^ d₂ * ⁅x, y⁆ ^ l₂)
    (hh₂z : h₂ * ⁅x, y⁆ * h₂⁻¹ = ⁅x, y⁆ ^ μ₂)
    (hirr₂ : ∀ i j : ZMod r, (i ≠ 0 ∨ j ≠ 0) →
      (∀ m : ZMod r, (a * i + c * j : ZMod r) ≠ m * i ∨ (b * i + d * j : ZMod r) ≠ m * j) ∨
      (∀ m : ZMod r, (a₂ * i + c₂ * j : ZMod r) ≠ m * i ∨ (b₂ * i + d₂ * j : ZMod r) ≠ m * j))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* G) {H : Subgroup S} (hH : H ≠ ⊤) :
    2 * r ^ 2 ≤ H.index := by
  have : Finite G := Finite.of_equiv S e.toEquiv
  have hZne : Subgroup.zpowers ⁅x, y⁆ ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
  exact le_index_of_injective_of_forall_not_le_index hH e.symm.toMonoidHom e.symm.injective hZne
    fun K hZK =>
      two_mul_sq_le_index_of_pair_of_not_mem hx hy hz1 hzx hzy hcard hhx hhy hhz hh₂x hh₂y hh₂z
        hirr₂ (fun hzK => hZK (Subgroup.zpowers_le.mpr hzK))

include hp hx hy hz1 hzx hzy hcard hhx hhy hhz hirr in
/-- If `h` normalizes `Q = Subgroup.closure {x, y}` and acts on `Q / Z ≅ (ZMod r)²` with no
invariant line, every subgroup `K ≤ G` not containing `⁅x, y⁆` has index at least `2 * r ^ 2`. -/
theorem two_mul_sq_le_index_of_not_mem [Finite G] {K : Subgroup G} (hzK : ⁅x, y⁆ ∉ K) :
    2 * r ^ 2 ≤ K.index :=
  two_mul_sq_le_index_of_pair_of_not_mem hx hy hz1 hzx hzy hcard hhx hhy hhz hhx hhy hhz
    (fun i j hij => Or.inl (hirr i j hij)) hzK

include hp hx hy hz1 hzx hzy hcard hhx hhy hhz hirr in
/-- If `h` normalizes `Q = Subgroup.closure {x, y}` and acts on `Q / Z ≅ (ZMod r)²` with no
invariant line, and `G` is isomorphic to a finite simple group `S`, then every proper subgroup
`H ≠ ⊤` of `S` has index at least `2 * r ^ 2`. -/
theorem two_mul_sq_le_index_of_ne_top {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* G) {H : Subgroup S} (hH : H ≠ ⊤) :
    2 * r ^ 2 ≤ H.index :=
  two_mul_sq_le_index_of_pair_of_ne_top hx hy hz1 hzx hzy hcard hhx hhy hhz hhx hhy hhz
    (fun i j hij => Or.inl (hirr i j hij)) e hH

end CubicTwoMulSq

section CubicThreeMulSq

variable {x y h : G} {r a b c d k₀ l₀ μ : ℕ} [hp : Fact r.Prime]
  (hr3 : 3 ≤ r)
  (hx : x ^ r = 1) (hy : y ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1)
  (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
  (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 3)
  (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k₀)
  (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l₀)
  (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ)
  (hirr₃ : ∀ i j : ZMod r, (i ≠ 0 ∨ j ≠ 0) →
    (∀ m : ZMod r, (a * i + c * j : ZMod r) ≠ m * i ∨ (b * i + d * j : ZMod r) ≠ m * j) ∧
    (∀ m : ZMod r,
      (a * (a * i + c * j) + c * (b * i + d * j) : ZMod r) ≠ m * i ∨
      (b * (a * i + c * j) + d * (b * i + d * j) : ZMod r) ≠ m * j))

include hp hr3 hx hy hz1 hzx hzy hcard hhx hhy hhz hirr₃ in
/-- If `3 ≤ r` and `h` acts on `Q / Z ≅ (ZMod r)²` with no invariant line under `h` and `h²`,
every subgroup `K ≤ G` not containing `⁅x, y⁆` has index at least `3 * r ^ 2`. -/
theorem three_mul_sq_le_index_of_not_mem [Finite G] {K : Subgroup G} (hzK : ⁅x, y⁆ ∉ K) :
    3 * r ^ 2 ≤ K.index := by
  have hr : 0 < r := hp.out.pos
  have hr1 : 1 < r := hp.out.one_lt
  have hz : ⁅x, y⁆ ^ r = 1 := commutator_pow_eq_one hx hzx
  set Q := Subgroup.closure ({x, y} : Set G)
  set KQ : Subgroup Q := K.subgroupOf Q
  have hKZ : ¬ centerSubgroup x y ≤ KQ := by
    intro hle
    exact hzK (hle (Subgroup.mem_zpowers (centerGen x y)))
  have hsq : r ^ 2 ≤ KQ.index := sq_le_index_of_not_le hx hy hz1 hzx hzy hcard hKZ
  have hmul_card : KQ.index * Nat.card KQ = r ^ 3 := by
    rw [KQ.index_mul_card, hcard]
  rcases eq_or_ne (Nat.card KQ) 1 with hcard1 | hcard_ne1
  · have hidx_cube : KQ.index = r ^ 3 := by
      rw [hcard1, mul_one] at hmul_card
      exact hmul_card
    have h3le : 3 * r ^ 2 ≤ KQ.index := by
      rw [hidx_cube, show r ^ 3 = r * r ^ 2 by ring]
      exact Nat.mul_le_mul_right (r ^ 2) hr3
    let ι : Q ⧸ KQ → G ⧸ K :=
      Quotient.lift (fun q : Q => ((q : G) : G ⧸ K)) fun q₁ q₂ hq => by
        have hq' : (QuotientGroup.mk q₁ : Q ⧸ KQ) = QuotientGroup.mk q₂ := Quotient.sound hq
        rw [QuotientGroup.eq, mem_subgroupOf] at hq'
        exact QuotientGroup.eq.mpr hq'
    have hι : Function.Injective ι := by
      intro a₁ a₂ ha
      induction a₁ using QuotientGroup.induction_on with | H q₁ =>
      induction a₂ using QuotientGroup.induction_on with | H q₂ =>
      rw [QuotientGroup.eq, mem_subgroupOf]
      exact QuotientGroup.eq.mp ha
    exact h3le.trans (Nat.card_le_card_of_injective ι hι)
  · have hcard_pos : 0 < Nat.card KQ := Nat.card_pos
    have hmin_prime : (Nat.card KQ).minFac.Prime := Nat.minFac_prime hcard_ne1
    have hdvd_r3 : (Nat.card KQ).minFac ∣ r ^ 3 :=
      dvd_trans (Nat.minFac_dvd _) ⟨KQ.index, by rw [← hmul_card, mul_comm]⟩
    have hdvd_r : (Nat.card KQ).minFac ∣ r := hmin_prime.dvd_of_dvd_pow hdvd_r3
    have hmin_eq : (Nat.card KQ).minFac = r :=
      (Nat.dvd_prime hp.out).mp hdvd_r |>.resolve_left hmin_prime.ne_one
    have hr_le_card : r ≤ Nat.card KQ :=
      Nat.le_of_dvd hcard_pos (hmin_eq ▸ Nat.minFac_dvd _)
    have hidx_sq : KQ.index = r ^ 2 := by
      have h1 : r ^ 2 * r ≤ KQ.index * r := Nat.mul_le_mul_right r hsq
      have h2 : KQ.index * r ≤ KQ.index * Nat.card KQ := Nat.mul_le_mul_left KQ.index hr_le_card
      rw [hmul_card, show r ^ 3 = r ^ 2 * r by ring] at h2
      exact Nat.eq_of_mul_eq_mul_right hr (le_antisymm h2 h1)
    have hKQ_card : Nat.card KQ = r := by
      rw [hidx_sq, show r ^ 3 = r ^ 2 * r by ring] at hmul_card
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hr 2) hmul_card
    have hKQ_ne_bot : KQ ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hKQ_card]
      exact hr1
    obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKQ_ne_bot
    set u : Q := u₀.1
    have huKQ : u ∈ KQ := u₀.2
    have hu1 : u ≠ 1 := fun h => hu₀1 (Subtype.ext h)
    have hu_not_Z : u ∉ centerSubgroup x y := by
      intro huZ
      apply hKZ
      have hZ_eq : Subgroup.zpowers u = centerSubgroup x y := by
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huZ)
        rw [card_centerSubgroup hx hz1 hzx, Nat.card_zpowers,
          orderOf_eq_prime (pow_eq_one_of_mem_centerSubgroup hx hzx u huZ) hu1]
      rw [← hZ_eq, Subgroup.zpowers_le]
      exact huKQ
    have hur : u₀ ^ r = 1 := by
      rw [← hKQ_card]
      exact pow_card_eq_one'
    have hKQ_eq : Subgroup.zpowers u₀ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hKQ_card, Nat.card_zpowers, orderOf_eq_prime hur hu₀1]
    obtain ⟨i, j, k, hi, hj, -, hu_nf⟩ := mem_closure_normalForm hr hx hy hzx hzy u.2
    have hij : (i : ZMod r) ≠ 0 ∨ (j : ZMod r) ≠ 0 := by
      by_contra! h0
      apply hu_not_Z
      have hi0 : i = 0 := by
        have := congrArg ZMod.val h0.1
        rwa [ZMod.val_natCast_of_lt hi, ZMod.val_zero] at this
      have hj0 : j = 0 := by
        have := congrArg ZMod.val h0.2
        rwa [ZMod.val_natCast_of_lt hj, ZMod.val_zero] at this
      have hu' : u = (centerGen x y) ^ k := by
        apply Subtype.ext
        change (u : G) = ⁅x, y⁆ ^ k
        rw [hu_nf, hi0, hj0, pow_zero, pow_zero, one_mul, one_mul]
      rw [hu']
      exact pow_mem (Subgroup.mem_zpowers _) k
    have hnot_mem : ∀ s : ℕ, (s = 1 ∨ s = 2) → ∀ q₀ : Q, (q₀ : G) * h ^ s ∉ K := by
      intro s hs q₀ hqh
      have hus_mem : h ^ s * (u : G) * (h ^ s)⁻¹ ∈ Q :=
        conj_pow_mem_closure_pair hx hy hzx hzy hhx hhy hhz s u.2
      let us : Q := ⟨h ^ s * (u : G) * (h ^ s)⁻¹, hus_mem⟩
      have hconjK : (q₀ * us * q₀⁻¹ : Q) ∈ KQ := by
        rw [mem_subgroupOf]
        have h1 : ((q₀ * us * q₀⁻¹ : Q) : G) =
            ((q₀ : G) * h ^ s) * (u : G) * ((q₀ : G) * h ^ s)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, us]; group
        rw [h1]
        exact K.mul_mem (K.mul_mem hqh huKQ) (K.inv_mem hqh)
      have hmem_zpow : (⟨q₀ * us * q₀⁻¹, hconjK⟩ : KQ) ∈ Subgroup.zpowers u₀ := by
        rw [hKQ_eq]
        exact Subgroup.mem_top _
      obtain ⟨n₁, hn₁⟩ := Subgroup.mem_zpowers_iff.mp hmem_zpow
      set m := Int.toNat (n₁ % r)
      have hm_eq : u₀ ^ n₁ = u₀ ^ m := zpow_eq_pow_mod_toNat hr hur n₁
      have hqu_eq : q₀ * us * q₀⁻¹ = u ^ m :=
        congrArg Subtype.val (hn₁.symm.trans hm_eq)
      have hcommZ : ⁅q₀, us⁆⁻¹ ∈ centerSubgroup x y :=
        inv_mem (commutator_mem_centerSubgroup hx hy hzx hzy q₀ us)
      obtain ⟨n₂, hn₂⟩ := Subgroup.mem_zpowers_iff.mp hcommZ
      set n := Int.toNat (n₂ % r)
      have hn_eq : (centerGen x y) ^ n₂ = (centerGen x y) ^ n :=
        zpow_eq_pow_mod_toNat hr (centerGen_pow_eq_one hx hzx) n₂
      have hcomm_eq : ⁅q₀, us⁆⁻¹ = (centerGen x y) ^ n := hn₂.symm.trans hn_eq
      have hus_eq : us = u ^ m * (centerGen x y) ^ n := by
        have hc := (Subgroup.mem_center_iff.mp (centerSubgroup_le_center hzx hzy hcommZ)
          (q₀ * us * q₀⁻¹)).symm
        calc us = ⁅q₀, us⁆⁻¹ * (q₀ * us * q₀⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = (q₀ * us * q₀⁻¹) * ⁅q₀, us⁆⁻¹ := hc
          _ = u ^ m * (centerGen x y) ^ n := by rw [hqu_eq, hcomm_eq]
      have hus_G : h ^ s * (u : G) * (h ^ s)⁻¹ = (u : G) ^ m * ⁅x, y⁆ ^ n :=
        congrArg Subtype.val hus_eq
      obtain ⟨m₀, hm₀⟩ := normalForm_pow hr hzx hzy hz i j k m
      have hrhs : (u : G) ^ m * ⁅x, y⁆ ^ n =
          x ^ (m * i) * y ^ (m * j) * ⁅x, y⁆ ^ (m₀ + n) := by
        rw [hu_nf, hm₀, mul_assoc, ← pow_add]
      obtain ⟨m₁, hm₁⟩ := conj_normalForm hx hzx hzy hhx hhy hhz i j k
      rcases hs with rfl | rfl
      · have hlhs : h ^ 1 * (u : G) * (h ^ 1)⁻¹ =
            x ^ (a * i + c * j) * y ^ (b * i + d * j) * ⁅x, y⁆ ^ m₁ := by
          rw [pow_one, hu_nf, hm₁]
        have heq_nf := hlhs.symm.trans (hus_G.trans hrhs)
        obtain ⟨hi_eq, hj_eq⟩ := eq_zmod_of_normalForm_eq hx hy hzx hzy hcard heq_nf
        push_cast at hi_eq hj_eq
        rcases (hirr₃ (i : ZMod r) (j : ZMod r) hij).1 (m : ZMod r) with hne | hne
        · exact hne hi_eq
        · exact hne hj_eq
      · obtain ⟨m₂, hm₂⟩ :=
          conj_normalForm hx hzx hzy hhx hhy hhz (a * i + c * j) (b * i + d * j) m₁
        have hlhs : h ^ 2 * (u : G) * (h ^ 2)⁻¹ =
            x ^ (a * (a * i + c * j) + c * (b * i + d * j)) *
              y ^ (b * (a * i + c * j) + d * (b * i + d * j)) * ⁅x, y⁆ ^ m₂ := by
          have hsq : h ^ 2 * (u : G) * (h ^ 2)⁻¹ = h * (h * (u : G) * h⁻¹) * h⁻¹ := by
            rw [sq]; group
          rw [hsq, hu_nf, hm₁, hm₂]
        have heq_nf := hlhs.symm.trans (hus_G.trans hrhs)
        obtain ⟨hi_eq, hj_eq⟩ := eq_zmod_of_normalForm_eq hx hy hzx hzy hcard heq_nf
        push_cast at hi_eq hj_eq
        rcases (hirr₃ (i : ZMod r) (j : ZMod r) hij).2 (m : ZMod r) with hne | hne
        · exact hne hi_eq
        · exact hne hj_eq
    let Φ : Fin 3 × (Q ⧸ KQ) → G ⧸ K := fun p =>
      Quotient.liftOn p.2 (fun q : Q => ((h ^ (p.1 : ℕ) * (q : G) : G) : G ⧸ K)) fun q₁ q₂ hq => by
        have hq' : (QuotientGroup.mk q₁ : Q ⧸ KQ) = QuotientGroup.mk q₂ := Quotient.sound hq
        rw [QuotientGroup.eq, mem_subgroupOf] at hq'
        apply QuotientGroup.eq.mpr
        have h1 : (h ^ (p.1 : ℕ) * (q₁ : G))⁻¹ * (h ^ (p.1 : ℕ) * (q₂ : G)) =
            (q₁ : G)⁻¹ * (q₂ : G) := by group
        rw [h1]
        exact hq'
    have hstep_lt : ∀ (s₁ s₂ : Fin 3) (q₁ q₂ : Q),
        s₁ < s₂ → Φ (s₁, QuotientGroup.mk q₁) = Φ (s₂, QuotientGroup.mk q₂) → False := by
      intro s₁ s₂ q₁ q₂ hlt heq
      have hk : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₂ : ℕ) * (q₂ : G)) ∈ K :=
        QuotientGroup.eq.mp heq
      set s := (s₂ : ℕ) - (s₁ : ℕ)
      have hs12 : s = 1 ∨ s = 2 := by omega
      have hs_add : (s₂ : ℕ) = (s₁ : ℕ) + s := by omega
      have hq₂s : h ^ s * (q₂ : G) * (h ^ s)⁻¹ ∈ Q :=
        conj_pow_mem_closure_pair hx hy hzx hzy hhx hhy hhz s q₂.2
      let q₀ : Q := q₁⁻¹ * ⟨h ^ s * (q₂ : G) * (h ^ s)⁻¹, hq₂s⟩
      have hq₀h : (q₀ : G) * h ^ s =
          (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₂ : ℕ) * (q₂ : G)) := by
        simp only [q₀, Subgroup.coe_mul, Subgroup.coe_inv, hs_add, pow_add]
        group
      exact hnot_mem s hs12 q₀ (hq₀h.symm ▸ hk)
    have hΦ : Function.Injective Φ := by
      rintro ⟨s₁, a₁⟩ ⟨s₂, a₂⟩ heq
      induction a₁ using QuotientGroup.induction_on with | H q₁ =>
      induction a₂ using QuotientGroup.induction_on with | H q₂ =>
      rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
      · exact False.elim (hstep_lt s₁ s₂ q₁ q₂ hlt heq)
      · refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, mem_subgroupOf]
        have hk : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₁ : ℕ) * (q₂ : G)) ∈ K :=
          QuotientGroup.eq.mp heq
        have h1 : (h ^ (s₁ : ℕ) * (q₁ : G))⁻¹ * (h ^ (s₁ : ℕ) * (q₂ : G)) =
            (q₁ : G)⁻¹ * (q₂ : G) := by group
        rwa [h1] at hk
      · exact False.elim (hstep_lt s₂ s₁ q₂ q₁ hgt heq.symm)
    have hcard_dom : Nat.card (Fin 3 × (Q ⧸ KQ)) = 3 * r ^ 2 := by
      rw [Nat.card_prod, Nat.card_fin, ← Subgroup.index, hidx_sq]
    rw [Subgroup.index, ← hcard_dom]
    exact Nat.card_le_card_of_injective Φ hΦ

include hp hr3 hx hy hz1 hzx hzy hcard hhx hhy hhz hirr₃ in
/-- If `3 ≤ r`, `h` acts on `Q / Z ≅ (ZMod r)²` with no invariant line under `h` and `h²`, and
`G` is isomorphic to a finite simple group `S`, then every proper subgroup `H ≠ ⊤` of `S` has
index at least `3 * r ^ 2`. -/
theorem three_mul_sq_le_index_of_ne_top {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* G) {H : Subgroup S} (hH : H ≠ ⊤) :
    3 * r ^ 2 ≤ H.index := by
  have : Finite G := Finite.of_equiv S e.toEquiv
  have hZne : Subgroup.zpowers ⁅x, y⁆ ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
  exact le_index_of_injective_of_forall_not_le_index hH e.symm.toMonoidHom e.symm.injective hZne
    fun K hZK =>
      three_mul_sq_le_index_of_not_mem hr3 hx hy hz1 hzx hzy hcard hhx hhy hhz hirr₃
        (fun hzK => hZK (Subgroup.zpowers_le.mpr hzK))

end CubicThreeMulSq

end Maroti.CubicWitness
