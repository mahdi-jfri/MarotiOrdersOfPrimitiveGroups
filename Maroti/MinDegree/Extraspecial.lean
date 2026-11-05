module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.FrattiniQuotient
public import Maroti.MinDegree.Heisenberg

/-!
# Minimum degree of faithful actions of extraspecial `p`-groups

An extraspecial `p`-group `P` (`CFSG.IsExtraspecialPGroup p P`) of order `p ^ (1 + 2 * m)` satisfies
the hypotheses of `Maroti.MinDegree.Heisenberg` with `Z = Subgroup.center P`:
* The commutator subgroup `[P, P] = Z` has order `p`, so `Z` has exponent `p` and is nontrivial.
* The Frattini subgroup is `Φ(P) = Z`, so `P ⧸ Z` is elementary abelian of exponent `p` and order
  `p ^ (2 * m)`.
* For every `x ∉ Z`, the commutator homomorphism `y ↦ ⁅x, y⁆` into `Z` is nontrivial, and hence
  surjective onto `Z` because `|Z| = p` is prime.

Consequently, every subgroup `K ≤ P` not containing `Z` has index at least `p ^ (m + 1)`, every
faithful action of `P` on a finite type `α` has `p ^ (m + 1) ≤ Nat.card α`, and if `P` embeds into a
finite simple group `G`, every proper subgroup of `G` has index at least `p ^ (m + 1)`.
-/

@[expose] public section

namespace Maroti

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

section ExtraspecialProps

variable (hP : CFSG.IsExtraspecialPGroup p P)
include hP

omit [Finite P] hp in
/-- In an extraspecial `p`-group `P`, every commutator lies in `Subgroup.center P`. -/
theorem commutatorElement_mem_center_of_isExtraspecialPGroup (x y : P) :
    ⁅x, y⁆ ∈ center P := by
  rw [← hP.2.1, _root_.commutator_def]
  exact commutator_mem_commutator (mem_top x) (mem_top y)

omit hp in
/-- In an extraspecial `p`-group `P`, every central element has `p`-th power `1`. -/
theorem pow_prime_eq_one_of_mem_center_of_isExtraspecialPGroup {z : P} (hz : z ∈ center P) :
    z ^ p = 1 := by
  classical
  cases nonempty_fintype (center P)
  have h1 : (⟨z, hz⟩ : center P) ^ Nat.card (center P) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  rw [hP.2.2.2] at h1
  exact congrArg Subtype.val h1

include hp in
/-- In an extraspecial `p`-group `P`, every element has `p`-th power in `Subgroup.center P`. -/
theorem pow_prime_mem_center_of_isExtraspecialPGroup (x : P) :
    x ^ p ∈ center P := by
  rw [← hP.2.2.1, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact (CFSG.GroupTheory.frattini_elementary_quotient hP.1).2.2.1 _

include hp in
/-- In an extraspecial `p`-group `P`, for any `x ∉ Subgroup.center P`, the commutator map
`y ↦ ⁅x, y⁆` is surjective onto `Subgroup.center P`. -/
theorem exists_commutatorElement_eq_of_isExtraspecialPGroup {x : P} (hx : x ∉ center P)
    {z : P} (hz : z ∈ center P) :
    ∃ y : P, ⁅x, y⁆ = z := by
  have hcomm := commutatorElement_mem_center_of_isExtraspecialPGroup hP
  let φ : P →* center P :=
    { toFun := fun y => ⟨⁅x, y⁆, hcomm x y⟩
      map_one' := Subtype.ext (commutatorElement_one_right x)
      map_mul' := fun y₁ y₂ =>
        Subtype.ext (commutatorElement_mul_right_of_le_center le_rfl hcomm x y₁ y₂) }
  have hnot : ∃ y₀ : P, φ y₀ ≠ 1 := by
    by_contra! hall
    apply hx
    rw [mem_center_iff]
    intro y
    have hy := congrArg Subtype.val (hall y)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hy).symm
  obtain ⟨y₀, hy₀⟩ := hnot
  have hdvd : Nat.card φ.range ∣ p := by
    rw [← hP.2.2.2]
    exact Subgroup.card_subgroup_dvd_card φ.range
  rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
  · exfalso
    have hsub : Subsingleton φ.range := Finite.card_le_one_iff_subsingleton.mp h1.le
    exact hy₀ (congrArg Subtype.val (Subsingleton.elim (⟨φ y₀, ⟨y₀, rfl⟩⟩ : φ.range) 1))
  · have htop : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (hp'.trans hP.2.2.2.symm)
    have hmem : (⟨z, hz⟩ : center P) ∈ φ.range := htop ▸ mem_top _
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, congrArg Subtype.val hy⟩

omit [Finite P] in
include hp in
/-- The center of an extraspecial `p`-group is nontrivial. -/
theorem center_ne_bot_of_isExtraspecialPGroup :
    center P ≠ ⊥ := by
  intro hbot
  have hc := hP.2.2.2
  rw [hbot, Subgroup.card_bot] at hc
  exact hp.out.ne_one hc.symm

omit [Finite P] in
include hp in
/-- In an extraspecial `p`-group `P` of order `p ^ (1 + 2 * m)`, the index of the center is
`(p ^ m) ^ 2`. -/
theorem index_center_eq_of_isExtraspecialPGroup {m : ℕ} (hcard : Nat.card P = p ^ (1 + 2 * m)) :
    (center P).index = (p ^ m) ^ 2 := by
  have hmul := Subgroup.index_mul_card (center P)
  rw [hP.2.2.2, hcard, add_comm 1 (2 * m), pow_add, pow_one, mul_comm 2 m, pow_mul] at hmul
  exact Nat.eq_of_mul_eq_mul_right hp.out.pos hmul

include hp in
/-- If `P` is an extraspecial `p`-group of order `p ^ (1 + 2 * m)` and `K ≤ P` does not contain
`Subgroup.center P`, then `p ^ (m + 1) ≤ K.index`. -/
theorem pow_le_index_of_isExtraspecialPGroup {m : ℕ} (hcard : Nat.card P = p ^ (1 + 2 * m))
    {K : Subgroup P} (hKZ : ¬ center P ≤ K) :
    p ^ (m + 1) ≤ K.index := by
  rw [pow_succ']
  exact mul_le_index_of_not_le le_rfl
    (commutatorElement_mem_center_of_isExtraspecialPGroup hP)
    (fun _ hz => pow_prime_eq_one_of_mem_center_of_isExtraspecialPGroup hP hz)
    (pow_prime_mem_center_of_isExtraspecialPGroup hP)
    (fun _ hx _ hz => exists_commutatorElement_eq_of_isExtraspecialPGroup hP hx hz)
    hKZ (index_center_eq_of_isExtraspecialPGroup hP hcard).symm.le

include hp in
/-- Every faithful action of an extraspecial `p`-group `P` of order `p ^ (1 + 2 * m)` on a finite
type `α` has degree `p ^ (m + 1) ≤ Nat.card α`. -/
theorem pow_le_card_of_isExtraspecialPGroup {m : ℕ} (hcard : Nat.card P = p ^ (1 + 2 * m))
    {α : Type*} [Finite α] [MulAction P α] [FaithfulSMul P α] :
    p ^ (m + 1) ≤ Nat.card α :=
  le_card_of_forall_not_le_index (center_ne_bot_of_isExtraspecialPGroup hP) fun _ hKZ =>
    pow_le_index_of_isExtraspecialPGroup hP hcard hKZ

include hp in
/-- If an extraspecial `p`-group `P` of order `p ^ (1 + 2 * m)` embeds into `G` and `G` acts
faithfully on a finite type `α`, then `p ^ (m + 1) ≤ Nat.card α`. -/
theorem pow_le_card_of_injective_of_isExtraspecialPGroup {m : ℕ}
    (hcard : Nat.card P = p ^ (1 + 2 * m)) {G α : Type*} [Group G] [Finite α] [MulAction G α]
    [FaithfulSMul G α] (f : P →* G) (hf : Function.Injective f) :
    p ^ (m + 1) ≤ Nat.card α :=
  le_card_of_injective_of_forall_not_le_index f hf (center_ne_bot_of_isExtraspecialPGroup hP)
    fun _ hKZ => pow_le_index_of_isExtraspecialPGroup hP hcard hKZ

include hp in
/-- If an extraspecial `p`-group `P` of order `p ^ (1 + 2 * m)` embeds into a finite simple group
`G`, then every proper subgroup `H ≠ ⊤` of `G` has index `p ^ (m + 1) ≤ H.index`. -/
theorem pow_le_index_of_injective_of_isExtraspecialPGroup {m : ℕ}
    (hcard : Nat.card P = p ^ (1 + 2 * m)) {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) (f : P →* G) (hf : Function.Injective f) :
    p ^ (m + 1) ≤ H.index :=
  le_index_of_injective_of_forall_not_le_index hH f hf (center_ne_bot_of_isExtraspecialPGroup hP)
    fun _ hKZ => pow_le_index_of_isExtraspecialPGroup hP hcard hKZ

end ExtraspecialProps

end Maroti
