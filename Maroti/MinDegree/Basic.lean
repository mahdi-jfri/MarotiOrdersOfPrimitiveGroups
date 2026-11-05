module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Card

/-!
# Minimum degree of faithful group actions: basic lemmas

This file relates the degree `Nat.card α` of a faithful group action of `G` on a finite type `α`
(and, in particular, the index `H.index` of a proper subgroup `H` of a simple group `G` via the
coset action on `G ⧸ H`) to subgroups of `G`:

* The theorem `Maroti.faithfulSMul_quotient_of_ne_top` shows that a simple group acts faithfully on
  the cosets of any proper subgroup.
* The theorems `Maroti.card_dvd_factorial_of_faithfulSMul` and
  `Maroti.card_dvd_index_factorial_of_ne_top` show that the order of `G` divides `(Nat.card α)!`
  (or `(H.index)!`), so every prime dividing `|G|` is at most the degree.
* The theorem `Maroti.exists_stabilizer_not_le` shows that in a faithful action no nontrivial
  subgroup fixes every point, so for any `Z ≠ ⊥` some point stabilizer does not contain `Z`.
* The theorems `Maroti.le_card_of_forall_not_le_index` and
  `Maroti.le_index_of_injective_of_forall_not_le_index` show that if a subgroup `Q` embeds in `G`
  and every subgroup of `Q` not containing `Z ≠ ⊥` has index at least `n₀`, then every faithful
  action of `G` has degree at least `n₀` (and every proper subgroup of `G`, when `G` is simple,
  has index at least `n₀`).
-/

@[expose] public section

namespace Maroti

open Equiv

variable {G H Q : Type*} [Group G] [Group H] [Group Q] {α : Type*}

/-- If `G` acts faithfully on `α`, then the permutation representation `G →* Perm α` is
injective. -/
theorem toPermHom_injective_of_faithfulSMul [MulAction G α] [FaithfulSMul G α] :
    Function.Injective (MulAction.toPermHom G α) := by
  intro g₁ g₂ h
  exact eq_of_smul_eq_smul fun x => Equiv.congr_fun h x

/-- If `G` acts faithfully on `α` and `f : H →* G` is injective, then the induced action of `H`
on `α` is faithful. -/
theorem faithfulSMul_of_injective [MulAction G α] [FaithfulSMul G α]
    (f : H →* G) (hf : Function.Injective f) :
    letI : MulAction H α := MulAction.compHom α f
    FaithfulSMul H α := by
  let _ : MulAction H α := MulAction.compHom α f
  refine ⟨fun {h₁ h₂} h => hf (eq_of_smul_eq_smul h)⟩

/-- A simple group `G` acts faithfully on the quotient `G ⧸ K` by any proper subgroup `K ≠ ⊤`. -/
theorem faithfulSMul_quotient_of_ne_top [IsSimpleGroup G] {K : Subgroup G} (hK : K ≠ ⊤) :
    FaithfulSMul G (G ⧸ K) := by
  have hcore : K.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore with h | h
    · exact h
    · exact False.elim (hK (top_unique (h ▸ K.normalCore_le)))
  rw [Subgroup.normalCore_eq_ker, MonoidHom.ker_eq_bot_iff] at hcore
  exact ⟨fun {g₁ g₂} h => hcore (Equiv.ext h)⟩

/-- If a finite group `G` acts faithfully on a finite type `α`, then `Nat.card G` divides
`(Nat.card α)!`. -/
theorem card_dvd_factorial_of_faithfulSMul [Finite G] [Finite α] [MulAction G α]
    [FaithfulSMul G α] :
    Nat.card G ∣ (Nat.card α).factorial := by
  classical
  cases nonempty_fintype α
  have h1 : Nat.card G ∣ Nat.card (Perm α) :=
    Subgroup.card_dvd_of_injective (MulAction.toPermHom G α) toPermHom_injective_of_faithfulSMul
  rwa [Nat.card_eq_fintype_card (α := Perm α), Fintype.card_perm, ← Nat.card_eq_fintype_card] at h1

/-- If a finite group `G` acts faithfully on a finite type `α`, then
`Nat.card G ≤ (Nat.card α)!`. -/
theorem card_le_factorial_of_faithfulSMul [Finite G] [Finite α] [MulAction G α]
    [FaithfulSMul G α] :
    Nat.card G ≤ (Nat.card α).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) card_dvd_factorial_of_faithfulSMul

/-- If `K` is a proper subgroup of a finite simple group `G`, then `Nat.card G` divides
`(K.index)!`. -/
theorem card_dvd_index_factorial_of_ne_top [Finite G] [IsSimpleGroup G] {K : Subgroup G}
    (hK : K ≠ ⊤) :
    Nat.card G ∣ K.index.factorial := by
  have _ : FaithfulSMul G (G ⧸ K) := faithfulSMul_quotient_of_ne_top hK
  exact card_dvd_factorial_of_faithfulSMul (G := G) (α := G ⧸ K)

/-- If `K` is a proper subgroup of a finite simple group `G`, then `Nat.card G ≤ (K.index)!`. -/
theorem card_le_index_factorial_of_ne_top [Finite G] [IsSimpleGroup G] {K : Subgroup G}
    (hK : K ≠ ⊤) :
    Nat.card G ≤ K.index.factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) (card_dvd_index_factorial_of_ne_top hK)

/-- Any prime dividing the order of a finite group acting faithfully on `α` is at most
`Nat.card α`. -/
theorem prime_le_card_of_faithfulSMul [Finite G] [Finite α] [MulAction G α] [FaithfulSMul G α]
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card G) :
    p ≤ Nat.card α :=
   hp.dvd_factorial.mp (dvd_trans hdvd card_dvd_factorial_of_faithfulSMul)

/-- Any prime dividing the order of a finite simple group `G` is at most the index of any proper
subgroup `K ≠ ⊤`. -/
theorem prime_le_index_of_ne_top [Finite G] [IsSimpleGroup G] {K : Subgroup G} (hK : K ≠ ⊤)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card G) :
    p ≤ K.index :=
  hp.dvd_factorial.mp (dvd_trans hdvd (card_dvd_index_factorial_of_ne_top hK))

/-- For any point `x : α` in an action of `G` on a finite type `α`, the index of the stabilizer of
`x` is at most `Nat.card α`. -/
theorem index_stabilizer_le_card [Finite α] [MulAction G α] (x : α) :
    (MulAction.stabilizer G x).index ≤ Nat.card α := by
  rw [Subgroup.index, ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

/-- If `G` acts faithfully on `α` and `Z ≤ G` is a nontrivial subgroup, then some point `x : α` is
not fixed by all of `Z`, that is, `¬ Z ≤ MulAction.stabilizer G x`. -/
theorem exists_stabilizer_not_le [MulAction G α] [FaithfulSMul G α] {Z : Subgroup G}
    (hZ : Z ≠ ⊥) :
    ∃ x : α, ¬ Z ≤ MulAction.stabilizer G x := by
  by_contra! h
  apply hZ
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact eq_of_smul_eq_smul fun x : α => by
    rw [one_smul]
    exact h x hz

/-- If `G` acts faithfully on a finite type `α`, `Z ≤ G` is nontrivial, and every subgroup of `G`
not containing `Z` has index at least `n₀`, then `n₀ ≤ Nat.card α`. -/
theorem le_card_of_forall_not_le_index [Finite α] [MulAction G α] [FaithfulSMul G α]
    {Z : Subgroup G} (hZ : Z ≠ ⊥) {n₀ : ℕ}
    (hidx : ∀ K : Subgroup G, ¬ Z ≤ K → n₀ ≤ K.index) :
    n₀ ≤ Nat.card α := by
  obtain ⟨x, hx⟩ := exists_stabilizer_not_le (α := α) hZ
  exact (hidx (MulAction.stabilizer G x) hx).trans (index_stabilizer_le_card x)

/-- If `f : Q →* G` is injective, `G` acts faithfully on a finite type `α`, `Z ≤ Q` is nontrivial,
and every subgroup of `Q` not containing `Z` has index at least `n₀`, then `n₀ ≤ Nat.card α`. -/
theorem le_card_of_injective_of_forall_not_le_index [Finite α] [MulAction G α] [FaithfulSMul G α]
    (f : Q →* G) (hf : Function.Injective f) {Z : Subgroup Q} (hZ : Z ≠ ⊥) {n₀ : ℕ}
    (hidx : ∀ K : Subgroup Q, ¬ Z ≤ K → n₀ ≤ K.index) :
    n₀ ≤ Nat.card α := by
  let _ : MulAction Q α := MulAction.compHom α f
  have _ : FaithfulSMul Q α := faithfulSMul_of_injective f hf
  exact le_card_of_forall_not_le_index hZ hidx

/-- If `f : Q →* G` is injective, `G` is a simple group, `H ≠ ⊤` is a proper subgroup of `G`,
`Z ≤ Q` is nontrivial, and every subgroup of `Q` not containing `Z` has index at least `n₀`, then
`n₀ ≤ H.index`. -/
theorem le_index_of_injective_of_forall_not_le_index [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) (f : Q →* G) (hf : Function.Injective f)
    {Z : Subgroup Q} (hZ : Z ≠ ⊥) {n₀ : ℕ}
    (hidx : ∀ K : Subgroup Q, ¬ Z ≤ K → n₀ ≤ K.index) :
    n₀ ≤ H.index := by
  have _ : FaithfulSMul G (G ⧸ H) := faithfulSMul_quotient_of_ne_top hH
  exact le_card_of_injective_of_forall_not_le_index (α := G ⧸ H) f hf hZ hidx

/-- For any group homomorphism `f : H →* G` and subgroup `K ≤ G` of finite index,
`(K.comap f).index ≤ K.index`. -/
theorem index_comap_le (f : H →* G) (K : Subgroup G) [Finite (G ⧸ K)] :
    (K.comap f).index ≤ K.index := by
  let φ : H ⧸ K.comap f → G ⧸ K :=
    Quotient.lift (fun h => (f h : G ⧸ K)) fun a b hab => by
      have hab' : (a : H ⧸ K.comap f) = b := Quotient.sound hab
      rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv] at hab'
      exact QuotientGroup.eq.mpr hab'
  have hφ : Function.Injective φ := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H b =>
    change (f a : G ⧸ K) = (f b : G ⧸ K) at hxy
    rw [QuotientGroup.eq, ← map_inv, ← map_mul] at hxy
    exact QuotientGroup.eq.mpr hxy
  exact Nat.card_le_card_of_injective φ hφ

/-- If `f : H →* G` is a group homomorphism, `G` acts faithfully on a finite type `α`,
`Z ≤ H` has `Z.map f ≠ ⊥`, and every subgroup of `H` not containing `Z` has index at least `n₀`,
then `n₀ ≤ Nat.card α`. -/
theorem le_card_of_map_ne_bot_of_forall_not_le_index [Finite α] [MulAction G α] [FaithfulSMul G α]
    (f : H →* G) {Z : Subgroup H} (hZ : Z.map f ≠ ⊥) {n₀ : ℕ}
    (hidx : ∀ M : Subgroup H, ¬ Z ≤ M → n₀ ≤ M.index) :
    n₀ ≤ Nat.card α := by
  obtain ⟨x, hx⟩ := exists_stabilizer_not_le (α := α) hZ
  let K := MulAction.stabilizer G x
  have _ : Finite (G ⧸ K) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G x)
  have hKZ' : ¬ Z ≤ K.comap f := fun hle => hx (Subgroup.map_le_iff_le_comap.mpr hle)
  exact (hidx (K.comap f) hKZ').trans ((index_comap_le f K).trans (index_stabilizer_le_card x))

/-- If `f : H →* G` is a group homomorphism, `G` is a finite simple group, `K ≠ ⊤` is a proper
subgroup of `G`, `Z ≤ H` has `Z.map f ≠ ⊥`, and every subgroup of `H` not containing `Z` has index
at least `n₀`, then `n₀ ≤ K.index`. -/
theorem le_index_of_map_ne_bot_of_forall_not_le_index [Finite G] [IsSimpleGroup G]
    {K : Subgroup G} (hK : K ≠ ⊤) (f : H →* G) {Z : Subgroup H} (hZ : Z.map f ≠ ⊥) {n₀ : ℕ}
    (hidx : ∀ M : Subgroup H, ¬ Z ≤ M → n₀ ≤ M.index) :
    n₀ ≤ K.index := by
  have _ : FaithfulSMul G (G ⧸ K) := faithfulSMul_quotient_of_ne_top hK
  exact le_card_of_map_ne_bot_of_forall_not_le_index (α := G ⧸ K) f hZ hidx

end Maroti
