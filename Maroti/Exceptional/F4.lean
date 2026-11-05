module

public import Maroti.Exceptional.TorusHeis
public import Maroti.Exceptional.ChevalleyE
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcG2F4Dim
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Const

/-!
# Untwisted Exceptional Groups of Type `F₄`

This file proves the subgroup index lower bound `2 * (p ^ f) ^ 6 ≤ H.index` and Maróti's bound
`|G| ≤ bound |α|` for primitive almost simple groups `G ≤ Perm α` with socle `F₄(p^f)` (Maróti,
Section 2, Step 2, pages 634–635).

* In odd characteristic (`p ≠ 2`), the long-root Heisenberg subgroup `q^(1+14)` of `F₄(q)` has `7`
  root pairs summing to the highest root `2α₁ + 3α₂ + 4α₃ + 2α₄` (`genCodeFacts_F4`). By
  `exists_pinnedX_commFormula_F4_exact`, every commutator coefficient in `F₄` has absolute value `1`
  or `2`, so it is nonzero in characteristic `p ≠ 2`. This yields `(p ^ f) ^ 7 ≤ H.index`, and since
  `p ≥ 3`, we have `2 * (p ^ f) ^ 6 < (p ^ f) ^ 7 ≤ H.index`.
* In characteristic `2` (`p = 2`), we combine two compatible root-pair Heisenberg systems in
  `F₄(q)`: a long-root system `H_long` with center `z₁ = x_{2,3,4,2}(1)` and `4` pairs, and a
  short-root system `H_short` with center `z₂ = x_{1,2,3,2}(1)` and `2` pairs. Using the Chevalley
  commutator relation `x_{-1,-1,-1,0}(1)⁻¹ * z₁ * x_{-1,-1,-1,0}(1) = z₁ * z₂ * x_{0,1,2,2}(1)` and
  a Weyl conjugation sending `(z₁, z₂)` to `(x_{0,1,2,2}(1), z₂)`,
  `HeisSystem.two_mul_card_mul_card_le_index_of_isSimpleGroup` gives `2 * (2 ^ f) ^ 6 ≤ H.index`.
-/

@[expose] public section

open scoped commutatorElement

namespace Maroti

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.RootOps
open CFSG.SignalizerFunctorTheorem.NonLocalExc
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

/-! ### Exact commutator constants and nil-pair commutativity in `F₄` -/

/-- Decidable check that `α` and `β` are distinct non-opposite roots of `τ` with no positive integer
linear combination `i • α + j • β` (`1 ≤ i, j ≤ 3`) a root. -/
def rootPairNilB (τ : Tag) (α β : Fin τ.rank → ℤ) : Prop :=
  isRootB τ α = true ∧ isRootB τ β = true ∧ α ≠ β ∧ α ≠ -β ∧
    ∀ p ∈ commCandidates, isRootB τ (p.1 • α + p.2 • β) = false

instance (τ : Tag) (α β : Fin τ.rank → ℤ) : Decidable (rootPairNilB τ α β) := by
  unfold rootPairNilB
  infer_instance

/-- If `rootPairNilB τ α β` holds, then `pinnedA τ K α c` and `pinnedA τ K β d` commute. -/
theorem pinnedA_comm_of_rootPairNilB {τ : Tag} {K : Type} [Field K]
    {α β : Fin τ.rank → ℤ} (h : rootPairNilB τ α β) (c d : K) :
    pinnedA τ K α c * pinnedA τ K β d = pinnedA τ K β d * pinnedA τ K α c := by
  obtain ⟨hα, hβ, hne, hne', hnil⟩ := h
  refine pinnedA_comm_of_nil (isRootB_iff.1 hα) (isRootB_iff.1 hβ) hne hne'
    (commPairs_eq_nil fun p hp hr => ?_) c d
  have hfalse := hnil p hp
  rw [isRootB_iff.2 hr] at hfalse
  exact Bool.noConfusion hfalse

/-- The list `commPairs τ α β` equals the filter of `commCandidates` by the boolean root test
`isRootB`. -/
theorem commPairs_eq_filter_isRootB (τ : Tag) (α β : Fin τ.rank → ℤ) :
    commPairs τ α β = commCandidates.filter fun p => isRootB τ (p.1 • α + p.2 • β) := by
  classical
  refine List.filter_congr fun p _ => ?_
  rw [Bool.eq_iff_iff, isRootB_iff, decide_eq_true_iff]

/-- In `F₄`, if `commPairs .F4 α β = [(1, 1)]`, then there is an integer `m` with
`|m| = if isRootB .F4 (β - α) then 2 else 1` such that
`((commConst .F4 α β (1, 1) : ℤ) : K) = (m : K)`. -/
theorem exists_eq_commConst_F4_of_single {K : Type} [Field K]
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hone : commPairs .F4 α β = [(1, 1)]) :
    ∃ m : ℤ, (|m| = if isRootB .F4 (β - α) then 2 else 1) ∧
      ((commConst .F4 α β (1, 1) : ℤ) : K) = (m : K) := by
  classical
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hα hβ hne hne'
  obtain ⟨-, hFC⟩ := commConst_spec.{0} hα hβ hne hne'
  have h1 := hF K 1 1
  have h2 := hFC K 1 1
  rw [hone] at h1 h2
  simp only [List.map_singleton, List.prod_singleton, one_pow, mul_one] at h1 h2
  have heq := pinnedX_injective .F4 K (1 • α + 1 • β) (h2.symm.trans h1)
  have hm := hC (1, 1) (by rw [hone]; simp)
  simp only [true_and, ← isRootB_iff] at hm
  exact ⟨C (1, 1), hm, heq⟩

/-- In `F₄`, if `(2 : K) ≠ 0`, then for every root pair in a `HeisGenFacts .F4 α0 S` system,
`((commConst .F4 (α0 - β) β (1, 1) : ℤ) : K) ≠ 0`. -/
theorem commConst_cast_ne_zero_F4_of_two_ne_zero {K : Type} [Field K]
    {S : Finset (Fin Tag.F4.rank → ℤ)} {α0 : Fin Tag.F4.rank → ℤ}
    (hF : HeisGenFacts .F4 α0 S) (h2 : (2 : K) ≠ 0) {β : Fin Tag.F4.rank → ℤ} (hβ : β ∈ S) :
    ((commConst .F4 (α0 - β) β (1, 1) : ℤ) : K) ≠ 0 := by
  obtain ⟨m, hm, heq⟩ := exists_eq_commConst_F4_of_single (K := K) (hF.isRoot_sub β hβ)
    (hF.isRoot_of_mem β hβ) (hF.sub_ne hβ hβ)
    (ne_neg_of_pos (hF.height_sub_pos hβ) (hF.pos β hβ)) (exists_comm_ss_gen hF hβ)
  rw [heq]
  have hcases : m = 1 ∨ m = -1 ∨ m = 2 ∨ m = -2 := by
    rcases Bool.eq_false_or_eq_true (isRootB .F4 (β - (α0 - β))) with h | h <;> rw [h] at hm
    · simp only [↓reduceIte] at hm
      rcases abs_cases m with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    · simp only [Bool.false_eq_true, ↓reduceIte] at hm
      rcases abs_cases m with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [Int.cast_one]
    exact one_ne_zero
  · rw [Int.cast_neg, Int.cast_one, neg_ne_zero]
    exact one_ne_zero
  · exact_mod_cast h2
  · rw [Int.cast_neg, neg_ne_zero]
    exact_mod_cast h2

/-- In `F₄`, if `isRootB .F4 (β - (α0 - β)) = false`, then
`((commConst .F4 (α0 - β) β (1, 1) : ℤ) : K) ≠ 0` in every field `K` (including characteristic
`2`). -/
theorem commConst_cast_ne_zero_F4_of_not_isRoot_sub {K : Type} [Field K]
    {S : Finset (Fin Tag.F4.rank → ℤ)} {α0 : Fin Tag.F4.rank → ℤ}
    (hF : HeisGenFacts .F4 α0 S) {β : Fin Tag.F4.rank → ℤ} (hβ : β ∈ S)
    (hnr : isRootB .F4 (β - (α0 - β)) = false) :
    ((commConst .F4 (α0 - β) β (1, 1) : ℤ) : K) ≠ 0 := by
  obtain ⟨m, hm, heq⟩ := exists_eq_commConst_F4_of_single (K := K) (hF.isRoot_sub β hβ)
    (hF.isRoot_of_mem β hβ) (hF.sub_ne hβ hβ)
    (ne_neg_of_pos (hF.height_sub_pos hβ) (hF.pos β hβ)) (exists_comm_ss_gen hF hβ)
  rw [heq]
  rw [hnr] at hm
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  have hcases : m = 1 ∨ m = -1 := by
    rcases abs_cases m with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rcases hcases with rfl | rfl
  · rw [Int.cast_one]
    exact one_ne_zero
  · rw [Int.cast_neg, Int.cast_one, neg_ne_zero]
    exact one_ne_zero

/-- In `F₄` over a field `K` of characteristic `2`, if `commPairs .F4 α β = [(1, 1)]` and
`isRootB .F4 (β - α) = true`, then `pinnedA .F4 K α c` and `pinnedA .F4 K β d` commute. -/
theorem pinnedA_comm_F4_of_single_charP_two {K : Type} [Field K] [CharP K 2]
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hone : commPairs .F4 α β = [(1, 1)])
    (hr : isRootB .F4 (β - α) = true) (c d : K) :
    pinnedA .F4 K α c * pinnedA .F4 K β d = pinnedA .F4 K β d * pinnedA .F4 K α c := by
  obtain ⟨m, hm, heq⟩ := exists_eq_commConst_F4_of_single (K := K) hα hβ hne hne' hone
  rw [hr] at hm
  simp only [↓reduceIte] at hm
  have hcases : m = 2 ∨ m = -2 := by
    rcases abs_cases m with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have h2 : (2 : K) = 0 := by simpa using (CharP.cast_eq_zero K 2)
  have hm0 : ((commConst .F4 α β (1, 1) : ℤ) : K) = 0 := by
    rw [heq]
    rcases hcases with rfl | rfl
    · exact_mod_cast h2
    · rw [Int.cast_neg, neg_eq_zero]
      exact_mod_cast h2
  have h := pinnedA_comm_single (K := K) hα hβ hne hne' hone c d
  rw [hm0, zero_mul, zero_mul, pinnedX_zero, ← pinnedX_neg, ← pinnedX_neg] at h
  refine pinnedA_ext ?_
  exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h)

/-! ### Characteristic-`2` paired Heisenberg data for `F₄` -/

/-- The `4` long-root pair codes for `H_long` in `F₄` with center `44218` (`(2, 3, 4, 2)`). -/
def f4LongCodes : List ℕ := [34953, 34969, 35481, 35497]

/-- The `2` short-root pair codes for `H_short` in `F₄` with center `43945` (`(1, 2, 3, 2)`). -/
def f4ShortCodes : List ℕ := [39048, 39304]

theorem genCodeFacts_F4_long : GenCodeFacts .F4 44218 f4LongCodes := by decide +kernel

theorem not_isRootB_sub_F4_long :
    ∀ c ∈ f4LongCodes,
      isRootB .F4 (decodeVec c - (decodeVec 44218 - decodeVec c)) = false := by
  decide +kernel

theorem isRoot_43945 : IsRoot .F4 (decodeVec 43945) := by
  rw [← isRootB_iff]
  decide +kernel

theorem f4Short_nil_TT :
    ∀ c ∈ f4ShortCodes, ∀ d ∈ f4ShortCodes, c ≠ d →
      rootPairNilB .F4 (decodeVec 43945 - decodeVec c) (decodeVec 43945 - decodeVec d) := by
  decide +kernel

theorem f4Short_nil_SS :
    ∀ c ∈ f4ShortCodes, ∀ d ∈ f4ShortCodes, c ≠ d →
      rootPairNilB .F4 (decodeVec c) (decodeVec d) := by
  decide +kernel

theorem f4Short_nil_zT :
    ∀ c ∈ f4ShortCodes,
      rootPairNilB .F4 (decodeVec 43945) (decodeVec 43945 - decodeVec c) := by
  decide +kernel

theorem f4Short_nil_zS :
    ∀ c ∈ f4ShortCodes,
      rootPairNilB .F4 (decodeVec 43945) (decodeVec c) := by
  decide +kernel

theorem f4Short_diag_isRoot_S :
    ∀ c ∈ f4ShortCodes, isRootB .F4 (decodeVec c) = true := by decide +kernel

theorem f4Short_diag_isRoot_T :
    ∀ c ∈ f4ShortCodes, isRootB .F4 (decodeVec 43945 - decodeVec c) = true := by decide +kernel

theorem f4Short_diag_ne :
    ∀ c ∈ f4ShortCodes,
      decodeVec (τ := .F4) c ≠ decodeVec 43945 - decodeVec c ∧
        decodeVec (τ := .F4) c ≠ -(decodeVec 43945 - decodeVec c) := by
  decide +kernel

theorem f4Short_diag_commCandidates :
    ∀ c ∈ f4ShortCodes, ∀ p ∈ commCandidates,
      (isRootB .F4 (p.1 • decodeVec c + p.2 • (decodeVec 43945 - decodeVec c)) = true ↔
        p = (1, 1)) := by
  decide +kernel

theorem f4Short_diag_commPairs {c : ℕ} (hc : c ∈ f4ShortCodes) :
    commPairs .F4 (decodeVec c) (decodeVec 43945 - decodeVec c) = [(1, 1)] :=
  commPairs_eq_single fun p hp => by
    rw [← isRootB_iff]
    exact f4Short_diag_commCandidates c hc p hp

theorem f4Short_diag_not_isRootB_sub :
    ∀ c ∈ f4ShortCodes,
      isRootB .F4 ((decodeVec 43945 - decodeVec c) - decodeVec c) = false := by
  decide +kernel

theorem f4Short_offdiag_ne :
    ∀ c ∈ f4ShortCodes, ∀ d ∈ f4ShortCodes, c ≠ d →
      decodeVec (τ := .F4) c ≠ decodeVec 43945 - decodeVec d ∧
        decodeVec (τ := .F4) c ≠ -(decodeVec 43945 - decodeVec d) := by
  decide +kernel

theorem f4Short_offdiag_commCandidates :
    ∀ c ∈ f4ShortCodes, ∀ d ∈ f4ShortCodes, c ≠ d → ∀ p ∈ commCandidates,
      (isRootB .F4 (p.1 • decodeVec c + p.2 • (decodeVec 43945 - decodeVec d)) = true ↔
        p = (1, 1)) := by
  decide +kernel

theorem f4Short_offdiag_commPairs {c d : ℕ} (hc : c ∈ f4ShortCodes) (hd : d ∈ f4ShortCodes)
    (hne : c ≠ d) :
    commPairs .F4 (decodeVec c) (decodeVec 43945 - decodeVec d) = [(1, 1)] :=
  commPairs_eq_single fun p hp => by
    rw [← isRootB_iff]
    exact f4Short_offdiag_commCandidates c hc d hd hne p hp

theorem f4Short_offdiag_isRootB_sub :
    ∀ c ∈ f4ShortCodes, ∀ d ∈ f4ShortCodes, c ≠ d →
      isRootB .F4 ((decodeVec 43945 - decodeVec d) - decodeVec c) = true := by
  decide +kernel

/-- The `2`-pair short-root Heisenberg system in `adjointGroup .F4 K` over a field `K` of
characteristic `2`, with center `decodeVec 43945` (`(1, 2, 3, 2)`). -/
noncomputable def heisSystemF4ShortChar2 {K : Type} [Field K] [CharP K 2] :
    HeisSystem ↥(adjointGroup .F4 K) K ↥(genS .F4 f4ShortCodes) where
  xa s c := pinnedA .F4 K (decodeVec 43945 - s.1) c
  xb s c := pinnedA .F4 K s.1 c
  z c := pinnedA .F4 K (decodeVec 43945) c
  ε s := -((commConst .F4 s.1 (decodeVec 43945 - s.1) (1, 1) : ℤ) : K)
  xa_add s c d := pinnedA_add _ c d
  xb_add s c d := pinnedA_add _ c d
  z_add c d := pinnedA_add _ c d
  z_injective := fun c d h => pinnedX_injective .F4 K _
    (congrArg (fun x : ↥(adjointGroup .F4 K) => (x : ModGL .F4 K)) h)
  ε_ne s := by
    obtain ⟨c, hc, hcs⟩ := mem_genS.1 s.2
    rw [← hcs, neg_ne_zero]
    obtain ⟨m, hm, heq⟩ := exists_eq_commConst_F4_of_single (K := K)
      ((isRootB_iff).1 (f4Short_diag_isRoot_S c hc))
      ((isRootB_iff).1 (f4Short_diag_isRoot_T c hc))
      (f4Short_diag_ne c hc).1 (f4Short_diag_ne c hc).2
      (f4Short_diag_commPairs hc)
    rw [heq]
    rw [f4Short_diag_not_isRootB_sub c hc] at hm
    simp only [Bool.false_eq_true, ↓reduceIte] at hm
    have hcases : m = 1 ∨ m = -1 := by
      rcases abs_cases m with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    rcases hcases with rfl | rfl
    · rw [Int.cast_one]
      exact one_ne_zero
    · rw [Int.cast_neg, Int.cast_one, neg_ne_zero]
      exact one_ne_zero
  xa_comm s t c d := by
    by_cases hst : s = t
    · subst hst; exact pinnedA_comm_self _ c d
    · obtain ⟨cs, hcs_mem, hcs⟩ := mem_genS.1 s.2
      obtain ⟨ct, hct_mem, hct⟩ := mem_genS.1 t.2
      have hne : cs ≠ ct := fun h => hst (Subtype.ext (by rw [← hcs, ← hct, h]))
      rw [← hcs, ← hct]
      exact pinnedA_comm_of_rootPairNilB (f4Short_nil_TT cs hcs_mem ct hct_mem hne) c d
  xb_comm s t c d := by
    by_cases hst : s = t
    · subst hst; exact pinnedA_comm_self _ c d
    · obtain ⟨cs, hcs_mem, hcs⟩ := mem_genS.1 s.2
      obtain ⟨ct, hct_mem, hct⟩ := mem_genS.1 t.2
      have hne : cs ≠ ct := fun h => hst (Subtype.ext (by rw [← hcs, ← hct, h]))
      rw [← hcs, ← hct]
      exact pinnedA_comm_of_rootPairNilB (f4Short_nil_SS cs hcs_mem ct hct_mem hne) c d
  z_comm_a c s d := by
    obtain ⟨cs, hcs_mem, hcs⟩ := mem_genS.1 s.2
    rw [← hcs]
    exact pinnedA_comm_of_rootPairNilB (f4Short_nil_zT cs hcs_mem) c d
  z_comm_b c s d := by
    obtain ⟨cs, hcs_mem, hcs⟩ := mem_genS.1 s.2
    rw [← hcs]
    exact pinnedA_comm_of_rootPairNilB (f4Short_nil_zS cs hcs_mem) c d
  xab_comm s t hst c d := by
    obtain ⟨cs, hcs_mem, hcs⟩ := mem_genS.1 s.2
    obtain ⟨ct, hct_mem, hct⟩ := mem_genS.1 t.2
    have hne : cs ≠ ct := fun h => hst (Subtype.ext (by rw [← hcs, ← hct, h]))
    rw [← hcs, ← hct]
    exact pinnedA_comm_F4_of_single_charP_two
      ((isRootB_iff).1 (f4Short_diag_isRoot_S cs hcs_mem))
      ((isRootB_iff).1 (f4Short_diag_isRoot_T ct hct_mem))
      (f4Short_offdiag_ne cs hcs_mem ct hct_mem hne).1
      (f4Short_offdiag_ne cs hcs_mem ct hct_mem hne).2
      (f4Short_offdiag_commPairs hcs_mem hct_mem hne)
      (f4Short_offdiag_isRootB_sub cs hcs_mem ct hct_mem hne) c d
  comm_ss s c d := by
    obtain ⟨cs, hcs_mem, hcs⟩ := mem_genS.1 s.2
    have hf := pinnedA_comm_single (K := K)
      ((isRootB_iff).1 (f4Short_diag_isRoot_S cs hcs_mem))
      ((isRootB_iff).1 (f4Short_diag_isRoot_T cs hcs_mem))
      (f4Short_diag_ne cs hcs_mem).1 (f4Short_diag_ne cs hcs_mem).2
      (f4Short_diag_commPairs hcs_mem) (-c) d
    simp only [add_sub_cancel] at hf
    rw [pinnedA_neg]
    refine pinnedA_ext ?_
    show ⁅pinnedX .F4 K s.1 (-c), pinnedX .F4 K (decodeVec 43945 - s.1) d⁆ = _
    rw [← hcs, commutatorElement_def, pinnedX_neg, pinnedX_neg, hf]
    congr 1
    ring

theorem card_genS_F4_long : (genS .F4 f4LongCodes).card = 4 := by decide +kernel

theorem card_genS_F4_short : (genS .F4 f4ShortCodes).card = 2 := by decide +kernel

theorem card_genS_F4_seven :
    (genS .F4 [34953, 34969, 35481, 35225, 35497, 39321, 39577]).card = 7 := by
  decide +kernel

theorem f4_cross_nil_zz :
    rootPairNilB .F4 (decodeVec 44218) (decodeVec 43945) := by decide +kernel

theorem f4_cross_nil_z1a2 :
    ∀ d ∈ f4ShortCodes, rootPairNilB .F4 (decodeVec 44218) (decodeVec 43945 - decodeVec d) := by
  decide +kernel

theorem f4_cross_nil_z1b2 :
    ∀ d ∈ f4ShortCodes, rootPairNilB .F4 (decodeVec 44218) (decodeVec d) := by
  decide +kernel

theorem f4_cross_nil_z2a1 :
    ∀ c ∈ f4LongCodes, rootPairNilB .F4 (decodeVec 43945) (decodeVec 44218 - decodeVec c) := by
  decide +kernel

theorem f4_cross_nil_z2b1 :
    ∀ c ∈ f4LongCodes, rootPairNilB .F4 (decodeVec 43945) (decodeVec c) := by
  decide +kernel

theorem f4_cross_nil_a1a2 :
    ∀ c ∈ f4LongCodes, ∀ d ∈ f4ShortCodes,
      rootPairNilB .F4 (decodeVec 44218 - decodeVec c) (decodeVec 43945 - decodeVec d) := by
  decide +kernel

theorem f4_cross_nil_b1a2 :
    ∀ c ∈ f4LongCodes, ∀ d ∈ f4ShortCodes,
      rootPairNilB .F4 (decodeVec c) (decodeVec 43945 - decodeVec d) := by
  decide +kernel

theorem f4_cross_nil_b2a1 :
    ∀ d ∈ f4ShortCodes, ∀ c ∈ f4LongCodes,
      rootPairNilB .F4 (decodeVec d) (decodeVec 44218 - decodeVec c) := by
  decide +kernel

theorem f4_cross_nil_z2z3 :
    rootPairNilB .F4 (decodeVec 43945) (decodeVec 43672) := by decide +kernel

/-! ### Weyl word conjugation and central root relations in characteristic `2` -/

/-- Simple reflection element `weylElt τ K i 1` in `adjointGroup τ K`. -/
noncomputable def weylA (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) : ↥(adjointGroup τ K) :=
  ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩

/-- Product of reversed simple reflection elements in `adjointGroup τ K`. -/
noncomputable def wordWeylA (τ : Tag) (K : Type) [Field K] (w : List ℕ) :
    ↥(adjointGroup τ K) :=
  ((w.map fun i => weylA τ K (τ.idx i)).reverse).prod

/-- In characteristic `2`, conjugating `pinnedA τ K β c` by `weylA τ K i` yields
`pinnedA τ K (reflect τ i β) c`. -/
theorem weylA_conj_pinnedA_of_charP_two {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (i : Fin τ.rank) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : K) :
    weylA τ K i * pinnedA τ K β c * (weylA τ K i)⁻¹ = pinnedA τ K (reflect τ i β) c := by
  have h2 : (2 : K) = 0 := by simpa using (CharP.cast_eq_zero K 2)
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hβ
  have hε1 : ε = 1 := by
    have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε - (ε - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  refine pinnedA_ext ?_
  show weylElt τ K i 1 * pinnedX τ K β c * (weylElt τ K i 1)⁻¹ = _
  rw [h, hε1, one_mul]
  rfl

/-- In characteristic `2`, conjugating `pinnedA τ K β c` by `wordWeylA τ K w` folds reflections
along `w`. -/
theorem wordWeylA_conj_pinnedA_of_charP_two {τ : Tag} {K : Type} [Field K] [CharP K 2] :
    ∀ (w : List ℕ) {β : Fin τ.rank → ℤ}, IsRoot τ β → ∀ c : K,
      wordWeylA τ K w * pinnedA τ K β c * (wordWeylA τ K w)⁻¹ =
        pinnedA τ K (w.foldl (fun v i => reflect τ (τ.idx i) v) β) c
  | [], _, _, c => by simp [wordWeylA]
  | i :: w, β, hβ, c => by
    have ih := wordWeylA_conj_pinnedA_of_charP_two w (IsRoot.reflect (τ.idx i) hβ) c
    rw [wordWeylA, List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
      mul_inv_rev, List.foldl_cons, ← wordWeylA, ← ih,
      ← weylA_conj_pinnedA_of_charP_two (τ.idx i) hβ c]
    group

/-- The Weyl word `[0, 1, 2, 1, 0]` in `F₄` sending `decodeVec 44218` to `decodeVec 43672` and
fixing `decodeVec 43945`. -/
def f4WeylWord : List ℕ := [0, 1, 2, 1, 0]

theorem foldl_f4WeylWord_44218 :
    f4WeylWord.foldl (fun v i => reflect .F4 (Tag.idx .F4 i) v) (decodeVec 44218) =
      decodeVec 43672 := by
  decide +kernel

theorem foldl_f4WeylWord_43945 :
    f4WeylWord.foldl (fun v i => reflect .F4 (Tag.idx .F4 i) v) (decodeVec 43945) =
      decodeVec 43945 := by
  decide +kernel

/-- In characteristic `2`, `pinnedA τ K α 1` has order dividing `2` and equals its own inverse. -/
theorem pinnedA_neg_one_eq_one_of_charP_two {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (α : Fin τ.rank → ℤ) : pinnedA τ K α (-1) = pinnedA τ K α 1 := by
  have h2 : (2 : K) = 0 := by simpa using (CharP.cast_eq_zero K 2)
  congr 1
  linear_combination -h2

theorem pinnedA_mul_self_of_charP_two {τ : Tag} {K : Type} [Field K] [CharP K 2]
    (α : Fin τ.rank → ℤ) : pinnedA τ K α 1 * pinnedA τ K α 1 = 1 := by
  have h2 : (2 : K) = 0 := by simpa using (CharP.cast_eq_zero K 2)
  rw [← pinnedA_add, show (1 : K) + 1 = 0 by linear_combination h2]
  exact pinnedA_ext (pinnedX_zero τ K α)

/-- In characteristic `2`, `pinnedA .F4 K (decodeVec 34679) 1` commutes with
`pinnedA .F4 K (decodeVec 43945) 1`. -/
theorem f4_char2_g_comm_z2 {K : Type} [Field K] [CharP K 2] :
    pinnedA .F4 K (decodeVec 34679) 1 * pinnedA .F4 K (decodeVec 43945) 1 =
      pinnedA .F4 K (decodeVec 43945) 1 * pinnedA .F4 K (decodeVec 34679) 1 := by
  classical
  set α : Fin Tag.F4.rank → ℤ := decodeVec 34679
  set β : Fin Tag.F4.rank → ℤ := decodeVec 43945
  have hα : IsRoot .F4 α := isRootB_iff.1 (by decide +kernel)
  have hβ : IsRoot .F4 β := isRootB_iff.1 (by decide +kernel)
  have hne : α ≠ β := by decide +kernel
  have hne' : α ≠ -β := by decide +kernel
  have hcp : commPairs .F4 α β = [(1, 1)] := by
    rw [commPairs_eq_filter_isRootB]
    decide +kernel
  have hsub : IsRoot .F4 (β - α) := isRootB_iff.1 (by decide +kernel)
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hα hβ hne hne'
  have hC11 := hC (1, 1) (by rw [hcp]; simp)
  simp only [true_and, hsub, ite_true] at hC11
  have h2 : (2 : K) = 0 := by simpa using (CharP.cast_eq_zero K 2)
  have hCK : ((C (1, 1) : ℤ) : K) = 0 := by
    have hcases : C (1, 1) = 2 ∨ C (1, 1) = -2 := by
      rcases abs_cases (C (1, 1)) with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    rcases hcases with h | h <;> rw [h] <;> simp [h2]
  have hf := hF K 1 1
  rw [hcp] at hf
  simp only [List.map_singleton, List.prod_singleton, hCK, zero_mul, pinnedX_zero] at hf
  rw [← pinnedX_neg, ← pinnedX_neg] at hf
  refine pinnedA_ext ?_
  exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact hf)

/-- In characteristic `2`, conjugating `z₁ = pinnedA .F4 K (decodeVec 44218) 1` by
`g = pinnedA .F4 K (decodeVec 34679) 1` yields `z₁ * z₂ * z₃`. -/
theorem f4_char2_conj_z1 {K : Type} [Field K] [CharP K 2] :
    (pinnedA .F4 K (decodeVec 34679) 1)⁻¹ * pinnedA .F4 K (decodeVec 44218) 1 *
        pinnedA .F4 K (decodeVec 34679) 1 =
      pinnedA .F4 K (decodeVec 44218) 1 * pinnedA .F4 K (decodeVec 43945) 1 *
        pinnedA .F4 K (decodeVec 43672) 1 := by
  classical
  set α : Fin Tag.F4.rank → ℤ := decodeVec 44218
  set β : Fin Tag.F4.rank → ℤ := decodeVec 34679
  have hα : IsRoot .F4 α := isRootB_iff.1 (by decide +kernel)
  have hβ : IsRoot .F4 β := isRootB_iff.1 (by decide +kernel)
  have hne : α ≠ β := by decide +kernel
  have hne' : α ≠ -β := by decide +kernel
  have hcp : commPairs .F4 α β = [(1, 1), (1, 2)] := by
    rw [commPairs_eq_filter_isRootB]
    decide +kernel
  have hsubB : isRootB .F4 (β - α) = false := by decide +kernel
  have hsub : ¬ IsRoot .F4 (β - α) := fun h => by
    rw [isRootB_iff.2 h] at hsubB
    exact Bool.noConfusion hsubB
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hα hβ hne hne'
  have h2 : (2 : K) = 0 := by simpa using (CharP.cast_eq_zero K 2)
  have hone_of_abs : ∀ m : ℤ, |m| = 1 → ((m : ℤ) : K) = 1 := by
    intro m hm
    have hcases : m = 1 ∨ m = -1 := by
      rcases abs_cases m with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    rcases hcases with rfl | rfl
    · simp
    · push_cast
      linear_combination -h2
  have hC11 : ((C (1, 1) : ℤ) : K) = 1 := by
    have h1 := hC (1, 1) (by rw [hcp]; simp)
    simp only [true_and, hsub, ite_false] at h1
    exact hone_of_abs _ h1
  have hC12 : ((C (1, 2) : ℤ) : K) = 1 := by
    have h1 := hC (1, 2) (by rw [hcp]; simp)
    have hne12 : ((1 : ℕ), (2 : ℕ)) ≠ (1, 1) := by decide
    simp only [hne12, false_and, ite_false] at h1
    exact hone_of_abs _ h1
  have hsum11 : (1 : ℕ) • α + (1 : ℕ) • β = decodeVec 43945 := by decide +kernel
  have hsum12 : (1 : ℕ) • α + (2 : ℕ) • β = decodeVec 43672 := by decide +kernel
  have hm1 : (-1 : K) = 1 := by linear_combination -h2
  have hf := hF K 1 1
  rw [hcp] at hf
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    hC11, hC12, hsum11, hsum12, hm1] at hf
  have hcommA : pinnedA .F4 K α 1 * pinnedA .F4 K β 1 * pinnedA .F4 K α 1 * pinnedA .F4 K β 1 =
      pinnedA .F4 K (decodeVec 43945) 1 * pinnedA .F4 K (decodeVec 43672) 1 :=
    pinnedA_ext hf
  have hginv : (pinnedA .F4 K β 1)⁻¹ = pinnedA .F4 K β 1 := by
    rw [pinnedA_neg, pinnedA_neg_one_eq_one_of_charP_two]
  have hz1sq : pinnedA .F4 K α 1 * pinnedA .F4 K α 1 = 1 := pinnedA_mul_self_of_charP_two α
  rw [hginv]
  calc pinnedA .F4 K β 1 * pinnedA .F4 K α 1 * pinnedA .F4 K β 1
      = (pinnedA .F4 K α 1 * pinnedA .F4 K α 1) *
          (pinnedA .F4 K β 1 * pinnedA .F4 K α 1 * pinnedA .F4 K β 1) := by
        rw [hz1sq, one_mul]
    _ = pinnedA .F4 K α 1 *
          (pinnedA .F4 K α 1 * pinnedA .F4 K β 1 * pinnedA .F4 K α 1 * pinnedA .F4 K β 1) := by
        group
    _ = pinnedA .F4 K α 1 * pinnedA .F4 K (decodeVec 43945) 1 *
          pinnedA .F4 K (decodeVec 43672) 1 := by
        rw [hcommA, mul_assoc]

/-- Helper for the cardinality of a finset subtype over roots. -/
theorem nat_card_coe_finset_eq {α : Type*} (S : Finset α) : Nat.card ↥S = S.card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Every proper subgroup `M` of `adjointGroup .F4 K` over a finite field `K` of characteristic `2`
has index at least `2 * Nat.card K ^ 6`. -/
theorem two_mul_pow_six_le_index_adjointGroup_F4_of_charP_two
    {K : Type} [Field K] [Finite K] [CharP K 2]
    [IsSimpleGroup ↥(adjointGroup .F4 K)]
    (M : Subgroup ↥(adjointGroup .F4 K)) (hM : M ≠ ⊤) :
    2 * Nat.card K ^ 6 ≤ M.index := by
  classical
  have hF_long := HeisGenFacts.of_codeFacts genCodeFacts_F4_long
  have hC_long : ∀ β ∈ genS .F4 f4LongCodes,
      ((commConst .F4 (decodeVec 44218 - β) β (1, 1) : ℤ) : K) ≠ 0 := by
    intro β hβ
    obtain ⟨c, hc, rfl⟩ := mem_genS.1 hβ
    exact commConst_cast_ne_zero_F4_of_not_isRoot_sub hF_long hβ (not_isRootB_sub_F4_long c hc)
  have hle := HeisSystem.two_mul_card_mul_card_le_index_of_isSimpleGroup
    (HeisSystem.swap (heisSystemGen (K := K) hF_long hC_long))
    (heisSystemF4ShortChar2 (K := K))
    (fun c₁ c₂ => pinnedA_comm_of_rootPairNilB f4_cross_nil_zz c₁ c₂)
    (fun c₁ s₂ d₂ => by
      obtain ⟨d, hd, hds⟩ := mem_genS.1 s₂.2
      change pinnedA .F4 K (decodeVec 44218) c₁ * pinnedA .F4 K (decodeVec 43945 - s₂.1) d₂ =
        pinnedA .F4 K (decodeVec 43945 - s₂.1) d₂ * pinnedA .F4 K (decodeVec 44218) c₁
      rw [← hds]
      exact pinnedA_comm_of_rootPairNilB (f4_cross_nil_z1a2 d hd) c₁ d₂)
    (fun c₁ s₂ d₂ => by
      obtain ⟨d, hd, hds⟩ := mem_genS.1 s₂.2
      change pinnedA .F4 K (decodeVec 44218) c₁ * pinnedA .F4 K s₂.1 d₂ =
        pinnedA .F4 K s₂.1 d₂ * pinnedA .F4 K (decodeVec 44218) c₁
      rw [← hds]
      exact pinnedA_comm_of_rootPairNilB (f4_cross_nil_z1b2 d hd) c₁ d₂)
    (fun c₂ s₁ d₁ => by
      obtain ⟨c, hc, hcs⟩ := mem_genS.1 s₁.2
      change pinnedA .F4 K (decodeVec 43945) c₂ * pinnedA .F4 K (decodeVec 44218 - s₁.1) d₁ =
        pinnedA .F4 K (decodeVec 44218 - s₁.1) d₁ * pinnedA .F4 K (decodeVec 43945) c₂
      rw [← hcs]
      exact pinnedA_comm_of_rootPairNilB (f4_cross_nil_z2a1 c hc) c₂ d₁)
    (fun c₂ s₁ d₁ => by
      obtain ⟨c, hc, hcs⟩ := mem_genS.1 s₁.2
      change pinnedA .F4 K (decodeVec 43945) c₂ * pinnedA .F4 K s₁.1 d₁ =
        pinnedA .F4 K s₁.1 d₁ * pinnedA .F4 K (decodeVec 43945) c₂
      rw [← hcs]
      exact pinnedA_comm_of_rootPairNilB (f4_cross_nil_z2b1 c hc) c₂ d₁)
    (fun s₁ s₂ d₁ d₂ => by
      obtain ⟨c, hc, hcs⟩ := mem_genS.1 s₁.2
      obtain ⟨d, hd, hds⟩ := mem_genS.1 s₂.2
      change pinnedA .F4 K (decodeVec 44218 - s₁.1) d₁ *
        pinnedA .F4 K (decodeVec 43945 - s₂.1) d₂ =
        pinnedA .F4 K (decodeVec 43945 - s₂.1) d₂ *
        pinnedA .F4 K (decodeVec 44218 - s₁.1) d₁
      rw [← hcs, ← hds]
      exact pinnedA_comm_of_rootPairNilB (f4_cross_nil_a1a2 c hc d hd) d₁ d₂)
    (fun s₁ s₂ c₁ d₂ => by
      obtain ⟨c, hc, hcs⟩ := mem_genS.1 s₁.2
      obtain ⟨d, hd, hds⟩ := mem_genS.1 s₂.2
      change pinnedA .F4 K s₁.1 c₁ * pinnedA .F4 K (decodeVec 43945 - s₂.1) d₂ =
        pinnedA .F4 K (decodeVec 43945 - s₂.1) d₂ * pinnedA .F4 K s₁.1 c₁
      rw [← hcs, ← hds]
      exact pinnedA_comm_of_rootPairNilB (f4_cross_nil_b1a2 c hc d hd) c₁ d₂)
    (fun s₂ s₁ c₂ d₁ => by
      obtain ⟨d, hd, hds⟩ := mem_genS.1 s₂.2
      obtain ⟨c, hc, hcs⟩ := mem_genS.1 s₁.2
      change pinnedA .F4 K s₂.1 c₂ * pinnedA .F4 K (decodeVec 44218 - s₁.1) d₁ =
        pinnedA .F4 K (decodeVec 44218 - s₁.1) d₁ * pinnedA .F4 K s₂.1 c₂
      rw [← hds, ← hcs]
      exact pinnedA_comm_of_rootPairNilB (f4_cross_nil_b2a1 d hd c hc) c₂ d₁)
    (z₃ := pinnedA .F4 K (decodeVec 43672) 1)
    (g := pinnedA .F4 K (decodeVec 34679) 1)
    (w := wordWeylA .F4 K f4WeylWord)
    f4_char2_conj_z1
    f4_char2_g_comm_z2
    (by
      change wordWeylA .F4 K f4WeylWord * pinnedA .F4 K (decodeVec 44218) 1 *
        (wordWeylA .F4 K f4WeylWord)⁻¹ = pinnedA .F4 K (decodeVec 43672) 1
      rw [wordWeylA_conj_pinnedA_of_charP_two f4WeylWord hF_long.isRoot_α0 1,
        foldl_f4WeylWord_44218])
    (by
      change wordWeylA .F4 K f4WeylWord * pinnedA .F4 K (decodeVec 43945) 1 *
        (wordWeylA .F4 K f4WeylWord)⁻¹ = pinnedA .F4 K (decodeVec 43945) 1
      rw [wordWeylA_conj_pinnedA_of_charP_two f4WeylWord isRoot_43945 1,
        foldl_f4WeylWord_43945])
    M hM
  rw [Nat.card_fun, Nat.card_fun, nat_card_coe_finset_eq, card_genS_F4_long,
    nat_card_coe_finset_eq, card_genS_F4_short, ← pow_add] at hle
  exact hle

/-! ### Subgroup index and Maróti bounds for `F₄(q)` -/

/-- Every proper subgroup `H` of `F₄(p^f)` has index at least `2 * (p ^ f) ^ 6`. -/
theorem index_ge_of_chevalley_F4 {S : Type} [Group S] {p f : ℕ}
    [IsSimpleGroup S] (h : ChevalleyExceptionalModel S .F4 p f)
    (H : Subgroup S) (hH : H ≠ ⊤) :
    2 * (p ^ f) ^ 6 ≤ H.index := by
  classical
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K p := charP_of_card_eq_prime_pow hcardK
  have : Finite (ModGL .F4 K) := finite_modGL
  have : Finite ↥(adjointGroup .F4 K) := Subtype.finite
  have hZ : Subgroup.center ↥(adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  let eAdj : ↥(adjointGroup .F4 K) ≃* S :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e.symm
  have : IsSimpleGroup ↥(adjointGroup .F4 K) := eAdj.isSimpleGroup
  let M : Subgroup ↥(adjointGroup .F4 K) := H.map eAdj.symm.toMonoidHom
  have hM : M ≠ ⊤ := by
    intro htop
    apply hH
    rw [eq_top_iff]
    intro x _
    have hx : eAdj.symm x ∈ M := by rw [htop]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    simpa using (eAdj.symm.injective hyx) ▸ hy
  have hidx : M.index = H.index := Subgroup.index_map_equiv H eAdj.symm
  by_cases hp2 : p = 2
  · subst hp2
    have hle := two_mul_pow_six_le_index_adjointGroup_F4_of_charP_two M hM
    rwa [hK, hidx] at hle
  · have h2 : (2 : K) ≠ 0 := by
      have := natCast_ne_zero_of_ne (K := K) (p := p) Nat.prime_two hp2
      simpa using this
    have hF7 := HeisGenFacts.of_codeFacts genCodeFacts_F4
    have hC7 : ∀ β ∈ genS .F4 [34953, 34969, 35481, 35225, 35497, 39321, 39577],
        ((commConst .F4 (decodeVec 44218 - β) β (1, 1) : ℤ) : K) ≠ 0 :=
      fun β hβ => commConst_cast_ne_zero_F4_of_two_ne_zero hF7 h2 hβ
    have hle := HeisSystem.card_le_index_of_isSimpleGroup
      (heisSystemGen (K := K) hF7 hC7) M hM
    rw [Nat.card_fun, hK, nat_card_coe_finset_eq, card_genS_F4_seven, hidx] at hle
    have hq2 : 2 ≤ p ^ f := (Nat.pow_le_pow_left hp.two_le 1).trans (Nat.pow_le_pow_right hp.pos hf)
    calc 2 * (p ^ f) ^ 6
        ≤ (p ^ f) * (p ^ f) ^ 6 := Nat.mul_le_mul_right _ hq2
      _ = (p ^ f) ^ 7 := (pow_succ' (p ^ f) 6).symm
      _ ≤ H.index := hle

/-- Any primitive almost simple group `G ≤ Perm α` with socle `F₄(p^f)` satisfies
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_chevalley_F4 {α : Type} [Finite α]
    {G : Subgroup (Equiv.Perm α)} [MulAction.IsPreprimitive G α]
    {S : Type} [Group S] {p f : ℕ} (hAS : IsAlmostSimpleWith G S)
    (h : ChevalleyExceptionalModel S .F4 p f) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsSimpleGroup S := hAS.isSimpleGroup
  have hcard : Nat.card S = ordF4 (p ^ f) := card_chevalleyExceptionalModel h
  have hout := (card_outerAut_F4 h).2
  have hidx : ∀ H : Subgroup S, H ≠ ⊤ → 2 * (p ^ f) ^ 6 ≤ H.index :=
    fun H hH => index_ge_of_chevalley_F4 h H hH
  obtain ⟨⟨hp, hf, -⟩, -⟩ := h
  have hq2 : 2 ≤ p ^ f := (Nat.pow_le_pow_left hp.two_le 1).trans (Nat.pow_le_pow_right hp.pos hf)
  have hfq : f ≤ p ^ f := (Nat.lt_pow_self hp.one_lt).le
  refine hAS.card_le_bound_of_outerAut_le hidx hout ?_
  rw [hcard]
  by_cases hq3 : 3 ≤ p ^ f
  · have h1024 : 2 ^ 10 ≤ 2 * (p ^ f) ^ 6 :=
      (by decide : 2 ^ 10 ≤ 2 * 3 ^ 6).trans
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hq3 6))
    have hlog : 10 ≤ Nat.log 2 (2 * (p ^ f) ^ 6) := Nat.le_log_of_pow_le (by decide) h1024
    have hq_cube : 2 * (p ^ f) ≤ (p ^ f) ^ 3 := by
      calc 2 * (p ^ f) ≤ 2 ^ 2 * (p ^ f) ^ 1 := by
            rw [pow_one]
            exact Nat.mul_le_mul_right _ (by decide)
        _ ≤ (p ^ f) ^ 2 * (p ^ f) ^ 1 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hq2 2)
        _ = (p ^ f) ^ 3 := by ring
    have hq6 : (p ^ f) ^ 6 ≤ 2 * (p ^ f) ^ 6 := Nat.le_mul_of_pos_left _ (by decide)
    have hq0 : 0 < p ^ f := by omega
    have hn0 : 0 < 2 * (p ^ f) ^ 6 := by positivity
    calc ordF4 (p ^ f) * (2 * f)
        ≤ (p ^ f) ^ 52 * (2 * (p ^ f)) :=
          Nat.mul_le_mul (ordF4_le_pow (p ^ f)) (Nat.mul_le_mul_left 2 hfq)
      _ ≤ (p ^ f) ^ 52 * (p ^ f) ^ 3 := Nat.mul_le_mul_left _ hq_cube
      _ = (p ^ f) ^ 55 := by ring
      _ ≤ (p ^ f) ^ 60 := Nat.pow_le_pow_right hq0 (by decide)
      _ = ((p ^ f) ^ 6) ^ 10 := by ring
      _ ≤ (2 * (p ^ f) ^ 6) ^ 10 := Nat.pow_le_pow_left hq6 10
      _ ≤ (2 * (p ^ f) ^ 6) ^ Nat.log 2 (2 * (p ^ f) ^ 6) := Nat.pow_le_pow_right hn0 hlog
      _ ≤ bound (2 * (p ^ f) ^ 6) := pow_log_le_bound hn0
  · have hq_eq : p ^ f = 2 := by omega
    have hf1 : f = 1 := by
      by_contra hne
      have hf2 : 2 ≤ f := by omega
      have : 4 ≤ p ^ f :=
        (Nat.pow_le_pow_left hp.two_le 2).trans (Nat.pow_le_pow_right hp.pos hf2)
      omega
    rw [hq_eq, hf1]
    exact (Nat.mul_le_mul_right 2 (ordF4_le_pow 2)).trans (by decide)

end Maroti
