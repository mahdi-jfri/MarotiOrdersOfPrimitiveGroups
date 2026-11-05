module

public import Maroti.Reduction.ProductAction

/-!
# Step 1: Reduction to almost simple groups

This file proves `Maroti.step1`, which reduces Theorem 1.1 of A. Maróti,
*On the orders of primitive groups*, J. Algebra 258 (2002), Section 2, Step 1, pages 633–634, from
arbitrary finite primitive permutation groups `G ≤ Perm α` of degree at least `2` to almost simple
primitive permutation groups.

If `|G| = 1`, then `|G| = 1 ≤ bound |α|`.
Otherwise `G` is nontrivial and acts primitively on the nontrivial finite set `α`. Let `N` be a
minimal normal subgroup of `G` (`exists_minimal_normal`). If `C_G(N) ≠ ⊥` or `N` is abelian, then
`|G| ≤ bound |α|` (`card_le_bound_of_centralizer_ne_bot`, `card_le_bound_of_comm_normal`).

When `C_G(N) = ⊥` and `N` is nonabelian, `N` is a direct product of `r ≥ 1` conjugate nonabelian
simple subgroups `F.S i` (`CFSG.Holt.General.AltRecPrim.nonempty_simpleFactors` in
`CFSG/Holt/General/AltRecPrimitiveONanScott.lean`). If `r = 1`, then `G` is almost simple with
socle `F.S 0` (`SimpleFactors.isAlmostSimpleWith_of_r_eq_one`) and the almost simple hypothesis
`hAS` gives `Conclusion G`. If `r ≥ 2` and `N_ω = ⊥`, then `N` acts regularly on `α` and
`|G| ≤ bound |α|` (`card_le_bound_of_regular_normal`). Finally, if `r ≥ 2` and `N_ω ≠ ⊥`, then
either every projection `(N_ω).map (F.proj i)` is `⊤`, giving `|G| ≤ bound |α|` by the diagonal
bound (`SimpleFactors.card_le_bound_of_forall_map_proj_eq_top`), or every projection is a proper
subgroup of `F.S i`, in which case applying `hAS` to the primitive almost simple component `H 0`
on `Δ 0 = F.S 0 ⧸ R 0` gives `Conclusion G`
(`SimpleFactors.conclusion_of_forall_map_proj_ne_top`).
-/

@[expose] public section

namespace Maroti

open Equiv MulAction CFSG.Holt.General.AltRecPrim

theorem stabilizer_map_subtype_eq_bot {α : Type*} {G : Subgroup (Perm α)} {N : Subgroup G}
    {ω : α} (hK : stabilizer N ω = ⊥) :
    stabilizer (N.map G.subtype) ω = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨_, n, hn, rfl⟩ hm
  rw [Subgroup.mem_bot]
  have hn_stab : (⟨n, hn⟩ : N) ∈ stabilizer N ω := mem_stabilizer_iff.mpr (mem_stabilizer_iff.mp hm)
  rw [hK, Subgroup.mem_bot] at hn_stab
  apply Subtype.ext
  exact congrArg (fun x : N => ((x : G) : Perm α)) hn_stab

/-- Step 1 of the proof of Theorem 1.1 (Maróti 2002, Section 2, pages 633–634): if Theorem 1.1
holds for all primitive almost simple permutation groups and every finite nonabelian simple group
`S` satisfies `|MulAut S| ≤ |S|²`, then Theorem 1.1 holds for all finite primitive permutation
groups of degree at least `2`. -/
theorem step1 (hAS : AlmostSimpleCase fun _ _ => True) (hAut : AutBound IsNonabelianSimple)
    {α : Type} [Finite α] [Nontrivial α] (G : Subgroup (Perm α)) [IsPreprimitive G α] :
    Conclusion G := by
  obtain ⟨ω⟩ := (inferInstance : Nonempty α)
  have h2 : 2 ≤ Nat.card α := Finite.one_lt_card
  rcases subsingleton_or_nontrivial G with hSubG | hNontrivG
  · right; right
    have : Unique G := uniqueOfSubsingleton 1
    rw [Nat.card_unique]
    exact (by omega : 1 ≤ Nat.card α).trans (self_le_bound (Nat.card α))
  · obtain ⟨N, hN, hNne, hNmin⟩ := exists_minimal_normal G
    by_cases hC : Subgroup.centralizer (N : Set G) = ⊥
    · by_cases hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a
      · exact Or.inr (Or.inr (card_le_bound_of_comm_normal ω hNne hab))
      · push Not at hab
        obtain ⟨F⟩ := nonempty_simpleFactors hN hNne hNmin hab
        by_cases hr : F.r = 1
        · have has := SimpleFactors.isAlmostSimpleWith_of_r_eq_one hN F hr hC
          exact (hAS α G (F.S ⟨0, F.one_le⟩) inferInstance has trivial).conclusion
        · have hr2 : 2 ≤ F.r := by
            have := F.one_le
            omega
          by_cases hK : stabilizer N ω = ⊥
          · right; right
            have : IsPretransitive (N.map G.subtype) α :=
              isPretransitive_of_normal_subgroup hNne
            exact card_le_bound_of_regular_normal map_subtype_conj_mem ω
              (stabilizer_map_subtype_eq_bot hK)
          · have : IsPretransitive N α := isPretransitive_of_normal_ne_bot hNne
            rcases SimpleFactors.forall_map_proj_eq_top_or_ne_top F hN ω with htop | hne
            · exact Or.inr (Or.inr
                (SimpleFactors.card_le_bound_of_forall_map_proj_eq_top F hAut hN hC hr2 ω htop h2))
            · exact SimpleFactors.conclusion_of_forall_map_proj_ne_top F hAS hN hr2 ω hK hne
    · exact Or.inr (Or.inr (card_le_bound_of_centralizer_ne_bot ω hNne hC))

end Maroti
