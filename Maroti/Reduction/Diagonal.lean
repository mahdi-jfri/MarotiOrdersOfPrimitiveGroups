module

public import Maroti.Reduction.Socle
public import CFSG.Assembly.OrderReductions.PermutationReduction

/-!
# Diagonal action reduction

This file proves the diagonal action case of Step 1 in Section 2 of A. Maróti,
*On the orders of primitive groups*, J. Algebra 258 (2002), pages 633–634, where a minimal normal
subgroup `N` of `G` has `r ≥ 2` nonabelian simple factors `F.S i` and the point stabilizer
`K = stabilizer N ω` projects surjectively onto every factor `F.S i`.

Every proper subgroup of a finite nonabelian simple group has index at least `5`
(`five_le_index_of_isNonabelianSimple`, from
`CFSG.OrderReductions.PermutationReduction.simple_noncommutative_proper_subgroup_index_ge_five` in
`CFSG/Assembly/OrderReductions/PermutationReduction.lean`), and every finite nonabelian simple
group has order at least `32` (`thirty_two_le_card_of_isNonabelianSimple`).

When `r ≥ 2`, `C_G(N) = ⊥`, and every projection `(stabilizer N ω).map (F.proj i)` is `⊤`,
repeated commutators in the perfect simple groups `F.S i` show that the kernels
`A i = ker (F.proj i|_K)` fall into equivalence classes of size at least `2`
(`SimpleFactors.forall_exists_ne_kerProjStab_eq`). Choosing one representative from each class
projects `K` injectively into the product of at most `r / 2` factors `F.S i`, giving
`|K| ≤ |F.S 0|^{r / 2}` (`SimpleFactors.card_stabilizer_le_pow_half`). Therefore
`|α| = [N : K] ≥ |F.S 0|^{(r + 1) / 2}`, and combining `|G| ≤ r! · |MulAut (F.S 0)|^r` with
`diagonal_bound_le` yields `|G| ≤ bound |α|`
(`SimpleFactors.card_le_bound_of_forall_map_proj_eq_top`).
-/

@[expose] public section

namespace Maroti

open Equiv MulAction CFSG.Holt.General.AltRecPrim

theorem not_isMulCommutative_of_isNonabelianSimple {S : Type} [Group S]
    (hS : IsNonabelianSimple S) : ¬ IsMulCommutative S := by
  rintro ⟨⟨hcomm⟩⟩
  obtain ⟨x, y, hxy⟩ := hS.2
  exact hxy (hcomm x y)

/-- Every proper subgroup of a finite nonabelian simple group has index at least `5`
(`CFSG.OrderReductions.PermutationReduction.simple_noncommutative_proper_subgroup_index_ge_five`,
`CFSG/Assembly/OrderReductions/PermutationReduction.lean`). -/
theorem five_le_index_of_isNonabelianSimple {S : Type} [Group S] [Finite S]
    (hS : IsNonabelianSimple S) (H : Subgroup S) (hH : H ≠ ⊤) : 5 ≤ H.index := by
  have := hS.1
  exact
    CFSG.OrderReductions.PermutationReduction.simple_noncommutative_proper_subgroup_index_ge_five
      S (not_isMulCommutative_of_isNonabelianSimple hS) H hH

theorem five_mul_prime_pow_le_card_of_dvd {S : Type} [Group S] [Finite S]
    (hS : IsNonabelianSimple S) (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (hdvd : p ^ k ∣ Nat.card S) : 5 * p ^ k ≤ Nat.card S := by
  have := hS.1
  have hnc := not_isMulCommutative_of_isNonabelianSimple hS
  obtain ⟨P⟩ : Nonempty (Sylow p S) := inferInstance
  have hpk : p ^ k ≤ Nat.card P :=
    Nat.le_of_dvd Nat.card_pos (P.pow_dvd_card_of_pow_dvd_card hdvd)
  have hp : p ∣ Nat.card S := (pow_one p ▸ Nat.pow_dvd_pow p hk).trans hdvd
  have h5 :=
    CFSG.OrderReductions.PermutationReduction.simple_noncommutative_sylow_card_mul_five_le_card
      S hnc p hp P
  omega

/-- Every finite nonabelian simple group has order at least `32`, proved from Sylow index bounds
in `CFSG/Assembly/OrderReductions/PermutationReduction.lean`. -/
theorem thirty_two_le_card_of_isNonabelianSimple (S : Type) [Group S] [Finite S]
    (hS : IsNonabelianSimple S) : 32 ≤ Nat.card S := by
  have := hS.1
  have hnc := not_isMulCommutative_of_isNonabelianSimple hS
  by_contra hlt
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hle : Nat.card S ≤ 31 := by omega
  have hmin : (Nat.card S).minFac ^ 2 ∣ Nat.card S :=
    CFSG.OrderReductions.Helpers.simple_noncommutative_minFac_sq_dvd_card S hnc
  have hnot_360 : ¬ Nat.card S ∣ 360 := by
    intro hdvd
    have h60 :=
      CFSG.OrderReductions.PermutationReduction.simple_noncommutative_small_order_of_dvd_360
        S hnc hdvd
    omega
  have hp_le : (Nat.card S).minFac ≤ 5 := by
    have hsq_le : (Nat.card S).minFac ^ 2 ≤ 31 := (Nat.le_of_dvd hpos hmin).trans hle
    nlinarith
  have hp_ge : 2 ≤ (Nat.card S).minFac := by
    have hne1 : Nat.card S ≠ 1 := fun h1 => hnot_360 (h1 ▸ one_dvd 360)
    exact (Nat.minFac_prime hne1).two_le
  have hsq : 4 ∣ Nat.card S ∨ 9 ∣ Nat.card S ∨ 25 ∣ Nat.card S := by
    generalize (Nat.card S).minFac = p at hp_ge hp_le hmin
    interval_cases p
    · exact Or.inl hmin
    · exact Or.inr (Or.inl hmin)
    · exact Or.inl ((by decide : 4 ∣ 4 ^ 2).trans hmin)
    · exact Or.inr (Or.inr hmin)
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h16 : ¬ 2 ^ 4 ∣ Nat.card S := fun h => by
    have := five_mul_prime_pow_le_card_of_dvd hS 2 4 (by decide) h; omega
  have h27 : ¬ 3 ^ 3 ∣ Nat.card S := fun h => by
    have := five_mul_prime_pow_le_card_of_dvd hS 3 3 (by decide) h; omega
  have h25 : ¬ 5 ^ 2 ∣ Nat.card S := fun h => by
    have := five_mul_prime_pow_le_card_of_dvd hS 5 2 (by decide) h; omega
  have h7 : ¬ 7 ^ 1 ∣ Nat.card S := fun h => by
    have := five_mul_prime_pow_le_card_of_dvd hS 7 1 (by decide) h; omega
  rcases hsq with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk1 : 1 ≤ k := by omega
    have hk7 : k ≤ 7 := by omega
    interval_cases k
    · exact hnot_360 (by rw [hk]; decide)
    · exact hnot_360 (by rw [hk]; decide)
    · exact hnot_360 (by rw [hk]; decide)
    · exact h16 (by rw [hk]; decide)
    · exact hnot_360 (by rw [hk]; decide)
    · exact hnot_360 (by rw [hk]; decide)
    · exact h7 (by rw [hk]; decide)
  · have hk1 : 1 ≤ k := by omega
    have hk3 : k ≤ 3 := by omega
    interval_cases k
    · exact hnot_360 (by rw [hk]; decide)
    · exact hnot_360 (by rw [hk]; decide)
    · exact h27 (by rw [hk]; decide)
  · have hk1 : k = 1 := by omega
    subst hk1
    exact h25 (by rw [hk]; decide)

/-- If every fiber of `f : Fin r → β` has at least two elements, then there is a subset
`R : Finset (Fin r)` of size `2 * R.card ≤ r` that meets every fiber of `f`. -/
theorem exists_finset_card_le_half_of_forall_exists_ne {r : ℕ} {β : Type*}
    (f : Fin r → β) (hf : ∀ i : Fin r, ∃ j ≠ i, f j = f i) :
    ∃ R : Finset (Fin r), 2 * R.card ≤ r ∧ ∀ j : Fin r, ∃ i ∈ R, f i = f j := by
  classical
  let R : Finset (Fin r) := Finset.univ.filter fun i => ∀ j : Fin r, f j = f i → i ≤ j
  have hR_inj : ∀ i₁ ∈ R, ∀ i₂ ∈ R, f i₁ = f i₂ → i₁ = i₂ := by
    intro i₁ hi₁ i₂ hi₂ h12
    have h1 := (Finset.mem_filter.mp hi₁).2 i₂ h12.symm
    have h2 := (Finset.mem_filter.mp hi₂).2 i₁ h12
    exact le_antisymm h1 h2
  let g : Fin r → Fin r := fun i => (hf i).choose
  have hg_ne : ∀ i, g i ≠ i := fun i => (hf i).choose_spec.1
  have hg_eq : ∀ i, f (g i) = f i := fun i => (hf i).choose_spec.2
  have hinj : Set.InjOn g R := by
    intro i₁ hi₁ i₂ hi₂ hg12
    apply hR_inj i₁ hi₁ i₂ hi₂
    rw [← hg_eq i₁, hg12, hg_eq i₂]
  have hdisj : Disjoint R (R.image g) := by
    rw [Finset.disjoint_left]
    intro x hxR hximg
    obtain ⟨i, hiR, rfl⟩ := Finset.mem_image.mp hximg
    have hxi : g i = i := hR_inj (g i) hxR i hiR (hg_eq i)
    exact hg_ne i hxi
  have hcard : 2 * R.card ≤ r := by
    calc 2 * R.card = R.card + R.card := Nat.two_mul R.card
      _ = R.card + (R.image g).card := by rw [Finset.card_image_of_injOn hinj]
      _ = (R ∪ R.image g).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_univ _
      _ = r := Fintype.card_fin r
  refine ⟨R, hcard, fun j => ?_⟩
  let C : Finset (Fin r) := Finset.univ.filter fun i => f i = f j
  have hjC : j ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩
  let i₀ := C.min' ⟨j, hjC⟩
  have hi₀C : i₀ ∈ C := Finset.min'_mem C ⟨j, hjC⟩
  have hfi₀ : f i₀ = f j := (Finset.mem_filter.mp hi₀C).2
  have hi₀R : i₀ ∈ R := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i₀, fun k hki => ?_⟩
    have hkC : k ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki.trans hfi₀⟩
    exact Finset.min'_le C k hkC
  exact ⟨i₀, hi₀R, hfi₀⟩

namespace SimpleFactors

variable {α : Type} {G : Subgroup (Perm α)} {N : Subgroup G} (F : SimpleFactors N)

/-- The restriction of `F.proj i` to `stabilizer N ω`. -/
noncomputable def projStab (ω : α) (i : Fin F.r) : stabilizer N ω →* F.S i :=
  (F.proj i).comp (stabilizer N ω).subtype

/-- The kernel `A i = {k ∈ stabilizer N ω | F.proj i k = 1}`. -/
noncomputable def kerProjStab (ω : α) (i : Fin F.r) : Subgroup (stabilizer N ω) :=
  (projStab F ω i).ker

instance kerProjStab_normal (ω : α) (i : Fin F.r) : (kerProjStab F ω i).Normal :=
  (projStab F ω i).normal_ker

theorem projStab_surjective (ω : α) {i : Fin F.r}
    (hi : (stabilizer N ω).map (F.proj i) = ⊤) :
    Function.Surjective (projStab F ω i) := by
  intro s
  have hs : s ∈ (stabilizer N ω).map (F.proj i) := hi ▸ Subgroup.mem_top s
  obtain ⟨k, hk, rfl⟩ := hs
  exact ⟨⟨k, hk⟩, rfl⟩

theorem card_S_eq (i j : Fin F.r) : Nat.card (F.S i) = Nat.card (F.S j) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_S F i j
  exact Nat.card_congr e.toEquiv

theorem isNonabelianSimple_S (i : Fin F.r) : IsNonabelianSimple (F.S i) := by
  refine ⟨F.isSimpleGroup i, ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute i
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩

theorem card_kerProjStab_eq [Finite G] (ω : α)
    (hK : ∀ i : Fin F.r, (stabilizer N ω).map (F.proj i) = ⊤) (i j : Fin F.r) :
    Nat.card (kerProjStab F ω i) = Nat.card (kerProjStab F ω j) := by
  have hidx : ∀ l : Fin F.r, (kerProjStab F ω l).index = Nat.card (F.S l) := by
    intro l
    rw [kerProjStab, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (projStab_surjective F ω (hK l))]
    exact Subgroup.card_top
  have h1 := (kerProjStab F ω i).card_mul_index
  have h2 := (kerProjStab F ω j).card_mul_index
  rw [hidx i, card_S_eq F i j] at h1
  rw [hidx j] at h2
  have hpos : 0 < Nat.card (F.S j) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem map_kerProjStab_eq_top_of_ne [Finite G] (ω : α)
    (hK : ∀ l : Fin F.r, (stabilizer N ω).map (F.proj l) = ⊤) {i j : Fin F.r}
    (hne : kerProjStab F ω j ≠ kerProjStab F ω i) :
    (kerProjStab F ω j).map (projStab F ω i) = ⊤ := by
  have := F.isSimpleGroup i
  have hnorm : ((kerProjStab F ω j).map (projStab F ω i)).Normal :=
    Subgroup.Normal.map inferInstance (projStab F ω i) (projStab_surjective F ω (hK i))
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · exfalso
    apply hne
    have hle : kerProjStab F ω j ≤ kerProjStab F ω i := by
      intro k hk
      rw [kerProjStab, MonoidHom.mem_ker]
      have hmem : projStab F ω i k ∈ (kerProjStab F ω j).map (projStab F ω i) := ⟨k, hk, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.eq_of_le_of_card_ge hle (card_kerProjStab_eq F ω hK i j).le
  · exact htop

theorem commutator_S_top_eq_top (i : Fin F.r) :
    ⁅(⊤ : Subgroup (F.S i)), (⊤ : Subgroup (F.S i))⁆ = ⊤ := by
  have := F.isSimpleGroup i
  have := CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect (F.S i)
    (not_isMulCommutative_of_isNonabelianSimple (isNonabelianSimple_S F i))
  exact Group.IsPerfect.commutator_eq_top

theorem exists_normal_le_kerProjStab_map_eq_top [Finite G] (ω : α)
    (hK : ∀ l : Fin F.r, (stabilizer N ω).map (F.proj l) = ⊤) (i : Fin F.r)
    (hno : ∀ j : Fin F.r, j ≠ i → kerProjStab F ω j ≠ kerProjStab F ω i)
    (s : Finset (Fin F.r)) (his : i ∉ s) :
    ∃ B : Subgroup (stabilizer N ω), B.Normal ∧
      (∀ j ∈ s, B ≤ kerProjStab F ω j) ∧ B.map (projStab F ω i) = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⊤, inferInstance, fun j hj => False.elim (Finset.notMem_empty j hj), ?_⟩
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (projStab_surjective F ω (hK i))
  | @insert j₀ s hj₀ ih =>
    have hj₀i : j₀ ≠ i := fun h => his (h ▸ Finset.mem_insert_self j₀ s)
    have his' : i ∉ s := fun h => his (Finset.mem_insert_of_mem h)
    obtain ⟨B, hBnorm, hBle, hBmap⟩ := ih his'
    refine ⟨⁅B, kerProjStab F ω j₀⁆, Subgroup.commutator_normal B (kerProjStab F ω j₀), ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Subgroup.commutator_le_right B (kerProjStab F ω j)
      · exact (Subgroup.commutator_le_left B (kerProjStab F ω j₀)).trans (hBle j hjs)
    · rw [Subgroup.map_commutator, hBmap, map_kerProjStab_eq_top_of_ne F ω hK (hno j₀ hj₀i),
        commutator_S_top_eq_top F i]

theorem subgroupOf_S_le_stabilizer_of_forall_kerProjStab_ne [Finite G] (ω : α)
    (hK : ∀ l : Fin F.r, (stabilizer N ω).map (F.proj l) = ⊤) (i : Fin F.r)
    (hno : ∀ j : Fin F.r, j ≠ i → kerProjStab F ω j ≠ kerProjStab F ω i) :
    (F.S i).subgroupOf N ≤ stabilizer N ω := by
  classical
  obtain ⟨B, -, hBle, hBmap⟩ := exists_normal_le_kerProjStab_map_eq_top F ω hK i hno
    (Finset.univ.erase i) (Finset.notMem_erase i Finset.univ)
  intro n hn
  have htop : (⟨(n : G), hn⟩ : F.S i) ∈ B.map (projStab F ω i) := hBmap ▸ Subgroup.mem_top _
  obtain ⟨b, hbB, hbi⟩ := htop
  have hsingle : ∀ j : Fin F.r, j ≠ i → F.e.symm (b : N) j = 1 := by
    intro j hj
    have hbj : b ∈ kerProjStab F ω j :=
      hBle j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) hbB
    exact hbj
  have hval : ((b : N) : G) = (n : G) := by
    have h1 := F.e_single i (F.e.symm (b : N)) hsingle
    rw [F.e.apply_symm_apply] at h1
    exact h1.trans (congrArg Subtype.val hbi)
  have hbn : (b : N) = n := Subtype.ext hval
  exact hbn ▸ b.2

theorem subgroupOf_S_le_stabilizer_of_coordPermHom (hN : N.Normal) (ω : α)
    {g : G} (hg : g ∈ stabilizer G ω) {i j : Fin F.r} (hij : coordPermHom F hN g i = j)
    (hi : (F.S i).subgroupOf N ≤ stabilizer N ω) :
    (F.S j).subgroupOf N ≤ stabilizer N ω := by
  have hmap : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j := by
    rw [map_conj_eq_coordPermHom F hN, hij]
  intro n hn
  rw [Subgroup.mem_subgroupOf, ← hmap] at hn
  obtain ⟨s, hs, hgs⟩ := hn
  have hsK : (⟨s, F.le i hs⟩ : N) ∈ stabilizer N ω := hi hs
  have hconj := conj_mem_stabilizer_N hN ω hg hsK
  have heq : (⟨g * s * g⁻¹, hN.conj_mem s (F.le i hs) g⟩ : N) = n := Subtype.ext hgs
  exact heq ▸ hconj

theorem eq_top_of_forall_subgroupOf_S_le {H : Subgroup N}
    (hall : ∀ i : Fin F.r, (F.S i).subgroupOf N ≤ H) : H = ⊤ := by
  classical
  have key : ∀ (s : Finset (Fin F.r)) (x : ∀ i : Fin F.r, F.S i),
      (∀ i ∉ s, x i = 1) → F.e x ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      have hx1 : x = 1 := funext fun i => hx i (Finset.notMem_empty i)
      rw [hx1, map_one]
      exact one_mem H
    | @insert i₀ s hi₀ ih =>
      intro x hx
      let y : ∀ i : Fin F.r, F.S i := (Pi.mulSingle i₀ (x i₀))⁻¹ * x
      have hxy : x = Pi.mulSingle i₀ (x i₀) * y :=
        (mul_inv_cancel_left (Pi.mulSingle i₀ (x i₀)) x).symm
      rw [hxy, map_mul]
      refine mul_mem (hall i₀ ?_) (ih y fun i his => ?_)
      · rw [Subgroup.mem_subgroupOf, F.e_mulSingle]
        exact (x i₀).2
      · by_cases hi : i = i₀
        · subst hi
          simp [y]
        · have hi' : i ∉ insert i₀ s := fun h => (Finset.mem_insert.mp h).elim hi his
          simp [y, Pi.mulSingle_eq_of_ne hi, hx i hi']
  rw [eq_top_iff]
  intro n _
  rw [← F.e.apply_symm_apply n]
  exact key Finset.univ (F.e.symm n) fun i hi => False.elim (hi (Finset.mem_univ i))

theorem stabilizer_eq_top_of_forall_subgroupOf_S_le (ω : α)
    (hall : ∀ i : Fin F.r, (F.S i).subgroupOf N ≤ stabilizer N ω) :
    stabilizer N ω = ⊤ :=
  eq_top_of_forall_subgroupOf_S_le F hall

theorem forall_exists_ne_kerProjStab_eq [Finite G] [IsPretransitive N α] (hN : N.Normal) (ω : α)
    (hK : ∀ l : Fin F.r, (stabilizer N ω).map (F.proj l) = ⊤)
    (hKne : stabilizer N ω ≠ ⊤) (i : Fin F.r) :
    ∃ j ≠ i, kerProjStab F ω j = kerProjStab F ω i := by
  by_contra h
  push Not at h
  have hi : (F.S i).subgroupOf N ≤ stabilizer N ω :=
    subgroupOf_S_le_stabilizer_of_forall_kerProjStab_ne F ω hK i h
  apply hKne
  apply stabilizer_eq_top_of_forall_subgroupOf_S_le F ω
  intro j
  obtain ⟨g, hg, hij⟩ := exists_mem_stabilizer_coordPermHom_eq F hN ω i j
  exact subgroupOf_S_le_stabilizer_of_coordPermHom F hN ω hg hij hi

theorem card_N_eq [Finite G] : Nat.card N = Nat.card (F.S ⟨0, F.one_le⟩) ^ F.r := by
  rw [← Nat.card_congr F.e.toEquiv, Nat.card_pi]
  have hcongr : ∀ i : Fin F.r, Nat.card (F.S i) = Nat.card (F.S ⟨0, F.one_le⟩) :=
    fun i => card_S_eq F i ⟨0, F.one_le⟩
  simp [hcongr]

theorem card_stabilizer_le_pow_half [Finite G] [IsPretransitive N α] (hN : N.Normal) (ω : α)
    (hK : ∀ l : Fin F.r, (stabilizer N ω).map (F.proj l) = ⊤)
    (hKne : stabilizer N ω ≠ ⊤) :
    Nat.card (stabilizer N ω) ≤ Nat.card (F.S ⟨0, F.one_le⟩) ^ (F.r / 2) := by
  obtain ⟨R, hRcard, hRcover⟩ := exists_finset_card_le_half_of_forall_exists_ne
    (kerProjStab F ω) (forall_exists_ne_kerProjStab_eq F hN ω hK hKne)
  let φ : stabilizer N ω →* ∀ i : R, F.S i.1 :=
    MonoidHom.pi fun i => projStab F ω i.1
  have hφ_inj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply F.eq_one_of_forall_proj_eq_one
    intro j
    obtain ⟨i, hiR, hij⟩ := hRcover j
    have hki : k ∈ kerProjStab F ω i := by
      have := congrArg (fun f : ∀ l : R, F.S l.1 => f ⟨i, hiR⟩) (MonoidHom.mem_ker.mp hk)
      exact this
    rw [hij] at hki
    exact hki
  have hcard_le := Nat.card_le_card_of_injective φ hφ_inj
  have hpi : Nat.card (∀ i : R, F.S i.1) = Nat.card (F.S ⟨0, F.one_le⟩) ^ R.card := by
    simp only [Nat.card_pi]
    have hcongr : ∀ i : R, Nat.card (F.S i.1) = Nat.card (F.S ⟨0, F.one_le⟩) :=
      fun i => card_S_eq F i.1 ⟨0, F.one_le⟩
    simp [hcongr]
  have hpow : Nat.card (F.S ⟨0, F.one_le⟩) ^ R.card ≤
      Nat.card (F.S ⟨0, F.one_le⟩) ^ (F.r / 2) :=
    Nat.pow_le_pow_right Nat.card_pos (by omega)
  exact (hcard_le.trans hpi.le).trans hpow

/-- In the diagonal case (`r ≥ 2` and every projection `(stabilizer N ω).map (F.proj i)` is `⊤`),
we have `|G| ≤ bound |α|` (Maróti, Section 2, Step 1, pages 633–634). -/
theorem card_le_bound_of_forall_map_proj_eq_top [Finite α] [IsPreprimitive G α]
    (hAut : AutBound IsNonabelianSimple) (hN : N.Normal)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) (hr : 2 ≤ F.r) (ω : α)
    (hK : ∀ l : Fin F.r, (stabilizer N ω).map (F.proj l) = ⊤)
    (h2 : 2 ≤ Nat.card α) :
    Nat.card G ≤ bound (Nat.card α) := by
  let S₀ := F.S ⟨0, F.one_le⟩
  have hNne : N ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute ⟨0, F.one_le⟩
    have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ F.le _ ha)
    rw [ha1, one_mul, mul_one] at hab
    exact hab rfl
  have htr : IsPretransitive N α := isPretransitive_of_normal_ne_bot hNne
  have hidx_eq : (stabilizer N ω).index = Nat.card α := by
    rw [Subgroup.index_eq_card, Nat.card_congr (orbitEquivQuotientStabilizer N ω).symm,
      orbit_eq_univ N ω, Nat.card_univ]
  have hKne : stabilizer N ω ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hidx_eq
    omega
  have hKcard := card_stabilizer_le_pow_half F hN ω hK hKne
  have hmul : Nat.card (stabilizer N ω) * Nat.card α = Nat.card S₀ ^ F.r := by
    rw [← hidx_eq, (stabilizer N ω).card_mul_index, card_N_eq F]
  have hn_ge : Nat.card S₀ ^ ((F.r + 1) / 2) ≤ Nat.card α := by
    have hsplit : F.r = F.r / 2 + (F.r + 1) / 2 := by omega
    have hpow_eq : Nat.card S₀ ^ F.r =
        Nat.card S₀ ^ (F.r / 2) * Nat.card S₀ ^ ((F.r + 1) / 2) := by
      rw [← pow_add, ← hsplit]
    have hle : Nat.card (stabilizer N ω) * Nat.card α ≤
        Nat.card S₀ ^ (F.r / 2) * Nat.card α :=
      Nat.mul_le_mul_right (Nat.card α) hKcard
    rw [hmul, hpow_eq] at hle
    exact Nat.le_of_mul_le_mul_left hle (Nat.pow_pos Nat.card_pos)
  have ht32 : 32 ≤ Nat.card S₀ :=
    thirty_two_le_card_of_isNonabelianSimple S₀ (isNonabelianSimple_S F ⟨0, F.one_le⟩)
  have hAutS₀ : Nat.card (MulAut S₀) ≤ Nat.card S₀ ^ 2 :=
    hAut S₀ (isNonabelianSimple_S F ⟨0, F.one_le⟩)
  have hG1 := card_le_factorial_mul_card_mulAut_pow F hN hC
  have hG2 : F.r.factorial * Nat.card (MulAut S₀) ^ F.r ≤
      F.r.factorial * (Nat.card S₀) ^ (2 * F.r) := by
    rw [pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hAutS₀ F.r)
  have hG3 := diagonal_bound_le ht32 hr
  have hG4 := bound_mono hn_ge
  exact ((hG1.trans hG2).trans hG3).trans hG4

end SimpleFactors

end Maroti
