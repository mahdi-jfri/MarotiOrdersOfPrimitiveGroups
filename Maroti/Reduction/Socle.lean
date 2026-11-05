module

public import Maroti.Reduction.RegularNormal
public import CFSG.Holt.General.AltRecPrimitiveONanScott

/-!
# Minimal normal subgroups and simple factors of the socle

This file analyzes a minimal normal subgroup `N` of a finite primitive permutation group
`G ≤ Perm α`, as part of Step 1 in Section 2 of A. Maróti, *On the orders of primitive groups*,
J. Algebra 258 (2002), pages 633–634 (see also Dixon and Mortimer, *Permutation Groups*,
Section 4.3).

Every nontrivial finite group `G` has a minimal normal subgroup `N` (`exists_minimal_normal`).
If `G ≤ Perm α` is primitive and either the centralizer `C_G(N)` is nontrivial or `N` is abelian,
then `C_G(N)` or `N` is a regular normal subgroup and `|G| ≤ bound |α|`
(`card_le_bound_of_centralizer_ne_bot`, `card_le_bound_of_comm_normal`).

When `C_G(N) = ⊥` and `N` is nonabelian, `N` decomposes as a direct product of `r ≥ 1` conjugate
nonabelian simple subgroups `F.S i` (`CFSG.Holt.General.AltRecPrim.SimpleFactors` in
`CFSG/Holt/General/AltRecPrimitiveONanScott.lean`). Conjugation gives a homomorphism
`F.coordPermHom hN : G →* Perm (Fin F.r)` whose kernel contains `N` and embeds into
`∏ i, MulAut (F.S i)`, yielding `|G| ≤ r! · |MulAut (F.S 0)|^r`
(`SimpleFactors.card_le_factorial_mul_card_mulAut_pow`). When `r = 1`, `G` is almost simple with
socle `F.S 0` (`SimpleFactors.isAlmostSimpleWith_of_r_eq_one`). Moreover, the point stabilizer
`G_ω` acts transitively on `Fin F.r` and normalizes `K = N_ω`, so either every projection
`π_i(K)` is `⊤` or every projection is a proper subgroup of `F.S i`
(`SimpleFactors.forall_map_proj_eq_top_or_ne_top`).
-/

@[expose] public section

namespace Maroti

open Equiv MulAction CFSG.Holt.General.AltRecPrim

variable {α : Type*}

/-- Every nontrivial finite group has a minimal normal subgroup. -/
theorem exists_minimal_normal (G : Type*) [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
  obtain ⟨N, ⟨hNn, hNne⟩, hNmin⟩ :=
    (Set.toFinite {M : Subgroup G | M.Normal ∧ M ≠ ⊥}).exists_minimal
      ⟨⊤, inferInstance, top_ne_bot⟩
  exact ⟨N, hNn, hNne, fun M hM hle =>
    (em (M = ⊥)).imp id fun hMne => le_antisymm hle (hNmin ⟨hM, hMne⟩ hle)⟩

section SubgroupOfPerm

variable {G : Subgroup (Perm α)}

theorem map_subtype_conj_mem {N : Subgroup G} [hN : N.Normal] :
    ∀ g ∈ G, ∀ n ∈ N.map G.subtype, g * n * g⁻¹ ∈ N.map G.subtype := by
  rintro g hg _ ⟨n, hn, rfl⟩
  exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, hN.conj_mem n hn ⟨g, hg⟩, rfl⟩

theorem isPretransitive_of_normal_subgroup [IsPreprimitive G α] {N : Subgroup G}
    [N.Normal] (hNne : N ≠ ⊥) : IsPretransitive (N.map G.subtype) α := by
  have htr : IsPretransitive N α := isPretransitive_of_normal_ne_bot hNne
  refine ⟨fun x y => ?_⟩
  obtain ⟨n, rfl⟩ := htr.exists_smul_eq x y
  exact ⟨⟨(n : Perm α), (n : G), n.2, rfl⟩, rfl⟩

/-- If `N` is a nontrivial normal subgroup of a primitive group `G ≤ Perm α` and
`C_G(N) ≠ ⊥`, then `|G| ≤ bound |α|`. -/
theorem card_le_bound_of_centralizer_ne_bot [Finite α] [IsPreprimitive G α] (ω : α)
    {N : Subgroup G} [hN : N.Normal] (hNne : N ≠ ⊥)
    (hCne : Subgroup.centralizer (N : Set G) ≠ ⊥) :
    Nat.card G ≤ bound (Nat.card α) := by
  let C : Subgroup G := Subgroup.centralizer (N : Set G)
  have hCnorm : C.Normal := by
    refine ⟨fun c hc g => Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
    have hn' : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    have hc' := Subgroup.mem_centralizer_iff.mp hc (g⁻¹ * n * g) hn'
    calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [hc']
      _ = (g * c * g⁻¹) * n := by group
  have : IsPretransitive (C.map G.subtype) α := isPretransitive_of_normal_subgroup hCne
  have : IsPretransitive (N.map G.subtype) α := isPretransitive_of_normal_subgroup hNne
  apply card_le_bound_of_centralizes_transitive ω (M := C.map G.subtype) (N := N.map G.subtype)
    map_subtype_conj_mem
  rintro _ ⟨c, hc, rfl⟩ _ ⟨n, hn, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc n hn).symm

/-- If `N` is a nontrivial abelian normal subgroup of a primitive group `G ≤ Perm α`, then
`|G| ≤ bound |α|`. -/
theorem card_le_bound_of_comm_normal [Finite α] [IsPreprimitive G α] (ω : α)
    {N : Subgroup G} [N.Normal] (hNne : N ≠ ⊥)
    (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) :
    Nat.card G ≤ bound (Nat.card α) := by
  have : IsPretransitive (N.map G.subtype) α := isPretransitive_of_normal_subgroup hNne
  apply card_le_bound_of_abelian_normal ω (M := N.map G.subtype) map_subtype_conj_mem
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (hab a ha b hb)

end SubgroupOfPerm

namespace SimpleFactors

variable {G : Type*} [Group G] {N : Subgroup G} (F : SimpleFactors N)

theorem S_ne {i j : Fin F.r} (hij : i ≠ j) : F.S i ≠ F.S j := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute i
  exact hab (F.commute_of_ne hij ha (h ▸ hb)).eq

theorem S_injective : Function.Injective F.S :=
  fun _ _ h => by_contra fun hij => S_ne F hij h

theorem map_conj_unique {g : G} {i j j' : Fin F.r}
    (hj : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j)
    (hj' : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j') : j = j' :=
  S_injective F (hj.symm.trans hj')

/-- The index in `Fin F.r` to which `g : G` conjugates `F.S i`. -/
noncomputable def coordFun (hN : N.Normal) (g : G) (i : Fin F.r) : Fin F.r :=
  (F.exists_map_conj_eq hN g i).choose

theorem map_conj_eq_coordFun (hN : N.Normal) (g : G) (i : Fin F.r) :
    (F.S i).map (MulAut.conj g).toMonoidHom = F.S (coordFun F hN g i) :=
  (F.exists_map_conj_eq hN g i).choose_spec

theorem coordFun_eq_iff (hN : N.Normal) (g : G) (i j : Fin F.r) :
    coordFun F hN g i = j ↔ (F.S i).map (MulAut.conj g).toMonoidHom = F.S j :=
  ⟨fun h => h ▸ map_conj_eq_coordFun F hN g i,
    fun h => map_conj_unique F (map_conj_eq_coordFun F hN g i) h⟩

theorem coordFun_one (hN : N.Normal) (i : Fin F.r) : coordFun F hN 1 i = i := by
  rw [coordFun_eq_iff, map_one]
  exact Subgroup.map_id (F.S i)

theorem coordFun_mul (hN : N.Normal) (g h : G) (i : Fin F.r) :
    coordFun F hN (g * h) i = coordFun F hN g (coordFun F hN h i) := by
  rw [coordFun_eq_iff, ← map_conj_eq_coordFun, ← map_conj_eq_coordFun, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The permutation of `Fin F.r` induced by conjugating the simple factors of `N` by `g`. -/
noncomputable def coordPerm (hN : N.Normal) (g : G) : Perm (Fin F.r) where
  toFun := coordFun F hN g
  invFun := coordFun F hN g⁻¹
  left_inv i := by rw [← coordFun_mul, inv_mul_cancel, coordFun_one]
  right_inv i := by rw [← coordFun_mul, mul_inv_cancel, coordFun_one]

/-- The homomorphism `G →* Perm (Fin F.r)` permuting the simple factors of `N`. -/
noncomputable def coordPermHom (hN : N.Normal) : G →* Perm (Fin F.r) where
  toFun := coordPerm F hN
  map_one' := Equiv.ext (coordFun_one F hN)
  map_mul' g h := Equiv.ext (coordFun_mul F hN g h)

@[simp]
theorem coordPermHom_apply (hN : N.Normal) (g : G) (i : Fin F.r) :
    coordPermHom F hN g i = coordFun F hN g i := rfl

theorem map_conj_eq_coordPermHom (hN : N.Normal) (g : G) (i : Fin F.r) :
    (F.S i).map (MulAut.conj g).toMonoidHom = F.S (coordPermHom F hN g i) :=
  map_conj_eq_coordFun F hN g i

theorem coordPermHom_eq_of_mem_N (hN : N.Normal) {n : G} (hn : n ∈ N) :
    coordPermHom F hN n = 1 := by
  apply Equiv.ext
  intro i
  change coordFun F hN n i = i
  rw [coordFun_eq_iff]
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact F.conj_mem ⟨n, hn⟩ hs
  · intro s hs
    exact ⟨n⁻¹ * s * n, by simpa using F.conj_mem ⟨n⁻¹, inv_mem hn⟩ hs, by simp [mul_assoc]⟩

theorem le_ker_coordPermHom (hN : N.Normal) : N ≤ (coordPermHom F hN).ker :=
  fun _ hn => coordPermHom_eq_of_mem_N F hN hn

theorem exists_coordPermHom_eq (hN : N.Normal) (i j : Fin F.r) :
    ∃ g : G, coordPermHom F hN g i = j := by
  obtain ⟨g, hg⟩ := F.conj i j
  exact ⟨g, (coordFun_eq_iff F hN g i j).mpr hg.symm⟩

/-- An element `g ∈ (coordPermHom F hN).ker` normalizes every factor `F.S i`. -/
theorem conj_mem_S_of_mem_ker (hN : N.Normal) {g : G} (hg : g ∈ (coordPermHom F hN).ker)
    (i : Fin F.r) {s : G} (hs : s ∈ F.S i) : g * s * g⁻¹ ∈ F.S i := by
  have h1 : coordPermHom F hN g i = i := by
    rw [MonoidHom.mem_ker.mp hg, Perm.one_apply]
  rw [← h1, ← map_conj_eq_coordPermHom F hN g i]
  exact ⟨s, hs, rfl⟩

/-- The automorphism of `F.S i` induced by an element of `(coordPermHom F hN).ker`. -/
noncomputable def factorAut (hN : N.Normal) (i : Fin F.r) (g : (coordPermHom F hN).ker) :
    MulAut (F.S i) where
  toFun s := ⟨(g : G) * s * (g : G)⁻¹, conj_mem_S_of_mem_ker F hN g.2 i s.2⟩
  invFun s := ⟨(g : G)⁻¹ * s * (g : G), by
    simpa using conj_mem_S_of_mem_ker F hN (inv_mem g.2) i s.2⟩
  left_inv s := by apply Subtype.ext; simp [mul_assoc]
  right_inv s := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- The homomorphism `(coordPermHom F hN).ker →* ∀ i, MulAut (F.S i)`. -/
noncomputable def kerToPiAut (hN : N.Normal) :
    (coordPermHom F hN).ker →* ∀ i : Fin F.r, MulAut (F.S i) where
  toFun g i := factorAut F hN i g
  map_one' := by
    funext i
    ext s
    simp [factorAut]
  map_mul' g h := by
    funext i
    ext s
    simp [factorAut, mul_assoc]

theorem kerToPiAut_injective (hN : N.Normal) (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (kerToPiAut F hN) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hgC : (g : G) ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hgn : (g : G) * n * (g : G)⁻¹ ∈ N := hN.conj_mem n hn g
    have hproj : ∀ i : Fin F.r, F.proj i ⟨(g : G) * n * (g : G)⁻¹, hgn⟩ = F.proj i ⟨n, hn⟩ := by
      intro i
      apply Subtype.ext
      have hmap : (F.S i).map (MulAut.conj (g : G)).toMonoidHom = F.S i := by
        have h1 : coordPermHom F hN g i = i := by
          rw [MonoidHom.mem_ker.mp g.2, Perm.one_apply]
        rw [map_conj_eq_coordPermHom F hN, h1]
      rw [F.proj_conj hmap ⟨n, hn⟩ hgn]
      have hgi := congrArg (fun φ : ∀ j, MulAut (F.S j) => (φ i (F.proj i ⟨n, hn⟩) : G)) hg
      exact hgi
    have heq : (⟨(g : G) * n * (g : G)⁻¹, hgn⟩ : N) = ⟨n, hn⟩ := by
      rw [← mul_inv_eq_one]
      apply F.eq_one_of_forall_proj_eq_one
      intro i
      rw [map_mul, map_inv, hproj i, mul_inv_cancel]
    have hval : (g : G) * n * (g : G)⁻¹ = n := congrArg Subtype.val heq
    calc n * (g : G) = ((g : G) * n * (g : G)⁻¹) * g := by rw [hval]
      _ = (g : G) * n := by group
  rw [hC, Subgroup.mem_bot] at hgC
  exact hgC

/-- Nonempty isomorphism `F.S i ≃* F.S j` for any `i, j`. -/
theorem nonempty_mulEquiv_S (i j : Fin F.r) : Nonempty (F.S i ≃* F.S j) := by
  obtain ⟨g, hg⟩ := F.conj i j
  exact ⟨((F.S i).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg.symm)⟩

/-- When `C_G(N) = ⊥`, `|G| ≤ r! · |MulAut (F.S 0)|^r`. -/
theorem card_le_factorial_mul_card_mulAut_pow [Finite G] (hN : N.Normal)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    Nat.card G ≤ F.r.factorial * Nat.card (MulAut (F.S ⟨0, F.one_le⟩)) ^ F.r := by
  let K := (coordPermHom F hN).ker
  have hidx : K.index ≤ F.r.factorial := by
    rw [Subgroup.index_ker]
    have := Nat.card_le_card_of_injective (coordPermHom F hN).range.subtype Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := Perm (Fin F.r)), Fintype.card_perm, Fintype.card_fin] at this
    exact this
  have hker : Nat.card K ≤ Nat.card (MulAut (F.S ⟨0, F.one_le⟩)) ^ F.r := by
    have hinj := Nat.card_le_card_of_injective (kerToPiAut F hN) (kerToPiAut_injective F hN hC)
    have hpi : Nat.card (∀ i : Fin F.r, MulAut (F.S i)) =
        Nat.card (MulAut (F.S ⟨0, F.one_le⟩)) ^ F.r := by
      simp only [Nat.card_pi]
      have hcongr : ∀ i : Fin F.r,
          Nat.card (MulAut (F.S i)) = Nat.card (MulAut (F.S ⟨0, F.one_le⟩)) := by
        intro i
        obtain ⟨e⟩ := nonempty_mulEquiv_S F i ⟨0, F.one_le⟩
        exact Nat.card_congr (MulAut.congr e).toEquiv
      simp [hcongr]
    exact hinj.trans hpi.le
  calc Nat.card G = K.index * Nat.card K := by rw [mul_comm, K.card_mul_index]
    _ ≤ F.r.factorial * Nat.card (MulAut (F.S ⟨0, F.one_le⟩)) ^ F.r :=
        Nat.mul_le_mul hidx hker

theorem S_zero_eq_N_of_r_eq_one (hr : F.r = 1) : F.S ⟨0, F.one_le⟩ = N := by
  apply le_antisymm (F.le _)
  intro n hn
  let i₀ : Fin F.r := ⟨0, F.one_le⟩
  have hsingle := F.e_single i₀ (F.e.symm ⟨n, hn⟩) fun j hj => by
    exfalso
    apply hj
    ext
    omega
  have hn_eq : n = (F.e.symm ⟨n, hn⟩ i₀ : G) := by
    have := (F.e.apply_symm_apply ⟨n, hn⟩).symm
    exact (congrArg Subtype.val this).trans hsingle
  rw [hn_eq]
  exact (F.e.symm ⟨n, hn⟩ i₀).2

/-- When `F.r = 1` and `C_G(N) = ⊥`, `G ≤ Perm α` is almost simple with socle `F.S 0`. -/
theorem isAlmostSimpleWith_of_r_eq_one {G : Subgroup (Perm α)} {N : Subgroup G}
    (hN : N.Normal) (F : SimpleFactors N) (hr : F.r = 1)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) :
    IsAlmostSimpleWith G (F.S ⟨0, F.one_le⟩) := by
  let i₀ : Fin F.r := ⟨0, F.one_le⟩
  have hSN : F.S i₀ = N := S_zero_eq_N_of_r_eq_one F hr
  let T : Subgroup (Perm α) := N.map G.subtype
  have hequ : N ≃* T := N.equivMapOfInjective G.subtype G.subtype_injective
  have : IsSimpleGroup (F.S i₀) := F.isSimpleGroup i₀
  have : IsSimpleGroup N := (MulEquiv.subgroupCongr hSN).symm.isSimpleGroup
  refine ⟨T, Subgroup.map_subtype_le N, map_subtype_conj_mem,
    hequ.symm.isSimpleGroup, ?_, ?_,
    ⟨hequ.symm.trans (MulEquiv.subgroupCongr hSN.symm)⟩⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute i₀
    have haN : a ∈ N := hSN ▸ ha
    have hbN : b ∈ N := hSN ▸ hb
    refine ⟨⟨(a : Perm α), a, haN, rfl⟩, ⟨(b : Perm α), b, hbN, rfl⟩, fun h => hab ?_⟩
    exact G.subtype_injective (congrArg Subtype.val h)
  · intro g hg hcomm
    have hgC : (⟨g, hg⟩ : G) ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      apply Subtype.ext
      exact (hcomm (n : Perm α) ⟨n, hn, rfl⟩).symm
    rw [hC, Subgroup.mem_bot] at hgC
    exact congrArg Subtype.val hgC

section Action

variable [MulAction G α] [IsPretransitive N α]

/-- Since `N` acts transitively on `α` and lies in `ker (coordPermHom F hN)`, the point stabilizer
`stabilizer G ω` maps onto the same permutations of `Fin F.r` as `G`, and in particular acts
transitively on `Fin F.r`. -/
theorem exists_mem_stabilizer_coordPermHom_eq (hN : N.Normal) (ω : α) (i j : Fin F.r) :
    ∃ g ∈ stabilizer G ω, coordPermHom F hN g i = j := by
  obtain ⟨g, hgi⟩ := exists_coordPermHom_eq F hN i j
  obtain ⟨m, hm⟩ := exists_smul_eq N ω (g • ω)
  refine ⟨(m : G)⁻¹ * g, ?_, ?_⟩
  · rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    exact hm.symm
  · rw [map_mul, map_inv, coordPermHom_eq_of_mem_N F hN m.2, inv_one, one_mul, hgi]

omit [IsPretransitive N α] in
theorem conj_mem_stabilizer_N (hN : N.Normal) (ω : α) {g : G} (hg : g ∈ stabilizer G ω)
    {k : N} (hk : k ∈ stabilizer N ω) :
    (⟨g * k * g⁻¹, hN.conj_mem k k.2 g⟩ : N) ∈ stabilizer N ω := by
  rw [mem_stabilizer_iff]
  change (g * (k : G) * g⁻¹) • ω = ω
  have hgω : g • ω = ω := mem_stabilizer_iff.mp hg
  have hg' : g⁻¹ • ω = ω := by rw [inv_smul_eq_iff, hgω]
  have hkω : (k : G) • ω = ω := mem_stabilizer_iff.mp hk
  rw [mul_smul, mul_smul, hg', hkω, hgω]

omit [IsPretransitive N α] in
theorem map_proj_stabilizer_eq_top_of_coordPermHom (hN : N.Normal) (ω : α)
    {g : G} (hg : g ∈ stabilizer G ω) {i j : Fin F.r} (hij : coordPermHom F hN g i = j)
    (hi : (stabilizer N ω).map (F.proj i) = ⊤) :
    (stabilizer N ω).map (F.proj j) = ⊤ := by
  have hmap : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j := by
    rw [map_conj_eq_coordPermHom F hN, hij]
  rw [eq_top_iff]
  rintro ⟨t, ht⟩ _
  have hts : g⁻¹ * t * g ∈ F.S i := by
    rw [← hmap] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    simpa [mul_assoc] using hs
  have htop : (⟨g⁻¹ * t * g, hts⟩ : F.S i) ∈ (stabilizer N ω).map (F.proj i) :=
    hi ▸ Subgroup.mem_top _
  obtain ⟨k, hk, hki⟩ := htop
  refine ⟨⟨g * k * g⁻¹, hN.conj_mem k k.2 g⟩, conj_mem_stabilizer_N hN ω hg hk, ?_⟩
  apply Subtype.ext
  rw [F.proj_conj hmap k (hN.conj_mem k k.2 g), congrArg Subtype.val hki]
  group

/-- Either every projection of `K = stabilizer N ω` to `F.S i` is `⊤`, or every projection is a
proper subgroup of `F.S i`. -/
theorem forall_map_proj_eq_top_or_ne_top (hN : N.Normal) (ω : α) :
    (∀ i : Fin F.r, (stabilizer N ω).map (F.proj i) = ⊤) ∨
      (∀ i : Fin F.r, (stabilizer N ω).map (F.proj i) ≠ ⊤) := by
  by_cases h : ∃ i : Fin F.r, (stabilizer N ω).map (F.proj i) = ⊤
  · left
    obtain ⟨i, hi⟩ := h
    intro j
    obtain ⟨g, hg, hij⟩ := exists_mem_stabilizer_coordPermHom_eq F hN ω i j
    exact map_proj_stabilizer_eq_top_of_coordPermHom F hN ω hg hij hi
  · right
    push Not at h
    exact h

end Action

end SimpleFactors

end Maroti
