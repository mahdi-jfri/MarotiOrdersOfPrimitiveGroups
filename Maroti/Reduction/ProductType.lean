module

public import Maroti.Reduction.Diagonal

/-!
# Product action decomposition

This file establishes the Cartesian product decomposition of the domain `α` when `G ≤ Perm α` is
primitive, `N` is a minimal normal subgroup with `r ≥ 2` simple factors `F.S i`, and every
projection `R i = (stabilizer N ω).map (F.proj i)` is a proper subgroup of `F.S i`
(Maróti, Section 2, Step 1, pages 633–634, and Dixon and Mortimer, *Permutation Groups*,
Section 4.3).

For any `stabilizer G ω`-invariant family of subgroups `Q i ≤ F.S i` with `R i ≤ Q i`, the
subgroup `(∏ i, Q i) · stabilizer G ω` contains `stabilizer G ω`. By maximality of
`stabilizer G ω`, either `∏ i, Q i ≤ stabilizer N ω` or `Q i = ⊤` for all `i`
(`SimpleFactors.prodSubgroup_le_stabilizer_or_eq_top`). Applying this dichotomy to `Q = R` shows
that `stabilizer N ω` equals the direct product `∏ i, R i` (`SimpleFactors.stabilizer_eq_prodR`).
Consequently, the orbit map of `N` on `ω` identifies `α` with the product space
`∀ i : Fin F.r, F.S i ⧸ R i` (`SimpleFactors.toCoord`), and every element `g : G` with
`coordPermHom F hN g i = j` induces a bijection `Δ i ≃ Δ j` between the coordinate spaces
(`SimpleFactors.coordEquiv`).
-/

@[expose] public section

namespace Maroti

open Equiv MulAction CFSG.Holt.General.AltRecPrim

namespace SimpleFactors

variable {α : Type} {G : Subgroup (Perm α)} {N : Subgroup G} (F : SimpleFactors N)

/-- The `i`-th projection of the point stabilizer `stabilizer N ω`. -/
noncomputable def R (ω : α) (i : Fin F.r) : Subgroup (F.S i) :=
  (stabilizer N ω).map (F.proj i)

/-- Given a family of subgroups `Q i ≤ F.S i`, their product subgroup inside `N`. -/
noncomputable def prodSubgroup (Q : ∀ i : Fin F.r, Subgroup (F.S i)) : Subgroup N :=
  ⨅ i : Fin F.r, (Q i).comap (F.proj i)

theorem mem_prodSubgroup_iff {Q : ∀ i : Fin F.r, Subgroup (F.S i)} {n : N} :
    n ∈ prodSubgroup F Q ↔ ∀ i : Fin F.r, F.proj i n ∈ Q i := by
  simp [prodSubgroup, Subgroup.mem_iInf, Subgroup.mem_comap]

/-- The product subgroup `∏ i, R i ≤ N`. -/
noncomputable def prodR (ω : α) : Subgroup N :=
  prodSubgroup F (R F ω)

theorem stabilizer_le_prodR (ω : α) : stabilizer N ω ≤ prodR F ω := by
  intro k hk
  rw [prodR, mem_prodSubgroup_iff]
  intro i
  exact ⟨k, hk, rfl⟩

theorem conj_mem_S_of_coordPermHom (hN : N.Normal) {g : G} {i j : Fin F.r}
    (hij : coordPermHom F hN g i = j) {s : G} (hs : s ∈ F.S i) :
    g * s * g⁻¹ ∈ F.S j := by
  have hmap : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j := by
    rw [map_conj_eq_coordPermHom F hN, hij]
  rw [← hmap]
  exact ⟨s, hs, rfl⟩

theorem proj_conj_of_coordPermHom (hN : N.Normal) {g : G} {i j : Fin F.r}
    (hij : coordPermHom F hN g i = j) (m : N) :
    F.proj j ⟨g * m * g⁻¹, hN.conj_mem m m.2 g⟩ =
      ⟨g * (F.proj i m : G) * g⁻¹,
        conj_mem_S_of_coordPermHom F hN hij (F.proj i m).2⟩ := by
  apply Subtype.ext
  have hmap : (F.S i).map (MulAut.conj g).toMonoidHom = F.S j := by
    rw [map_conj_eq_coordPermHom F hN, hij]
  exact F.proj_conj hmap m (hN.conj_mem m m.2 g)

theorem conj_mem_R (hN : N.Normal) (ω : α) {g : G} (hg : g ∈ stabilizer G ω)
    {i j : Fin F.r} (hij : coordPermHom F hN g i = j) {s : F.S i} (hs : s ∈ R F ω i) :
    (⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩ : F.S j) ∈ R F ω j := by
  obtain ⟨k, hk, rfl⟩ := hs
  refine ⟨⟨g * k * g⁻¹, hN.conj_mem k k.2 g⟩, conj_mem_stabilizer_N hN ω hg hk, ?_⟩
  exact proj_conj_of_coordPermHom F hN hij k

/-- A family `Q : ∀ i, Subgroup (F.S i)` is invariant under `stabilizer G ω` if conjugating by
`g ∈ stabilizer G ω` with `coordPermHom F hN g i = j` maps `Q i` into `Q j`. -/
def IsStabInvariant (hN : N.Normal) (ω : α) (Q : ∀ i : Fin F.r, Subgroup (F.S i)) : Prop :=
  ∀ {g : G}, g ∈ stabilizer G ω → ∀ {i j : Fin F.r} (hij : coordPermHom F hN g i = j)
    {s : F.S i}, s ∈ Q i →
    (⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩ : F.S j) ∈ Q j

theorem isStabInvariant_R (hN : N.Normal) (ω : α) : IsStabInvariant F hN ω (R F ω) :=
  fun hg => conj_mem_R F hN ω hg

theorem conj_mem_prodSubgroup (hN : N.Normal) (ω : α) {Q : ∀ i : Fin F.r, Subgroup (F.S i)}
    (hQ : IsStabInvariant F hN ω Q) {g : G} (hg : g ∈ stabilizer G ω)
    {m : N} (hm : m ∈ prodSubgroup F Q) :
    (⟨g * m * g⁻¹, hN.conj_mem m m.2 g⟩ : N) ∈ prodSubgroup F Q := by
  rw [mem_prodSubgroup_iff] at hm ⊢
  intro j
  let i := (coordPermHom F hN g)⁻¹ j
  have hij : coordPermHom F hN g i = j := (coordPermHom F hN g).apply_symm_apply j
  rw [proj_conj_of_coordPermHom F hN hij m]
  exact hQ hg hij (hm i)

/-- The subgroup `{g : G | ∃ m ∈ prodSubgroup F Q, g • ω = (m : G) • ω}` containing
`stabilizer G ω`. -/
noncomputable def stabSupProd (hN : N.Normal) (ω : α) (Q : ∀ i : Fin F.r, Subgroup (F.S i))
    (hQ : IsStabInvariant F hN ω Q) : Subgroup G where
  carrier := {g : G | ∃ m ∈ prodSubgroup F Q, g • ω = (m : G) • ω}
  one_mem' := ⟨1, one_mem _, rfl⟩
  mul_mem' {g₁ g₂} := by
    rintro ⟨m₁, hm₁, hg₁⟩ ⟨m₂, hm₂, hg₂⟩
    have hh₁ : (m₁ : G)⁻¹ * g₁ ∈ stabilizer G ω := by
      rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hg₁]
    let h₁ := (m₁ : G)⁻¹ * g₁
    let m₂' : N := ⟨h₁ * m₂ * h₁⁻¹, hN.conj_mem m₂ m₂.2 h₁⟩
    have hm₂' : m₂' ∈ prodSubgroup F Q := conj_mem_prodSubgroup F hN ω hQ hh₁ hm₂
    refine ⟨m₁ * m₂', mul_mem hm₁ hm₂', ?_⟩
    have hmul : g₁ * (m₂ : G) = (m₁ : G) * (m₂' : G) * h₁ := by
      simp only [h₁, m₂']
      group
    calc (g₁ * g₂) • ω = g₁ • (g₂ • ω) := mul_smul g₁ g₂ ω
      _ = g₁ • ((m₂ : G) • ω) := by rw [hg₂]
      _ = (g₁ * (m₂ : G)) • ω := (mul_smul g₁ (m₂ : G) ω).symm
      _ = ((m₁ : G) * (m₂' : G) * h₁) • ω := by rw [hmul]
      _ = ((m₁ : G) * (m₂' : G)) • (h₁ • ω) := mul_smul _ h₁ ω
      _ = ((m₁ * m₂' : N) : G) • ω := by rw [mem_stabilizer_iff.mp hh₁]; rfl
  inv_mem' {g} := by
    rintro ⟨m, hm, hg⟩
    have hh : (m : G)⁻¹ * g ∈ stabilizer G ω := by
      rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hg]
    have hh' : g⁻¹ * (m : G) ∈ stabilizer G ω := by
      simpa [mul_assoc] using inv_mem hh
    let h' := g⁻¹ * (m : G)
    let m' : N := ⟨h' * (m⁻¹ : N) * h'⁻¹, hN.conj_mem (m⁻¹ : N) (inv_mem m.2) h'⟩
    have hm' : m' ∈ prodSubgroup F Q := conj_mem_prodSubgroup F hN ω hQ hh' (inv_mem hm)
    refine ⟨m', hm', ?_⟩
    have heq : (m' : G) * h' = g⁻¹ := by
      simp only [m', h', Subgroup.coe_inv]
      group
    calc g⁻¹ • ω = ((m' : G) * h') • ω := by rw [heq]
      _ = (m' : G) • (h' • ω) := mul_smul (m' : G) h' ω
      _ = (m' : G) • ω := by rw [mem_stabilizer_iff.mp hh']

theorem stabilizer_le_stabSupProd (hN : N.Normal) (ω : α) (Q : ∀ i : Fin F.r, Subgroup (F.S i))
    (hQ : IsStabInvariant F hN ω Q) :
    stabilizer G ω ≤ stabSupProd F hN ω Q hQ :=
  fun _ hg => ⟨1, one_mem _, by rw [mem_stabilizer_iff.mp hg, OneMemClass.coe_one, one_smul]⟩

theorem coe_mem_stabSupProd_iff (hN : N.Normal) (ω : α) (Q : ∀ i : Fin F.r, Subgroup (F.S i))
    (hQ : IsStabInvariant F hN ω Q) (hRQ : ∀ i : Fin F.r, R F ω i ≤ Q i) (n : N) :
    (n : G) ∈ stabSupProd F hN ω Q hQ ↔ n ∈ prodSubgroup F Q := by
  have hle : stabilizer N ω ≤ prodSubgroup F Q := by
    refine (stabilizer_le_prodR F ω).trans fun m hm => ?_
    rw [prodR, mem_prodSubgroup_iff] at hm
    rw [mem_prodSubgroup_iff]
    exact fun i => hRQ i (hm i)
  constructor
  · rintro ⟨m, hm, hnm⟩
    have hstab : m⁻¹ * n ∈ stabilizer N ω := by
      rw [mem_stabilizer_iff]
      change ((m : G)⁻¹ * (n : G)) • ω = ω
      rw [mul_smul, inv_smul_eq_iff, hnm]
    have hmul := mul_mem hm (hle hstab)
    simpa using hmul
  · intro hn
    exact ⟨n, hn, rfl⟩

/-- By maximality of `stabilizer G ω`, any `stabilizer G ω`-invariant family `Q` containing `R`
either satisfies `prodSubgroup F Q ≤ stabilizer N ω` or `Q i = ⊤` for all `i`. -/
theorem prodSubgroup_le_stabilizer_or_eq_top [IsPreprimitive G α] [Nontrivial α]
    (hN : N.Normal) (ω : α) (Q : ∀ i : Fin F.r, Subgroup (F.S i))
    (hQ : IsStabInvariant F hN ω Q) (hRQ : ∀ i : Fin F.r, R F ω i ≤ Q i) :
    prodSubgroup F Q ≤ stabilizer N ω ∨ ∀ i : Fin F.r, Q i = ⊤ := by
  have hmax : IsCoatom (stabilizer G ω) :=
    IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G ω
  rcases hmax.le_iff.mp (stabilizer_le_stabSupProd F hN ω Q hQ) with htop | hle
  · right
    intro i
    rw [eq_top_iff]
    intro s _
    let n : N := F.e (Pi.mulSingle i s)
    have hnG : (n : G) ∈ stabSupProd F hN ω Q hQ := htop ▸ Subgroup.mem_top (n : G)
    have hnQ : n ∈ prodSubgroup F Q := (coe_mem_stabSupProd_iff F hN ω Q hQ hRQ n).mp hnG
    have hproj : F.proj i n = s := by
      simp [n, SimpleFactors.proj_apply]
    simpa [hproj] using (mem_prodSubgroup_iff F).mp hnQ i
  · left
    intro n hn
    have hnG : (n : G) ∈ stabSupProd F hN ω Q hQ :=
      (coe_mem_stabSupProd_iff F hN ω Q hQ hRQ n).mpr hn
    rw [hle] at hnG
    exact mem_stabilizer_iff.mp hnG

/-- When every projection `R i = (stabilizer N ω).map (F.proj i)` is proper,
`stabilizer N ω = prodR F ω`. -/
theorem stabilizer_eq_prodR [IsPreprimitive G α] [Nontrivial α] (hN : N.Normal) (ω : α)
    (hR : ∀ i : Fin F.r, R F ω i ≠ ⊤) :
    stabilizer N ω = prodR F ω := by
  apply le_antisymm (stabilizer_le_prodR F ω)
  rcases prodSubgroup_le_stabilizer_or_eq_top F hN ω (R F ω)
    (isStabInvariant_R F hN ω) (fun _ => le_rfl) with hle | htop
  · exact hle
  · exfalso
    exact hR ⟨0, F.one_le⟩ (htop ⟨0, F.one_le⟩)

/-- The `i`-th coordinate space `Δ i = F.S i ⧸ R i`. -/
abbrev Δ (ω : α) (i : Fin F.r) : Type := F.S i ⧸ R F ω i

/-- The coordinate tuple of `n : N` in `∀ i, Δ i`. -/
noncomputable def nToCoord (ω : α) (n : N) : ∀ i : Fin F.r, Δ F ω i :=
  fun i => QuotientGroup.mk (F.proj i n)

theorem nToCoord_eq_iff (ω : α) (n₁ n₂ : N) :
    nToCoord F ω n₁ = nToCoord F ω n₂ ↔ n₁⁻¹ * n₂ ∈ prodR F ω := by
  rw [funext_iff, prodR, mem_prodSubgroup_iff]
  refine forall_congr' fun i => ?_
  rw [nToCoord, nToCoord, QuotientGroup.eq, ← map_inv, ← map_mul]

theorem nToCoord_surjective (ω : α) : Function.Surjective (nToCoord F ω) := by
  intro c
  let s : ∀ i : Fin F.r, F.S i := fun i => Quotient.out (c i)
  refine ⟨F.e s, funext fun i => ?_⟩
  change QuotientGroup.mk (F.proj i (F.e s)) = c i
  rw [SimpleFactors.proj_apply, MulEquiv.symm_apply_apply]
  exact Quotient.out_eq (c i)

section CoordinateEquiv

variable [IsPreprimitive G α] [Nontrivial α]

include F in
omit [Nontrivial α] in
theorem isPretransitive_N (hN : N.Normal) : IsPretransitive N α := by
  apply isPretransitive_of_normal_ne_bot
  intro hbot
  obtain ⟨a, ha, b, hb, hab⟩ := F.not_commute ⟨0, F.one_le⟩
  have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ F.le _ ha)
  rw [ha1, one_mul, mul_one] at hab
  exact hab rfl

/-- Chosen element of `N` sending `ω` to `x`. -/
noncomputable def smulRep (hN : N.Normal) (ω x : α) : N :=
  ((isPretransitive_N F hN).exists_smul_eq ω x).choose

omit [Nontrivial α] in
@[simp]
theorem smulRep_smul (hN : N.Normal) (ω x : α) : (smulRep F hN ω x : G) • ω = x :=
  ((isPretransitive_N F hN).exists_smul_eq ω x).choose_spec

theorem nToCoord_smulRep_smul (hN : N.Normal) (ω : α) (hR : ∀ i : Fin F.r, R F ω i ≠ ⊤)
    (n : N) : nToCoord F ω (smulRep F hN ω ((n : G) • ω)) = nToCoord F ω n := by
  rw [nToCoord_eq_iff, ← stabilizer_eq_prodR F hN ω hR, mem_stabilizer_iff]
  change ((smulRep F hN ω ((n : G) • ω) : G)⁻¹ * (n : G)) • ω = ω
  rw [mul_smul, inv_smul_eq_iff, smulRep_smul]

/-- The canonical identification `α ≃ ∀ i : Fin F.r, Δ i`. -/
noncomputable def toCoord (hN : N.Normal) (ω : α) (hR : ∀ i : Fin F.r, R F ω i ≠ ⊤) :
    α ≃ ∀ i : Fin F.r, Δ F ω i :=
  Equiv.ofBijective (fun x => nToCoord F ω (smulRep F hN ω x)) ⟨by
    intro x y hxy
    rw [nToCoord_eq_iff, ← stabilizer_eq_prodR F hN ω hR, mem_stabilizer_iff] at hxy
    have h1 : ((smulRep F hN ω x : G)⁻¹ * (smulRep F hN ω y : G)) • ω = ω := hxy
    rw [mul_smul, inv_smul_eq_iff, smulRep_smul, smulRep_smul] at h1
    exact h1.symm, by
    intro c
    obtain ⟨n, rfl⟩ := nToCoord_surjective F ω c
    exact ⟨(n : G) • ω, nToCoord_smulRep_smul F hN ω hR n⟩⟩

@[simp]
theorem toCoord_smul_omega (hN : N.Normal) (ω : α) (hR : ∀ i : Fin F.r, R F ω i ≠ ⊤)
    (n : N) (i : Fin F.r) :
    toCoord F hN ω hR ((n : G) • ω) i = QuotientGroup.mk (F.proj i n) := by
  change nToCoord F ω (smulRep F hN ω ((n : G) • ω)) i = nToCoord F ω n i
  rw [nToCoord_smulRep_smul F hN ω hR n]

theorem toCoord_omega (hN : N.Normal) (ω : α) (hR : ∀ i : Fin F.r, R F ω i ≠ ⊤)
    (i : Fin F.r) :
    toCoord F hN ω hR ω i = QuotientGroup.mk 1 := by
  have := toCoord_smul_omega F hN ω hR 1 i
  simpa using this

/-- If `coordPermHom F hN g i = j`, then `toCoord (g • x) j` depends only on `toCoord x i`. -/
theorem toCoord_smul_eq_of_toCoord_eq (hN : N.Normal) (ω : α) (hR : ∀ i : Fin F.r, R F ω i ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) {x y : α}
    (hxy : toCoord F hN ω hR x i = toCoord F hN ω hR y i) :
    toCoord F hN ω hR (g • x) j = toCoord F hN ω hR (g • y) j := by
  let m₁ := smulRep F hN ω x
  let m₂ := smulRep F hN ω y
  let n := smulRep F hN ω (g • ω)
  have hn : (n : G) • ω = g • ω := smulRep_smul F hN ω (g • ω)
  let g₀ : G := (n : G)⁻¹ * g
  have hg₀ : g₀ ∈ stabilizer G ω := by
    rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hn]
  have hg₀_ij : coordPermHom F hN g₀ i = j := by
    rw [map_mul, map_inv, coordPermHom_eq_of_mem_N F hN n.2, inv_one, one_mul, hij]
  have hgx : g • x = ((n * ⟨g₀ * m₁ * g₀⁻¹, hN.conj_mem m₁ m₁.2 g₀⟩ : N) : G) • ω := by
    have hmul : g * (m₁ : G) = (n : G) * (g₀ * m₁ * g₀⁻¹) * g₀ := by
      simp only [g₀]
      group
    calc g • x = g • ((m₁ : G) • ω) := by rw [smulRep_smul]
      _ = (g * (m₁ : G)) • ω := (mul_smul g (m₁ : G) ω).symm
      _ = ((n : G) * (g₀ * m₁ * g₀⁻¹) * g₀) • ω := by rw [hmul]
      _ = ((n : G) * (g₀ * m₁ * g₀⁻¹)) • (g₀ • ω) := mul_smul _ g₀ ω
      _ = ((n * ⟨g₀ * m₁ * g₀⁻¹, hN.conj_mem m₁ m₁.2 g₀⟩ : N) : G) • ω := by
        rw [mem_stabilizer_iff.mp hg₀]; rfl
  have hgy : g • y = ((n * ⟨g₀ * m₂ * g₀⁻¹, hN.conj_mem m₂ m₂.2 g₀⟩ : N) : G) • ω := by
    have hmul : g * (m₂ : G) = (n : G) * (g₀ * m₂ * g₀⁻¹) * g₀ := by
      simp only [g₀]
      group
    calc g • y = g • ((m₂ : G) • ω) := by rw [smulRep_smul]
      _ = (g * (m₂ : G)) • ω := (mul_smul g (m₂ : G) ω).symm
      _ = ((n : G) * (g₀ * m₂ * g₀⁻¹) * g₀) • ω := by rw [hmul]
      _ = ((n : G) * (g₀ * m₂ * g₀⁻¹)) • (g₀ • ω) := mul_smul _ g₀ ω
      _ = ((n * ⟨g₀ * m₂ * g₀⁻¹, hN.conj_mem m₂ m₂.2 g₀⟩ : N) : G) • ω := by
        rw [mem_stabilizer_iff.mp hg₀]; rfl
  rw [hgx, hgy, toCoord_smul_omega, toCoord_smul_omega, QuotientGroup.eq,
    map_mul, map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hconj : (F.proj j ⟨g₀ * m₁ * g₀⁻¹, hN.conj_mem m₁ m₁.2 g₀⟩)⁻¹ *
      F.proj j ⟨g₀ * m₂ * g₀⁻¹, hN.conj_mem m₂ m₂.2 g₀⟩ =
      F.proj j ⟨g₀ * (m₁⁻¹ * m₂ : N) * g₀⁻¹, hN.conj_mem (m₁⁻¹ * m₂) (m₁⁻¹ * m₂).2 g₀⟩ := by
    rw [← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hconj, proj_conj_of_coordPermHom F hN hg₀_ij (m₁⁻¹ * m₂)]
  apply conj_mem_R F hN ω hg₀ hg₀_ij
  have hm12 : QuotientGroup.mk (s := R F ω i) (F.proj i m₁) =
      QuotientGroup.mk (s := R F ω i) (F.proj i m₂) := by
    have hx' : x = (m₁ : G) • ω := (smulRep_smul F hN ω x).symm
    have hy' : y = (m₂ : G) • ω := (smulRep_smul F hN ω y).symm
    simpa [hx', hy', toCoord_smul_omega] using hxy
  rw [QuotientGroup.eq, ← map_inv, ← map_mul] at hm12
  exact hm12

/-- The action of `g : G` from `Δ i` to `Δ j` when `coordPermHom F hN g i = j`. -/
noncomputable def actCoord (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) (i j : Fin F.r) (d : Δ F ω i) : Δ F ω j :=
  toCoord F hN ω hR (g • (toCoord F hN ω hR).symm (Function.update (nToCoord F ω 1) i d)) j

theorem toCoord_smul (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) (x : α) :
    toCoord F hN ω hR (g • x) j = actCoord F hN ω hR g i j (toCoord F hN ω hR x i) := by
  apply toCoord_smul_eq_of_toCoord_eq F hN ω hR g hij
  rw [Equiv.apply_symm_apply, Function.update_self]

theorem actCoord_one (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (i : Fin F.r) (d : Δ F ω i) :
    actCoord F hN ω hR 1 i i d = d := by
  simp [actCoord]

theorem actCoord_mul (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g₁ g₂ : G) {i j k : Fin F.r} (_hij : coordPermHom F hN g₂ i = j)
    (hjk : coordPermHom F hN g₁ j = k) (d : Δ F ω i) :
    actCoord F hN ω hR (g₁ * g₂) i k d =
      actCoord F hN ω hR g₁ j k (actCoord F hN ω hR g₂ i j d) := by
  let x := (toCoord F hN ω hR).symm (Function.update (nToCoord F ω 1) i d)
  change toCoord F hN ω hR ((g₁ * g₂) • x) k =
    actCoord F hN ω hR g₁ j k (toCoord F hN ω hR (g₂ • x) j)
  rw [mul_smul, toCoord_smul F hN ω hR g₁ hjk (g₂ • x)]

/-- The equivalence `Δ i ≃ Δ j` induced by `g : G` when `coordPermHom F hN g i = j`. -/
noncomputable def coordEquiv (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) :
    Δ F ω i ≃ Δ F ω j where
  toFun := actCoord F hN ω hR g i j
  invFun := actCoord F hN ω hR g⁻¹ j i
  left_inv d := by
    have hij' : coordPermHom F hN g⁻¹ j = i := by
      rw [map_inv, Perm.inv_def, ← hij, Equiv.symm_apply_apply]
    rw [← actCoord_mul F hN ω hR g⁻¹ g hij hij', inv_mul_cancel, actCoord_one]
  right_inv d := by
    have hij' : coordPermHom F hN g⁻¹ j = i := by
      rw [map_inv, Perm.inv_def, ← hij, Equiv.symm_apply_apply]
    rw [← actCoord_mul F hN ω hR g g⁻¹ hij' hij, mul_inv_cancel, actCoord_one]

@[simp]
theorem coordEquiv_apply (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) (d : Δ F ω i) :
    coordEquiv F hN ω hR g hij d = actCoord F hN ω hR g i j d := rfl

@[simp]
theorem coordEquiv_symm (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) :
    (coordEquiv F hN ω hR g hij).symm = coordEquiv F hN ω hR g⁻¹
      (by rw [map_inv, Perm.inv_def, ← hij, Equiv.symm_apply_apply]) := rfl

theorem toCoord_smul_eq_coordEquiv (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (g : G) {i j : Fin F.r} (hij : coordPermHom F hN g i = j) (x : α) :
    toCoord F hN ω hR (g • x) j = coordEquiv F hN ω hR g hij (toCoord F hN ω hR x i) :=
  toCoord_smul F hN ω hR g hij x

theorem coordEquiv_of_mem_N (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    (n : N) (i : Fin F.r) (d : Δ F ω i) :
    coordEquiv F hN ω hR (n : G)
      (by rw [coordPermHom_eq_of_mem_N F hN n.2, Perm.one_apply]) d =
      F.proj i n • d := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective d
  let m : N := F.e (Pi.mulSingle i s)
  have hm : toCoord F hN ω hR ((m : G) • ω) i = QuotientGroup.mk s := by
    rw [toCoord_smul_omega, SimpleFactors.proj_apply, MulEquiv.symm_apply_apply,
      Pi.mulSingle_eq_same]
  rw [← hm, ← toCoord_smul_eq_coordEquiv]
  change toCoord F hN ω hR (((n * m : N) : G) • ω) i = _
  rw [toCoord_smul_omega, map_mul, hm]
  have hproj : F.proj i m = s := by
    rw [SimpleFactors.proj_apply, MulEquiv.symm_apply_apply, Pi.mulSingle_eq_same]
  rw [hproj]
  rfl

theorem coordEquiv_of_mem_stabilizer (hN : N.Normal) (ω : α) (hR : ∀ l : Fin F.r, R F ω l ≠ ⊤)
    {g : G} (hg : g ∈ stabilizer G ω) {i j : Fin F.r} (hij : coordPermHom F hN g i = j)
    (s : F.S i) :
    coordEquiv F hN ω hR g hij (QuotientGroup.mk s) =
      QuotientGroup.mk ⟨g * (s : G) * g⁻¹, conj_mem_S_of_coordPermHom F hN hij s.2⟩ := by
  let m : N := F.e (Pi.mulSingle i s)
  have hm : toCoord F hN ω hR ((m : G) • ω) i = QuotientGroup.mk s := by
    rw [toCoord_smul_omega, SimpleFactors.proj_apply, MulEquiv.symm_apply_apply,
      Pi.mulSingle_eq_same]
  rw [← hm, ← toCoord_smul_eq_coordEquiv]
  have hgm : g • ((m : G) • ω) = ((⟨g * m * g⁻¹, hN.conj_mem m m.2 g⟩ : N) : G) • ω := by
    have h1 : g • ((m : G) • ω) = (g * (m : G) * g⁻¹) • (g • ω) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    rw [h1, mem_stabilizer_iff.mp hg]
  rw [hgm, toCoord_smul_omega, proj_conj_of_coordPermHom F hN hij m]
  have hproj : F.proj i m = s := by
    rw [SimpleFactors.proj_apply, MulEquiv.symm_apply_apply, Pi.mulSingle_eq_same]
  rw [hproj]

end CoordinateEquiv

end SimpleFactors

end Maroti
