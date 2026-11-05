module

public import Maroti.Exceptional.AutBound
public import CFSG.SignalizerFunctorTheorem.NonLocal.PermHeis
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Heis

/-!
# Torus-Weighted Heisenberg Lower Bounds on Permutation Degrees

This file proves general lower bounds on the degree `Nat.card Λ` of a permutation representation
`π : S →* Equiv.Perm Λ` (and on the index `M.index` of a proper subgroup `M < S` of a finite
simple group `S`) from three configurations:
* A root-group Heisenberg triple `(z, a, b)` with a `K`-bilinear commutator map
  `β : V →ₗ[K] V →ₗ[K] K` normalized by a torus homomorphism `t : T →* S` acting on `z` via
  `χ : T →* Kˣ`, yielding `Nat.card χ.range * Nat.card V + 1 ≤ Nat.card Λ`
  (`card_range_mul_card_add_one_le_card_of_heis_root`).
* A single root subgroup `z : Multiplicative K →* S` normalized by a torus `t : T →* S` acting via
  `χ : T →* Kˣ`, yielding `Nat.card χ.range + 1 ≤ Nat.card Λ`
  (`card_range_add_one_le_card_of_torus_root`).
* A `HeisSystem Γ K I` from `CFSG.SignalizerFunctorTheorem.NonLocalExc.Heis`, yielding both
  torus-weighted bounds `Nat.card χ.range * Nat.card (I → K) + 1 ≤ M.index` and direct Heisenberg
  translation bounds `Nat.card (I → K) ≤ M.index` and `2 * Nat.card (I → K) ≤ M.index` (in
  characteristic `2`).
-/

@[expose] public section

open scoped commutatorElement

namespace Maroti

open CFSG.SignalizerFunctorTheorem.NonLocal
open CFSG.SignalizerFunctorTheorem.NonLocalExc

/-! ### Faithful coset permutation action of a simple group -/

/-- If `G` is a simple group, `M < G` is a proper subgroup, and `g ≠ 1`, then `g` acts
nontrivially on the coset space `G ⧸ M`. -/
theorem toPermHom_quotient_ne_one_of_ne_one {G : Type*} [Group G] [IsSimpleGroup G]
    {M : Subgroup G} (hM : M ≠ ⊤) {g : G} (hg : g ≠ 1) :
    MulAction.toPermHom G (G ⧸ M) g ≠ 1 := by
  let π : G →* Equiv.Perm (G ⧸ M) := MulAction.toPermHom G (G ⧸ M)
  have hker_le : π.ker ≤ M := by
    intro x hx
    have h1 := congrArg (fun σ : Equiv.Perm (G ⧸ M) => σ (QuotientGroup.mk (1 : G))) hx
    simp only [π, MulAction.toPermHom_apply, MulAction.toPerm_apply,
      Equiv.Perm.coe_one, id_eq] at h1
    have h2 := QuotientGroup.leftRel_apply.mp (Quotient.exact h1)
    simpa using h2
  have hker_bot : π.ker = ⊥ :=
    (π.normal_ker.eq_bot_or_eq_top).resolve_right (fun htop => hM (top_unique (htop ▸ hker_le)))
  intro hπ
  apply hg
  rwa [← MonoidHom.mem_ker, hker_bot, Subgroup.mem_bot] at hπ

/-! ### Torus-weighted root Heisenberg permutation bound -/

/-- If `S` acts on a finite type `Λ` via `π : S →* Equiv.Perm Λ` such that `z (ofAdd 1)` acts
nontrivially, where `(z, a, b)` is a Heisenberg triple over a finite field `K` and finite
`K`-module `V` with right-nondegenerate bilinear pairing `β : V →ₗ[K] V →ₗ[K] K`, normalized by
`t : T →* S` with central character `χ : T →* Kˣ`, then
`Nat.card χ.range * Nat.card V + 1 ≤ Nat.card Λ`. -/
theorem card_range_mul_card_add_one_le_card_of_heis_root
    {S Λ : Type*} [Group S] [Finite Λ] (π : S →* Equiv.Perm Λ)
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hinj : ∀ (c : K) (u : V), z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u) = 1 →
      c = 0 ∧ u = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v)
    {T : Type*} [Group T] (t : T →* S) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)))
    (hta : ∀ s u, ∃ u', t s * a (Multiplicative.ofAdd u) * (t s)⁻¹ =
      a (Multiplicative.ofAdd u'))
    (hnt : π (z (Multiplicative.ofAdd 1)) ≠ 1) :
    Nat.card χ.range * Nat.card V + 1 ≤ Nat.card Λ := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Fintype K := Fintype.ofFinite K
  have : Fintype V := Fintype.ofFinite V
  have : Fintype Λ := Fintype.ofFinite Λ
  have ha0 : ∀ u : V, a (Multiplicative.ofAdd u) = 1 → u = 0 := by
    intro u h
    refine (hinj 0 u ?_).2
    rw [ofAdd_zero, map_one, one_mul]
    exact h
  have haI : ∀ x y : V, a (Multiplicative.ofAdd x) = a (Multiplicative.ofAdd y) → x = y := by
    intro x y h
    refine sub_eq_zero.1 (ha0 _ ?_)
    rw [ofAdd_sub, map_div, h]
    exact div_self' _
  have hkey : ∀ (c1 c2 : Multiplicative K) (u1 u2 : Multiplicative V),
      z c1 * z c2 * (a u1 * a u2) = z c1 * a u1 * (z c2 * a u2) := by
    intro c1 c2 u1 u2
    calc z c1 * z c2 * (a u1 * a u2) = z c1 * (z c2 * a u1) * a u2 := by simp only [mul_assoc]
      _ = z c1 * (a u1 * z c2) * a u2 := by rw [hza c2 u1]
      _ = z c1 * a u1 * (z c2 * a u2) := by simp only [mul_assoc]
  let φ : Multiplicative (K × V) →* S :=
    { toFun := fun x => z (Multiplicative.ofAdd x.toAdd.1) * a (Multiplicative.ofAdd x.toAdd.2)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
        exact hkey _ _ _ _ }
  have hAex : ∀ s : T, ∃ A : V →+ V,
      (∀ u, t s * a (Multiplicative.ofAdd u) * (t s)⁻¹ = a (Multiplicative.ofAdd (A u))) ∧
        Function.Surjective A := by
    intro s
    choose f hf using hta s
    have hfadd : ∀ u v, f (u + v) = f u + f v := by
      intro u v
      apply haI
      rw [← hf, ofAdd_add, map_mul, ofAdd_add, map_mul, ← hf, ← hf]
      group
    let A : V →+ V := AddMonoidHom.mk' f hfadd
    refine ⟨A, hf, ?_⟩
    have hAinj : Function.Injective A := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      apply ha0
      have h1 := hf u
      have h2 : f u = 0 := hu
      rw [h2, ofAdd_zero, map_one] at h1
      calc a (Multiplicative.ofAdd u)
          = (t s)⁻¹ * (t s * a (Multiplicative.ofAdd u) * (t s)⁻¹) * t s := by group
        _ = 1 := by rw [h1]; group
    exact Finite.injective_iff_surjective.1 hAinj
  choose Am hAm hAsurj using hAex
  have hconjT : ∀ (s : T) (c : K) (u : V), t s * φ (Multiplicative.ofAdd (c, u)) * (t s)⁻¹ =
      φ (Multiplicative.ofAdd ((χ s : K) * c, Am s u)) := by
    intro s c u
    show t s * (z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u)) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)) * a (Multiplicative.ofAdd (Am s u))
    rw [← htz s c, ← hAm s u]
    group
  have hconjB : ∀ (v : V) (c : K) (u : V),
      b v * φ (Multiplicative.ofAdd (c, u)) * (b v)⁻¹ =
        φ (Multiplicative.ofAdd (c + β u v, u)) := by
    intro v c u
    show b v * (z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u)) * (b v)⁻¹ =
      z (Multiplicative.ofAdd (c + β u v)) * a (Multiplicative.ofAdd u)
    calc b v * (z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u)) * (b v)⁻¹
        = (b v * z (Multiplicative.ofAdd c)) * a (Multiplicative.ofAdd u) * (b v)⁻¹ := by
          simp only [mul_assoc]
      _ = (z (Multiplicative.ofAdd c) * b v) * a (Multiplicative.ofAdd u) * (b v)⁻¹ := by
          rw [hbz]
      _ = z (Multiplicative.ofAdd c) * (b v * a (Multiplicative.ofAdd u) * (b v)⁻¹) := by
          simp only [mul_assoc]
      _ = z (Multiplicative.ofAdd c) * (a (Multiplicative.ofAdd u) *
          z (Multiplicative.ofAdd (β u v))) := by rw [hab]
      _ = z (Multiplicative.ofAdd c) * (z (Multiplicative.ofAdd (β u v)) *
          a (Multiplicative.ofAdd u)) := by rw [hza]
      _ = z (Multiplicative.ofAdd (c + β u v)) * a (Multiplicative.ofAdd u) := by
          rw [ofAdd_add, map_mul, mul_assoc]
  obtain ⟨sec, hsec⟩ : ∃ sec : χ.range → T, ∀ k, χ (sec k) = (k : Kˣ) :=
    ⟨fun k => (MonoidHom.mem_range.1 k.2).choose,
      fun k => (MonoidHom.mem_range.1 k.2).choose_spec⟩
  let g : χ.range × V → S := fun x => b x.2 * t (sec x.1)
  have hgconj : ∀ (x : χ.range × V) (c : K) (u : V),
      g x * φ (Multiplicative.ofAdd (c, u)) * (g x)⁻¹ =
        φ (Multiplicative.ofAdd (((x.1 : Kˣ) : K) * c + β (Am (sec x.1) u) x.2,
          Am (sec x.1) u)) := by
    intro x c u
    have e1 := hconjT (sec x.1) c u
    have e2 := hconjB x.2 ((χ (sec x.1) : K) * c) (Am (sec x.1) u)
    rw [hsec x.1] at e1 e2
    calc g x * φ (Multiplicative.ofAdd (c, u)) * (g x)⁻¹
        = b x.2 * (t (sec x.1) * φ (Multiplicative.ofAdd (c, u)) *
          (t (sec x.1))⁻¹) * (b x.2)⁻¹ := by
          simp only [g, mul_inv_rev, mul_assoc]
      _ = _ := by rw [e1, e2]
  let U := Multiplicative (K × V)
  let A : Subgroup U := ⊤
  let ρ : U →* Module.End ℂ (Λ → ℂ) := ((permFunHom Λ).comp π).comp φ
  have hA : IsMulCommutative A := inferInstance
  have hinv : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let u₁ : U := Multiplicative.ofAdd (1, 0)
  have hφu₁ : φ u₁ = z (Multiplicative.ofAdd 1) := by
    show z (Multiplicative.ofAdd 1) * a (Multiplicative.ofAdd 0) = z (Multiplicative.ofAdd 1)
    rw [ofAdd_zero, map_one a, mul_one]
  have hρu₁ : ρ u₁ ≠ 1 := by
    show permFunHom Λ (π (φ u₁)) ≠ 1
    rw [hφu₁]
    exact permFunHom_ne_one hnt
  have hT : ρ u₁ - 1 ≠ 0 := sub_ne_zero.mpr hρu₁
  obtain ⟨χ₀, w₀, hev0, hTw⟩ :=
    exists_jointEigenvector_apply_ne_zero ρ A hA hinv (ρ u₁ - 1) hT
  have hw0 : w₀ ≠ 0 := by
    rintro rfl
    exact hTw (map_zero _)
  have hχu₁ : χ₀ ⟨u₁, trivial⟩ ≠ 1 := by
    intro h
    apply hTw
    rw [LinearMap.sub_apply, hev0 ⟨u₁, trivial⟩, h, one_smul, Module.End.one_apply, sub_self]
  have hχmul : ∀ x y : A, χ₀ (x * y) = χ₀ x * χ₀ y := by
    intro x y
    have h1 : ρ ((x * y : A) : U) w₀ = (χ₀ x * χ₀ y) • w₀ := by
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hev0 y, map_smul, hev0 x, smul_smul,
        mul_comm]
    have h2 := hev0 (x * y)
    rw [h1] at h2
    exact (smul_left_injective ℂ hw0 h2).symm
  have hχ1 : χ₀ 1 = 1 := by
    have := hχmul 1 1
    rw [one_mul] at this
    have h3 : χ₀ 1 * (χ₀ 1 - 1) = 0 := by rw [mul_sub, mul_one, ← this, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exfalso
      have := hev0 1
      rw [h, zero_smul, Subgroup.coe_one, map_one, Module.End.one_apply] at this
      exact hw0 this
    · exact sub_eq_zero.mp h
  have hχne : ∀ x : A, χ₀ x ≠ 0 := by
    intro x h
    have := hχmul x x⁻¹
    rw [mul_inv_cancel, hχ1, h, zero_mul] at this
    exact one_ne_zero this
  let ψ : K → ℂ := fun c => χ₀ ⟨Multiplicative.ofAdd (c, 0), trivial⟩
  have hψ1 : ψ 1 ≠ 1 := hχu₁
  have hψne : ∀ c : K, ψ c ≠ 0 := fun c => hχne _
  have hψadd : ∀ c d : K, ψ (c + d) = ψ c * ψ d := by
    intro c d
    have h := hχmul ⟨Multiplicative.ofAdd (c, 0), trivial⟩ ⟨Multiplicative.ofAdd (d, 0), trivial⟩
    change χ₀ ⟨Multiplicative.ofAdd (c + d, 0), trivial⟩ =
      χ₀ ⟨Multiplicative.ofAdd (c, 0), trivial⟩ * χ₀ ⟨Multiplicative.ofAdd (d, 0), trivial⟩
    rw [← h]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← ofAdd_add]
    simp
  have hχsplit : ∀ (c : K) (u : V),
      χ₀ ⟨Multiplicative.ofAdd (c, u), trivial⟩ =
        ψ c * χ₀ ⟨Multiplicative.ofAdd (0, u), trivial⟩ := by
    intro c u
    have h := hχmul ⟨Multiplicative.ofAdd (c, 0), trivial⟩ ⟨Multiplicative.ofAdd (0, u), trivial⟩
    change χ₀ ⟨Multiplicative.ofAdd (c, u), trivial⟩ =
      χ₀ ⟨Multiplicative.ofAdd (c, 0), trivial⟩ * χ₀ ⟨Multiplicative.ofAdd (0, u), trivial⟩
    rw [← h]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← ofAdd_add]
    simp
  let w : Option (χ.range × V) → (Λ → ℂ)
    | none => fun _ => 1
    | some x => permFunHom Λ (π (g x)⁻¹) w₀
  let χ' : Option (χ.range × V) → A → ℂ
    | none => fun _ => 1
    | some x => fun m =>
        χ₀ ⟨Multiplicative.ofAdd (((x.1 : Kˣ) : K) * m.1.toAdd.1 +
          β (Am (sec x.1) m.1.toAdd.2) x.2, Am (sec x.1) m.1.toAdd.2), trivial⟩
  have hΛ : Nonempty Λ := by
    by_contra! hE
    exact hnt (Subsingleton.elim _ _)
  have hw : ∀ i, w i ≠ 0 := by
    rintro (_ | x)
    · rcases hΛ with ⟨x₀⟩
      intro h
      exact one_ne_zero (congrFun h x₀)
    · intro h
      apply hw0
      have h1 : permFunHom Λ (π (g x)) (permFunHom Λ (π (g x)⁻¹) w₀) = w₀ := by
        rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
          Module.End.one_apply]
      rw [← h1]
      exact (congrArg (permFunHom Λ (π (g x))) h).trans (map_zero _)
  have hev : ∀ i (m : A), ρ m (w i) = χ' i m • w i := by
    rintro (_ | x) ⟨m, -⟩
    · ext x₀
      simp [w, χ', ρ, permFunHom_apply]
    · set c := m.toAdd.1
      set u := m.toAdd.2
      have hm : m = Multiplicative.ofAdd (c, u) := rfl
      show permFunHom Λ (π (φ m)) (permFunHom Λ (π (g x)⁻¹) w₀) =
        χ' (some x) ⟨m, trivial⟩ • permFunHom Λ (π (g x)⁻¹) w₀
      have h1 : permFunHom Λ (π (φ m)) (permFunHom Λ (π (g x)⁻¹) w₀) =
          permFunHom Λ (π (g x)⁻¹) (permFunHom Λ (π (g x * φ m * (g x)⁻¹)) w₀) := by
        rw [← Module.End.mul_apply, ← map_mul, ← map_mul, ← Module.End.mul_apply, ← map_mul,
          ← map_mul]
        congr 2
        group
      rw [h1, hm, hgconj x c u]
      have h2 := hev0 ⟨Multiplicative.ofAdd (((x.1 : Kˣ) : K) * c +
        β (Am (sec x.1) u) x.2, Am (sec x.1) u), trivial⟩
      change permFunHom Λ (π (φ _)) w₀ = χ' (some x) ⟨m, trivial⟩ • w₀ at h2
      rw [h2, map_smul, ← hm]
  have hχ'inl : ∀ (x : χ.range × V) (c : K),
      χ' (some x) ⟨Multiplicative.ofAdd (c, 0), trivial⟩ = ψ (((x.1 : Kˣ) : K) * c) := by
    intro x c
    simp [χ', ψ]
  have hχ'inj : Function.Injective χ' := by
    rintro (_ | x) (_ | y) hxy
    · rfl
    · exfalso
      have h1 := congrFun hxy ⟨Multiplicative.ofAdd (((y.1 : Kˣ)⁻¹ : Kˣ), 0), trivial⟩
      rw [hχ'inl] at h1
      change (1 : ℂ) = ψ (((y.1 : Kˣ) : K) * ((y.1 : Kˣ)⁻¹ : Kˣ)) at h1
      rw [Units.mul_inv] at h1
      exact hψ1 h1.symm
    · exfalso
      have h1 := congrFun hxy ⟨Multiplicative.ofAdd (((x.1 : Kˣ)⁻¹ : Kˣ), 0), trivial⟩
      rw [hχ'inl] at h1
      change ψ (((x.1 : Kˣ) : K) * ((x.1 : Kˣ)⁻¹ : Kˣ)) = (1 : ℂ) at h1
      rw [Units.mul_inv] at h1
      exact hψ1 h1
    · congr 1
      have hr : x.1 = y.1 := by
        by_contra hne
        have hd : ((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K) ≠ 0 := by
          refine sub_ne_zero.mpr fun h => hne ?_
          exact Subtype.ext (Units.ext h)
        have h1 := congrFun hxy ⟨Multiplicative.ofAdd ((((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K))⁻¹, 0),
          trivial⟩
        rw [hχ'inl, hχ'inl] at h1
        have h2 : ((x.1 : Kˣ) : K) * (((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K))⁻¹ =
            ((y.1 : Kˣ) : K) * (((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K))⁻¹ + 1 := by
          calc ((x.1 : Kˣ) : K) * (((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K))⁻¹
              = ((y.1 : Kˣ) : K) * (((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K))⁻¹ +
                (((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K)) *
                  (((x.1 : Kˣ) : K) - ((y.1 : Kˣ) : K))⁻¹ := by ring
            _ = _ := by rw [mul_inv_cancel₀ hd]
        rw [h2, hψadd] at h1
        exact hψ1 (mul_left_cancel₀ (hψne _) (h1.trans (mul_one _).symm))
      have hv : x.2 = y.2 := by
        by_contra hne
        obtain ⟨u₀, hu₀⟩ := hβ (x.2 - y.2) (sub_ne_zero.mpr hne)
        set d : K := β u₀ (x.2 - y.2)
        let u' : V := d⁻¹ • u₀
        have hu' : β u' x.2 = β u' y.2 + 1 := by
          have hsub : β u' x.2 - β u' y.2 = 1 := by
            calc β u' x.2 - β u' y.2 = β u' (x.2 - y.2) := (map_sub (β u') x.2 y.2).symm
              _ = d⁻¹ * d := by simp [u', d, map_smul, smul_eq_mul]
              _ = 1 := inv_mul_cancel₀ hu₀
          linear_combination hsub
        obtain ⟨u, hu⟩ := hAsurj (sec x.1) u'
        have h1 := congrFun hxy ⟨Multiplicative.ofAdd (0, u), trivial⟩
        simp only [χ', toAdd_ofAdd, mul_zero, zero_add, ← hr, hu] at h1
        rw [hχsplit (β u' x.2) u', hχsplit (β u' y.2) u'] at h1
        have h2 : ψ (β u' x.2) = ψ (β u' y.2) :=
          mul_right_cancel₀ (hχne ⟨Multiplicative.ofAdd (0, u'), trivial⟩) h1
        rw [hu', hψadd] at h2
        exact hψ1 (mul_left_cancel₀ (hψne _) (h2.trans (mul_one _).symm))
      exact Prod.ext hr hv
  have hli := linearIndependent_of_distinct_weights ρ A hA w χ' hw hev hχ'inj
  have : Fintype χ.range := Fintype.ofFinite χ.range
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_prod,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hcard
  exact hcard

/-- Variant of `card_range_mul_card_add_one_le_card_of_heis_root` deducing `hinj` from
injectivity of `z` and left-nondegeneracy `hβl` of `β`. -/
theorem card_range_mul_card_add_one_le_card_of_heis_root_of_inj
    {S Λ : Type*} [Group S] [Finite Λ] (π : S →* Equiv.Perm Λ)
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hβl : ∀ u : V, u ≠ 0 → ∃ v, β u v ≠ 0)
    (hz : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v)
    {T : Type*} [Group T] (t : T →* S) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)))
    (hta : ∀ s u, ∃ u', t s * a (Multiplicative.ofAdd u) * (t s)⁻¹ =
      a (Multiplicative.ofAdd u'))
    (hnt : π (z (Multiplicative.ofAdd 1)) ≠ 1) :
    Nat.card χ.range * Nat.card V + 1 ≤ Nat.card Λ := by
  refine card_range_mul_card_add_one_le_card_of_heis_root π z a b β hβ ?_ hza hab hbz t χ htz hta
    hnt
  intro c u h
  have ha : a (Multiplicative.ofAdd u) = (z (Multiplicative.ofAdd c))⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  have hβ0 : ∀ v, β u v = 0 := by
    intro v
    apply hz
    have h1 := hab u v
    have h2 : b v * (z (Multiplicative.ofAdd c))⁻¹ * (b v)⁻¹ = (z (Multiplicative.ofAdd c))⁻¹ := by
      rw [← map_inv, hbz, mul_inv_cancel_right]
    rw [ha, h2] at h1
    exact mul_eq_left.1 h1.symm
  have hu : u = 0 := by
    by_contra hu0
    obtain ⟨v, hv⟩ := hβl u hu0
    exact hv (hβ0 v)
  subst hu
  refine ⟨hz c ?_, rfl⟩
  rwa [ofAdd_zero, map_one a, mul_one] at h

/-- Specialization of `card_range_mul_card_add_one_le_card_of_heis_root_of_inj` with trivial
torus (`T = Unit`), giving `Nat.card V + 1 ≤ Nat.card Λ`. -/
theorem card_add_one_le_card_of_heis_root_of_inj_one
    {S Λ : Type*} [Group S] [Finite Λ] (π : S →* Equiv.Perm Λ)
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hβl : ∀ u : V, u ≠ 0 → ∃ v, β u v ≠ 0)
    (hz : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v)
    (hnt : π (z (Multiplicative.ofAdd 1)) ≠ 1) :
    Nat.card V + 1 ≤ Nat.card Λ := by
  have h := card_range_mul_card_add_one_le_card_of_heis_root_of_inj π z a b β hβ hβl hz hza hab
    hbz (T := Unit) 1 1 (fun _ _ => by simp) (fun _ u => ⟨u, by simp⟩) hnt
  have h1 : Nat.card (1 : Unit →* Kˣ).range = 1 := by
    rw [MonoidHom.range_one, Subgroup.card_bot]
  rwa [h1, one_mul] at h

/-- Specialization of `card_range_mul_card_add_one_le_card_of_heis_root_of_inj` to a single root
subgroup `z : Multiplicative K →* S` normalized by a torus `t : T →* S` (`V = Fin 0 → K`),
giving `Nat.card χ.range + 1 ≤ Nat.card Λ`. -/
theorem card_range_add_one_le_card_of_torus_root
    {S Λ : Type*} [Group S] [Finite Λ] (π : S →* Equiv.Perm Λ)
    {K : Type*} [Field K] [Finite K]
    (z : Multiplicative K →* S)
    (hz : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0)
    {T : Type*} [Group T] (t : T →* S) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)))
    (hnt : π (z (Multiplicative.ofAdd 1)) ≠ 1) :
    Nat.card χ.range + 1 ≤ Nat.card Λ := by
  have h := card_range_mul_card_add_one_le_card_of_heis_root_of_inj π z
    (V := Fin 0 → K) 1 (fun _ => 1) 0
    (fun v hv => False.elim (hv (Subsingleton.elim v 0)))
    (fun u hu => False.elim (hu (Subsingleton.elim u 0)))
    hz (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    t χ htz (fun _ u => ⟨u, by simp⟩) hnt
  have hV : Nat.card (Fin 0 → K) = 1 := by simp
  rwa [hV, mul_one] at h

/-! ### Subgroup index versions for finite simple groups -/

/-- Subgroup index version of `card_range_mul_card_add_one_le_card_of_heis_root` for a proper
subgroup `M < S` of a finite simple group `S`. -/
theorem card_range_mul_card_add_one_le_index_of_heis_root
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hinj : ∀ (c : K) (u : V), z (Multiplicative.ofAdd c) * a (Multiplicative.ofAdd u) = 1 →
      c = 0 ∧ u = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v)
    {T : Type*} [Group T] (t : T →* S) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)))
    (hta : ∀ s u, ∃ u', t s * a (Multiplicative.ofAdd u) * (t s)⁻¹ =
      a (Multiplicative.ofAdd u'))
    (M : Subgroup S) (hM : M ≠ ⊤) :
    Nat.card χ.range * Nat.card V + 1 ≤ M.index := by
  rw [Subgroup.index_eq_card]
  have hz1 : z (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    have h0 := (hinj 1 0 (by rw [ofAdd_zero, map_one a, mul_one]; exact h)).1
    exact one_ne_zero h0
  exact card_range_mul_card_add_one_le_card_of_heis_root (MulAction.toPermHom S (S ⧸ M))
    z a b β hβ hinj hza hab hbz t χ htz hta (toPermHom_quotient_ne_one_of_ne_one hM hz1)

/-- Subgroup index version of `card_add_one_le_card_of_heis_root_of_inj_one` for a proper
subgroup `M < S` of a finite simple group `S`. -/
theorem card_add_one_le_index_of_heis_root_of_inj_one
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (z : Multiplicative K →* S) (a : Multiplicative V →* S) (b : V → S)
    (β : V →ₗ[K] V →ₗ[K] K) (hβ : ∀ v : V, v ≠ 0 → ∃ u, β u v ≠ 0)
    (hβl : ∀ u : V, u ≠ 0 → ∃ v, β u v ≠ 0)
    (hz : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0)
    (hza : ∀ c u, z c * a u = a u * z c)
    (hab : ∀ u v, b v * a (Multiplicative.ofAdd u) * (b v)⁻¹ =
      a (Multiplicative.ofAdd u) * z (Multiplicative.ofAdd (β u v)))
    (hbz : ∀ (c : Multiplicative K) (v : V), b v * z c = z c * b v)
    (M : Subgroup S) (hM : M ≠ ⊤) :
    Nat.card V + 1 ≤ M.index := by
  rw [Subgroup.index_eq_card]
  have hz1 : z (Multiplicative.ofAdd 1) ≠ 1 := fun h => one_ne_zero (hz 1 h)
  exact card_add_one_le_card_of_heis_root_of_inj_one (MulAction.toPermHom S (S ⧸ M))
    z a b β hβ hβl hz hza hab hbz (toPermHom_quotient_ne_one_of_ne_one hM hz1)

/-- Subgroup index version of `card_range_add_one_le_card_of_torus_root` for a proper subgroup
`M < S` of a finite simple group `S`. -/
theorem card_range_add_one_le_index_of_torus_root
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {K : Type*} [Field K] [Finite K]
    (z : Multiplicative K →* S)
    (hz : ∀ c : K, z (Multiplicative.ofAdd c) = 1 → c = 0)
    {T : Type*} [Group T] (t : T →* S) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * z (Multiplicative.ofAdd c) * (t s)⁻¹ =
      z (Multiplicative.ofAdd ((χ s : K) * c)))
    (M : Subgroup S) (hM : M ≠ ⊤) :
    Nat.card χ.range + 1 ≤ M.index := by
  rw [Subgroup.index_eq_card]
  have hz1 : z (Multiplicative.ofAdd 1) ≠ 1 := fun h => one_ne_zero (hz 1 h)
  exact card_range_add_one_le_card_of_torus_root (MulAction.toPermHom S (S ⧸ M))
    z hz t χ htz (toPermHom_quotient_ne_one_of_ne_one hM hz1)

/-! ### Subgroup index bounds from `HeisSystem` -/

section HeisSystemBridge

variable {Γ : Type*} [Group Γ] {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]
  (H : HeisSystem Γ K I)

/-- Central root homomorphism `Multiplicative K →* Γ` of `H : HeisSystem Γ K I`. -/
def heisSysZ : Multiplicative K →* Γ where
  toFun c := H.z c.toAdd
  map_one' := H.z_zero
  map_mul' c d := H.z_add c.toAdd d.toAdd

/-- Single-coordinate `xa` homomorphism `Multiplicative K →* Γ` of `H : HeisSystem Γ K I`. -/
def heisSysXa (i : I) : Multiplicative K →* Γ where
  toFun c := H.xa i c.toAdd
  map_one' := H.xa_zero i
  map_mul' c d := H.xa_add i c.toAdd d.toAdd

/-- Product `xa` homomorphism `Multiplicative (I → K) →* Γ` of `H : HeisSystem Γ K I`. -/
noncomputable def heisSysXaProd : Multiplicative (I → K) →* Γ :=
  (MonoidHom.noncommPiCoprod (fun i : I => heisSysXa H i)
    (by intro i j _ x y; exact H.xa_comm i j x.toAdd y.toAdd)).comp
    (MulEquiv.piMultiplicative (fun _ : I => K)).toMonoidHom

theorem heisSysXaProd_single (i : I) (d : K) :
    heisSysXaProd H (Multiplicative.ofAdd (Pi.single i d)) = H.xa i d := by
  have h : (MulEquiv.piMultiplicative (fun _ : I => K)).toMonoidHom
      (Multiplicative.ofAdd (Pi.single i d)) = Pi.mulSingle i (Multiplicative.ofAdd d) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [MulEquiv.piMultiplicative]
    · simp [MulEquiv.piMultiplicative, hj]
  rw [heisSysXaProd, MonoidHom.comp_apply, h, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

/-- Bilinear commutator pairing `(I → K) →ₗ[K] (I → K) →ₗ[K] K` of `H : HeisSystem Γ K I`. -/
def heisSysBeta : (I → K) →ₗ[K] (I → K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun u v => ∑ i, H.ε i * u i * v i)
    (fun u u' v => by simp [mul_add, add_mul, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun u v v' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

omit [DecidableEq I] in
theorem heisSysBeta_apply (u v : I → K) : heisSysBeta H u v = ∑ i, H.ε i * u i * v i := rfl

theorem heisSysBeta_nondeg_right {v : I → K} (hv : v ≠ 0) : ∃ u, heisSysBeta H u v ≠ 0 := by
  obtain ⟨i, hi0⟩ := Function.ne_iff.1 hv
  have hi : v i ≠ 0 := hi0
  refine ⟨Pi.single i (1 / (H.ε i * v i)), ?_⟩
  rw [heisSysBeta_apply, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
    have h1 := H.ε_ne i
    have e : H.ε i * (1 / (H.ε i * v i)) * v i = 1 := by field_simp
    rw [e]
    exact one_ne_zero
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem heisSysBeta_nondeg_left {u : I → K} (hu : u ≠ 0) : ∃ v, heisSysBeta H u v ≠ 0 := by
  obtain ⟨i, hi0⟩ := Function.ne_iff.1 hu
  have hi : u i ≠ 0 := hi0
  refine ⟨Pi.single i (1 / (H.ε i * u i)), ?_⟩
  rw [heisSysBeta_apply, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
    have h1 := H.ε_ne i
    have e : H.ε i * u i * (1 / (H.ε i * u i)) = 1 := by field_simp
    rw [e]
    exact one_ne_zero
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Inverse `yElt` map `(I → K) → Γ` of `H : HeisSystem Γ K I`. -/
noncomputable def heisSysB (v : I → K) : Γ := (H.yElt v)⁻¹

omit [DecidableEq I] in
theorem heisSysB_comm_z (c : Multiplicative K) (v : I → K) :
    heisSysB H v * heisSysZ H c = heisSysZ H c * heisSysB H v :=
  ((Commute.inv_left (H.yElt_comm_z v c.toAdd))).eq

theorem heisSysZ_comm_xaProd (c : Multiplicative K) (u : Multiplicative (I → K)) :
    heisSysZ H c * heisSysXaProd H u = heisSysXaProd H u * heisSysZ H c := by
  have hall : ∀ w : I → K, ∀ c' : K, H.z c' * heisSysXaProd H (Multiplicative.ofAdd w) =
      heisSysXaProd H (Multiplicative.ofAdd w) * H.z c' := by
    intro w c'
    have hw : w = ∑ i, Pi.single i (w i) := (Finset.univ_sum_single w).symm
    rw [hw]
    refine Finset.sum_induction _ (fun x => H.z c' * heisSysXaProd H (Multiplicative.ofAdd x) =
        heisSysXaProd H (Multiplicative.ofAdd x) * H.z c') ?_ ?_ ?_
    · intro x y hx hy
      rw [ofAdd_add, map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    · simp
    · intro i _
      rw [heisSysXaProd_single]
      exact H.z_comm_a c' i _
  exact hall u.toAdd c.toAdd

theorem heisSysXaProd_conj (v u : I → K) :
    heisSysB H v * heisSysXaProd H (Multiplicative.ofAdd u) * (heisSysB H v)⁻¹ =
      heisSysXaProd H (Multiplicative.ofAdd u) * H.z (heisSysBeta H u v) := by
  have key : ∀ x : I → K,
      heisSysB H v * heisSysXaProd H (Multiplicative.ofAdd x) * (heisSysB H v)⁻¹ =
        heisSysXaProd H (Multiplicative.ofAdd x) * H.z (heisSysBeta H x v) := by
    intro x
    have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
    rw [hx]
    refine Finset.sum_induction _ (fun x => heisSysB H v *
        heisSysXaProd H (Multiplicative.ofAdd x) * (heisSysB H v)⁻¹ =
          heisSysXaProd H (Multiplicative.ofAdd x) * H.z (heisSysBeta H x v)) ?_ ?_ ?_
    · intro x y hx hy
      have hzc : ∀ c : K, H.z c * heisSysXaProd H (Multiplicative.ofAdd y) =
          heisSysXaProd H (Multiplicative.ofAdd y) * H.z c := fun c =>
        heisSysZ_comm_xaProd H (Multiplicative.ofAdd c) _
      calc heisSysB H v * heisSysXaProd H (Multiplicative.ofAdd (x + y)) * (heisSysB H v)⁻¹
          = (heisSysB H v * heisSysXaProd H (Multiplicative.ofAdd x) * (heisSysB H v)⁻¹) *
            (heisSysB H v * heisSysXaProd H (Multiplicative.ofAdd y) * (heisSysB H v)⁻¹) := by
            rw [ofAdd_add, map_mul]; group
        _ = heisSysXaProd H (Multiplicative.ofAdd x) * H.z (heisSysBeta H x v) *
            (heisSysXaProd H (Multiplicative.ofAdd y) * H.z (heisSysBeta H y v)) := by rw [hx, hy]
        _ = heisSysXaProd H (Multiplicative.ofAdd x) *
            (H.z (heisSysBeta H x v) * heisSysXaProd H (Multiplicative.ofAdd y)) *
            H.z (heisSysBeta H y v) := by simp only [mul_assoc]
        _ = heisSysXaProd H (Multiplicative.ofAdd x) *
            (heisSysXaProd H (Multiplicative.ofAdd y) * H.z (heisSysBeta H x v)) *
            H.z (heisSysBeta H y v) := by rw [hzc]
        _ = heisSysXaProd H (Multiplicative.ofAdd (x + y)) * H.z (heisSysBeta H (x + y) v) := by
            rw [ofAdd_add, map_mul, map_add, LinearMap.add_apply, H.z_add]
            simp only [mul_assoc]
    · simp [H.z_zero]
    · intro i _
      rw [heisSysXaProd_single]
      have h1 := H.comm_yElt_xa v i (x i)
      rw [commutatorElement_def, inv_inv] at h1
      have h2 : heisSysB H v * H.xa i (x i) * (heisSysB H v)⁻¹ =
          H.z (H.ε i * v i * x i) * H.xa i (x i) := by
        rw [heisSysB, inv_inv]
        calc (H.yElt v)⁻¹ * H.xa i (x i) * H.yElt v
            = ((H.yElt v)⁻¹ * H.xa i (x i) * H.yElt v * (H.xa i (x i))⁻¹) * H.xa i (x i) := by
              group
          _ = _ := by rw [h1]
      rw [h2]
      have h3 : heisSysBeta H (Pi.single i (x i)) v = H.ε i * v i * x i := by
        rw [heisSysBeta_apply, Finset.sum_eq_single i]
        · simp only [Pi.single_eq_same]; ring
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [h3]
      exact H.z_comm_a _ i _
  exact key u

end HeisSystemBridge

/-- If `Γ` is a finite simple group, `H : HeisSystem Γ K I` is a Heisenberg system, and `t : T →* Γ`
normalizes `H` with central character `χ : T →* Kˣ` and `t s * H.xa i d * (t s)⁻¹ = H.xa i d'`,
then every proper subgroup `M < Γ` has index at least `Nat.card χ.range * Nat.card (I → K) + 1`. -/
theorem HeisSystem.card_range_mul_card_add_one_le_index_of_isSimpleGroup
    {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    {K : Type} [Field K] [Finite K] {I : Type} [Fintype I] [DecidableEq I]
    (H : HeisSystem Γ K I)
    {T : Type*} [Group T] (t : T →* Γ) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * H.z c * (t s)⁻¹ = H.z ((χ s : K) * c))
    (htxa : ∀ s (i : I) (d : K), ∃ d' : K, t s * H.xa i d * (t s)⁻¹ = H.xa i d')
    (M : Subgroup Γ) (hM : M ≠ ⊤) :
    Nat.card χ.range * Nat.card (I → K) + 1 ≤ M.index := by
  rw [Subgroup.index_eq_card]
  have hz : ∀ c : K, heisSysZ H (Multiplicative.ofAdd c) = 1 → c = 0 :=
    fun c h => H.z_injective (h.trans H.z_zero.symm)
  have hz1 : heisSysZ H (Multiplicative.ofAdd 1) ≠ 1 := fun h => one_ne_zero (hz 1 h)
  have hta : ∀ s (u : I → K), ∃ u' : I → K,
      t s * heisSysXaProd H (Multiplicative.ofAdd u) * (t s)⁻¹ =
        heisSysXaProd H (Multiplicative.ofAdd u') := by
    intro s u
    have hw : u = ∑ i, Pi.single i (u i) := (Finset.univ_sum_single u).symm
    rw [hw]
    refine Finset.sum_induction _ (fun x : I → K => ∃ u' : I → K,
      t s * heisSysXaProd H (Multiplicative.ofAdd x) * (t s)⁻¹ =
        heisSysXaProd H (Multiplicative.ofAdd u')) ?_ ?_ ?_
    · rintro x y ⟨x', hx⟩ ⟨y', hy⟩
      refine ⟨x' + y', ?_⟩
      rw [ofAdd_add, map_mul, ofAdd_add, map_mul, ← hx, ← hy]
      group
    · exact ⟨0, by simp⟩
    · intro i _
      obtain ⟨d', hd'⟩ := htxa s i (u i)
      refine ⟨Pi.single i d', ?_⟩
      rw [heisSysXaProd_single, heisSysXaProd_single, hd']
  exact card_range_mul_card_add_one_le_card_of_heis_root_of_inj
    (MulAction.toPermHom Γ (Γ ⧸ M)) (heisSysZ H) (heisSysXaProd H) (heisSysB H) (heisSysBeta H)
    (fun v hv => heisSysBeta_nondeg_right H hv)
    (fun u hu => heisSysBeta_nondeg_left H hu)
    hz (heisSysZ_comm_xaProd H) (fun u v => heisSysXaProd_conj H v u) (heisSysB_comm_z H)
    t χ htz hta (toPermHom_quotient_ne_one_of_ne_one hM hz1)

/-- If `Γ` is a finite simple group and `H : HeisSystem Γ K I` is a Heisenberg system, then every
proper subgroup `M < Γ` has index at least `Nat.card (I → K)`. -/
theorem HeisSystem.card_le_index_of_isSimpleGroup
    {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    {K : Type} [Field K] [Finite K] {I : Type} [Fintype I] [DecidableEq I]
    (H : HeisSystem Γ K I) (M : Subgroup Γ) (hM : M ≠ ⊤) :
    Nat.card (I → K) ≤ M.index := by
  have h := HeisSystem.card_range_mul_card_add_one_le_index_of_isSimpleGroup H
    (T := Unit) 1 1 (fun _ _ => by simp) (fun _ _ d => ⟨d, by simp⟩) M hM
  have h1 : Nat.card (1 : Unit →* Kˣ).range = 1 := by
    rw [MonoidHom.range_one, Subgroup.card_bot]
  rw [h1, one_mul] at h
  omega

/-- If `Γ` is a finite simple group and `H : HeisSystem Γ K I` is a Heisenberg system over a finite
field `K` of characteristic `2`, then every proper subgroup `M < Γ` has index at least
`2 * Nat.card (I → K)`. -/
theorem HeisSystem.two_mul_card_le_index_of_isSimpleGroup
    {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    {K : Type} [Field K] [Finite K] [CharP K 2] {I : Type} [Fintype I] [DecidableEq I]
    (H : HeisSystem Γ K I) (M : Subgroup Γ) (hM : M ≠ ⊤) :
    2 * Nat.card (I → K) ≤ M.index := by
  rw [Subgroup.index_eq_card]
  have hA := H.isMulCommutative_A
  have : Finite H.A := Subtype.finite
  have hz1 : H.z 1 ≠ 1 := fun h => one_ne_zero (H.z_injective (h.trans H.z_zero.symm))
  have hzsq : H.z 1 * H.z 1 = 1 := by
    rw [← H.z_add, show (1 : K) + 1 = ((2 : ℕ) : K) by norm_num, CharP.cast_eq_zero, H.z_zero]
  have hHD : ∀ c c' : I → K, c ≠ c' → ∀ u ∈ H.Z, ∃ a ∈ H.A,
      ⁅(H.yElt c)⁻¹, a⁆ = u * ⁅(H.yElt c')⁻¹, a⁆ := by
    rintro c c' hne _ ⟨e, rfl⟩
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
    have hδ : c t - c' t ≠ 0 := sub_ne_zero.mpr ht
    have hε := H.ε_ne t
    have hεδ : H.ε t * (c t - c' t) ≠ 0 := mul_ne_zero hε hδ
    refine ⟨H.xa t (e / (H.ε t * (c t - c' t))), H.xa_mem_A _ _, ?_⟩
    rw [H.comm_yElt_xa, H.comm_yElt_xa, ← H.z_add]
    congr 1
    field_simp
    ring
  exact two_mul_card_le_card_of_heisenberg_perm (MulAction.toPermHom Γ (Γ ⧸ M))
    H.A H.Z hA H.Z_le_A H.yElt (fun c a ha => H.comm_yElt_mem_Z c a ha) hHD
    (H.z_mem_Z 1) hzsq (toPermHom_quotient_ne_one_of_ne_one hM hz1) (fun c => H.yElt_comm_z c 1)

/-! ### Swapped and paired Heisenberg systems in characteristic `2` -/

/-- The Heisenberg system obtained by swapping `xa` and `xb` and negating `ε`. -/
def HeisSystem.swap {Γ : Type*} [Group Γ] {K : Type*} [Field K] {I : Type*}
    (H : HeisSystem Γ K I) : HeisSystem Γ K I where
  xa := H.xb
  xb := H.xa
  z := H.z
  ε s := -H.ε s
  xa_add := H.xb_add
  xb_add := H.xa_add
  z_add := H.z_add
  z_injective := H.z_injective
  ε_ne s := neg_ne_zero.mpr (H.ε_ne s)
  xa_comm := H.xb_comm
  xb_comm := H.xa_comm
  z_comm_a := H.z_comm_b
  z_comm_b := H.z_comm_a
  xab_comm s t hst c d := (H.xab_comm t s hst.symm d c).symm
  comm_ss s c d := by
    have hxa0 : H.xa s 0 = 1 := H.xa_zero s
    have hxb0 : H.xb s 0 = 1 := by
      have h := H.xb_add s 0 0
      rw [add_zero] at h
      exact mul_eq_left.mp h.symm
    have hxa_neg : H.xa s (-c) = (H.xa s c)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← H.xa_add, neg_add_cancel, hxa0]
    have hxb_neg : (H.xb s (-d))⁻¹ = H.xb s d := by
      rw [inv_eq_iff_mul_eq_one, ← H.xb_add, neg_add_cancel, hxb0]
    have h1 := H.comm_ss s (-d) (-c)
    rw [hxb_neg, hxa_neg] at h1
    have h2 : ⁅(H.xa s c)⁻¹, H.xb s d⁆ = (⁅H.xb s d, (H.xa s c)⁻¹⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2, h1, ← H.z_neg]
    congr 1
    ring

/-- If `σ₁, σ₂, σ₃, τ, ν` are permutations of `Λ` such that `σ₂ ≠ 1`, `σ₁` and `σ₂` commute,
`τ⁻¹ * σ₁ * τ = σ₁ * σ₂ * σ₃`, `τ` commutes with `σ₂`, `ν * σ₁ * ν⁻¹ = σ₃`, and
`ν * σ₂ * ν⁻¹ = σ₂`, then there exists `x₀ : Λ` moved by both `σ₁` and `σ₂`. -/
theorem exists_moved_both_of_conj_mul {Λ : Type*}
    (σ₁ σ₂ σ₃ τ ν : Equiv.Perm Λ)
    (hσ₂ : σ₂ ≠ 1) (h12 : σ₁ * σ₂ = σ₂ * σ₁)
    (hτ1 : τ⁻¹ * σ₁ * τ = σ₁ * σ₂ * σ₃) (hτ2 : τ * σ₂ = σ₂ * τ)
    (hν1 : ν * σ₁ * ν⁻¹ = σ₃) (hν2 : ν * σ₂ * ν⁻¹ = σ₂) :
    ∃ x₀ : Λ, σ₁ x₀ ≠ x₀ ∧ σ₂ x₀ ≠ x₀ := by
  by_contra! hno
  have hno' : ∀ x : Λ, σ₂ x ≠ x → σ₁ x = x := by
    intro x hx
    by_contra h1
    exact hx (hno x h1)
  have hno₃ : ∀ x : Λ, σ₂ x ≠ x → σ₃ x = x := by
    intro x hx
    have hν2' : ∀ z, ν (σ₂ (ν⁻¹ z)) = σ₂ z := fun z =>
      congrArg (fun p : Equiv.Perm Λ => p z) hν2
    have hν1' : ∀ z, ν (σ₁ (ν⁻¹ z)) = σ₃ z := fun z =>
      congrArg (fun p : Equiv.Perm Λ => p z) hν1
    have hy : σ₂ (ν⁻¹ x) ≠ ν⁻¹ x := by
      intro h
      apply hx
      rw [← hν2' x, h]
      simp
    have h1 := hno' (ν⁻¹ x) hy
    rw [← hν1' x, h1]
    simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Λ, σ₂ x₀ ≠ x₀ := by
    by_contra! h
    exact hσ₂ (Equiv.ext h)
  have h1 : σ₁ x₀ = x₀ := hno' x₀ hx₀
  have h3 : σ₃ x₀ = x₀ := hno₃ x₀ hx₀
  have hτx₀ : σ₂ (τ x₀) ≠ τ x₀ := by
    have h := congrArg (fun p : Equiv.Perm Λ => p x₀) hτ2.symm
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at h
    rw [h]
    exact fun h' => hx₀ (τ.injective h')
  have h1τ : σ₁ (τ x₀) = τ x₀ := hno' (τ x₀) hτx₀
  have hlhs : (τ⁻¹ * σ₁ * τ) x₀ = x₀ := by
    simp [h1τ]
  have hrhs : (σ₁ * σ₂ * σ₃) x₀ = σ₂ x₀ := by
    have h12' := congrArg (fun p : Equiv.Perm Λ => p x₀) h12
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, h1] at h12'
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, h3, h12']
  rw [hτ1, hrhs] at hlhs
  exact hx₀ hlhs

/-- Given two commuting involutions `σ₁, σ₂ : Equiv.Perm Λ` and a point `x₀ : Λ` moved by both
`σ₁` and `σ₂`, the intersection `antiInv σ₁ ⊓ antiInv σ₂` contains a nonzero function. -/
theorem exists_ne_zero_mem_antiInv_inf {Λ : Type*} {σ₁ σ₂ : Equiv.Perm Λ}
    (hσ₁ : σ₁ * σ₁ = 1) (hσ₂ : σ₂ * σ₂ = 1) (h12 : σ₁ * σ₂ = σ₂ * σ₁)
    {x₀ : Λ} (hx₁ : σ₁ x₀ ≠ x₀) (hx₂ : σ₂ x₀ ≠ x₀) :
    ∃ f ∈ antiInv σ₁ ⊓ antiInv σ₂, f ≠ 0 := by
  classical
  have h11 : ∀ z, σ₁ (σ₁ z) = z := fun z => by
    simpa using congrArg (fun p : Equiv.Perm Λ => p z) hσ₁
  have h22 : ∀ z, σ₂ (σ₂ z) = z := fun z => by
    simpa using congrArg (fun p : Equiv.Perm Λ => p z) hσ₂
  have hcomm : ∀ z, σ₁ (σ₂ z) = σ₂ (σ₁ z) := fun z =>
    congrArg (fun p : Equiv.Perm Λ => p z) h12
  let f₁ : Λ → ℂ := fun y => (if y = x₀ then (1 : ℂ) else 0) - (if y = σ₁ x₀ then 1 else 0)
  have hf₁ : ∀ y, f₁ (σ₁ y) = - f₁ y := by
    intro y
    have e1 : σ₁ y = x₀ ↔ y = σ₁ x₀ :=
      ⟨fun h => by rw [← h, h11], fun h => by rw [h, h11]⟩
    have e2 : σ₁ y = σ₁ x₀ ↔ y = x₀ := σ₁.injective.eq_iff
    simp only [f₁, e1, e2]
    ring
  by_cases hsame : σ₂ x₀ = σ₁ x₀
  · refine ⟨f₁, ⟨mem_antiInv.2 hf₁, mem_antiInv.2 fun y => ?_⟩, ?_⟩
    · have e1 : σ₂ y = x₀ ↔ y = σ₁ x₀ := by
        rw [← hsame]
        exact ⟨fun h => by rw [← h, h22], fun h => by rw [h, h22]⟩
      have e2 : σ₂ y = σ₁ x₀ ↔ y = x₀ := by
        rw [← hsame]
        exact σ₂.injective.eq_iff
      simp only [f₁, e1, e2]
      ring
    · intro h
      have := congrFun h x₀
      simp [f₁, Ne.symm hx₁] at this
  · let f : Λ → ℂ := fun y => f₁ y - f₁ (σ₂ y)
    refine ⟨f, ⟨mem_antiInv.2 fun y => ?_, mem_antiInv.2 fun y => ?_⟩, ?_⟩
    · simp only [f, ← hcomm y, hf₁ y, hf₁ (σ₂ y)]
      ring
    · simp only [f, h22 y]
      ring
    · intro h
      have := congrFun h x₀
      simp [f, f₁, Ne.symm hx₁, hx₂, hsame] at this

/-- If `H₁ : HeisSystem Γ K I₁` and `H₂ : HeisSystem Γ K I₂` are two compatible Heisenberg systems
over a finite field `K` of characteristic `2` such that some point `x₀ : Λ` is moved by both
`π (H₁.z 1)` and `π (H₂.z 1)`, then `2 * (Nat.card (I₁ → K) * Nat.card (I₂ → K)) ≤ Nat.card Λ`. -/
theorem HeisSystem.two_mul_card_mul_card_le_card_of_perm
    {Γ Λ : Type*} [Group Γ] [Finite Γ] [Finite Λ] (π : Γ →* Equiv.Perm Λ)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (H₁ : HeisSystem Γ K I₁) (H₂ : HeisSystem Γ K I₂)
    (hzz : ∀ c₁ c₂, H₁.z c₁ * H₂.z c₂ = H₂.z c₂ * H₁.z c₁)
    (hz₁a₂ : ∀ c₁ s₂ d₂, H₁.z c₁ * H₂.xa s₂ d₂ = H₂.xa s₂ d₂ * H₁.z c₁)
    (hz₁b₂ : ∀ c₁ s₂ d₂, H₁.z c₁ * H₂.xb s₂ d₂ = H₂.xb s₂ d₂ * H₁.z c₁)
    (hz₂a₁ : ∀ c₂ s₁ d₁, H₂.z c₂ * H₁.xa s₁ d₁ = H₁.xa s₁ d₁ * H₂.z c₂)
    (hz₂b₁ : ∀ c₂ s₁ d₁, H₂.z c₂ * H₁.xb s₁ d₁ = H₁.xb s₁ d₁ * H₂.z c₂)
    (ha₁a₂ : ∀ s₁ s₂ d₁ d₂, H₁.xa s₁ d₁ * H₂.xa s₂ d₂ = H₂.xa s₂ d₂ * H₁.xa s₁ d₁)
    (hb₁a₂ : ∀ s₁ s₂ c₁ d₂, H₁.xb s₁ c₁ * H₂.xa s₂ d₂ = H₂.xa s₂ d₂ * H₁.xb s₁ c₁)
    (hb₂a₁ : ∀ s₂ s₁ c₂ d₁, H₂.xb s₂ c₂ * H₁.xa s₁ d₁ = H₁.xa s₁ d₁ * H₂.xb s₂ c₂)
    (hmove : ∃ x₀ : Λ, π (H₁.z 1) x₀ ≠ x₀ ∧ π (H₂.z 1) x₀ ≠ x₀) :
    2 * (Nat.card (I₁ → K) * Nat.card (I₂ → K)) ≤ Nat.card Λ := by
  classical
  have hz₁sq : H₁.z 1 * H₁.z 1 = 1 := by
    rw [← H₁.z_add, show (1 : K) + 1 = ((2 : ℕ) : K) by norm_num, CharP.cast_eq_zero, H₁.z_zero]
  have hz₂sq : H₂.z 1 * H₂.z 1 = 1 := by
    rw [← H₂.z_add, show (1 : K) + 1 = ((2 : ℕ) : K) by norm_num, CharP.cast_eq_zero, H₂.z_zero]
  let σ₁ : Equiv.Perm Λ := π (H₁.z 1)
  let σ₂ : Equiv.Perm Λ := π (H₂.z 1)
  have hσ₁ : σ₁ * σ₁ = 1 := by rw [← map_mul, hz₁sq, map_one]
  have hσ₂ : σ₂ * σ₂ = 1 := by rw [← map_mul, hz₂sq, map_one]
  have hσ₁₂ : σ₁ * σ₂ = σ₂ * σ₁ := by rw [← map_mul, ← map_mul, hzz 1 1]
  let W : Submodule ℂ (Λ → ℂ) := antiInv σ₁ ⊓ antiInv σ₂
  obtain ⟨x₀, hx₁, hx₂⟩ := hmove
  obtain ⟨f₀, hf₀W, hf₀0⟩ := exists_ne_zero_mem_antiInv_inf hσ₁ hσ₂ hσ₁₂ hx₁ hx₂
  let C : Subgroup Γ := Subgroup.centralizer {H₁.z 1, H₂.z 1}
  have hmemC : ∀ g : Γ, g ∈ C ↔ g * H₁.z 1 = H₁.z 1 * g ∧ g * H₂.z 1 = H₂.z 1 * g := by
    intro g
    simp only [C, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  have hπC₁ : ∀ g : C, π (g : Γ) * σ₁ = σ₁ * π (g : Γ) := fun g => by
    rw [← map_mul, ← map_mul, ((hmemC g).1 g.2).1]
  have hπC₂ : ∀ g : C, π (g : Γ) * σ₂ = σ₂ * π (g : Γ) := fun g => by
    rw [← map_mul, ← map_mul, ((hmemC g).1 g.2).2]
  let ρ : C →* Module.End ℂ W :=
    { toFun := fun g => (permFunHom Λ (π (g : Γ))).restrict fun _ hf =>
        ⟨permFunHom_mem_antiInv (hπC₁ g) hf.1, permFunHom_mem_antiInv (hπC₂ g) hf.2⟩
      map_one' := by
        refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
        simp
      map_mul' := fun g g' => by
        refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
        change permFunHom Λ (π ((g * g' : C) : Γ)) (f : Λ → ℂ) x =
          permFunHom Λ (π (g : Γ)) (permFunHom Λ (π (g' : Γ)) (f : Λ → ℂ)) x
        simp [map_mul] }
  have hρ_apply : ∀ (g : C) (w : W) (x : Λ),
      ((ρ g w : W) : Λ → ℂ) x = (w : Λ → ℂ) ((π (g : Γ))⁻¹ x) := fun _ _ _ => rfl
  let A : Subgroup Γ := Subgroup.closure (H₁.genA ∪ H₂.genA)
  let Z : Subgroup Γ := Subgroup.closure (Set.range H₁.z ∪ Set.range H₂.z)
  have hA₁le : H₁.A ≤ A := Subgroup.closure_mono Set.subset_union_left
  have hA₂le : H₂.A ≤ A := Subgroup.closure_mono Set.subset_union_right
  have hZ₁le : H₁.Z ≤ Z := by
    rintro _ ⟨c, rfl⟩
    exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hZ₂le : H₂.Z ≤ Z := by
    rintro _ ⟨c, rfl⟩
    exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  have hZA : Z ≤ A := Subgroup.closure_mono fun g hg => by
    rcases hg with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
  have hgenA_comm : ∀ x ∈ H₁.genA ∪ H₂.genA, ∀ y ∈ H₁.genA ∪ H₂.genA, x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact H₁.genA_comm x hx y hy
    · rcases hx with ⟨c₁, rfl⟩ | ⟨⟨s₁, d₁⟩, rfl⟩ <;>
        rcases hy with ⟨c₂, rfl⟩ | ⟨⟨s₂, d₂⟩, rfl⟩
      · exact hzz c₁ c₂
      · exact hz₁a₂ c₁ s₂ d₂
      · exact (hz₂a₁ c₂ s₁ d₁).symm
      · exact ha₁a₂ s₁ s₂ d₁ d₂
    · rcases hx with ⟨c₂, rfl⟩ | ⟨⟨s₂, d₂⟩, rfl⟩ <;>
        rcases hy with ⟨c₁, rfl⟩ | ⟨⟨s₁, d₁⟩, rfl⟩
      · exact (hzz c₁ c₂).symm
      · exact hz₂a₁ c₂ s₁ d₁
      · exact (hz₁a₂ c₁ s₂ d₂).symm
      · exact (ha₁a₂ s₁ s₂ d₁ d₂).symm
    · exact H₂.genA_comm x hx y hy
  have hA : IsMulCommutative A :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hgenA_comm x hx y hy
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨a, ha⟩ ⟨b, hb⟩)
  have hz₁Z : H₁.z 1 ∈ Z := hZ₁le (H₁.z_mem_Z 1)
  have hz₂Z : H₂.z 1 ∈ Z := hZ₂le (H₂.z_mem_Z 1)
  have hAC : A ≤ C := fun a ha => (hmemC a).2
    ⟨hAcomm a ha (H₁.z 1) (hZA hz₁Z), hAcomm a ha (H₂.z 1) (hZA hz₂Z)⟩
  have hy₁_comm_A₂ : ∀ (c₁ : I₁ → K) {a : Γ}, a ∈ H₂.A → H₁.yElt c₁ * a = a * H₁.yElt c₁ := by
    intro c₁ a ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨c₂, rfl⟩ | ⟨⟨s₂, d₂⟩, rfl⟩
      · exact (Finset.noncommProd_commute (Finset.univ : Finset I₁)
          (fun s₁ => H₁.xb s₁ (c₁ s₁)) (fun _ _ _ _ _ => H₁.xb_comm _ _ _ _)
          (H₂.z c₂) (fun s₁ _ => hz₂b₁ c₂ s₁ (c₁ s₁))).symm
      · exact (Finset.noncommProd_commute (Finset.univ : Finset I₁)
          (fun s₁ => H₁.xb s₁ (c₁ s₁)) (fun _ _ _ _ _ => H₁.xb_comm _ _ _ _)
          (H₂.xa s₂ d₂) (fun s₁ _ => (hb₁a₂ s₁ s₂ (c₁ s₁) d₂).symm)).symm
    | one => simp
    | mul x y _ _ ih₁ ih₂ => rw [← mul_assoc, ih₁, mul_assoc, ih₂, ← mul_assoc]
    | inv x _ ih => exact (Commute.inv_right ih).eq
  have hy₂_comm_A₁ : ∀ (c₂ : I₂ → K) {a : Γ}, a ∈ H₁.A → H₂.yElt c₂ * a = a * H₂.yElt c₂ := by
    intro c₂ a ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨c₁, rfl⟩ | ⟨⟨s₁, d₁⟩, rfl⟩
      · exact (Finset.noncommProd_commute (Finset.univ : Finset I₂)
          (fun s₂ => H₂.xb s₂ (c₂ s₂)) (fun _ _ _ _ _ => H₂.xb_comm _ _ _ _)
          (H₁.z c₁) (fun s₂ _ => hz₁b₂ c₁ s₂ (c₂ s₂))).symm
      · exact (Finset.noncommProd_commute (Finset.univ : Finset I₂)
          (fun s₂ => H₂.xb s₂ (c₂ s₂)) (fun _ _ _ _ _ => H₂.xb_comm _ _ _ _)
          (H₁.xa s₁ d₁) (fun s₂ _ => (hb₂a₁ s₂ s₁ (c₂ s₂) d₁).symm)).symm
    | one => simp
    | mul x y _ _ ih₁ ih₂ => rw [← mul_assoc, ih₁, mul_assoc, ih₂, ← mul_assoc]
    | inv x _ ih => exact (Commute.inv_right ih).eq
  let y : (I₁ → K) × (I₂ → K) → Γ := fun c => H₁.yElt c.1 * H₂.yElt c.2
  have hyC : ∀ c, y c ∈ C := fun c => (hmemC (y c)).2
    ⟨by
      have h1 := H₁.yElt_comm_z c.1 1
      have h2 := hy₂_comm_A₁ c.2 (H₁.z_mem_A 1)
      calc H₁.yElt c.1 * H₂.yElt c.2 * H₁.z 1 = H₁.yElt c.1 * (H₂.yElt c.2 * H₁.z 1) := by group
        _ = H₁.yElt c.1 * (H₁.z 1 * H₂.yElt c.2) := by rw [h2]
        _ = (H₁.yElt c.1 * H₁.z 1) * H₂.yElt c.2 := by group
        _ = H₁.z 1 * (H₁.yElt c.1 * H₂.yElt c.2) := by rw [h1]; group,
     by
      have h1 := hy₁_comm_A₂ c.1 (H₂.z_mem_A 1)
      have h2 := H₂.yElt_comm_z c.2 1
      calc H₁.yElt c.1 * H₂.yElt c.2 * H₂.z 1 = H₁.yElt c.1 * (H₂.yElt c.2 * H₂.z 1) := by group
        _ = H₁.yElt c.1 * (H₂.z 1 * H₂.yElt c.2) := by rw [h2]
        _ = (H₁.yElt c.1 * H₂.z 1) * H₂.yElt c.2 := by group
        _ = H₂.z 1 * (H₁.yElt c.1 * H₂.yElt c.2) := by rw [h1]; group⟩
  have hcomm_A₁ : ∀ (c : (I₁ → K) × (I₂ → K)) {a : Γ}, a ∈ H₁.A →
      ⁅(y c)⁻¹, a⁆ = ⁅(H₁.yElt c.1)⁻¹, a⁆ := by
    intro c a ha
    have h1 : ⁅(H₁.yElt c.1)⁻¹, a⁆ ∈ H₁.A := H₁.Z_le_A (H₁.comm_yElt_mem_Z c.1 a ha)
    have h2 : H₂.yElt c.2 * ((H₁.yElt c.1)⁻¹ * a * H₁.yElt c.1) =
        ((H₁.yElt c.1)⁻¹ * a * H₁.yElt c.1) * H₂.yElt c.2 := by
      have : (H₁.yElt c.1)⁻¹ * a * H₁.yElt c.1 = ⁅(H₁.yElt c.1)⁻¹, a⁆ * a := by
        simp [commutatorElement_def]
      rw [this]
      exact hy₂_comm_A₁ c.2 (mul_mem h1 ha)
    simp only [y, commutatorElement_def, inv_inv]
    calc (H₁.yElt c.1 * H₂.yElt c.2)⁻¹ * a * (H₁.yElt c.1 * H₂.yElt c.2) * a⁻¹
        = (H₂.yElt c.2)⁻¹ * (((H₁.yElt c.1)⁻¹ * a * H₁.yElt c.1) * H₂.yElt c.2) * a⁻¹ := by
          group
      _ = (H₂.yElt c.2)⁻¹ * (H₂.yElt c.2 * ((H₁.yElt c.1)⁻¹ * a * H₁.yElt c.1)) * a⁻¹ := by
          rw [h2]
      _ = (H₁.yElt c.1)⁻¹ * a * H₁.yElt c.1 * a⁻¹ := by group
  have hcomm_A₂ : ∀ (c : (I₁ → K) × (I₂ → K)) {a : Γ}, a ∈ H₂.A →
      ⁅(y c)⁻¹, a⁆ = ⁅(H₂.yElt c.2)⁻¹, a⁆ := by
    intro c a ha
    have h1 := hy₁_comm_A₂ c.1 ha
    simp only [y, commutatorElement_def, inv_inv]
    calc (H₁.yElt c.1 * H₂.yElt c.2)⁻¹ * a * (H₁.yElt c.1 * H₂.yElt c.2) * a⁻¹
        = (H₂.yElt c.2)⁻¹ * (H₁.yElt c.1)⁻¹ * (a * H₁.yElt c.1) * H₂.yElt c.2 * a⁻¹ := by
          group
      _ = (H₂.yElt c.2)⁻¹ * (H₁.yElt c.1)⁻¹ * (H₁.yElt c.1 * a) * H₂.yElt c.2 * a⁻¹ := by
          rw [h1]
      _ = (H₂.yElt c.2)⁻¹ * a * H₂.yElt c.2 * a⁻¹ := by group
  have hcomm : ∀ c, ∀ a ∈ A, ⁅(y c)⁻¹, a⁆ ∈ Z := by
    intro c a ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · rw [hcomm_A₁ c (Subgroup.subset_closure hg)]
        exact hZ₁le (H₁.comm_yElt_mem_Z c.1 g (Subgroup.subset_closure hg))
      · rw [hcomm_A₂ c (Subgroup.subset_closure hg)]
        exact hZ₂le (H₂.comm_yElt_mem_Z c.2 g (Subgroup.subset_closure hg))
    | one => rw [commutatorElement_one_right]; exact one_mem _
    | mul x x' hx hx' ih₁ ih₂ =>
      have h1 : ⁅(y c)⁻¹, x * x'⁆ = ⁅(y c)⁻¹, x⁆ * (x * ⁅(y c)⁻¹, x'⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      have h2 : x * ⁅(y c)⁻¹, x'⁆ * x⁻¹ = ⁅(y c)⁻¹, x'⁆ := by
        have := hAcomm x hx _ (hZA ih₂)
        rw [this]; group
      rw [h1, h2]
      exact mul_mem ih₁ ih₂
    | inv x hx ih =>
      have h1 : ⁅(y c)⁻¹, x⁻¹⁆ = x⁻¹ * (⁅(y c)⁻¹, x⁆)⁻¹ * x := by
        simp only [commutatorElement_def]; group
      have h2 : x⁻¹ * (⁅(y c)⁻¹, x⁆)⁻¹ * x = (⁅(y c)⁻¹, x⁆)⁻¹ := by
        have := hAcomm x⁻¹ (inv_mem hx) _ (hZA (inv_mem ih))
        rw [this]; group
      rw [h1, h2]
      exact inv_mem ih
  let A' : Subgroup C := A.subgroupOf C
  let Z' : Subgroup C := Z.subgroupOf C
  let y' : (I₁ → K) × (I₂ → K) → C := fun c => ⟨y c, hyC c⟩
  have hcoe : ∀ g h : C, ((⁅g, h⁆ : C) : Γ) = ⁅(g : Γ), (h : Γ)⁆ := fun g h => by
    simp [commutatorElement_def]
  have : Finite A := Subtype.finite
  have : Finite A' := Finite.of_equiv A (Subgroup.subgroupOfEquivOfLe hAC).symm.toEquiv
  have hA' : IsMulCommutative A' := isMulCommutative_iff.2 fun a b =>
    Subtype.ext <| Subtype.ext <|
      hAcomm _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
  have hinv : (Nat.card A' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hZA' : Z' ≤ A' := fun g hg =>
    Subgroup.mem_subgroupOf.2 (hZA (Subgroup.mem_subgroupOf.1 hg))
  have hcomm' : ∀ c, ∀ a ∈ A', ⁅(y' c)⁻¹, a⁆ ∈ Z' := fun c a ha => by
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact hcomm c a (Subgroup.mem_subgroupOf.1 ha)
  let z₁' : C := ⟨H₁.z 1, hAC (hZA hz₁Z)⟩
  let z₂' : C := ⟨H₂.z 1, hAC (hZA hz₂Z)⟩
  have hz₁'Z : z₁' ∈ Z' := Subgroup.mem_subgroupOf.2 hz₁Z
  have hz₂'Z : z₂' ∈ Z' := Subgroup.mem_subgroupOf.2 hz₂Z
  have hρz₁ : ∀ w : W, ρ z₁' w = -w := fun w => by
    refine Subtype.ext (funext fun x => ?_)
    rw [hρ_apply, Submodule.coe_neg, Pi.neg_apply]
    change (w : Λ → ℂ) (σ₁⁻¹ x) = - (w : Λ → ℂ) x
    rw [inv_eq_of_mul_eq_one_right hσ₁]
    exact mem_antiInv.1 w.2.1 x
  have hρz₂ : ∀ w : W, ρ z₂' w = -w := fun w => by
    refine Subtype.ext (funext fun x => ?_)
    rw [hρ_apply, Submodule.coe_neg, Pi.neg_apply]
    change (w : Λ → ℂ) (σ₂⁻¹ x) = - (w : Λ → ℂ) x
    rw [inv_eq_of_mul_eq_one_right hσ₂]
    exact mem_antiInv.1 w.2.2 x
  have hnt' : ∃ z ∈ Z', ρ z ≠ 1 := by
    refine ⟨z₁', hz₁'Z, fun h1 => ?_⟩
    have h2 : ρ z₁' ⟨f₀, hf₀W⟩ = ⟨f₀, hf₀W⟩ := by rw [h1]; rfl
    rw [hρz₁] at h2
    have h3 : -f₀ = f₀ := congrArg Subtype.val h2
    exact hf₀0 (self_eq_neg.1 h3.symm)
  have hfinrank := card_le_finrank_of_translations ρ A' Z' hA' hinv hZA' y' hcomm' hnt'
    (fun ξ hmul hne _ hreal c c' hcc' => by
      obtain ⟨w, hw0, hw⟩ := hreal
      have hξ₁ : ξ z₁' ≠ 1 := by
        have h1 := hw z₁' hz₁'Z
        rw [hρz₁, ← neg_one_smul ℂ w] at h1
        have h2 : ξ z₁' = -1 := (smul_left_injective ℂ hw0 h1).symm
        rw [h2]
        norm_num
      have hξ₂ : ξ z₂' ≠ 1 := by
        have h1 := hw z₂' hz₂'Z
        rw [hρz₂, ← neg_one_smul ℂ w] at h1
        have h2 : ξ z₂' = -1 := (smul_left_injective ℂ hw0 h1).symm
        rw [h2]
        norm_num
      let ξΓ : Γ → ℂ := fun g => if h : g ∈ C then ξ ⟨g, h⟩ else 1
      have hξΓ : ∀ g : C, ξΓ (g : Γ) = ξ g := fun g => dite_eq_left g.2
      by_cases hc1 : c.1 ≠ c'.1
      · have hmul₁ : ∀ u ∈ H₁.Z, ∀ v ∈ H₁.Z, ξΓ (u * v) = ξΓ u * ξΓ v := by
          intro u hu v hv
          have huZ : u ∈ Z := hZ₁le hu
          have hvZ : v ∈ Z := hZ₁le hv
          have := hmul ⟨u, hAC (hZA huZ)⟩ (Subgroup.mem_subgroupOf.2 huZ)
            ⟨v, hAC (hZA hvZ)⟩ (Subgroup.mem_subgroupOf.2 hvZ)
          simpa [ξΓ, hAC (hZA huZ), hAC (hZA hvZ), hAC (hZA (mul_mem huZ hvZ))] using this
        have hne₁ : ∀ u ∈ H₁.Z, ξΓ u ≠ 0 := by
          intro u hu
          have huZ : u ∈ Z := hZ₁le hu
          simpa [ξΓ, hAC (hZA huZ)] using hne ⟨u, hAC (hZA huZ)⟩ (Subgroup.mem_subgroupOf.2 huZ)
        have hnt₁ : ∃ u ∈ H₁.Z, ξΓ u ≠ 1 :=
          ⟨H₁.z 1, H₁.z_mem_Z 1, by rw [show H₁.z 1 = (z₁' : Γ) from rfl, hξΓ]; exact hξ₁⟩
        obtain ⟨a, ha₁, hdist₁⟩ := H₁.exists_dist ξΓ hmul₁ hne₁ hnt₁ c.1 c'.1 hc1
        have haA : a ∈ A := hA₁le ha₁
        refine ⟨⟨a, hAC haA⟩, Subgroup.mem_subgroupOf.2 haA, ?_⟩
        have e1 : ξ ⁅(y' c)⁻¹, ⟨a, hAC haA⟩⁆ = ξΓ ⁅(H₁.yElt c.1)⁻¹, a⁆ := by
          rw [← hξΓ]; exact congrArg ξΓ (hcomm_A₁ c ha₁)
        have e2 : ξ ⁅(y' c')⁻¹, ⟨a, hAC haA⟩⁆ = ξΓ ⁅(H₁.yElt c'.1)⁻¹, a⁆ := by
          rw [← hξΓ]; exact congrArg ξΓ (hcomm_A₁ c' ha₁)
        rw [e1, e2]
        exact hdist₁
      · have hc2 : c.2 ≠ c'.2 := fun h => hcc' (Prod.ext (not_not.1 hc1) h)
        have hmul₂ : ∀ u ∈ H₂.Z, ∀ v ∈ H₂.Z, ξΓ (u * v) = ξΓ u * ξΓ v := by
          intro u hu v hv
          have huZ : u ∈ Z := hZ₂le hu
          have hvZ : v ∈ Z := hZ₂le hv
          have := hmul ⟨u, hAC (hZA huZ)⟩ (Subgroup.mem_subgroupOf.2 huZ)
            ⟨v, hAC (hZA hvZ)⟩ (Subgroup.mem_subgroupOf.2 hvZ)
          simpa [ξΓ, hAC (hZA huZ), hAC (hZA hvZ), hAC (hZA (mul_mem huZ hvZ))] using this
        have hne₂ : ∀ u ∈ H₂.Z, ξΓ u ≠ 0 := by
          intro u hu
          have huZ : u ∈ Z := hZ₂le hu
          simpa [ξΓ, hAC (hZA huZ)] using hne ⟨u, hAC (hZA huZ)⟩ (Subgroup.mem_subgroupOf.2 huZ)
        have hnt₂ : ∃ u ∈ H₂.Z, ξΓ u ≠ 1 :=
          ⟨H₂.z 1, H₂.z_mem_Z 1, by rw [show H₂.z 1 = (z₂' : Γ) from rfl, hξΓ]; exact hξ₂⟩
        obtain ⟨a, ha₂, hdist₂⟩ := H₂.exists_dist ξΓ hmul₂ hne₂ hnt₂ c.2 c'.2 hc2
        have haA : a ∈ A := hA₂le ha₂
        refine ⟨⟨a, hAC haA⟩, Subgroup.mem_subgroupOf.2 haA, ?_⟩
        have e1 : ξ ⁅(y' c)⁻¹, ⟨a, hAC haA⟩⁆ = ξΓ ⁅(H₂.yElt c.2)⁻¹, a⁆ := by
          rw [← hξΓ]; exact congrArg ξΓ (hcomm_A₂ c ha₂)
        have e2 : ξ ⁅(y' c')⁻¹, ⟨a, hAC haA⟩⁆ = ξΓ ⁅(H₂.yElt c'.2)⁻¹, a⁆ := by
          rw [← hξΓ]; exact congrArg ξΓ (hcomm_A₂ c' ha₂)
        rw [e1, e2]
        exact hdist₂)
  rw [Nat.card_prod] at hfinrank
  have hle_anti : Module.finrank ℂ W ≤ Module.finrank ℂ (antiInv σ₁) :=
    Submodule.finrank_mono inf_le_left
  have htwo := two_mul_finrank_antiInv_le σ₁ hσ₁
  omega

/-- If `Γ` is a finite simple group, `H₁ : HeisSystem Γ K I₁` and `H₂ : HeisSystem Γ K I₂` are two
compatible Heisenberg systems over a finite field `K` of characteristic `2`, and there exist
`z₃ g w : Γ` such that `H₂.z 1` commutes with `z₃` and `g`,
`g⁻¹ * H₁.z 1 * g = H₁.z 1 * H₂.z 1 * z₃`, `w * H₁.z 1 * w⁻¹ = z₃`, and
`w * H₂.z 1 * w⁻¹ = H₂.z 1`, then every proper subgroup `M < Γ` has index at least
`2 * (Nat.card (I₁ → K) * Nat.card (I₂ → K))`. -/
theorem HeisSystem.two_mul_card_mul_card_le_index_of_isSimpleGroup
    {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (H₁ : HeisSystem Γ K I₁) (H₂ : HeisSystem Γ K I₂)
    (hzz : ∀ c₁ c₂, H₁.z c₁ * H₂.z c₂ = H₂.z c₂ * H₁.z c₁)
    (hz₁a₂ : ∀ c₁ s₂ d₂, H₁.z c₁ * H₂.xa s₂ d₂ = H₂.xa s₂ d₂ * H₁.z c₁)
    (hz₁b₂ : ∀ c₁ s₂ d₂, H₁.z c₁ * H₂.xb s₂ d₂ = H₂.xb s₂ d₂ * H₁.z c₁)
    (hz₂a₁ : ∀ c₂ s₁ d₁, H₂.z c₂ * H₁.xa s₁ d₁ = H₁.xa s₁ d₁ * H₂.z c₂)
    (hz₂b₁ : ∀ c₂ s₁ d₁, H₂.z c₂ * H₁.xb s₁ d₁ = H₁.xb s₁ d₁ * H₂.z c₂)
    (ha₁a₂ : ∀ s₁ s₂ d₁ d₂, H₁.xa s₁ d₁ * H₂.xa s₂ d₂ = H₂.xa s₂ d₂ * H₁.xa s₁ d₁)
    (hb₁a₂ : ∀ s₁ s₂ c₁ d₂, H₁.xb s₁ c₁ * H₂.xa s₂ d₂ = H₂.xa s₂ d₂ * H₁.xb s₁ c₁)
    (hb₂a₁ : ∀ s₂ s₁ c₂ d₁, H₂.xb s₂ c₂ * H₁.xa s₁ d₁ = H₁.xa s₁ d₁ * H₂.xb s₂ c₂)
    {z₃ g w : Γ}
    (hg1 : g⁻¹ * H₁.z 1 * g = H₁.z 1 * H₂.z 1 * z₃)
    (hg2 : g * H₂.z 1 = H₂.z 1 * g)
    (hw1 : w * H₁.z 1 * w⁻¹ = z₃)
    (hw2 : w * H₂.z 1 * w⁻¹ = H₂.z 1)
    (M : Subgroup Γ) (hM : M ≠ ⊤) :
    2 * (Nat.card (I₁ → K) * Nat.card (I₂ → K)) ≤ M.index := by
  rw [Subgroup.index_eq_card]
  let π : Γ →* Equiv.Perm (Γ ⧸ M) := MulAction.toPermHom Γ (Γ ⧸ M)
  have hz₂1 : H₂.z 1 ≠ 1 := fun h => one_ne_zero (H₂.z_injective (h.trans H₂.z_zero.symm))
  have hmove := exists_moved_both_of_conj_mul (π (H₁.z 1)) (π (H₂.z 1)) (π z₃) (π g) (π w)
    (toPermHom_quotient_ne_one_of_ne_one hM hz₂1)
    (by rw [← map_mul, ← map_mul, hzz 1 1])
    (by rw [← map_inv, ← map_mul, ← map_mul, hg1, map_mul, map_mul])
    (by rw [← map_mul, ← map_mul, hg2])
    (by rw [← map_inv, ← map_mul, ← map_mul, hw1])
    (by rw [← map_inv, ← map_mul, ← map_mul, hw2])
  exact HeisSystem.two_mul_card_mul_card_le_card_of_perm π H₁ H₂
    hzz hz₁a₂ hz₁b₂ hz₂a₁ hz₂b₁ ha₁a₂ hb₁a₂ hb₂a₁ hmove

end Maroti
