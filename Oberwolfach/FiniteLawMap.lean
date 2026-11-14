module

public import Oberwolfach.DisjointPatternSampling

@[expose] public section

/-! Exact pushforward laws for categorical projections and product samples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

namespace FiniteLaw

def map {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (μ : FiniteLaw Ω) (f : Ω → Γ) : FiniteLaw Γ where
  mass γ := ∑ ω, if f ω = γ then μ.mass ω else 0
  nonneg γ := Finset.sum_nonneg (fun ω _ => by split_ifs; exact μ.nonneg ω; exact le_refl _)
  total := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact μ.total

def categorical {k : ℕ} (ρ : Fin k → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1) : FiniteLaw (Fin k) where
  mass := ρ
  nonneg := hρ
  total := htotal

end FiniteLaw

theorem finiteLaw_ext
    {Ω : Type*} [Fintype Ω] {μ ν : FiniteLaw Ω} (h : ∀ ω, μ.mass ω = ν.mass ω) : μ = ν := by
  cases μ with
  | mk m hm ht =>
    cases ν with
    | mk n hn hs =>
      have heq : m = n := funext h
      subst n
      rfl

theorem finiteLaw_map_probability
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (μ : FiniteLaw Ω) (f : Ω → Γ) (A : Γ → Prop) :
    (μ.map f).probability A = μ.probability (fun ω => A (f ω)) := by
  unfold FiniteLaw.probability
  change (∑ γ, if A γ then (∑ ω, if f ω = γ then μ.mass ω else 0) else 0) = _
  have hh (γ : Γ) : (if A γ then (∑ ω, if f ω = γ then μ.mass ω else 0) else 0) =
      ∑ ω, if f ω = γ then (if A (f ω) then μ.mass ω else 0) else 0 := by
    by_cases ha : A γ
    · simp only [ha, ite_true]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hf : f ω = γ <;> simp [hf, ha]
    · simp only [ha, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro ω _
      by_cases hf : f ω = γ <;> simp [hf, ha]
  simp_rw [hh]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem finiteLaw_map_common_event
    {Ω Γ X Y : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (f : Ω → Γ) (E : Ω → Prop)
    (admissible : Γ → X → Prop) (conclusion : Γ → X → Y → Prop)
    (hE : ∀ ω, E ω → ∀ x, admissible (f ω) x → ∃ y, conclusion (f ω) x y) :
    μ.probability E ≤ (μ.map f).probability (fun γ => ∀ x, admissible γ x → ∃ y, conclusion γ x y) := by
  rw [finiteLaw_map_probability]
  exact finiteLaw_probability_mono μ _ _ hE

theorem finiteLaw_pi_map
    {E : Type*} [Fintype E] [DecidableEq E]
    {State Out : E → Type*} [∀ e, Fintype (State e)] [∀ e, Fintype (Out e)]
    (μ : ∀ e, FiniteLaw (State e)) (f : ∀ e, State e → Out e) :
    (FiniteLaw.pi μ).map (fun σ e => f e (σ e)) =
      FiniteLaw.pi (fun e => (μ e).map (f e)) := by
  apply finiteLaw_ext
  intro τ
  dsimp only [FiniteLaw.map, FiniteLaw.pi]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : (fun e => f e (σ e)) = τ
  · have he (e : E) : f e (σ e) = τ e := congrFun h e
    simp [he]
  · have he : ∃ e, f e (σ e) ≠ τ e := by
      by_contra hn
      apply h
      funext e
      by_contra hf
      exact hn ⟨e, hf⟩
    obtain ⟨e, he⟩ := he
    rw [ite_eq_right h]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

theorem categoricalDirection_map_colour
    {k : ℕ} (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1) :
    (FiniteLaw.categoricalDirection ρ hρ htotal).map Prod.fst =
      FiniteLaw.categorical ρ hρ htotal := by
  apply finiteLaw_ext
  intro a
  dsimp only [FiniteLaw.map, FiniteLaw.categoricalDirection, FiniteLaw.categorical]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring


theorem categoricalDirection_map_direction
    {k : ℕ} (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1) :
    (FiniteLaw.categoricalDirection ρ hρ htotal).map Prod.snd = FiniteLaw.fairCoin := by
  apply finiteLaw_ext
  intro b
  dsimp only [FiniteLaw.map, FiniteLaw.categoricalDirection, FiniteLaw.fairCoin]
  rw [Fintype.sum_prod_type]
  cases b <;> simp [← Finset.sum_div, htotal]

theorem categoricalDirection_colour_probability
    {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (A : (E → Fin k) → Prop) :
    (FiniteLaw.pi (fun _ : E => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => A (fun e => (σ e).1)) =
      (FiniteLaw.pi (fun _ : E => FiniteLaw.categorical ρ hρ htotal)).probability A := by
  rw [← finiteLaw_map_probability]
  rw [finiteLaw_pi_map]
  simp_rw [categoricalDirection_map_colour]

theorem categoricalDirection_direction_probability
    {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (A : (E → Bool) → Prop) :
    (FiniteLaw.pi (fun _ : E => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => A (fun e => (σ e).2)) =
      (FiniteLaw.pi (fun _ : E => FiniteLaw.fairCoin)).probability A := by
  rw [← finiteLaw_map_probability]
  rw [finiteLaw_pi_map]
  simp_rw [categoricalDirection_map_direction]

theorem categoricalDirection_common_event_projection
    {E X Y : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (B : (E → Fin k × Bool) → Prop)
    (admissible : (E → Fin k) → X → Prop)
    (conclusion : (E → Fin k) → X → Y → Prop)
    (hB : ∀ σ, B σ → ∀ x, admissible (fun e => (σ e).1) x →
      ∃ y, conclusion (fun e => (σ e).1) x y) :
    (FiniteLaw.pi (fun _ : E => FiniteLaw.categoricalDirection ρ hρ htotal)).probability B ≤
      (FiniteLaw.pi (fun _ : E => FiniteLaw.categorical ρ hρ htotal)).probability
        (fun c => ∀ x, admissible c x → ∃ y, conclusion c x y) := by
  have hh := finiteLaw_map_common_event
    (FiniteLaw.pi (fun _ : E => FiniteLaw.categoricalDirection ρ hρ htotal))
    (fun σ e => (σ e).1) B admissible conclusion hB
  rw [finiteLaw_pi_map] at hh
  simp_rw [categoricalDirection_map_colour] at hh
  exact hh

end Oberwolfach
