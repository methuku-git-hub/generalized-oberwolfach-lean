module

public import Oberwolfach.FiniteLawMap

@[expose] public section

/-! Restricting the independent sample to the actual physical edges.
Unused coordinates can be removed without changing the induced law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_restrict
    {E : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) (A : Finset E) :
    (FiniteLaw.pi μ).map (fun σ (e : A) => σ e) =
      FiniteLaw.pi (fun e : A => μ e) := by
  apply finiteLaw_ext
  intro τ
  let s (e : E) : State e := if he : e ∈ A then τ ⟨e, he⟩ else Classical.choice (finiteLaw_nonempty (μ e))
  have heq (σ : ∀ e, State e) : (fun e : A => σ e) = τ ↔ ∀ e ∈ A, σ e = s e := by
    constructor
    · intro h e he
      simpa only [s, dite_eq_left he] using congrFun h ⟨e, he⟩
    · intro h
      funext e
      simpa only [s, dite_eq_left e.2] using h e e.2
  have hp (σ : ∀ e, State e) : patternValue A s σ =
      if (fun e : A => σ e) = τ then 1 else 0 := by
    by_cases h : (fun e : A => σ e) = τ
    · have hh := heq σ |>.mp h
      simp only [h, ite_true]
      unfold patternValue
      exact Finset.prod_eq_one (fun e he => by simp [hh e he])
    · have hh : ∃ e ∈ A, σ e ≠ s e := by
        by_contra hn
        apply h
        exact (heq σ).mpr (by simpa using hn)
      obtain ⟨e, he, hne⟩ := hh
      simp only [h, ite_false]
      unfold patternValue
      exact Finset.prod_eq_zero he (by simp [hne])
  have hm : ((FiniteLaw.pi μ).map (fun σ (e : A) => σ e)).mass τ =
      (FiniteLaw.pi μ).expectation (patternValue A s) := by
    dsimp only [FiniteLaw.map, FiniteLaw.expectation]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hp]
    split_ifs <;> simp
  rw [hm, finiteLaw_expectation_pattern]
  dsimp only [FiniteLaw.pi]
  rw [Finset.prod_subtype A (fun _ => Iff.rfl)]
  apply Finset.prod_congr rfl
  intro e _
  simp [s, e.2]

end Oberwolfach
