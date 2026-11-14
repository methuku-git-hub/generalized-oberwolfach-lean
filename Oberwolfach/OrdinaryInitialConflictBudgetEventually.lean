module

public import Oberwolfach.OrdinaryTrackedComplementFiniteErrors

@[expose] public section
/-! The first-level forbidden-edge contribution is a fixed constant and
fits into one further positive linear margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_conflict_budget_eventually
    (d:ℕ) (η:ℝ) (hη:0<η):
    ∃N:ℕ,∀n:ℕ,N≤n→∀cost:ℝ,cost≤14*η*n→
      cost+2*((3*d:ℕ):ℝ)≤15*η*n :=by
  have hC:0≤(2*((3*d:ℕ):ℝ)):=by positivity
  obtain ⟨N,hN⟩:=ordinary_tracked_complement_finite_errors (2*((3*d:ℕ):ℝ)) η hC hη
  refine ⟨N,?_⟩
  intro n hn cost hcost
  have hpow:0≤(n:ℝ)^(3/5:ℝ):=by positivity
  have hh:=hN n hn
  linarith
end Oberwolfach
