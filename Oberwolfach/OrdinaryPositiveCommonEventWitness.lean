module

public import Oberwolfach.OrdinaryReservoirErrorEventuallySmall
public import Oberwolfach.FiniteLawPositiveLowerBoundWitness

@[expose] public section
/-! The explicit reservoir error allows the same common event to be
realized by a positive-mass sample for all sufficiently large hosts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_positive_common_event_witness
    (lossE χ:ℝ) (hmargin:lossE+χ<1):
    ∃N:ℕ,1 ≤ N ∧ ∀n:ℕ,N ≤ n  → 
    ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Good:Ω → Prop),
      1-lossE-2/(n:ℝ)-(1/(n:ℝ)+2/(n:ℝ)^2)-χ ≤ μ.probability Good  → 
      ∃z,0<μ.mass z ∧ Good z :=by
  obtain ⟨N,hN,hpositive⟩:=ordinary_reservoir_error_eventually_small lossE χ hmargin
  refine ⟨N,hN,?_⟩
  intro n hn Ω _ μ Good hprob
  exact finiteLaw_positive_lower_bound_witness μ Good _ (hpositive n hn) hprob
end Oberwolfach
