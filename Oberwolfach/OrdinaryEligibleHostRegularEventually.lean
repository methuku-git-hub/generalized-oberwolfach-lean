module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget
public import Oberwolfach.OrdinaryEligibleHost

@[expose] public section
/-! The eligible host differs from the original regular host at only a fixed
number of neighbours per vertex, hence has the required linear error. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_eligible_host_regular_eventually (d:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(P:SimpleGraph (Fin n)) (D:ℕ),P.IsRegularOfDegree D→
      ∀(π:Equiv.Perm (Fin n)) x,|((ordinaryEligibleHost P π d).degree x:ℝ)-D|≤ε*n :=by
  obtain ⟨N,hN⟩:=ordinary_constant_eventually_below_linear_rate ε ((6*d+4:ℕ):ℝ) hε
  refine ⟨N,?_⟩
  intro n hn P D hreg π x
  have hd:=ordinary_eligible_host_degree P π d x
  have hhi:((ordinaryEligibleHost P π d).degree x:ℝ)≤D:=by
    have h:=hd.1
    rw [hreg x] at h
    exact_mod_cast h
  have hlo:(D:ℝ)≤((ordinaryEligibleHost P π d).degree x:ℝ)+((6*d+4:ℕ):ℝ):=by
    have h:=hd.2
    rw [hreg x] at h
    exact_mod_cast h
  rw [abs_le]
  constructor <;> linarith [hN n hn]
end Oberwolfach
