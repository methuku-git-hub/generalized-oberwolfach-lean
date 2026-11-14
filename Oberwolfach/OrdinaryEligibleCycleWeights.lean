module

public import Oberwolfach.OrdinaryEligibleHost
public import Oberwolfach.PositiveOrdinaryCycleWeights
public import Oberwolfach.AlmostSpanningCyclePacking
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section
/-! Choose the cycle weights used by approximate matching on the eligible
subgraph, losing only a fixed degree from the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) eligibleCycleWeightFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_eligible_cycle_weights (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃c B:ℝ,0<c ∧ 0<B ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),
    (∀v,(cycleThreshold r+α)*n≤(P.degree v:ℝ))→
    ∃w:OrdinaryCycle (ordinaryEligibleHost P π d) r→ℝ,
      (∀C,c/(n:ℝ)^(r-2)≤w C ∧ w C≤B/(n:ℝ)^(r-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then w C else 0)=
        if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) :=by
  obtain ⟨c,B,hc,hB,N₀,hN₀,hweight⟩:=positive_ordinary_fractional_cycle_weights r hr (α/2) (by positivity)
  refine ⟨c,B,hc,hB,?_⟩
  intro d
  obtain ⟨N₁,hN₁⟩:=eventually_constant_le_linear ((6*d+4:ℕ):ℝ) (α/2) (by positivity)
  refine ⟨max N₀ N₁,?_⟩
  intro n hn P π hmin
  have hloss:=hN₁ n (by omega)
  have hmin':∀v,(cycleThreshold r+α/2)*(Fintype.card (Fin n):ℝ)≤
      ((ordinaryEligibleHost P π d).degree v:ℝ):=by
    intro v
    have hd:=ordinary_eligible_host_degree P π d v
    have hlo:((P.degree v:ℝ))≤((ordinaryEligibleHost P π d).degree v:ℝ)+((6*d+4:ℕ):ℝ):=by exact_mod_cast hd.2
    have hh:=hmin v
    simp only [Fintype.card_fin]
    nlinarith
  obtain ⟨w,hw,he⟩:=hweight (Fin n) (by simpa using (show N₀≤n by omega)) (ordinaryEligibleHost P π d) hmin'
  refine ⟨w,by simpa only [Fintype.card_fin] using hw,?_⟩
  exact ordinary_cycle_incidence_load_adjacency (ordinaryEligibleHost P π d) r w he
end Oberwolfach
