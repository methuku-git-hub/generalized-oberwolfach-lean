module

public import Oberwolfach.OrdinarySelectedPostDemandLocalTarget
public import Oberwolfach.OrdinaryExactAssignedHubSlackUpper

@[expose] public section

/-! The local target estimate uses the mean supplied by the original
assigned sampling recipe, for the same postmatching demand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_post_demand_local_targets_eventually
    (ε cBudget θ z a γ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (hz:0<z)
    (hε:ε≤cBudget/16) (hzfloor:cBudget*θ≤z) (ha:a≤z/16) (hγ:γ≤z/16):
    ∃N:ℕ,∀{n K D:ℕ},N≤n→0<n→0<K→0<D→∀{U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv lam:ℝ)
    (m d:ℕ),7≤m → 2≤d → 0 ≤ rsv → rsv≤1/100 → 1/θ≤d →
    0 < initialIndexDensity U D→initialIndexDensity U D≤1→
    ∀(S:Set ℕ),(∀u,AllowedCycleLengths (F u) S)→OrdinaryClassReserveBound F hF i₀ rsv→
    ∀(π:Equiv.Perm (Fin n)) (P Del Target Protect Bad:SimpleGraph (Fin n))
    (Inner:Finset (Fin n)) (Hubs:Finset U) (bRate:ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret),
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1);
    (Inner.card:ℝ)≤ε*n→OrdinaryZeroRetentionEvent π d false σ→
    (∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))→
    OrdinarySelectedPostDemandOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner bRate σ tret Jret→
    OrdinarySelectedPostDemandTargetResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner Hubs bRate z σ tret Jret :=by
  obtain ⟨N,hbase⟩:=ordinary_selected_post_demand_local_target_eventually ε cBudget θ z a γ hθ.le hz hε hzfloor ha hγ
  refine ⟨N,?_⟩
  intro n K D hn hn0 hK hD U _ _ F hF Cres i₀ rsv lam m d hm hd hs0 hs1 hda hρ hρ1 S hS hClass
    π P Del Target Protect Bad Inner Hubs bRate σ tret Jret q s hInner hzero hlocal hpost
  have hc:8≤(m:ℝ)+1:=by exact_mod_cast (show 8≤m+1 by omega)
  have hslack:=ordinary_exact_assigned_hub_slack_upper hn0 hD F hF K hK i₀ rsv θ ((m:ℝ)+1) d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 S hS hClass
  exact hbase hn F hF Cres i₀ rsv lam m d π P Del Target Protect Bad Inner Hubs bRate σ tret Jret q s
    hInner hzero hslack hlocal hpost
end Oberwolfach
