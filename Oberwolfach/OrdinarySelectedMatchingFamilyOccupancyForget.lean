module

public import Oberwolfach.OrdinarySelectedMatchingFamilyLocalOccupancy
public import Oberwolfach.OrdinarySelectedMatchingFamilyLocalResult

@[expose] public section

/-! The strengthened coherent family is accepted by the existing
postmatching demand and edited-target construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_selected_matching_family_occupancy_forget
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv θ lam a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Del:SimpleGraph (Fin n)) (Inner:Finset (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
    (h:OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lam a γ m d π P Del Inner σ tret Jret):
    OrdinarySelectedMatchingFamilyLocalResult F hF Cres i₀ rsv θ lam a γ m d π P Del Inner σ tret Jret :=by
  unfold OrdinarySelectedMatchingFamilyLocalOccupancyResult at h
  unfold OrdinarySelectedMatchingFamilyLocalResult
  obtain ⟨L,hL,hrows,hlocal,hmass,p,hocc,hdis⟩:=h
  exact ⟨L,hL,hrows,hlocal,hmass,p,hdis⟩
end Oberwolfach
