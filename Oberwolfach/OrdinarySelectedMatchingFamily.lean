module

public import Oberwolfach.OrdinarySelectedMatchingPackagesResult
public import Oberwolfach.OrdinarySelectedMatchingFamilyResult

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_selected_matching_packages_form_family
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv θ lam a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Del:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
    (h:OrdinarySelectedMatchingPackagesResult F hF Cres i₀ rsv θ lam a γ m d π P Del σ tret Jret):
    OrdinarySelectedMatchingFamilyResult F hF Cres i₀ rsv θ lam a γ m d π P Del σ tret Jret :=by
  unfold OrdinarySelectedMatchingPackagesResult at h
  unfold OrdinarySelectedMatchingFamilyResult
  obtain ⟨L,hL,hrows,hmass,hsource⟩:=h
  refine ⟨L,hL,hrows,hmass,?_⟩
  let p:=fun u=>Classical.choice (hsource u)
  refine ⟨p,?_⟩
  intro u v huv
  have hh:=ordinary_physical_pair_hub_rim_packs_named (K:=K) π d m
    (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))
    (rawMarkedPairSpokes π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) true true)
  unfold ordinaryPhysicalPairHubRimPacksShape at hh
  exact hh L hL u v huv (p u).marker (p v).marker (p u).hGood (p v).hGood
end Oberwolfach
