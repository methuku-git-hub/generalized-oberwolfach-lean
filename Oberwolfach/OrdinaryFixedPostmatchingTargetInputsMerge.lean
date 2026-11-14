module

public import Oberwolfach.OrdinaryFixedPostmatchingInputs
public import Oberwolfach.OrdinaryFixedPostmatchingTargetInputs

@[expose] public section

/-! The list and absorber conditions depend only on the sample and target;
they combine with the refined demand for its own coherent matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_postmatching_target_inputs_merge
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv θ lam a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Target:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U)))
    (lamList bRate z:ℝ)
    (hbase:OrdinaryFixedPostmatchingInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=longPhysicalStateGraph P σ {0}\Bad
    let Protect:=ordinaryMatchingProtect Reference Inner Kabs
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    OrdinarySelectedPostDemandTargetResult F hF Cres i₀ rsv θ lam a γ m d π P (Sample\Target)
      Target Protect Bad Inner Hubs bRate z σ 0 J→
    OrdinaryFixedPostmatchingTargetInputs F hF Cres i₀ rsv θ lam a γ m d π P Target σ Inner Hubs Kabs lamList bRate z :=by
  intro Sample Bad Reference Protect J htarget
  unfold OrdinaryFixedPostmatchingInputs at hbase
  unfold OrdinaryFixedPostmatchingTargetInputs
  obtain ⟨h1,h2,h3,h4,h5,h6,_⟩:=hbase
  exact ⟨h1,h2,h3,h4,h5,h6,htarget⟩
end Oberwolfach
