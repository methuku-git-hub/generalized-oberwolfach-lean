module

public import Oberwolfach.OrdinaryTrackedComplementFromPostmatchingStateZeroShape
public import Oberwolfach.OrdinaryTrackedComplementFromPostmatching
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! Express the tracked remainder interface using the same state-zero
reference graph as the two-deletion placement construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_from_postmatching_state_zero {n q K:ℕ}
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (i₀:Fin K) (r m d:ℕ)
    (rsv θ lamMatch a γ δ:ℝ) (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))):
    OrdinaryTrackedComplementFromPostmatchingStateZeroShape Fs hFs C i₀ r m d rsv θ lamMatch a γ δ P S π σ Inner Hubs Kabs :=by
  have hh:=ordinary_tracked_complement_from_postmatching Fs hFs C i₀ r m d rsv θ lamMatch a γ δ P S π σ Inner Hubs Kabs
  unfold OrdinaryTrackedComplementFromPostmatchingShape at hh
  unfold OrdinaryTrackedComplementFromPostmatchingStateZeroShape
  rw [ordinary_shared_sample_reference_graph_eq_state_zero P σ] at hh
  exact hh
end Oberwolfach
