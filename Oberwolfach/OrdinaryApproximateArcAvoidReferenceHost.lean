module

public import Oberwolfach.OrdinaryApproximateRimsAvoidReference

@[expose] public section
/-! The approximate arc host may be a restricted subgraph while the
reference uses the original parent graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_approximate_arc_avoids_reference_host {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (Host P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (x y:Fin n):
    rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→
      (⊤\longPhysicalStateGraph P σ {0}).Adj x y:=by
  intro harc
  have hh:=ordinary_approximate_arc_avoids_reference Host Del π d σ x y harc
  have hHost:Host.Adj x y:=by
    rcases harc with h|h
    · exact ((markedPhysicalRim_eq_one_iff Host π (3*d) _ false x y).mp h).2.1
    · have h':=((markedPhysicalRim_eq_one_iff Host π (3*d) _ true x (π.symm y)).mp h).2.1
      simpa using h'
  refine ⟨hh.1,?_⟩
  intro hRef
  exact hh.2 ⟨hHost,hRef.2⟩
end Oberwolfach
