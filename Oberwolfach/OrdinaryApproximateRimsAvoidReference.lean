module

public import Oberwolfach.RawMixedPhysicalArcHost
public import Oberwolfach.RawMarkedRimDeletion
public import Oberwolfach.MarkedExpandedApproximateProjection
public import Oberwolfach.LongPreparationPhysicalStates

@[expose] public section
/-! Every directed approximate rim avoids the selected reference colour,
even after deleting arbitrary physical edges from the approximate layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_approximate_arc_avoids_reference {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (x y:Fin n):
    rawMixedPhysicalArc P π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→
      (⊤\longPhysicalStateGraph P σ {0}).Adj x y:=by
  intro harc
  have hp:P.Adj x y:=by
    rcases harc with h|h
    · exact ((markedPhysicalRim_eq_one_iff P π (3*d) _ false x y).mp h).2.1
    · have hh:=((markedPhysicalRim_eq_one_iff P π (3*d) _ true x (π.symm y)).mp h).2.1
      simpa using hh
  refine ⟨hp.ne,?_⟩
  intro hRef
  have hz:(σ (Sum.inl s(x,y))).1=0:=by simpa using hRef.2
  have hnone:rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset (Sum.inl s(x,y))=none:=by
    simp [rawMarkedDeleteRims,rawExpandedApproximateCollapse,markedExpandedApproximateCollapse,hz]
  rcases harc with h|h
  · have hh:=((markedPhysicalRim_eq_one_iff P π (3*d) _ false x y).mp h).2.2
    change rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset (Sum.inl s(x,y))=some (false,orientationBit x y) at hh
    rw [hnone] at hh
    cases hh
  · have hh:=((markedPhysicalRim_eq_one_iff P π (3*d) _ true x (π.symm y)).mp h).2.2
    change rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset (Sum.inl s(x,π (π.symm y)))=some (true,orientationBit x (π (π.symm y))) at hh
    rw [Equiv.apply_symm_apply] at hh
    rw [hnone] at hh
    cases hh
end Oberwolfach
