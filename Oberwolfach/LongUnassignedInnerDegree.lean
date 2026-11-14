module

public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section
/-! The fixed-inner-set unassigned row count is exactly the degree of the
physically unassigned graph restricted to the inner vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_unassigned_restricted_degree_eq
    (P:SimpleGraph V) (I:Finset V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (v:V) (hv:v∈I):
    (spanningRestriction (longPhysicalStateGraph P σ {4}) I).degree v=
      ((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:=by
  rw [spanningRestriction_degree,if_pos hv]
  congr 1
  ext w
  simp [longPhysicalStateGraph,SimpleGraph.mem_neighborFinset,and_assoc,and_left_comm,and_comm]

theorem long_unassigned_restricted_degree_from_row
    (P:SimpleGraph V) (I:Finset V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (u θ t:ℝ) (hu:0≤u) (hθ:0≤θ) (huhi:u≤2*θ)
    (hrow:∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|≤t):
    ∀v∈I,((spanningRestriction (longPhysicalStateGraph P σ {4}) I).degree v:ℝ)≤2*θ*I.card+t:=by
  intro v hv
  rw [long_unassigned_restricted_degree_eq P I σ v hv]
  have hc:((P.neighborFinset v∩I).card:ℝ)≤I.card:=by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)
  have hc0:(0:ℝ)≤(P.neighborFinset v∩I).card:=by positivity
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hh:=le_abs_self (((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card-u*(P.neighborFinset v∩I).card)
  have h1:=mul_le_mul_of_nonneg_left hc hu
  have h2:=mul_le_mul_of_nonneg_right huhi hI0
  linarith [hrow v hv]
end Oberwolfach
