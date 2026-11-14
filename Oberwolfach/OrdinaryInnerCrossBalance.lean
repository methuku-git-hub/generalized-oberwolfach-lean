module

public import Oberwolfach.OrdinaryBoundaryDegreeProfiles
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section
/-! The protected induced pair has exactly the cross profile at each inner
root, and zero balance error at every root outside it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_balance_from_cross_profile
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (b:ℝ) (hb:0≤b)
    (hcross:∀v∈I,|((Q.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤b):
    ∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b:=by
  intro v
  rw [spanningRestriction_degree]
  by_cases hv:v∈I
  · rw [if_pos hv]
    have he:(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J))=J.filter (H v):=by
      ext u;simp [hv,and_comm]
    rw [he]
    exact hcross v hv
  · simp [hv,hb]
end Oberwolfach
