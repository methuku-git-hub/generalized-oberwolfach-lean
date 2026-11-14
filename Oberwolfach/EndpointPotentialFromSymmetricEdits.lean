module

public import Oberwolfach.EndpointPotentialSymmetricChanges
public import Oberwolfach.GraphDifferenceChangedDegree

@[expose] public section
/-! Directly charge endpoint potential errors to the original symmetric
neighborhood edit bounds, including both added and deleted edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem endpoint_potential_from_symmetric_edits
    (P R R' H H' F:SimpleGraph V) (A B:Finset V) (x:V) (weight:Sym2 V→ℝ) (d C L:ℝ)
    (hA:0<A.card) (hBA:B.card≤A.card) (hC:0≤C) (hL:0≤L)
    (hw:∀e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet→
      0≤weight e/d∧weight e/d≤C/(A.card:ℝ)^2)
    (hR:∀v,((changed (R.neighborFinset v) (R'.neighborFinset v)).card:ℝ)≤L)
    (hH:∀v,((changed (H.neighborFinset v) (H'.neighborFinset v)).card:ℝ)≤L):
    (∀v,|endpointRowPotential P R' H' F A B x v weight d-endpointRowPotential P R H F A B x v weight d|
      ≤10*C*L/A.card) ∧
    (∀u,|endpointIndexPotential P R' H' F A x u weight d-endpointIndexPotential P R H F A x u weight d|
      ≤6*C*L/A.card):=by
  have hr1:∀v,((R\R').degree v:ℝ)≤L:=by
    intro v
    have hh:((R\R').degree v:ℝ)≤(changed (R'.neighborFinset v) (R.neighborFinset v)).card:=by
      exact_mod_cast graph_difference_degree_le_changed R R' v
    apply hh.trans
    simpa [changed,Finset.union_comm] using hR v
  have hr2:∀v,((R'\R).degree v:ℝ)≤L:=by
    intro v
    have hh:((R'\R).degree v:ℝ)≤(changed (R.neighborFinset v) (R'.neighborFinset v)).card:=by
      exact_mod_cast graph_difference_degree_le_changed R' R v
    exact hh.trans (hR v)
  have hh1:∀v,((H\H').degree v:ℝ)≤L:=by
    intro v
    have hh:((H\H').degree v:ℝ)≤(changed (H'.neighborFinset v) (H.neighborFinset v)).card:=by
      exact_mod_cast graph_difference_degree_le_changed H H' v
    apply hh.trans
    simpa [changed,Finset.union_comm] using hH v
  have hh2:∀v,((H'\H).degree v:ℝ)≤L:=by
    intro v
    have hh:((H'\H).degree v:ℝ)≤(changed (H.neighborFinset v) (H'.neighborFinset v)).card:=by
      exact_mod_cast graph_difference_degree_le_changed H' H v
    exact hh.trans (hH v)
  exact endpoint_potential_symmetric_change_bounds P R R' H H' F A B x weight d C L hA hBA hC hL hw
    hr1 hr2 hh1 hh2
end Oberwolfach
