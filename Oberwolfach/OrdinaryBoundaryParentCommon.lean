module

public import Oberwolfach.BoundarySupportEvent

@[expose] public section
/-! A uniform minimum neighborhood in the inner domain gives the two-root
common-neighborhood lower bound used by the ordinary cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_boundary_parent_common_of_min_degree
    (P:SimpleGraph V) (X:Finset V) (d:ℝ)
    (hdeg:∀v,d*X.card≤((X∩P.neighborFinset v).card:ℝ)):
    ∀a c,(2*d-1)*X.card≤((common X {a,c} (fun x=>P.neighborFinset x)).card:ℝ):=by
  intro a c
  let A:=X∩P.neighborFinset a
  let B:=X∩P.neighborFinset c
  have hu:A∪B⊆X:=Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hcard:(A∪B).card≤X.card:=Finset.card_le_card hu
  have he:((A∪B).card:ℝ)+(A∩B).card=(A.card:ℝ)+B.card:=by
    exact_mod_cast Finset.card_union_add_card_inter A B
  have hh:((A∪B).card:ℝ)≤X.card:=Nat.cast_le.mpr hcard
  rw [common_neighbourhood_pair]
  change (2*d-1)*X.card≤((A∩B).card:ℝ)
  have ha:=hdeg a
  have hc:=hdeg c
  change d*X.card≤(A.card:ℝ) at ha
  change d*X.card≤(B.card:ℝ) at hc
  nlinarith only [ha,hc,he,hh]
end Oberwolfach
