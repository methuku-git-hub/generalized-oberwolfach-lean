module

public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges
public import Oberwolfach.OrdinaryBoundaryExtensionStability

@[expose] public section
/-! Boundary extension counts survive an arbitrary actual physical edit,
    losing at most three times its maximum degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_counts_after_physical_edit
    (Q Q':SimpleGraph V) (H H':V→U→Prop) (X:Finset V) (b L:ℝ)
    (hcounts:∀u a c,b≤(((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hedit:∀w:V⊕U,((changed ((ordinaryPhysicalGraph Q H).neighborFinset w)
      ((ordinaryPhysicalGraph Q' H').neighborFinset w)).card:ℝ)≤L):
    ∀u a c,b-3*L≤(((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ):=by
  have htyped:=ordinary_physical_edit_to_typed_changes Q Q' H H' L hedit
  intro u a c
  have hh:=ordinary_boundary_extension_count_stability Q Q' H H' X a c u L
    (htyped.1 a) (htyped.1 c) (htyped.2.2 u)
  have he (G:SimpleGraph V) (K:V→U→Prop):
      X.filter (fun v=>G.Adj a v∧G.Adj v c∧K v u)=
      (X.filter (fun v=>K v u))∩G.neighborFinset a∩G.neighborFinset c:=by
    ext v
    simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    have hg:=G.adj_comm v c
    tauto
  rw [he,he] at hh
  have hl:=(abs_le.mp hh).2
  linarith only [hcounts u a c,hl]
end Oberwolfach
