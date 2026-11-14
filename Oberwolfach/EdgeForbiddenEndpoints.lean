module

public import Oberwolfach.EdgeConflictDegree

@[expose] public section
/-! Forbidden indices at a physical edge are the union of the two
endpoint-forbidden sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [DecidableEq V] [DecidableEq W]

def edgeAssignmentForbidden (B:V→Finset W) (e:Sym2 V):Finset W:=e.toFinset.biUnion B

theorem edge_assignment_forbidden_at_most (B:V→Finset W) (bound:ℝ)
    (hB:∀v,((B v).card:ℝ)≤bound) (x y:V):
    ((edgeAssignmentForbidden B s(x,y)).card:ℝ)≤2*bound:=by
  have hsub:(edgeAssignmentForbidden B s(x,y)).card≤(B x).card+(B y).card:=by
    simpa [edgeAssignmentForbidden,Sym2.toFinset_mk_eq] using Finset.card_union_le (B x) (B y)
  have hh:((edgeAssignmentForbidden B s(x,y)).card:ℝ)≤((B x).card:ℝ)+(B y).card:=by exact_mod_cast hsub
  linarith [hB x,hB y]
end Oberwolfach
