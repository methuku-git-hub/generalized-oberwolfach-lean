module

public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! Every endpoint of an assigned physical edge avoids the forbidden index
set used when assigning that edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem assigned_endpoints_avoid_forbidden (G:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V)
    (horient:∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e)
    (Bad:V→Finset I) (hallowed:∀e∈G.edgeFinset,∀v∈e.toFinset,assign e∉Bad v):
    ∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs G assign orient i)→i∉Bad v := by
  intro i v hv
  obtain ⟨a,ha,hva⟩:=Finset.mem_biUnion.mp hv
  obtain ⟨e,he,heq⟩:=Finset.mem_image.mp ha
  have heK:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
  have hei:assign e=i:=(Finset.mem_filter.mp he).2
  have hve:v∈e.toFinset:=by
    rw [←horient e heK]
    simp only [prescribedArcPhysical,Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton]
    simpa [heq] using hva
  simpa [hei] using hallowed e heK v hve
theorem assigned_endpoints_have_allowed_edge (G:SimpleGraph V) (assign:Sym2 V→I) (orient:Sym2 V→V×V)
    (horient:∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e)
    (L:Sym2 V→Finset I) (hallowed:∀e∈G.edgeFinset,assign e∈L e):
    ∀i v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs G assign orient i)→
      ∃e∈G.edgeFinset,v∈e.toFinset ∧ i∈L e := by
  intro i v hv
  obtain ⟨a,ha,hva⟩:=Finset.mem_biUnion.mp hv
  obtain ⟨e,he,heq⟩:=Finset.mem_image.mp ha
  have heK:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
  have hei:assign e=i:=(Finset.mem_filter.mp he).2
  have hve:v∈e.toFinset:=by
    rw [←horient e heK]
    simp only [prescribedArcPhysical,Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton]
    simpa [heq] using hva
  refine ⟨e,heK,hve,?_⟩
  simpa [hei] using hallowed e heK
end Oberwolfach
