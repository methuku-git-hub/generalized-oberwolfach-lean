module

public import Oberwolfach.EdgeAssignmentToPhysical
public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! List and endpoint-forbidden conditions give the exact disjointness
conditions required by the prescribed-position construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nonempty W]

theorem assigned_edges_avoid_old_images (G:SimpleGraph V)
    (f:{e:Sym2 V // e∈G.edgeFinset}→W) (orient:Sym2 V→V×V)
    (horient:∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e)
    (B:V→Finset W) (old:W→Finset V)
    (hOld:∀v i,v∈old i→i∈B v)
    (hB:∀e,∀v∈e.1.toFinset,f e∉B v):
    ∀i,Disjoint (old i) (prescribedMatchingEndpoints (prescribedAssignedArcs G (extendEdgeAssignment G f) orient i)) := by
  intro i
  apply Finset.disjoint_left.mpr
  intro v hvOld hvEnd
  obtain ⟨a,ha,hva⟩:=Finset.mem_biUnion.mp hvEnd
  obtain ⟨e,he,heq⟩:=Finset.mem_image.mp ha
  have heK:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
  have hei:extendEdgeAssignment G f e=i:=(Finset.mem_filter.mp he).2
  have hve:v∈e.toFinset:=by
    rw [←horient e heK]
    simp only [prescribedArcPhysical,Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton]
    simpa [heq] using hva
  have hf:f ⟨e,heK⟩=i:=by simpa [extend_edge_assignment_value G f e heK] using hei
  have hb:=hB ⟨e,heK⟩ v hve
  exact hb (by rw [hf];exact hOld v i hvOld)

theorem assigned_edges_avoid_inner_indices (G:SimpleGraph V)
    (f:{e:Sym2 V // e∈G.edgeFinset}→W) (orient:Sym2 V→V×V)
    (L:Sym2 V→Finset W) (inner:Finset W)
    (hAllowed:∀e,f e∈L e.1) (hOutside:∀e∈G.edgeFinset,Disjoint (L e) inner):
    ∀i,i∈inner→prescribedAssignedArcs G (extendEdgeAssignment G f) orient i=∅ := by
  intro i hi
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨e,he,heq⟩:=Finset.mem_image.mp ha
  have heK:e∈G.edgeFinset:=(Finset.mem_filter.mp he).1
  have hei:extendEdgeAssignment G f e=i:=(Finset.mem_filter.mp he).2
  have hf:f ⟨e,heK⟩=i:=by simpa [extend_edge_assignment_value G f e heK] using hei
  have hL:f ⟨e,heK⟩∈L e:=hAllowed ⟨e,heK⟩
  rw [hf] at hL
  exact (Finset.disjoint_left.mp (hOutside e heK)) hL hi
end Oberwolfach
