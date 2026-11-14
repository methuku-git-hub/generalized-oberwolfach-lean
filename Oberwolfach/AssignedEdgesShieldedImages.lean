module

public import Oberwolfach.AssignedEdgesCallerInputs

@[expose] public section
/-! Allowed edge labels need shield only those old vertices on that edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nonempty W]

theorem assigned_edges_avoid_shielded_old_images (G:SimpleGraph V)
    (f:{e:Sym2 V // e∈G.edgeFinset}→W) (orient:Sym2 V→V×V)
    (horient:∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e)
    (L:Sym2 V→Finset W) (B:V→Finset W) (old:W→Finset V)
    (hShield:∀i e v,e∈G.edgeFinset→v∈e.toFinset→v∈old i→i∈L e→i∈B v)
    (hAllowed:∀e,f e∈L e.val) (hB:∀e,∀v∈e.val.toFinset,f e∉B v):
    ∀i,Disjoint (old i) (prescribedMatchingEndpoints (prescribedAssignedArcs G (extendEdgeAssignment G f) orient i)):=by
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
  have hl:i∈L e:=by simpa [hf] using hAllowed ⟨e,heK⟩
  have hb:=hB ⟨e,heK⟩ v hve
  exact hb (by rw [hf];exact hShield i e v heK hve hvOld hl)
end Oberwolfach
