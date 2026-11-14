module

public import Oberwolfach.FiniteSequenceWalkEdges

@[expose] public section
/-! The physical edge set of a walk is the set of consecutive vertex pairs
of its finite vertex sequence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def walkPhysicalEdges {V:Type*} [DecidableEq V] {G:SimpleGraph V} {a b:V} (p:G.Walk a b):Finset (Finset V) :=
  (p.edges.map Sym2.toFinset).toFinset

theorem finite_sequence_walk_edge_set
    {V:Type*} [DecidableEq V] (G:SimpleGraph V) (n:ℕ) (f:Fin (n+1)→V)
    {a b:V} (p:G.Walk a b) (hlen:p.length=n) (hsupp:p.support=List.ofFn f):
    walkPhysicalEdges p=Finset.univ.image (fun i:Fin n=>{f i.castSucc,f i.succ}) := by
  ext s
  simp only [walkPhysicalEdges,List.mem_toFinset,List.mem_map,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,rfl⟩
    obtain ⟨i,hi,heq⟩:=List.mem_iff_getElem.mp he
    subst e
    have hin:i<n:=by simpa [SimpleGraph.Walk.length_edges,hlen] using hi
    exact ⟨⟨i,hin⟩,(finite_sequence_walk_edge_at G n f p hlen hsupp ⟨i,hin⟩).symm⟩
  · rintro ⟨i,heq⟩
    have hi:i.val<p.edges.length:=by simpa [SimpleGraph.Walk.length_edges,hlen] using i.isLt
    refine ⟨p.edges[i.val],List.getElem_mem hi,?_⟩
    exact (finite_sequence_walk_edge_at G n f p hlen hsupp i).trans heq
end Oberwolfach
