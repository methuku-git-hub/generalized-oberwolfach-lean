module

public import Oberwolfach.FiniteSequenceWalkEdges

@[expose] public section
/-! The Sym2 edge set of a walk with a prescribed finite vertex sequence is
exactly its set of consecutive pairs. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_sequence_walk_sym2_edge_set
    {V:Type*} [DecidableEq V] (G:SimpleGraph V) (n:ℕ) (f:Fin (n+1)→V)
    {a b:V} (p:G.Walk a b) (hlen:p.length=n) (hsupp:p.support=List.ofFn f):
    p.edges.toFinset=Finset.univ.image (fun i:Fin n=>s(f i.castSucc,f i.succ)):=by
  classical
  have hv:∀j:ℕ,(hj:j≤n)→p.getVert j=f ⟨j,by omega⟩:=by
    intro j hj
    have hh:=p.getVert_eq_support_getElem? (n:=j) (by omega)
    rw [hsupp] at hh
    simpa only [List.getElem?_ofFn,dif_pos (show j<n+1 by omega),Option.some.injEq] using hh
  have hedge (i:Fin n):
      p.edges[i.val]'(by simpa [SimpleGraph.Walk.length_edges,hlen] using i.isLt)=s(f i.castSucc,f i.succ):=by
    have hi:i.val<p.edges.length:=by simpa [SimpleGraph.Walk.length_edges,hlen] using i.isLt
    rw [SimpleGraph.Walk.getElem_edges hi,hv i.val (by omega),hv (i.val+1) (by omega)]
    have h1:(⟨i.val,by omega⟩:Fin (n+1))=i.castSucc:=Fin.ext rfl
    have h2:(⟨i.val+1,by omega⟩:Fin (n+1))=i.succ:=Fin.ext rfl
    rw [h1,h2]
  ext z
  simp only [List.mem_toFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro hz
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hz
    have hin:i<n:=by simpa [SimpleGraph.Walk.length_edges,hlen] using hi
    refine ⟨⟨i,hin⟩,?_⟩
    exact (hedge ⟨i,hin⟩).symm.trans he
  · rintro ⟨i,he⟩
    have hi:i.val<p.edges.length:=by simpa [SimpleGraph.Walk.length_edges,hlen] using i.isLt
    exact he ▸ (hedge i ▸ List.getElem_mem hi)
end Oberwolfach
