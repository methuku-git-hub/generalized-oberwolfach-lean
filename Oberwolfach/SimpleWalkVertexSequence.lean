module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Data.List.Nodup

@[expose] public section
/-! An indexed simple walk is an injective vertex sequence with exactly its
walk support and its original consecutive edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def simpleWalkVertexEmbedding {V:Type*} (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath):Fin (p.length+1)↪V := by
  have hn:p.support.Nodup:=by simpa only [SimpleGraph.Walk.isPath_def] using hp
  refine ⟨fun i=>p.getVert i.val,?_⟩
  intro i j hij
  have hi:p.getVert i.val=p.support.get ⟨i.val,by simpa only [p.length_support] using i.isLt⟩:=by
    exact p.getVert_eq_support_getElem (by omega)
  have hj:p.getVert j.val=p.support.get ⟨j.val,by simpa only [p.length_support] using j.isLt⟩:=by
    exact p.getVert_eq_support_getElem (by omega)
  have hget:=hn.injective_get (hi.symm.trans (hij.trans hj))
  have hval:i.val=j.val:=congrArg (fun k:Fin p.support.length=>k.val) hget
  exact Fin.ext hval

theorem simple_walk_vertex_embedding_adjacent {V:Type*} (G:SimpleGraph V) {a b:V}
    (p:G.Walk a b) (hp:p.IsPath):
    ∀k:Fin p.length,G.Adj (simpleWalkVertexEmbedding G p hp k.castSucc)
      (simpleWalkVertexEmbedding G p hp k.succ):=by
  intro k
  exact p.adj_getVert_succ k.isLt

theorem simple_walk_vertex_embedding_support {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) {a b:V} (p:G.Walk a b) (hp:p.IsPath):
    Finset.univ.image (simpleWalkVertexEmbedding G p hp)=p.support.toFinset:=by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,List.mem_toFinset]
  constructor
  · rintro ⟨i,rfl⟩
    exact p.getVert_mem_support i.val
  · intro hx
    obtain ⟨i,hi⟩:=List.mem_iff_get.mp hx
    let k:Fin (p.length+1):=⟨i.val,by simpa only [p.length_support] using i.isLt⟩
    refine ⟨k,?_⟩
    change p.getVert k.val=x
    rw [p.getVert_eq_support_getElem (by omega)]
    exact hi
end Oberwolfach
