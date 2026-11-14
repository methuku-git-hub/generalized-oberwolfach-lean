module

public import Oberwolfach.FiniteSequenceWalkDarts

@[expose] public section
/-! The physical edge set of a walk is the set of consecutive vertex pairs
of its finite vertex sequence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def walkPhysicalArcs {V:Type*} [DecidableEq V] {G:SimpleGraph V} {a b:V} (p:G.Walk a b):Finset (V×V) :=
  (p.darts.map SimpleGraph.Dart.toProd).toFinset

theorem finite_sequence_walk_arc_set
    {V:Type*} [DecidableEq V] (G:SimpleGraph V) (n:ℕ) (f:Fin (n+1)→V)
    {a b:V} (p:G.Walk a b) (hlen:p.length=n) (hsupp:p.support=List.ofFn f):
    walkPhysicalArcs p=Finset.univ.image (fun i:Fin n=>(f i.castSucc,f i.succ)) := by
  ext s
  simp only [walkPhysicalArcs,List.mem_toFinset,List.mem_map,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,rfl⟩
    obtain ⟨i,hi,heq⟩:=List.mem_iff_getElem.mp he
    subst e
    have hin:i<n:=by simpa [SimpleGraph.Walk.length_darts,hlen] using hi
    exact ⟨⟨i,hin⟩,(finite_sequence_walk_dart_at G n f p hlen hsupp ⟨i,hin⟩).symm⟩
  · rintro ⟨i,heq⟩
    have hi:i.val<p.darts.length:=by simpa [SimpleGraph.Walk.length_darts,hlen] using i.isLt
    refine ⟨p.darts[i.val],List.getElem_mem hi,?_⟩
    exact (finite_sequence_walk_dart_at G n f p hlen hsupp i).trans heq
end Oberwolfach
