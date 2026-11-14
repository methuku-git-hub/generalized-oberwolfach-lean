module

public import Oberwolfach.CycleWalkTailSupport
public import Oberwolfach.SimpleWalkLengthEmbeddingGetVert

@[expose] public section
/-! Match disjoint source cycles to disjoint target cycles of the same sizes,
preserving their directed cyclic orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_cycle_families_match
    {X V I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G:SimpleGraph X) (H:SimpleGraph V) (a:I→X) (p:∀i,G.Walk (a i) (a i))
    (hp:∀i,(p i).IsCycle) (u:I→V) (q:∀i,H.Walk (u i) (u i))
    (hq:∀i,(q i).IsCycle) (hlen:∀i,(q i).length=(p i).length)
    (hpdis:∀i j,i≠j→Disjoint (p i).support.toFinset (p j).support.toFinset)
    (hqdis:∀i j,i≠j→Disjoint (q i).support.toFinset (q j).support.toFinset):
    ∃φ:{x // x∈Finset.univ.biUnion (fun i=>(p i).tail.support.toFinset)}↪V,
      ∀i (k:Fin ((p i).tail.length+1)),
        φ ⟨(p i).tail.getVert k.val,
          Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr ((p i).tail.getVert_mem_support _)⟩⟩=
          (q i).tail.getVert k.val:=by
  have hpt:∀i,(p i).tail.IsPath:=fun i=>(hp i).isPath_tail
  have hqt:∀i,(q i).tail.IsPath:=fun i=>(hq i).isPath_tail
  have hlent:∀i,(q i).tail.length=(p i).tail.length:=by
    intro i
    simp only [SimpleGraph.Walk.length_tail,hlen]
  have hpdt:∀i j,i≠j→Disjoint (p i).tail.support.toFinset (p j).tail.support.toFinset:=by
    intro i j hij
    simpa only [cycle_tail_support_eq G (p i) (hp i),cycle_tail_support_eq G (p j) (hp j)] using hpdis i j hij
  have hqdt:∀i j,i≠j→Disjoint (q i).tail.support.toFinset (q j).tail.support.toFinset:=by
    intro i j hij
    simpa only [cycle_tail_support_eq H (q i) (hq i),cycle_tail_support_eq H (q j) (hq j)] using hqdis i j hij
  obtain ⟨φ,hφ⟩:=disjoint_simple_walk_families_match G H
    (fun i=>(p i).snd) a (fun i=>(p i).tail) hpt
    (fun i=>(q i).snd) u (fun i=>(q i).tail) hqt hlent hpdt hqdt
  refine ⟨φ,?_⟩
  intro i k
  have hh:=hφ i k
  simpa only [simple_walk_length_embedding_getVert] using hh
end Oberwolfach
