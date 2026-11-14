module

public import Oberwolfach.DisjointActualCycleMatching

@[expose] public section
/-! Matching a directed target cycle preserves every directed arc, including
the closing arc, on the same disjoint source-cycle vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_cycle_families_match_directed
    {X V I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G:SimpleGraph X) (H:SimpleGraph V) (a:I→X) (p:∀i,G.Walk (a i) (a i))
    (hp:∀i,(p i).IsCycle) (u:I→V) (q:∀i,H.Walk (u i) (u i))
    (hq:∀i,(q i).IsCycle) (hlen:∀i,(q i).length=(p i).length)
    (hpdis:∀i j,i≠j→Disjoint (p i).support.toFinset (p j).support.toFinset)
    (hqdis:∀i j,i≠j→Disjoint (q i).support.toFinset (q j).support.toFinset)
    (A:Finset (V×V)) (hdir:∀i k,k<(q i).length→((q i).getVert k,(q i).getVert (k+1))∈A):
    ∃φ:{x // x∈Finset.univ.biUnion (fun i=>(p i).tail.support.toFinset)}↪V,
      ∀i k,(hk:k<(p i).length)→
        (φ ⟨(p i).getVert k,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,by
          rw [cycle_tail_support_eq G (p i) (hp i)];exact List.mem_toFinset.mpr ((p i).getVert_mem_support _)⟩⟩,
         φ ⟨(p i).getVert (k+1),Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,by
          rw [cycle_tail_support_eq G (p i) (hp i)];exact List.mem_toFinset.mpr ((p i).getVert_mem_support _)⟩⟩)∈A:=by
  obtain ⟨φ,hφ⟩:=disjoint_cycle_families_match G H a p hp u q hq hlen hpdis hqdis
  have hmap:∀i k,(hk:k≤(p i).length)→
      φ ⟨(p i).getVert k,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,by
        rw [cycle_tail_support_eq G (p i) (hp i)];exact List.mem_toFinset.mpr ((p i).getVert_mem_support _)⟩⟩=(q i).getVert k:=by
    intro i k hk
    by_cases hk0:k=0
    · subst k
      have hh:=hφ i ⟨(p i).tail.length,by omega⟩
      dsimp only [Fin.val_mk] at hh
      have hleft:(p i).tail.getVert (p i).tail.length=a i:=(p i).tail.getVert_length
      have ht:(q i).tail.length=(p i).tail.length:=by simp only [SimpleGraph.Walk.length_tail,hlen]
      have hright:(q i).tail.getVert (p i).tail.length=u i:=by rw [←ht];exact (q i).tail.getVert_length
      simpa only [hleft,hright,SimpleGraph.Walk.getVert_zero] using hh
    · have hkpos:0<k:=by omega
      have ht:(p i).tail.length+1=(p i).length:=(p i).length_tail_add_one (hp i).not_nil
      have hh:=hφ i ⟨k-1,by omega⟩
      dsimp only [Fin.val_mk] at hh
      have he:k-1+1=k:=by omega
      simpa only [SimpleGraph.Walk.getVert_tail,he] using hh
  refine ⟨φ,?_⟩
  intro i k hk
  rw [hmap i k (by omega),hmap i (k+1) (by omega)]
  apply hdir
  rw [hlen]
  exact hk
end Oberwolfach
