module

public import Oberwolfach.FiniteSequenceWalkSym2Edges
public import Oberwolfach.BufferedOrientedPathOrbit
public import Oberwolfach.FactorOrientedPhysicalEdges

@[expose] public section
/-! The reserved walk edges are exactly the physical edges of their
oriented source tails. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_oriented_walk_deleted_edges
    {X I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X) (σ:Equiv.Perm X)
    (hstep:∀i (p:Fin (n i)),σ (inner i p.castSucc)=inner i p.succ)
    (p:∀i,G.Walk (inner i 0) (inner i (Fin.last (n i))))
    (hlen:∀i,(p i).length=n i) (hsupp:∀i,(p i).support=List.ofFn (inner i)):
    (Finset.univ.biUnion (fun i=>(p i).edges.toFinset))=
      (markedIntervalRootSet σ n (fun i=>inner i 0)).image (factorOrientedPhysicalEdge σ):=by
  classical
  have horbit:=buffered_path_follows_permutation n inner σ hstep
  ext z
  constructor
  · intro hz
    obtain ⟨i,_,hz⟩:=Finset.mem_biUnion.mp hz
    rw [finite_sequence_walk_sym2_edge_set G (n i) (inner i) (p i) (hlen i) (hsupp i)] at hz
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨inner i j.castSucc,?_,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
      exact (horbit i j.castSucc).symm
    · change s(inner i j.castSucc,σ (inner i j.castSucc))=z
      rw [hstep i j]
      exact hj
  · intro hz
    obtain ⟨x,hx,hxz⟩:=Finset.mem_image.mp hz
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hi
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    rw [finite_sequence_walk_sym2_edge_set G (n i) (inner i) (p i) (hlen i) (hsupp i)]
    refine Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩
    have hh:inner i j.castSucc=x:=(horbit i j.castSucc).trans hj
    change s(inner i j.castSucc,inner i j.succ)=z
    rw [←hstep i j,hh]
    exact hxz
end Oberwolfach
