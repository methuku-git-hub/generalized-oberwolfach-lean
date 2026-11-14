module

public import Oberwolfach.PartialFactorEdgeDisjointness
public import Oberwolfach.FiniteSequenceWalkEdgeSet

@[expose] public section
/-! Partial factors whose image edges are covered by cross-hub-disjoint walk
edges are physically edge-disjoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem partial_factor_edges_disjoint_of_walk_coverage
    {U V:Type} [DecidableEq V]
    (D:U→Type) (F:∀u,SimpleGraph (D u)) (ψ:∀u,D u→V)
    (I:U→Type*) [∀u,Fintype (I u)]
    (H:SimpleGraph V) (start finish:∀u,I u→V)
    (q:∀u (i:I u),H.Walk (start u i) (finish u i))
    (hdis:∀u v,u≠v→∀i:I u,∀j:I v,Disjoint (walkPhysicalEdges (q u i)) (walkPhysicalEdges (q v j)))
    (hcover:∀u x y,(F u).Adj x y→({ψ u x,ψ u y}:Finset V)∈Finset.univ.biUnion (fun i:I u=>walkPhysicalEdges (q u i))):
    ∀u v,u≠v→Disjoint (partialFactorPhysicalEdges (D u) (F u) (ψ u))
      (partialFactorPhysicalEdges (D v) (F v) (ψ v)):=by
  classical
  intro u v huv
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x,y,hxy,rfl⟩:=hz
  obtain ⟨x',y',hxy',heq⟩:=hz'
  have hpair:({ψ u x,ψ u y}:Finset V)={ψ v x',ψ v y'}:=by
    have hh:=congrArg Sym2.toFinset heq
    simpa only [Sym2.toFinset_mk_eq] using hh
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp (hcover u x y hxy)
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp (hcover v x' y' hxy')
  have hj':({ψ u x,ψ u y}:Finset V)∈walkPhysicalEdges (q v j):=by rw [hpair];exact hj
  exact Finset.disjoint_left.mp (hdis u v huv i j) hi hj'
end Oberwolfach
