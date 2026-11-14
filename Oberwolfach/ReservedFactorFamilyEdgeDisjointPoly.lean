module

public import Oberwolfach.ReservedFactorFamilyWalkEmbeddingFull
public import Oberwolfach.BufferedEmbeddingWalkEdgeCoverage
public import Oberwolfach.PartialFactorWalkEdgeDisjointnessPoly

@[expose] public section
/-! Cross-hub-disjoint target walk edges give edge-disjoint reserved partial
factor maps while retaining the original source buffers and block witnesses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_factor_family_to_edge_disjoint_walk_maps_poly
    {X W U:Type*} [Fintype X] [DecidableEq X] [DecidableEq W]
    (F:U→SimpleGraph X) (hF:∀u,(F u).IsRegularOfDegree 2) (H:SimpleGraph W)
    (I J:U→Type*) [∀u,Fintype (I u)] [∀u,Fintype (J u)]
    (components:∀u,I u↪(F u).ConnectedComponent)
    (e:∀u (i:I u),SimpleGraph.cycleGraph (Fintype.card (components u i)) ≃g (components u i).toSimpleGraph)
    (c d:ℕ) (t:∀u,J u→ℕ) (ht:∀u j,t u j≤d)
    (hcapacity:∀u,Fintype.card (J u)≤∑i:I u,Fintype.card (components u i)/(c*d+5))
    (start finish:∀u,J u→W) (q:∀u (j:J u),H.Walk (start u j) (finish u j))
    (hq:∀u j,(q u j).IsPath) (hlen:∀u j,(q u j).length=c*t u j)
    (hqdis:∀u (j l:J u),j≠l→Disjoint (q u j).support.toFinset (q u l).support.toFinset)
    (hqedge:∀u v,u≠v→∀j:J u,∀l:J v,Disjoint (walkPhysicalEdges (q u j)) (walkPhysicalEdges (q v l))):
    ∃index:∀u,J u↪LongReservedBlockIndex (F u) (components u) c d,
    ∃ext:∀u (j:J u),Fin (c*t u j+5)↪X,
    ∃inner:∀u (j:J u),Fin (c*t u j+1)↪X,
    ∃φ:∀u,{x // x∈Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))}↪W,
      (∀u j,ext u j=longReservedSigmaBlock (F u) (components u) c d (e u) (index u j) (t u j) (ht u j)) ∧
      (∀u j (k:Fin (c*t u j+1)),inner u j k=ext u j ⟨k.val+2,by omega⟩) ∧
      (∀u j k,ext u j k∈(components u (index u j).1).supp) ∧
      (∀u (j l:J u),j≠l→Disjoint (Finset.univ.image (ext u j)) (Finset.univ.image (ext u l))) ∧
      (∀u (j:J u),∃p:(F u).Walk (ext u j ⟨0,by omega⟩) (ext u j ⟨c*t u j+4,by omega⟩),
        p.length=c*t u j+4 ∧ p.support=List.ofFn (ext u j)) ∧
      (∀u (j:J u) (k:Fin (c*t u j+1)),
        φ u ⟨inner u j k,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=
          simpleWalkLengthEmbedding H (q u j) (hq u j) (c*t u j) (hlen u j) k) ∧
      (∀u x y,(F u).Adj x.val y.val→H.Adj (φ u x) (φ u y)) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdgesPoly {x // x∈Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))}
          ((F u).induce (↑(Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))):Set X)) (φ u))
        (partialFactorPhysicalEdgesPoly {x // x∈Finset.univ.biUnion (fun j:J v=>Finset.univ.image (inner v j))}
          ((F v).induce (↑(Finset.univ.biUnion (fun j:J v=>Finset.univ.image (inner v j))):Set X)) (φ v))) := by
  classical
  obtain ⟨index,ext,inner,φ,hext,hinner,hcomponents,hdis,hwalk,hmatch,hgraph⟩:=
    reserved_factor_family_to_disjoint_walks_with_buffers F hF H I J components e c d t ht hcapacity start finish q hq hlen hqdis
  let D (u:U):={x // x∈Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))}
  let F' (u:U):SimpleGraph (D u):=(F u).induce (↑(Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))):Set X)
  have hcover:∀u (x y:D u),(F' u).Adj x y→
      ({φ u x,φ u y}:Finset W)∈Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)):=by
    intro u x y hxy
    exact regular_two_buffered_embedding_walk_edge_coverage (F u) (hF u) H (fun j:J u=>c*t u j)
      (ext u) (inner u) (hinner u) (hwalk u) (hdis u) (Finset.univ:Finset (J u))
      (start u) (finish u) (q u) (hq u) (hlen u) (φ u) (fun j hj k=>hmatch u j k) x y hxy
  have hedge:=partial_factor_edges_disjoint_of_walk_coverage_poly D F' (fun u=>φ u) J H start finish q hqedge hcover
  exact ⟨index,ext,inner,φ,hext,hinner,hcomponents,hdis,hwalk,hmatch,hgraph,hedge⟩
end Oberwolfach
