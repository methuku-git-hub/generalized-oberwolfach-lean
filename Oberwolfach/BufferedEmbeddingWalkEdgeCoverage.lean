module

public import Oberwolfach.BufferedPathEmbeddingEdgeCoverage
public import Oberwolfach.SimpleWalkLengthPhysicalEdges

@[expose] public section
/-! Each edge of an index-matched buffered partial map is a physical edge
of one of its designated target walks. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_embedding_walk_edge_coverage
    {V W I:Type*} [Fintype V] [DecidableEq V] [DecidableEq W] [DecidableEq I]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (H:SimpleGraph W)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hwalk:∀i,∃p:G.Walk (ext i ⟨0,by omega⟩) (ext i ⟨n i+4,by omega⟩),
      p.length=n i+4 ∧ p.support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I) (start finish:I→W) (q:∀i,H.Walk (start i) (finish i))
    (hq:∀i,(q i).IsPath) (hlen:∀i,(q i).length=n i)
    (φ:{x // x∈A.biUnion (fun i=>Finset.univ.image (inner i))}→W)
    (hmatch:∀i (hi:i∈A) (k:Fin (n i+1)),
      φ ⟨inner i k,Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=
        simpleWalkLengthEmbedding H (q i) (hq i) (n i) (hlen i) k):
    ∀x y,G.Adj x.val y.val→({φ x,φ y}:Finset W)∈A.biUnion (fun i=>walkPhysicalEdges (q i)):=by
  classical
  intro x y hxy
  let target (i:I):Fin (n i+1)→W:=simpleWalkLengthEmbedding H (q i) (hq i) (n i) (hlen i)
  obtain ⟨i,hi,k,h⟩:=regular_two_buffered_embedding_edge_coverage G hG n ext inner hinner hwalk hdis A target φ hmatch x y hxy
  have he:=simple_walk_length_embedding_edge_mem H (q i) (hq i) (n i) (hlen i) k
  refine Finset.mem_biUnion.mpr ⟨i,hi,?_⟩
  rcases h with ⟨hx,hy⟩|⟨hy,hx⟩
  · simpa only [hx,hy] using he
  · rw [hx,hy,Finset.pair_comm]
    exact he
end Oberwolfach
