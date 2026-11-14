module

public import Oberwolfach.DisjointPieceEmbeddingGlue
public import Oberwolfach.RegularTwoBufferedPathSeparation
public import Oberwolfach.WalkOfFnSupportAdj

@[expose] public section
/-! Buffered source walks supply the edge coverage needed to glue the
corresponding disjoint partial graph embeddings. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_walk_edge_cover
    {V I:Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hwalk:∀i,∃p:G.Walk (ext i ⟨0,by omega⟩) (ext i ⟨n i+4,by omega⟩),
      p.length=n i+4 ∧ p.support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I):
    ∀x y,x∈A.biUnion (fun i=>Finset.univ.image (inner i))→
      y∈A.biUnion (fun i=>Finset.univ.image (inner i))→G.Adj x y→
      ∃i∈A,x∈Finset.univ.image (inner i) ∧ y∈Finset.univ.image (inner i):=by
  have hstep:∀i (k:Fin (n i+4)),
      G.Adj (ext i ⟨k.val,by omega⟩) (ext i ⟨k.val+1,by omega⟩):=by
    intro i k
    obtain ⟨p,hlen,hsupport⟩:=hwalk i
    exact walk_ofFn_support_adjacent G (n i+4) (ext i) p hlen hsupport k
  exact regular_two_buffered_path_edge_cover G hG n ext inner hinner hstep hdis A

theorem regular_two_buffered_walk_embeddings_glue
    {V W I:Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (H:SimpleGraph W)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hwalk:∀i,∃p:G.Walk (ext i ⟨0,by omega⟩) (ext i ⟨n i+4,by omega⟩),
      p.length=n i+4 ∧ p.support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I)
    (f:∀i,{x // x∈Finset.univ.image (inner i)}↪W)
    (hf:∀i∈A,∀j∈A,i≠j→Disjoint (Set.range (f i)) (Set.range (f j)))
    (hlocal:∀i∈A,∀x y (hx:x∈Finset.univ.image (inner i)) (hy:y∈Finset.univ.image (inner i)),
      G.Adj x y→H.Adj (f i ⟨x,hx⟩) (f i ⟨y,hy⟩)):
    ∃φ:{x // x∈A.biUnion (fun i=>Finset.univ.image (inner i))}↪W,
      (∀i (hi:i∈A) (x:V) (hx:x∈Finset.univ.image (inner i)),
        φ ⟨x,Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩=f i ⟨x,hx⟩) ∧
      (∀x y,G.Adj x.val y.val→H.Adj (φ x) (φ y)):=by
  classical
  have hsubset (i:I):Finset.univ.image (inner i)⊆Finset.univ.image (ext i):=by
    intro x hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    rw [hinner i k]
    exact Finset.mem_image.mpr ⟨⟨k.val+2,by omega⟩,Finset.mem_univ _,rfl⟩
  have hpieces:∀i∈A,∀j∈A,i≠j→Disjoint (Finset.univ.image (inner i)) (Finset.univ.image (inner j)):=by
    intro i hi j hj hij
    exact (hdis i j hij).mono (hsubset i) (hsubset j)
  exact disjoint_piece_graph_embeddings_glue A (fun i=>Finset.univ.image (inner i))
    hpieces f hf G H (regular_two_buffered_walk_edge_cover G hG n ext inner hinner hwalk hdis A) hlocal
end Oberwolfach
