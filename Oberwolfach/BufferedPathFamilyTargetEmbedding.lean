module

public import Oberwolfach.BufferedWalkEmbeddingGlue
public import Oberwolfach.BufferedPathTargetEmbedding

@[expose] public section
/-! Match disjoint buffered source walks to disjoint target paths and glue the
resulting local maps into one graph-preserving partial embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_path_family_target_embedding
    {V W I:Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (H:SimpleGraph W)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hwalk:∀i,∃p:G.Walk (ext i ⟨0,by omega⟩) (ext i ⟨n i+4,by omega⟩),
      p.length=n i+4 ∧ p.support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I) (target:∀i,Fin (n i+1)↪W)
    (htarget:∀i (k:Fin (n i)),H.Adj (target i ⟨k.val,by omega⟩) (target i ⟨k.val+1,by omega⟩))
    (htargetDis:∀i∈A,∀j∈A,i≠j→Disjoint (Set.range (target i)) (Set.range (target j))):
    ∃φ:{x // x∈A.biUnion (fun i=>Finset.univ.image (inner i))}↪W,
      (∀i (hi:i∈A) (k:Fin (n i+1)),
        φ ⟨inner i k,Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=target i k) ∧
      (∀x y,G.Adj x.val y.val→H.Adj (φ x) (φ y)):=by
  classical
  have hstep:∀i (k:Fin (n i+4)),
      G.Adj (ext i ⟨k.val,by omega⟩) (ext i ⟨k.val+1,by omega⟩):=by
    intro i k
    obtain ⟨p,hlen,hsupport⟩:=hwalk i
    exact walk_ofFn_support_adjacent G (n i+4) (ext i) p hlen hsupport k
  have hexists (i:I):=regular_two_buffered_path_target_embedding G hG H (n i) (ext i) (inner i)
    (hinner i) (hstep i) (target i) (htarget i)
  let f (i:I):{x // x∈Finset.univ.image (inner i)}↪W:=Classical.choose (hexists i)
  have hf (i:I):=
    Classical.choose_spec (hexists i)
  have hfdis:∀i∈A,∀j∈A,i≠j→Disjoint (Set.range (f i)) (Set.range (f j)):=by
    intro i hi j hj hij
    exact (htargetDis i hi j hj hij).mono (hf i).2.1 (hf j).2.1
  have hlocal:∀i∈A,∀x y (hx:x∈Finset.univ.image (inner i)) (hy:y∈Finset.univ.image (inner i)),
      G.Adj x y→H.Adj (f i ⟨x,hx⟩) (f i ⟨y,hy⟩):=by
    intro i hi x y hx hy hxy
    exact (hf i).2.2 ⟨x,hx⟩ ⟨y,hy⟩ hxy
  obtain ⟨φ,hφ,hgraph⟩:=regular_two_buffered_walk_embeddings_glue G hG H n ext inner hinner hwalk hdis A f hfdis hlocal
  refine ⟨φ,?_,hgraph⟩
  intro i hi k
  let hx:inner i k∈Finset.univ.image (inner i):=Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  exact (hφ i hi (inner i k) hx).trans ((hf i).1 k)
end Oberwolfach
