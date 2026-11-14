module

public import Oberwolfach.BufferedPathFamilyTargetEmbedding
public import Oberwolfach.SimpleWalkLengthEmbedding

@[expose] public section
/-! Use simple target walks, rather than separately supplied target vertex
embeddings, in the buffered source-path partial embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_paths_to_disjoint_simple_walks
    {V W I:Type*} [Fintype V] [DecidableEq V] [DecidableEq W] [DecidableEq I]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (H:SimpleGraph W)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hwalk:∀i,∃p:G.Walk (ext i ⟨0,by omega⟩) (ext i ⟨n i+4,by omega⟩),
      p.length=n i+4 ∧ p.support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I) (start finish:I→W) (q:∀i,H.Walk (start i) (finish i))
    (hq:∀i,(q i).IsPath) (hlen:∀i,(q i).length=n i)
    (hqdis:∀i∈A,∀j∈A,i≠j→Disjoint (q i).support.toFinset (q j).support.toFinset):
    ∃φ:{x // x∈A.biUnion (fun i=>Finset.univ.image (inner i))}↪W,
      (∀i (hi:i∈A) (k:Fin (n i+1)),
        φ ⟨inner i k,Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=
          simpleWalkLengthEmbedding H (q i) (hq i) (n i) (hlen i) k) ∧
      (∀x y,G.Adj x.val y.val→H.Adj (φ x) (φ y)):=by
  classical
  let target (i:I):Fin (n i+1)↪W:=simpleWalkLengthEmbedding H (q i) (hq i) (n i) (hlen i)
  have htarget:∀i (k:Fin (n i)),H.Adj (target i ⟨k.val,by omega⟩) (target i ⟨k.val+1,by omega⟩):=by
    intro i k
    exact simple_walk_length_embedding_adjacent H (q i) (hq i) (n i) (hlen i) k
  have hmem (i:I) {x:W}:x∈Set.range (target i)→x∈(q i).support.toFinset:=by
    rintro ⟨k,rfl⟩
    rw [←simple_walk_length_embedding_support H (q i) (hq i) (n i) (hlen i)]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  have htargetDis:∀i∈A,∀j∈A,i≠j→Disjoint (Set.range (target i)) (Set.range (target j)):=by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Finset.disjoint_left.mp (hqdis i hi j hj hij) (hmem i hxi) (hmem j hxj)
  exact regular_two_buffered_path_family_target_embedding G hG H n ext inner hinner hwalk hdis A target htarget htargetDis
end Oberwolfach
