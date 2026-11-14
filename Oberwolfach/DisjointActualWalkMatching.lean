module

public import Oberwolfach.DisjointPieceEmbeddingGlue
public import Oberwolfach.FiniteSequenceRangeEmbedding
public import Oberwolfach.SimpleWalkLengthEmbedding

@[expose] public section
/-! Match a fixed family of disjoint actual source walks to disjoint target
walks of the same lengths. This preserves every indexed vertex and does not
reallocate the source walks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_simple_walk_families_match
    {X V I:Type} [DecidableEq X] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G:SimpleGraph X) (H:SimpleGraph V) (a b:I→X) (p:∀i,G.Walk (a i) (b i))
    (hp:∀i,(p i).IsPath) (u v:I→V) (q:∀i,H.Walk (u i) (v i))
    (hq:∀i,(q i).IsPath) (hlen:∀i,(q i).length=(p i).length)
    (hpdis:∀i j,i≠j→Disjoint (p i).support.toFinset (p j).support.toFinset)
    (hqdis:∀i j,i≠j→Disjoint (q i).support.toFinset (q j).support.toFinset):
    ∃φ:{x // x∈Finset.univ.biUnion (fun i=>(p i).support.toFinset)}↪V,
      ∀i (k:Fin ((p i).length+1)),
        φ ⟨simpleWalkLengthEmbedding G (p i) (hp i) (p i).length rfl k,
          Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,by
            rw [←simple_walk_length_embedding_support G (p i) (hp i) (p i).length rfl]
            exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=
          simpleWalkLengthEmbedding H (q i) (hq i) (p i).length (hlen i) k:=by
  classical
  let source (i:I):Fin ((p i).length+1)↪X:=simpleWalkLengthEmbedding G (p i) (hp i) (p i).length rfl
  let target (i:I):Fin ((p i).length+1)↪V:=simpleWalkLengthEmbedding H (q i) (hq i) (p i).length (hlen i)
  have hf (i:I):∃f:{x // x∈Finset.univ.image (source i)}↪V,
      ∀k,f ⟨source i k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩=target i k:=
    finite_sequence_range_embedding _ (source i) (target i)
  choose f hfmatch using hf
  have hsource (i:I):Finset.univ.image (source i)=(p i).support.toFinset:=
    simple_walk_length_embedding_support G (p i) (hp i) (p i).length rfl
  have htarget (i:I):Finset.univ.image (target i)=(q i).support.toFinset:=
    simple_walk_length_embedding_support H (q i) (hq i) (p i).length (hlen i)
  have hsrc:∀i∈(Finset.univ:Finset I),∀j∈(Finset.univ:Finset I),i≠j→
      Disjoint (Finset.univ.image (source i)) (Finset.univ.image (source j)):=by
    intro i _ j _ hij
    simpa only [hsource] using hpdis i j hij
  have htgt:∀i∈(Finset.univ:Finset I),∀j∈(Finset.univ:Finset I),i≠j→
      Disjoint (Set.range (f i)) (Set.range (f j)):=by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x ⟨xi,hxi⟩ ⟨xj,hxj⟩
    obtain ⟨ki,_,hki⟩:=Finset.mem_image.mp xi.property
    obtain ⟨kj,_,hkj⟩:=Finset.mem_image.mp xj.property
    have hi:x∈(q i).support.toFinset:=by
      rw [←htarget i]
      apply Finset.mem_image.mpr
      refine ⟨ki,Finset.mem_univ _,?_⟩
      have hh:=hfmatch i ki
      have heq:(⟨source i ki,Finset.mem_image.mpr ⟨ki,Finset.mem_univ _,rfl⟩⟩:{x // x∈Finset.univ.image (source i)})=xi:=Subtype.ext hki
      rw [heq] at hh
      exact hh.symm.trans hxi
    have hj:x∈(q j).support.toFinset:=by
      rw [←htarget j]
      apply Finset.mem_image.mpr
      refine ⟨kj,Finset.mem_univ _,?_⟩
      have hh:=hfmatch j kj
      have heq:(⟨source j kj,Finset.mem_image.mpr ⟨kj,Finset.mem_univ _,rfl⟩⟩:{x // x∈Finset.univ.image (source j)})=xj:=Subtype.ext hkj
      rw [heq] at hh
      exact hh.symm.trans hxj
    exact Finset.disjoint_left.mp (hqdis i j hij) hi hj
  obtain ⟨φ,hφ⟩:=disjoint_piece_embeddings_glue Finset.univ (fun i=>Finset.univ.image (source i)) hsrc f htgt
  have hunion:(Finset.univ.biUnion (fun i=>Finset.univ.image (source i)))=
      Finset.univ.biUnion (fun i=>(p i).support.toFinset):=by simp only [hsource]
  let embed' : {x // x∈Finset.univ.biUnion (fun i=>(p i).support.toFinset)}↪
      {x // x∈Finset.univ.biUnion (fun i=>Finset.univ.image (source i))}:=
    ⟨fun x=>⟨x.val,by rw [hunion];exact x.property⟩,by intro x y h;apply Subtype.ext;exact congrArg (fun (z:{x // x∈Finset.univ.biUnion (fun i=>Finset.univ.image (source i))})=>z.val) h⟩
  refine ⟨embed'.trans φ,?_⟩
  intro i k
  have hm:source i k∈Finset.univ.image (source i):=Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  change φ ⟨source i k,_⟩=target i k
  exact (hφ i (Finset.mem_univ _) (source i k) hm).trans (hfmatch i k)
end Oberwolfach
