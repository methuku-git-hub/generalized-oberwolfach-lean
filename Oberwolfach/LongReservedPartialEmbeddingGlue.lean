module

public import Oberwolfach.LongReservedPrescribedSubwalks
public import Oberwolfach.BufferedWalkEmbeddingGlue

@[expose] public section
/-! Reserve the original prescribed factor paths and glue any compatible
local graph embeddings of those paths into one partial embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_paths_with_partial_embedding_glue
    {V I J:Type*} [Fintype V] [DecidableEq V] [Fintype I] [Fintype J]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent)
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (c d:ℕ) (t:J→ℕ) (ht:∀a,t a≤d)
    (hcapacity:Fintype.card J≤∑i:I,Fintype.card (components i)/(c*d+5)):
    ∃index:J↪LongReservedBlockIndex G components c d,
    ∃ext:∀a:J,Fin (c*t a+5)↪V,
    ∃inner:∀a:J,Fin (c*t a+1)↪V,
      (∀a,ext a=longReservedSigmaBlock G components c d e (index a) (t a) (ht a)) ∧
      (∀(a:J) (j:Fin (c*t a+1)),inner a j=ext a ⟨j.val+2,by omega⟩) ∧
      (∀a j,ext a j∈(components (index a).1).supp) ∧
      (∀a b:J,a≠b→Disjoint (Finset.univ.image (ext a)) (Finset.univ.image (ext b))) ∧
      (∀a:J,∃p:G.Walk (inner a ⟨0,by omega⟩) (inner a ⟨c*t a,by omega⟩),
        p.IsPath ∧ p.length=c*t a ∧ p.support=List.ofFn (inner a) ∧
        ∃q:G.Walk (ext a ⟨0,by omega⟩) (ext a ⟨c*t a+4,by omega⟩),
          q.IsPath ∧ q.length=c*t a+4 ∧ q.support=List.ofFn (ext a) ∧ p.IsSubwalk q) ∧
      ∀(W:Type) (H:SimpleGraph W)
        (f:∀a:J,{x // x∈Finset.univ.image (inner a)}↪W),
        (∀a b:J,a≠b→Disjoint (Set.range (f a)) (Set.range (f b)))→
        (∀a:J,∀x y (hx:x∈Finset.univ.image (inner a)) (hy:y∈Finset.univ.image (inner a)),
          G.Adj x y→H.Adj (f a ⟨x,hx⟩) (f a ⟨y,hy⟩))→
        ∃φ:{x // x∈Finset.univ.biUnion (fun a:J=>Finset.univ.image (inner a))}↪W,
          (∀a:J,∀x:V,∀hx:x∈Finset.univ.image (inner a),
            φ ⟨x,Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,hx⟩⟩=f a ⟨x,hx⟩) ∧
          (∀x y,G.Adj x.val y.val→H.Adj (φ x) (φ y)):=by
  classical
  obtain ⟨index,ext,inner,hext,hinner,hcomponents,hdis,hpaths⟩:=
    long_reserved_prescribed_subwalks G hG components e c d t ht hcapacity
  refine ⟨index,ext,inner,hext,hinner,hcomponents,hdis,hpaths,?_⟩
  intro W H f hf hlocal
  have hwalk:∀a:J,∃q:G.Walk (ext a ⟨0,by omega⟩) (ext a ⟨c*t a+4,by omega⟩),
      q.length=c*t a+4 ∧ q.support=List.ofFn (ext a):=by
    intro a
    obtain ⟨p,hppath,hplen,hpsupp,q,hqpath,hqlen,hqsupp,hsub⟩:=hpaths a
    exact ⟨q,hqlen,hqsupp⟩
  have hf':∀a∈(Finset.univ:Finset J),∀b∈(Finset.univ:Finset J),a≠b→Disjoint (Set.range (f a)) (Set.range (f b)):=by
    intro a ha b hb hab
    exact hf a b hab
  have hlocal':∀a∈(Finset.univ:Finset J),∀x y (hx:x∈Finset.univ.image (inner a)) (hy:y∈Finset.univ.image (inner a)),
      G.Adj x y→H.Adj (f a ⟨x,hx⟩) (f a ⟨y,hy⟩):=by
    intro a ha x y hx hy hxy
    exact hlocal a x y hx hy hxy
  obtain ⟨φ,hφ,hgraph⟩:=regular_two_buffered_walk_embeddings_glue (V:=V) (W:=W) (I:=J) G hG H (fun a:J=>c*t a)
    ext inner hinner hwalk hdis (Finset.univ:Finset J) f hf' hlocal'
  refine ⟨φ,?_,hgraph⟩
  intro a x hx
  exact hφ a (Finset.mem_univ _) x hx
end Oberwolfach
