module

public import Oberwolfach.LongReservedTargetPathEmbeddingPoly
public import Oberwolfach.SimpleWalkLengthEmbedding

@[expose] public section
/-! Map the original reserved factor paths to any equal-length family of
vertex-disjoint simple target walks. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_paths_to_disjoint_simple_walks_poly
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
      ∀(W:Type*) [DecidableEq W] (H:SimpleGraph W) (start finish:J→W)
        (q:∀a:J,H.Walk (start a) (finish a)) (hq:∀a,(q a).IsPath)
        (hlen:∀a,(q a).length=c*t a)
        (hqdis:∀a b:J,a≠b→Disjoint (q a).support.toFinset (q b).support.toFinset),
        ∃φ:{x // x∈Finset.univ.biUnion (fun a:J=>Finset.univ.image (inner a))}↪W,
          (∀a:J,∀k:Fin (c*t a+1),
            φ ⟨inner a k,Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=
              simpleWalkLengthEmbedding H (q a) (hq a) (c*t a) (hlen a) k) ∧
          (∀x y,G.Adj x.val y.val→H.Adj (φ x) (φ y)):=by
  classical
  obtain ⟨index,ext,inner,hext,hinner,hcomponents,hdis,hpaths,hmap⟩:=
    long_reserved_paths_to_disjoint_target_paths_poly G hG components e c d t ht hcapacity
  refine ⟨index,ext,inner,hext,hinner,hcomponents,hdis,hpaths,?_⟩
  intro W _ H start finish q hq hlen hqdis
  let target (a:J):Fin (c*t a+1)↪W:=simpleWalkLengthEmbedding H (q a) (hq a) (c*t a) (hlen a)
  have hadj:∀a:J,∀k:Fin (c*t a),H.Adj (target a ⟨k.val,by omega⟩) (target a ⟨k.val+1,by omega⟩):=by
    intro a k
    exact simple_walk_length_embedding_adjacent H (q a) (hq a) (c*t a) (hlen a) k
  have hmem (a:J) {x:W}:x∈Set.range (target a)→x∈(q a).support.toFinset:=by
    rintro ⟨k,rfl⟩
    rw [←simple_walk_length_embedding_support H (q a) (hq a) (c*t a) (hlen a)]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  have htargetDis:∀a b:J,a≠b→Disjoint (Set.range (target a)) (Set.range (target b)):=by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    exact Finset.disjoint_left.mp (hqdis a b hab) (hmem a hxa) (hmem b hxb)
  exact hmap W H target hadj htargetDis
end Oberwolfach
