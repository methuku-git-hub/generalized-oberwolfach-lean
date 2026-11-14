module

public import Oberwolfach.LongReservedSimpleWalkEmbeddingPoly

@[expose] public section
/-! Choose a reserved partial embedding for every factor from its own
matching family of disjoint target walks. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_factor_family_to_disjoint_walks
    {X W U:Type*} [Fintype X] [DecidableEq X] [DecidableEq W]
    (F:U→SimpleGraph X) (hF:∀u,(F u).IsRegularOfDegree 2) (H:SimpleGraph W)
    (I J:U→Type*) [∀u,Fintype (I u)] [∀u,Fintype (J u)]
    (components:∀u,I u↪(F u).ConnectedComponent)
    (e:∀u (i:I u),SimpleGraph.cycleGraph (Fintype.card (components u i)) ≃g (components u i).toSimpleGraph)
    (c d:ℕ) (t:∀u,J u→ℕ) (ht:∀u j,t u j≤d)
    (hcapacity:∀u,Fintype.card (J u)≤∑i:I u,Fintype.card (components u i)/(c*d+5))
    (start finish:∀u,J u→W) (q:∀u (j:J u),H.Walk (start u j) (finish u j))
    (hq:∀u j,(q u j).IsPath) (hlen:∀u j,(q u j).length=c*t u j)
    (hqdis:∀u (j l:J u),j≠l→Disjoint (q u j).support.toFinset (q u l).support.toFinset):
    ∃inner:∀u (j:J u),Fin (c*t u j+1)↪X,
    ∃φ:∀u,{x // x∈Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner u j))}↪W,
      (∀u (j:J u) (k:Fin (c*t u j+1)),
        φ u ⟨inner u j k,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=
          simpleWalkLengthEmbedding H (q u j) (hq u j) (c*t u j) (hlen u j) k) ∧
      (∀u x y,(F u).Adj x.val y.val→H.Adj (φ u x) (φ u y)):=by
  classical
  have hexists (u:U):∃inner:∀j:J u,Fin (c*t u j+1)↪X,
      ∃φ:{x // x∈Finset.univ.biUnion (fun j:J u=>Finset.univ.image (inner j))}↪W,
        (∀(j:J u) (k:Fin (c*t u j+1)),
          φ ⟨inner j k,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=
            simpleWalkLengthEmbedding H (q u j) (hq u j) (c*t u j) (hlen u j) k) ∧
        (∀x y,(F u).Adj x.val y.val→H.Adj (φ x) (φ y)):=by
    obtain ⟨index,ext,inner,hext,hinner,hcomponents,hdis,hpaths,hmap⟩:=
      long_reserved_paths_to_disjoint_simple_walks_poly (F u) (hF u) (components u) (e u) c d (t u) (ht u) (hcapacity u)
    obtain ⟨φ,hmatch,hgraph⟩:=hmap W H (start u) (finish u) (q u) (hq u) (hlen u) (hqdis u)
    exact ⟨inner,φ,hmatch,hgraph⟩
  choose inner φ hmatch hgraph using hexists
  exact ⟨inner,φ,hmatch,hgraph⟩
end Oberwolfach
