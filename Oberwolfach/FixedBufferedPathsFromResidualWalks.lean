module

public import Oberwolfach.BufferedPathBoundaryCompletion
public import Oberwolfach.BufferedPathInteriorCompletion
public import Oberwolfach.BufferedPathFamilyTargetEmbedding
public import Oberwolfach.BufferedEmbeddingWalkEdgeCoverage
public import Oberwolfach.PartialFactorWalkEdgeDisjointnessPoly
public import Oberwolfach.SimpleWalkLengthEmbedding

@[expose] public section
/-! Reconstruct partial factor maps on already chosen buffered source paths,
using the disjoint residual walks without choosing new source blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixed_buffered_paths_from_residual_walks
    {X V U:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    {J:U→Type} [∀u,Fintype (J u)] [∀u,DecidableEq (J u)]
    (F:U→SimpleGraph X) (hF:∀u,(F u).IsRegularOfDegree 2) (H:SimpleGraph V)
    (n:∀u,J u→ℕ) (ext:∀u j,Fin (n u j+5)↪X) (inner:∀u j,Fin (n u j+1)↪X)
    (hinner:∀u j p,inner u j p=ext u j ⟨p.val+2,by omega⟩)
    (hwalk:∀u j,∃p:(F u).Walk (ext u j 0) (ext u j (Fin.last (n u j+4))),
      p.length=n u j+4 ∧ p.support=List.ofFn (ext u j))
    (hdis:∀u j k,j≠k→Disjoint (Finset.univ.image (ext u j)) (Finset.univ.image (ext u k)))
    (start finish:∀u,J u→V) (q:∀u j,H.Walk (start u j) (finish u j))
    (hq:∀u j,(q u j).IsPath) (hlen:∀u j,(q u j).length=n u j)
    (hqdis:∀u j k,j≠k→Disjoint (q u j).support.toFinset (q u k).support.toFinset)
    (hqedge:∀u v,u≠v→∀j:J u,∀k:J v,Disjoint (walkPhysicalEdges (q u j)) (walkPhysicalEdges (q v k))):
    ∃fA:∀u,{x // x∈bufferedPathFullDomain (n u) (inner u)}↪V,
      (∀u j p,fA u ⟨inner u j p,buffered_path_vertex_mem_domain (n u) (inner u) j p⟩=
        simpleWalkLengthEmbedding H (q u j) (hq u j) (n u j) (hlen u j) p) ∧
      (∀u x y,(F u).Adj x.1 y.1→H.Adj (fA u x) (fA u y)) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
          ((F u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set X)) (fA u))
        (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n v) (inner v)}
          ((F v).induce (↑(bufferedPathFullDomain (n v) (inner v)):Set X)) (fA v))):=by
  classical
  have hex:∀u,∃f:{x // x∈bufferedPathFullDomain (n u) (inner u)}↪V,
      (∀j p,f ⟨inner u j p,buffered_path_vertex_mem_domain (n u) (inner u) j p⟩=
        simpleWalkLengthEmbedding H (q u j) (hq u j) (n u j) (hlen u j) p) ∧
      (∀x y,(F u).Adj x.1 y.1→H.Adj (f x) (f y)):=by
    intro u
    let target (j:J u):Fin (n u j+1)↪V:=simpleWalkLengthEmbedding H (q u j) (hq u j) (n u j) (hlen u j)
    have hadj:∀j (k:Fin (n u j)),H.Adj (target j ⟨k.val,by omega⟩) (target j ⟨k.val+1,by omega⟩):=by
      intro j k
      exact simple_walk_length_embedding_adjacent H (q u j) (hq u j) (n u j) (hlen u j) k
    have hmem (j:J u) {x:V}:x∈Set.range (target j)→x∈(q u j).support.toFinset:=by
      rintro ⟨k,rfl⟩
      rw [←simple_walk_length_embedding_support H (q u j) (hq u j) (n u j) (hlen u j)]
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    have htargetDis:∀j∈(Finset.univ:Finset (J u)),∀k∈(Finset.univ:Finset (J u)),j≠k→Disjoint (Set.range (target j)) (Set.range (target k)):=by
      intro j _ k _ hjk
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Finset.disjoint_left.mp (hqdis u j k hjk) (hmem j hx) (hmem k hy)
    obtain ⟨f,hmatch,hgraph⟩:=regular_two_buffered_path_family_target_embedding (F u) (hF u) H (n u) (ext u) (inner u)
      (hinner u) (hwalk u) (hdis u) Finset.univ target hadj htargetDis
    exact ⟨f,fun j p=>hmatch j (Finset.mem_univ _) p,hgraph⟩
  choose fA hmatch hgraph using hex
  let Domain (u:U):Type:={x // x∈bufferedPathFullDomain (n u) (inner u)}
  let Part (u:U):SimpleGraph (Domain u):=(F u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set X)
  have hcover:∀u (x y:Domain u),(Part u).Adj x y→
      ({fA u x,fA u y}:Finset V)∈Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)):=by
    intro u x y hxy
    exact regular_two_buffered_embedding_walk_edge_coverage (F u) (hF u) H (n u)
      (ext u) (inner u) (hinner u) (hwalk u) (hdis u) Finset.univ
      (start u) (finish u) (q u) (hq u) (hlen u) (fA u) (fun j _ p=>hmatch u j p) x y hxy
  have hedge:=partial_factor_edges_disjoint_of_walk_coverage_poly Domain Part (fun u=>fA u) J H start finish q hqedge hcover
  exact ⟨fA,hmatch,hgraph,hedge⟩
end Oberwolfach
