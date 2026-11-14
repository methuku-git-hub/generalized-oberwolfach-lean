module

public import Oberwolfach.ResidualPieceUnions

@[expose] public section
/-! Assemble retained pieces from a vertex-disjoint family of directed cycles. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem retained_cycle_family_source_pieces (H:SimpleGraph V) (R:Finset V)
    (hisol:∀x,x∉R→∀y,¬H.Adj x y) (D:V→V→Prop):
    ∀ orig:List (PrescribedSourcePiece V),
    orig.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)→
    (∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D)→
    ∃ ps:List (PrescribedSourcePiece V),
      ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈ps,p.OriginalValid D) ∧
      (∀x,x∈sourcePieceVerticesUnion ps ↔ x∈sourcePieceVerticesUnion orig ∧ x∈R) ∧
      sourcePieceEdgesUnion ps=(sourcePieceEdgesUnion orig).filter (fun e=>e∈H.edgeFinset) := by
  intro orig
  induction orig with
  | nil =>
    intro _ _
    refine ⟨[],by simp,by simp,?_,?_⟩
    · intro x;simp [sourcePieceVerticesUnion]
    · simp [sourcePieceEdgesUnion]
  | cons p orig ih =>
    intro hpair hvalid
    have hpairs:=List.pairwise_cons.mp hpair
    obtain ⟨a,xs,hp,hcycle⟩:=hvalid p (by simp)
    subst p
    obtain ⟨front,hfront,hfrontvalid,hfrontV,hfrontE⟩:=
      retained_cycle_source_pieces H R hisol D a xs hcycle.1 hcycle.2.1 hcycle.2.2
    have htailvalid:∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D := by
      intro q hq
      exact hvalid q (by simp [hq])
    obtain ⟨tail,htail,htailvalid',htailV,htailE⟩:=ih hpairs.2 htailvalid
    refine ⟨front++tail,?_,?_,?_,?_⟩
    · rw [List.pairwise_append]
      refine ⟨hfront,htail,?_⟩
      intro p hp q hq
      apply Finset.disjoint_left.mpr
      intro x hxp hxq
      have hxfront:x∈sourcePieceVerticesUnion front := source_piece_vertex_mem_union front p hp x (List.mem_toFinset.mp hxp)
      have hxtail:x∈sourcePieceVerticesUnion tail := source_piece_vertex_mem_union tail q hq x (List.mem_toFinset.mp hxq)
      have hxa:x∈a::xs := (hfrontV x).1 hxfront |>.1
      have hxorig:x∈sourcePieceVerticesUnion orig := (htailV x).1 hxtail |>.1
      obtain ⟨q',hq',hxq'⟩:=Finset.mem_biUnion.mp hxorig
      have hdis:=hpairs.1 q' (List.mem_toFinset.mp hq')
      exact Finset.disjoint_left.mp hdis (List.mem_toFinset.mpr hxa) hxq'
    · intro q hq
      rcases List.mem_append.mp hq with hq|hq
      · exact hfrontvalid q hq
      · exact htailvalid' q hq
    · intro x
      rw [source_piece_vertices_union_append]
      have horig:sourcePieceVerticesUnion (.cycle a xs::orig) =
          (a::xs).toFinset∪sourcePieceVerticesUnion orig := by
        simp [sourcePieceVerticesUnion,PrescribedSourcePiece.vertices]
      rw [horig]
      simp only [Finset.mem_union,List.mem_toFinset,hfrontV x,htailV x]
      tauto
    · rw [source_piece_edges_union_append,hfrontE,htailE]
      have horig:sourcePieceEdgesUnion (.cycle a xs::orig) =
          prescribedOrderedPathEdges ((a::xs)++[a])∪sourcePieceEdgesUnion orig := by
        simp [sourcePieceEdgesUnion,PrescribedSourcePiece.edges]
      rw [horig,Finset.filter_union]
end Oberwolfach
