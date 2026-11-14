module

public import Oberwolfach.ResidualPieceMapUnions

@[expose] public section
/-! Transfer the ordered residual pieces to the type of surviving vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem source_pieces_on_surviving_subtype
    (R:Finset V) (D:V→V→Prop) (ps:List (PrescribedSourcePiece V))
    (hp:ps.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hv:∀p∈ps,p.Shape ∧ p.OriginalValid D)
    (hR:sourcePieceVerticesUnion ps=R):
    ∃ qs:List (PrescribedSourcePiece {x // x∈R}),
      qs.map (fun q=>q.map Subtype.val)=ps ∧
      qs.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀q∈qs,q.Shape ∧ q.OriginalValid (fun x y=>D x.1 y.1)) ∧
      sourcePieceVerticesUnion qs=Finset.univ := by
  have hsub:∀p∈ps,p.vertices.toFinset⊆R:=by
    intro p hp x hx
    rw [←hR]
    exact source_piece_vertex_mem_union ps p hp x (List.mem_toFinset.mp hx)
  obtain ⟨qs,hqs⟩:=source_piece_list_lift_to_vertex_subtype R ps hsub
  refine ⟨qs,hqs,?_,?_,?_⟩
  · rw [←hqs,List.pairwise_map] at hp
    apply hp.imp
    intro p q hpq
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx':x.1∈(p.map Subtype.val).vertices.toFinset:=by
      rw [prescribed_piece_map_vertices]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,List.mem_toFinset.mp hx,rfl⟩)
    have hy':x.1∈(q.map Subtype.val).vertices.toFinset:=by
      rw [prescribed_piece_map_vertices]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,List.mem_toFinset.mp hy,rfl⟩)
    exact (Finset.disjoint_left.mp hpq) hx' hy'
  · intro q hq
    apply subtype_piece_validity_reflected R q D
    apply (hv (q.map Subtype.val) ?_).2
    rw [←hqs]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  · have himage:(sourcePieceVerticesUnion qs).image Subtype.val=R:=by
      rw [←source_piece_map_vertices_union,hqs,hR]
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    have hx:x.1∈(sourcePieceVerticesUnion qs).image Subtype.val:=by rw [himage];exact x.2
    obtain ⟨y,hy,heq⟩:=Finset.mem_image.mp hx
    have :y=x:=Subtype.ext heq
    simpa [this] using hy
end Oberwolfach
