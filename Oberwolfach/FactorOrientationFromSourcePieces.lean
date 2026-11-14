module

public import Oberwolfach.ComponentCycleIsoFirstEdge
public import Oberwolfach.FactorOrientationAlignment
public import Oberwolfach.ActualSourceOrientationProperties

@[expose] public section
/-! Choose the actual factor cycle orders to agree with the source-piece
orientation fixed before residual embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_cycle_orders_align_with_source_pieces
    {X:Type} [Fintype X] [DecidableEq X] (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hEdges:sourcePieceEdgesUnion pieces=G.edgeFinset)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces):
    ∃ e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
      ∀x,D x (factorCycleOrientation G e x):=by
  classical
  obtain ⟨hcover,hin⟩:=actual_source_orientation_covers_and_has_unique_incoming G pieces D hpair hvalid hEdges hArcs
  have hex (C:G.ConnectedComponent):
      ∃e:SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
        D (e ⟨0,by have h:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1;omega⟩).val
          (e ⟨1,by have h:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1;omega⟩).val:=by
    have h3:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1
    obtain ⟨e₀⟩:=(component_regular_two_cycle_iso G hG C).2
    let z0:Fin (Fintype.card C):=⟨0,by omega⟩
    let z1:Fin (Fintype.card C):=⟨1,by omega⟩
    have hrot:finRotate (Fintype.card C) z0=z1:=by
      apply (fin_rotate_succ_iff h3 z0 z1).1
      simp only [z0,z1,Fin.val_mk,Nat.zero_add,Nat.mod_eq_of_lt (by omega : 1<Fintype.card C)]
    have hcycle:(SimpleGraph.cycleGraph (Fintype.card C)).Adj z0 z1:=by
      apply (cycleGraph_modular_adj (by omega) _ _).2
      exact Or.inl ((fin_rotate_succ_iff h3 z0 z1).2 hrot)
    have hadj:G.Adj (e₀ z0).val (e₀ z1).val:=(e₀.map_rel_iff.mpr hcycle)
    rcases hcover _ _ hadj with hforward | hreverse
    · exact ⟨e₀,hforward⟩
    · obtain ⟨e₁,he0,he1⟩:=component_cycle_iso_with_first_edge G hG C (e₀ z1) (e₀ z0) hadj.symm
      refine ⟨e₁,?_⟩
      simpa only [he0,he1] using hreverse
  choose e he using hex
  refine ⟨e,factor_orientation_aligns_from_component_edges G hG e D hcover hin ?_⟩
  intro C
  have h3:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1
  let z0:Fin (Fintype.card C):=⟨0,by omega⟩
  let z1:Fin (Fintype.card C):=⟨1,by omega⟩
  have hrot:finRotate (Fintype.card C) z0=z1:=by
    apply (fin_rotate_succ_iff h3 z0 z1).1
    simp only [z0,z1,Fin.val_mk,Nat.zero_add,Nat.mod_eq_of_lt (by omega : 1<Fintype.card C)]
  refine ⟨e C z0,?_⟩
  rw [factor_cycle_orientation_on_component G e C (e C z0)]
  simpa only [RelIso.symm_apply_apply,hrot] using he C
end Oberwolfach
