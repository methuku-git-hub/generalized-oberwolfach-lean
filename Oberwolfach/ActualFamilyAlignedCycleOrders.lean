module

public import Oberwolfach.FactorOrientationFromSourcePieces

@[expose] public section
/-! Choose all source cycle orders after fixing the source-piece orientation
and before selecting the residual data. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_family_aligned_cycle_orders
    {U:Type} [Fintype U] [DecidableEq U] {X:U→Type}
    [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (F:∀w,SimpleGraph (X w)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (D:∀w,X w→X w→Prop) (orig:∀w,List (PrescribedSourcePiece (X w)))
    (hpair:∀w,(orig w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hcycles:∀w p,p∈orig w→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D w))
    (hwhole:∀w,sourcePieceVerticesUnion (orig w)=Finset.univ ∧ sourcePieceEdgesUnion (orig w)=(F w).edgeFinset)
    (hD:∀w x y,D w x y↔(x,y)∈sourcePieceArcsUnion (orig w)):
    ∃e:∀w (C:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
      ∀w x,D w x (factorCycleOrientation (F w) (e w) x):=by
  classical
  have hex (w:U):∃e:∀C:(F w).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
      ∀x,D w x (factorCycleOrientation (F w) e x):=by
    apply factor_cycle_orders_align_with_source_pieces (F w) (hF w) (orig w) (D w) (hpair w) ?_ (hwhole w).2 (hD w)
    intro p hp
    obtain ⟨a,xs,rfl,hv⟩:=hcycles w p hp
    exact hv
  choose e he using hex
  exact ⟨e,he⟩
end Oberwolfach
