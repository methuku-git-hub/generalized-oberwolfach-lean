module

public import Oberwolfach.PrescribedPieceArcPhysical
public import Oberwolfach.PrescribedPathScheduleChain

@[expose] public section
/-! Every listed oriented source-piece arc belongs to its source digraph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_piece_arc_source (p:PrescribedSourcePiece X) (D:X→X→Prop) (F:SimpleGraph X)
    (hp:p.Valid D F) (e:X×X) (he:e∈p.arcs):D e.1 e.2 := by
  cases p with
  | path xs =>
    have hh:=((prescribed_directed_edges_chain (fun x y=>D x y ∧ ¬F.Adj x y) xs).mp hp.2) e he
    exact hh.1
  | cycle a xs =>
    have hc:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) ((a::xs)++[a]):=
      (prescribed_path_through_chain D F xs a a).mp hp.2.2
    have hh:=((prescribed_directed_edges_chain (fun x y=>D x y ∧ ¬F.Adj x y) _).mp hc) e he
    exact hh.1
end Oberwolfach
