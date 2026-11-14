module

public import Oberwolfach.ActualFixedSourceLateComplementOriented
public import Oberwolfach.ResidualActualLateContinuationOriented

@[expose] public section
/-! Strengthen the continuation for the exact factor orientation that was
already selected, retaining physical orientations of the assigned edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem fixed_source_late_continuation_oriented
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (D:∀i,X i→X i→Prop) (orig:∀i,List (PrescribedSourcePiece (X i)))
    (hpair:∀i,(orig i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hcycles:∀i p,p∈orig i→∃a xs,p=.cycle a xs ∧ p.OriginalValid (D i))
    (hwhole:∀i,sourcePieceVerticesUnion (orig i)=Finset.univ ∧ sourcePieceEdgesUnion (orig i)=(F i).edgeFinset)
    (hD:∀i x y,D i x y↔(x,y)∈sourcePieceArcsUnion (orig i)):
    LateComplementContinuationOriented (V:=V) F D:=by
  exact actual_fixed_source_late_indices_complement_oriented (V:=V) F hF D orig hpair hcycles hwhole hD
end Oberwolfach
