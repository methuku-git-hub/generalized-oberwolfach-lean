module

public import Oberwolfach.PrescribedPathScheduleInfix

@[expose] public section
/-! The segment schedule covers exactly the edges of the ordered source path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

def prescribedOrderedPathEdges:List X→Finset (Sym2 X)
  | []=>∅
  | [_]=>∅
  | x::y::xs=>insert s(x,y) (prescribedOrderedPathEdges (y::xs))

theorem prescribed_path_edges_pivot (x:X) (post:List X):
    ∀ pre:List X,prescribedOrderedPathEdges (pre++x::post)=
      prescribedOrderedPathEdges (pre++[x])∪prescribedOrderedPathEdges (x::post) := by
  intro pre
  induction pre with
  | nil => simp [prescribedOrderedPathEdges]
  | cons a pre ih =>
    cases pre with
    | nil => simp [prescribedOrderedPathEdges]
    | cons b bs =>
      simp only [List.cons_append,prescribedOrderedPathEdges]
      simp only [List.cons_append] at ih
      rw [ih]
      exact (Finset.insert_union _ _ _).symm

def prescribedSegmentEdges (segments:List (PrescribedPathSegment X)):Finset (Sym2 X):=
  segments.toFinset.biUnion (fun seg=>prescribedOrderedPathEdges (prescribedPathSegmentVertices seg))

theorem prescribed_path_segments_edge_union (A:Finset X):
    ∀ (xs:List X) (left:Option X) (acc:List X),
      prescribedSegmentEdges (prescribedPathSegments A left acc xs)=
        prescribedOrderedPathEdges (left.toList++acc.reverse++xs) := by
  intro xs
  induction xs with
  | nil =>
    intro left acc
    simp [prescribedPathSegments,prescribedSegmentEdges,prescribedPathSegmentVertices]
  | cons x xs ih =>
    intro left acc
    by_cases hx:x∈A
    · simp only [prescribedPathSegments,hx,ite_true,prescribedSegmentEdges,List.toFinset_cons,Finset.biUnion_insert]
      rw [show (prescribedPathSegments A (some x) [] xs).toFinset.biUnion
          (fun seg=>prescribedOrderedPathEdges (prescribedPathSegmentVertices seg)) =
            prescribedOrderedPathEdges (x::xs) by simpa [prescribedSegmentEdges] using ih (some x) []]
      simpa [prescribedPathSegmentVertices,List.append_assoc] using
        (prescribed_path_edges_pivot x xs (left.toList++acc.reverse)).symm
    · simp only [prescribedPathSegments,hx,ite_false]
      simpa [List.reverse_cons,List.append_assoc] using ih left (x::acc)
end Oberwolfach
