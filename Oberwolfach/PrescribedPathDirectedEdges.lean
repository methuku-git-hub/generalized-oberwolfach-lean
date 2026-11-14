module

public import Oberwolfach.PrescribedPathScheduleInfix
public import Mathlib.Data.List.Chain

@[expose] public section
/-! Oriented edges of scheduled source paths, retaining their direction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

def prescribedDirectedPathEdges:List X→Finset (X×X)
  | []=>∅
  | [_]=>∅
  | x::y::xs=>insert (x,y) (prescribedDirectedPathEdges (y::xs))

theorem prescribed_directed_path_edges_pivot (x:X) (post:List X):
    ∀ pre:List X,prescribedDirectedPathEdges (pre++x::post)=
      prescribedDirectedPathEdges (pre++[x])∪prescribedDirectedPathEdges (x::post) := by
  intro pre
  induction pre with
  | nil => simp [prescribedDirectedPathEdges]
  | cons a pre ih =>
    cases pre with
    | nil => simp [prescribedDirectedPathEdges]
    | cons b bs =>
      simp only [List.cons_append,prescribedDirectedPathEdges]
      simp only [List.cons_append] at ih
      rw [ih]
      exact (Finset.insert_union _ _ _).symm

def prescribedSegmentDirectedEdges (segments:List (PrescribedPathSegment X)):Finset (X×X):=
  segments.toFinset.biUnion (fun seg=>prescribedDirectedPathEdges (prescribedPathSegmentVertices seg))

theorem prescribed_path_segments_directed_union (A:Finset X):
    ∀ (xs:List X) (left:Option X) (acc:List X),
      prescribedSegmentDirectedEdges (prescribedPathSegments A left acc xs)=
        prescribedDirectedPathEdges (left.toList++acc.reverse++xs) := by
  intro xs
  induction xs with
  | nil =>
    intro left acc
    simp [prescribedPathSegments,prescribedSegmentDirectedEdges,prescribedPathSegmentVertices]
  | cons x xs ih =>
    intro left acc
    by_cases hx:x∈A
    · simp only [prescribedPathSegments,hx,ite_true,prescribedSegmentDirectedEdges,List.toFinset_cons,Finset.biUnion_insert]
      rw [show (prescribedPathSegments A (some x) [] xs).toFinset.biUnion
          (fun seg=>prescribedDirectedPathEdges (prescribedPathSegmentVertices seg)) =
            prescribedDirectedPathEdges (x::xs) by simpa [prescribedSegmentDirectedEdges] using ih (some x) []]
      simpa [prescribedPathSegmentVertices,List.append_assoc] using
        (prescribed_directed_path_edges_pivot x xs (left.toList++acc.reverse)).symm
    · simp only [prescribedPathSegments,hx,ite_false]
      simpa [List.reverse_cons,List.append_assoc] using ih left (x::acc)

theorem prescribed_directed_edges_chain (R:X→X→Prop):
    ∀ xs:List X,List.IsChain R xs ↔ ∀ e∈prescribedDirectedPathEdges xs,R e.1 e.2 := by
  intro xs
  induction xs with
  | nil => simp [prescribedDirectedPathEdges]
  | cons x xs ih =>
    cases xs with
    | nil => simp [prescribedDirectedPathEdges]
    | cons y ys =>
      simp only [List.isChain_cons_cons,prescribedDirectedPathEdges,Finset.forall_mem_insert]
      exact and_congr_right (fun _=>ih)

theorem prescribed_empty_segment_directed_edges (A:Finset X) (seg:PrescribedPathSegment X)
    (hfree:seg.free=[])
    (hleft:∀ a,seg.left=some a→a∈A) (hright:∀ b,seg.right=some b→b∈A):
    ∀ e∈prescribedDirectedPathEdges (prescribedPathSegmentVertices seg),e.1∈A ∧ e.2∈A := by
  rcases seg with ⟨left,as,right⟩
  simp only at hfree
  subst as
  cases left with
  | none => cases right <;> simp [prescribedPathSegmentVertices,prescribedDirectedPathEdges]
  | some a =>
    cases right with
    | none => simp [prescribedPathSegmentVertices,prescribedDirectedPathEdges]
    | some b =>
      intro e he
      have he':e=(a,b):=by simpa [prescribedPathSegmentVertices,prescribedDirectedPathEdges] using he
      subst e
      exact ⟨hleft a rfl,hright b rfl⟩
theorem prescribed_directed_path_edge_endpoints:
    ∀ (xs:List X) (e:X×X),e∈prescribedDirectedPathEdges xs→e.1∈xs ∧ e.2∈xs := by
  intro xs
  induction xs with
  | nil => intro e he;simp [prescribedDirectedPathEdges] at he
  | cons x xs ih =>
    cases xs with
    | nil => intro e he;simp [prescribedDirectedPathEdges] at he
    | cons y ys =>
      intro e he
      simp only [prescribedDirectedPathEdges,Finset.mem_insert] at he
      rcases he with he|he
      · subst e;simp
      · have hh:=ih e he
        exact ⟨by simp [hh.1],by simp [hh.2]⟩
end Oberwolfach
