module

public import Oberwolfach.PrescribedPathSchedule
public import Mathlib.Data.List.Infix

@[expose] public section
/-! Every scheduled path is a contiguous portion of its source path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

def prescribedPathSegmentVertices (seg:PrescribedPathSegment X):List X:=
  seg.left.toList++seg.free++seg.right.toList

theorem prescribed_path_segment_infix (A:Finset X):
    ∀ (xs:List X) (left:Option X) (acc:List X)
      (seg:PrescribedPathSegment X),seg∈prescribedPathSegments A left acc xs→
      prescribedPathSegmentVertices seg <:+: (left.toList++acc.reverse++xs) := by
  intro xs
  induction xs with
  | nil =>
    intro left acc seg hs
    simp only [prescribedPathSegments,List.mem_singleton] at hs
    subst seg
    simp [prescribedPathSegmentVertices]
  | cons x xs ih =>
    intro left acc seg hs
    by_cases hx:x∈A
    · simp only [prescribedPathSegments,hx,ite_true,List.mem_cons] at hs
      rcases hs with hs|hs
      · subst seg
        refine ⟨[],xs,?_⟩
        simp [prescribedPathSegmentVertices,List.append_assoc]
      · have hi:=ih (some x) [] seg hs
        have hsuf:(x::xs) <:+: (left.toList++acc.reverse++x::xs):=by
          refine ⟨left.toList++acc.reverse,[],?_⟩
          simp [List.append_assoc]
        exact (by simpa using hi : prescribedPathSegmentVertices seg <:+: (x::xs)).trans hsuf
    · simp only [prescribedPathSegments,hx,ite_false] at hs
      have hi:=ih left (x::acc) seg hs
      simpa [List.reverse_cons,List.append_assoc] using hi
end Oberwolfach
