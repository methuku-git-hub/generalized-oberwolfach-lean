module

public import Oberwolfach.PrescribedPathScheduleInfix
public import Oberwolfach.PrescribedAnchoredComponentSteps
public import Oberwolfach.ExtendingListFreePath
public import Mathlib.Data.List.Chain

@[expose] public section
/-! A contiguous scheduled segment inherits the source path's directed arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_path_from_chain (D:X→X→Prop) (F:SimpleGraph X) (forward:Bool):
    ∀ (as:List X) (a:X),DirectedPathFrom D F forward a as ↔
      List.IsChain (fun x y=>(if forward then D x y else D y x) ∧ ¬F.Adj x y) (a::as) := by
  intro as
  induction as with
  | nil => intro a;simp [DirectedPathFrom]
  | cons x xs ih =>
    intro a
    rw [List.isChain_cons_cons]
    simp only [DirectedPathFrom,ih,and_assoc]

theorem prescribed_path_through_chain (D:X→X→Prop) (F:SimpleGraph X):
    ∀ (as:List X) (a b:X),DirectedPathThrough D F a b as ↔
      List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (a::as++[b]) := by
  intro as
  induction as with
  | nil => intro a b;simp [DirectedPathThrough,List.isChain_cons_cons]
  | cons x xs ih =>
    intro a b
    simp only [List.cons_append,List.isChain_cons_cons,DirectedPathThrough,ih,and_assoc]

theorem prescribed_path_segment_inherits_chain (A:Finset X) (xs:List X)
    (R:X→X→Prop) (hchain:List.IsChain R xs)
    (seg:PrescribedPathSegment X) (hseg:seg∈prescribedPathSegments A none [] xs):
    List.IsChain R (prescribedPathSegmentVertices seg) := by
  apply hchain.infix
  simpa using prescribed_path_segment_infix A xs none [] seg hseg
theorem prescribed_path_segment_left_path (D:X→X→Prop) (F:SimpleGraph X)
    (seg:PrescribedPathSegment X) (a:X) (hl:seg.left=some a) (hr:seg.right=none)
    (h:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (prescribedPathSegmentVertices seg)):
    DirectedPathFrom D F true a seg.free := by
  apply (prescribed_path_from_chain D F true seg.free a).mpr
  simpa [prescribedPathSegmentVertices,hl,hr] using h

theorem prescribed_path_segment_two_path (D:X→X→Prop) (F:SimpleGraph X)
    (seg:PrescribedPathSegment X) (a b:X) (hl:seg.left=some a) (hr:seg.right=some b)
    (h:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (prescribedPathSegmentVertices seg)):
    DirectedPathThrough D F a b seg.free := by
  apply (prescribed_path_through_chain D F seg.free a b).mpr
  simpa [prescribedPathSegmentVertices,hl,hr] using h

theorem prescribed_path_segment_free_path (D:X→X→Prop) (F:SimpleGraph X)
    (seg:PrescribedPathSegment X) (hl:seg.left=none) (hr:seg.right=none) (hne:seg.free≠[])
    (h:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (prescribedPathSegmentVertices seg)):
    DirectedNonemptyPath D F true seg.free := by
  cases hs:seg.free with
  | nil => exact (hne hs).elim
  | cons a xs =>
    change DirectedPathFrom D F true a xs
    apply (prescribed_path_from_chain D F true xs a).mpr
    simpa [prescribedPathSegmentVertices,hl,hr,hs] using h

theorem prescribed_path_segment_right_path (D:X→X→Prop) (F:SimpleGraph X)
    (seg:PrescribedPathSegment X) (b:X) (hl:seg.left=none) (hr:seg.right=some b)
    (h:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (prescribedPathSegmentVertices seg)):
    DirectedPathFrom D F false b seg.free.reverse := by
  apply (prescribed_path_from_chain D F false seg.free.reverse b).mpr
  have hf:List.IsChain (fun x y=>D x y ∧ ¬F.Adj y x) (seg.free++[b]):=by
    have hh:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (seg.free++[b]):=by
      simpa [prescribedPathSegmentVertices,hl,hr] using h
    exact hh.imp (by intro x y hxy;exact ⟨hxy.1,by simpa [SimpleGraph.adj_comm] using hxy.2⟩)
  have hv:=List.isChain_reverse.mpr hf
  simpa [List.reverse_append] using hv
end Oberwolfach
