module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Split an ordered source path at its prescribed vertices, retaining the
prescribed boundary vertices of every intervening free run. Empty runs may
be discarded after the prescribed edges have been reserved. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure PrescribedPathSegment (X:Type) where
  left:Option X
  free:List X
  right:Option X

variable {X:Type} [DecidableEq X]

def prescribedPathSegments (A:Finset X):Option X→List X→List X→List (PrescribedPathSegment X)
  | left,acc,[]=>[⟨left,acc.reverse,none⟩]
  | left,acc,x::xs=>
    if x∈A then ⟨left,acc.reverse,some x⟩::prescribedPathSegments A (some x) [] xs
    else prescribedPathSegments A left (x::acc) xs

theorem prescribed_path_segments_free_vertices (A:Finset X):
    ∀ (xs:List X) (left:Option X) (acc:List X),
      (prescribedPathSegments A left acc xs).flatMap PrescribedPathSegment.free =
        acc.reverse++xs.filter (fun x=>x∉A) := by
  intro xs
  induction xs with
  | nil => intro left acc;simp [prescribedPathSegments]
  | cons x xs ih =>
    intro left acc
    by_cases hx:x∈A
    · simp [prescribedPathSegments,hx,ih]
    · simp [prescribedPathSegments,hx,ih,List.reverse_cons,List.append_assoc]
theorem prescribed_path_segment_free_mem (A:Finset X) (xs:List X)
    (seg:PrescribedPathSegment X) (hseg:seg∈prescribedPathSegments A none [] xs):
    ∀ x∈seg.free,x∈xs ∧ x∉A := by
  intro x hx
  have hm:x∈(prescribedPathSegments A none [] xs).flatMap PrescribedPathSegment.free:=by
    exact List.mem_flatMap.mpr ⟨seg,hseg,hx⟩
  simpa [prescribed_path_segments_free_vertices] using hm

theorem prescribed_path_segment_boundaries (A:Finset X):
    ∀ (xs:List X) (left:Option X) (acc:List X),
      (∀ y,left=some y→y∈A) →
      ∀ seg∈prescribedPathSegments A left acc xs,
        (∀ y,seg.left=some y→y∈A) ∧ (∀ y,seg.right=some y→y∈A) := by
  intro xs
  induction xs with
  | nil =>
    intro left acc hl seg hs
    simp only [prescribedPathSegments,List.mem_singleton] at hs
    subst seg
    exact ⟨hl,by simp⟩
  | cons x xs ih =>
    intro left acc hl seg hs
    by_cases hx:x∈A
    · simp only [prescribedPathSegments,hx,ite_true,List.mem_cons] at hs
      rcases hs with hs|hs
      · subst seg
        constructor
        · exact hl
        · intro y hy
          cases hy
          exact hx
      · exact ih (some x) [] (by intro y hy;cases hy;exact hx) seg hs
    · simp only [prescribedPathSegments,hx,ite_false] at hs
      exact ih left (x::acc) hl seg hs
theorem prescribed_path_segment_free_nodup (A:Finset X) (xs:List X) (hxs:xs.Nodup)
    (seg:PrescribedPathSegment X) (hseg:seg∈prescribedPathSegments A none [] xs):
    seg.free.Nodup := by
  have hf:(xs.filter (fun x=>x∉A)).Nodup:=hxs.filter _
  have hflat:(prescribedPathSegments A none [] xs).flatMap PrescribedPathSegment.free |>.Nodup:=by
    simpa [prescribed_path_segments_free_vertices] using hf
  exact (List.nodup_flatMap.mp hflat).1 seg hseg

theorem prescribed_path_segment_boundaries_distinct (A:Finset X):
    ∀ (xs:List X) (left:Option X) (acc:List X),xs.Nodup→
      (∀ y,left=some y→y∉xs) →
      ∀ seg∈prescribedPathSegments A left acc xs,
        ∀ a b,seg.left=some a→seg.right=some b→a≠b := by
  intro xs
  induction xs with
  | nil =>
    intro left acc hn hl seg hs a b ha hb
    simp only [prescribedPathSegments,List.mem_singleton] at hs
    subst seg
    simp at hb
  | cons x xs ih =>
    intro left acc hn hl seg hs a b ha hb
    have hnodup:xs.Nodup:=(List.nodup_cons.mp hn).2
    have hxnot:x∉xs:=(List.nodup_cons.mp hn).1
    by_cases hx:x∈A
    · simp only [prescribedPathSegments,hx,ite_true,List.mem_cons] at hs
      rcases hs with hs|hs
      · subst seg
        simp only at ha hb
        cases hb
        intro he
        subst a
        exact hl x ha (by simp)
      · exact ih (some x) [] hnodup (by intro y hy;cases hy;exact hxnot) seg hs a b ha hb
    · simp only [prescribedPathSegments,hx,ite_false] at hs
      apply ih left (x::acc) hnodup (by intro y hy hym;exact hl y hy (by simp [hym])) seg hs a b ha hb
end Oberwolfach
