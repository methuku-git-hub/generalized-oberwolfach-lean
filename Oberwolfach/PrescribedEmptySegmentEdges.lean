module

public import Oberwolfach.PrescribedPathScheduleEdgeForms
public import Oberwolfach.PrescribedFamilyStateInitial
public import Mathlib.Data.List.Chain

@[expose] public section
/-! A segment with no free vertices contributes only an already prescribed
source edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_empty_segment_edges
    (Q F:SimpleGraph X) (A:Finset X) (D:X→X→Prop)
    (hDQ:∀ x y,D x y→Q.Adj x y) (seg:PrescribedPathSegment X)
    (hfree:seg.free=[])
    (hleft:∀ a,seg.left=some a→a∈A) (hright:∀ b,seg.right=some b→b∈A)
    (hchain:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (prescribedPathSegmentVertices seg)):
    prescribedOrderedPathEdges (prescribedPathSegmentVertices seg)⊆prescribedInducedSourceEdges Q A := by
  rcases seg with ⟨left,as,right⟩
  simp only at hfree
  subst as
  cases left with
  | none =>
    cases right <;> simp [prescribedPathSegmentVertices,prescribedOrderedPathEdges]
  | some a =>
    cases right with
    | none => simp [prescribedPathSegmentVertices,prescribedOrderedPathEdges]
    | some b =>
      have hc:List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) [a,b]:=by
        simpa [prescribedPathSegmentVertices] using hchain
      have hab:D a b:=((List.isChain_cons_cons.mp hc).1).1
      have ha:a∈A:=hleft a rfl
      have hb:b∈A:=hright b rfl
      intro e he
      have he':e=s(a,b):=by simpa [prescribedPathSegmentVertices,prescribedOrderedPathEdges] using he
      subst e
      apply Finset.mem_filter.mpr
      constructor
      · simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hDQ a b hab
      · intro x hx
        simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl|rfl <;> assumption
end Oberwolfach
