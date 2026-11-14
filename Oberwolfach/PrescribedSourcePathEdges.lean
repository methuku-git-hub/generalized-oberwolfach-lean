module

public import Oberwolfach.PrescribedPathPhysicalEdges
public import Oberwolfach.PrescribedOneSidedPhysicalEdges

@[expose] public section
/-! The edge set listed by a source path is contained in its source graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_two_ended_source_edges (D:X→X→Prop) (Q F:SimpleGraph X)
    (hDQ:∀ x y,D x y→Q.Adj x y) (b:X):
    ∀ as:List X,∀ a:X,DirectedPathThrough D F a b as→
      prescribedPathPhysicalEdges a b as⊆Q.edgeFinset := by
  intro as
  induction as with
  | nil =>
    intro a hp e he
    have he':e=s(a,b):=by simpa [prescribedPathPhysicalEdges] using he
    subst e
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hDQ a b hp.1
  | cons x xs ih =>
    intro a hp e he
    simp only [prescribedPathPhysicalEdges,Finset.mem_insert] at he
    rcases he with he|he
    · subst e
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hDQ a x hp.1
    · exact ih x hp.2.2 he

theorem prescribed_one_ended_source_edges (D:X→X→Prop) (Q F:SimpleGraph X)
    (hDQ:∀ x y,D x y→Q.Adj x y) (forward:Bool):
    ∀ as:List X,∀ a:X,DirectedPathFrom D F forward a as→
      prescribedOneSidedPhysicalEdges a as⊆Q.edgeFinset := by
  intro as
  induction as with
  | nil => intro a hp e he;simp [prescribedOneSidedPhysicalEdges] at he
  | cons x xs ih =>
    intro a hp e he
    simp only [prescribedOneSidedPhysicalEdges,Finset.mem_insert] at he
    rcases he with he|he
    · subst e
      have hadj:Q.Adj a x:=by
        cases forward with
        | false => exact (hDQ x a (by simpa using hp.1)).symm
        | true => exact hDQ a x (by simpa using hp.1)
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hadj
    · exact ih x hp.2.2 he
end Oberwolfach
