module

public import Oberwolfach.FactorComponentsAllCycles

@[expose] public section
/-! Relate the source-piece path condition to explicit consecutive arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem directed_path_through_iff_chain (D:V→V→Prop) (F:SimpleGraph V):
    ∀ (xs:List V) (x y:V),
      DirectedPathThrough D F x y xs ↔
        List.IsChain (fun a b=>D a b ∧ ¬F.Adj a b) (x::xs++[y]) := by
  intro xs
  induction xs with
  | nil => intro x y; simp [DirectedPathThrough]
  | cons z zs ih =>
    intro x y
    simp only [DirectedPathThrough, List.cons_append, List.isChain_cons_cons]
    rw [ih z y]
    tauto

theorem directed_cycle_through_iff_chain (D:V→V→Prop) (F:SimpleGraph V)
    (x:V) (xs:List V):
    DirectedCycleThrough D F (x::xs) ↔
      List.IsChain (fun a b=>D a b ∧ ¬F.Adj a b) ((x::xs)++[x]) := by
  simpa [DirectedCycleThrough] using directed_path_through_iff_chain D F xs x x
end Oberwolfach
