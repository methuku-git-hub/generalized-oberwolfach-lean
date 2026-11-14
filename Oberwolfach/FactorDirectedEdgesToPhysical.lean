module

public import Oberwolfach.FactorComponentsAllCycles
public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! The physical edge underlying each arc in an ordered walk is a walk edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

theorem directed_path_edge_is_physical:
    ∀ (xs:List V) (x y:V), (x,y)∈prescribedDirectedPathEdges xs →
      s(x,y)∈prescribedOrderedPathEdges xs := by
  intro xs
  induction xs with
  | nil => intro x y he; simp [prescribedDirectedPathEdges] at he
  | cons a xs ih =>
    cases xs with
    | nil => intro x y he; simp [prescribedDirectedPathEdges] at he
    | cons b bs =>
      intro x y he
      simp only [prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at he
      simp only [prescribedOrderedPathEdges,Finset.mem_insert]
      rcases he with ⟨rfl,rfl⟩|he
      · exact Or.inl rfl
      · exact Or.inr (ih x y he)
end Oberwolfach
