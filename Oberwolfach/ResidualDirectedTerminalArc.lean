module

public import Oberwolfach.ResidualRetainedPathBlocks
public import Oberwolfach.PrescribedPathDirectedEdges

@[expose] public section
/-! On an ordered path whose terminal vertex does not occur earlier, the
only arc entering that vertex is its closing arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

theorem directed_arc_into_appended_terminal:
    ∀ (xs:List V) (a u:V),a∉xs→(u,a)∈prescribedDirectedPathEdges (xs++[a])→
      xs.getLast?=some u := by
  intro xs
  induction xs with
  | nil => intro a u _ h;simp [prescribedDirectedPathEdges] at h
  | cons x xs ih =>
    intro a u hna h
    have hxa:x≠a := by intro h;subst x;exact hna (by simp)
    have hna':a∉xs := fun h=>hna (by simp [h])
    cases xs with
    | nil =>
      simp [prescribedDirectedPathEdges] at h
      subst u
      simp
    | cons y ys =>
      have hya:y≠a := by intro h;subst y;exact hna (by simp)
      simp only [List.cons_append,prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at h
      rcases h with ⟨_,hay⟩|h
      · exact (hya hay.symm).elim
      · have ht:=ih a u hna' h
        simpa using ht
end Oberwolfach
