module

public import Oberwolfach.ResidualDirectedTerminalArc

@[expose] public section
/-! In a simple ordered cycle, the arc into its first vertex is the last arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

theorem directed_cycle_incoming_arc_is_closing (a u:V) (xs:List V)
    (hn:(a::xs).Nodup)
    (h:(u,a)∈prescribedDirectedPathEdges ((a::xs)++[a])):
    (a::xs).getLast?=some u := by
  have hna:a∉xs := (List.nodup_cons.mp hn).1
  cases xs with
  | nil =>
    simp [prescribedDirectedPathEdges] at h
    subst u
    simp
  | cons x xs =>
    have hxa:x≠a := by intro h;subst x;exact hna (by simp)
    simp only [List.cons_append,prescribedDirectedPathEdges,Finset.mem_insert,Prod.mk.injEq] at h
    rcases h with ⟨_,hxa'⟩|h
    · exact (hxa hxa'.symm).elim
    · have ht:=directed_arc_into_appended_terminal (x::xs) a u hna h
      simpa using ht
end Oberwolfach
