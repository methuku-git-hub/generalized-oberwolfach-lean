module

public import Oberwolfach.PrescribedPathPhysicalEdges
public import Oberwolfach.PrescribedOneSidedPhysicalEdges

@[expose] public section
/-! Every physical edge of an ordered path has both endpoints in its listed
source vertices, including the prescribed boundaries. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_two_ended_edge_endpoints (b:X):
    ∀ as:List X,∀ a:X,∀ e∈prescribedPathPhysicalEdges a b as,
      ∀ x∈e.toFinset,x∈insert a (insert b as.toFinset) := by
  intro as
  induction as with
  | nil =>
    intro a e he x hx
    have he':e=s(a,b):=by simpa [prescribedPathPhysicalEdges] using he
    subst e
    simpa using hx
  | cons z zs ih =>
    intro a e he x hx
    simp only [prescribedPathPhysicalEdges,Finset.mem_insert] at he
    rcases he with he|he
    · subst e
      have hx':x=a ∨ x=z:=by simpa using hx
      simp only [List.toFinset_cons,Finset.mem_insert]
      tauto
    · have hh:=ih z e he x hx
      simp only [List.toFinset_cons,Finset.mem_insert] at hh ⊢
      tauto

theorem prescribed_one_ended_edge_endpoints:
    ∀ as:List X,∀ a:X,∀ e∈prescribedOneSidedPhysicalEdges a as,
      ∀ x∈e.toFinset,x∈insert a as.toFinset := by
  intro as
  induction as with
  | nil => intro a e he;simp [prescribedOneSidedPhysicalEdges] at he
  | cons z zs ih =>
    intro a e he x hx
    simp only [prescribedOneSidedPhysicalEdges,Finset.mem_insert] at he
    rcases he with he|he
    · subst e
      have hx':x=a ∨ x=z:=by simpa using hx
      simp only [List.toFinset_cons,Finset.mem_insert]
      tauto
    · have hh:=ih z e he x hx
      simp only [List.toFinset_cons,Finset.mem_insert] at hh ⊢
      tauto
end Oberwolfach
