module

public import Oberwolfach.ResidualCutCyclePaths

@[expose] public section
/-! Every vertex of a nontrivial ordered path is incident with a path edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

theorem ordered_path_vertex_incident_edge:
    ∀ (xs:List V) (x:V),2≤xs.length→x∈xs→
      ∃ y,s(x,y)∈prescribedOrderedPathEdges xs := by
  intro xs
  induction xs with
  | nil => intro x hlen;simp at hlen
  | cons a xs ih =>
    cases xs with
    | nil => intro x hlen;simp at hlen
    | cons b bs =>
      intro x hlen hx
      simp only [List.mem_cons] at hx
      rcases hx with hxa|hxb|hrest
      · subst x
        exact ⟨b,by simp [prescribedOrderedPathEdges]⟩
      · subst x
        refine ⟨a,?_⟩
        simp [prescribedOrderedPathEdges,Sym2.eq_swap]
      · have ht:2≤(b::bs).length := by
          cases bs with
          | nil => simp at hrest
          | cons z zs => simp
        obtain ⟨y,hy⟩:=ih x ht (by simp [hrest])
        exact ⟨y,by simp [prescribedOrderedPathEdges,hy]⟩
end Oberwolfach
