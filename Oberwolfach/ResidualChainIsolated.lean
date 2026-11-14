module

public import Oberwolfach.ResidualSplitPathInfix

@[expose] public section
/-! An isolated vertex in an ordered graph path is its only vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem chain_with_isolated_vertex_singleton (H:SimpleGraph V):
    ∀ (xs:List V),List.IsChain H.Adj xs→∀ x∈xs,(∀ y,¬H.Adj x y)→xs=[x] := by
  intro xs
  induction xs with
  | nil => intro hc x hx;simp at hx
  | cons a xs ih =>
    cases xs with
    | nil =>
      intro hc x hx _
      have : x=a := by simpa using hx
      simp [this]
    | cons b bs =>
      intro hc x hx hisol
      have hc':H.Adj a b ∧ List.IsChain H.Adj (b::bs) := by simpa using hc
      simp only [List.mem_cons] at hx
      rcases hx with hxa|hxt
      · subst x
        exact (hisol b hc'.1).elim
      · have hxt':x∈b::bs := by simpa only [List.mem_cons] using hxt
        have ht:=ih hc'.2 x hxt' hisol
        have hbx:b=x := by
          have hh:=congrArg List.head? ht
          simpa using hh
        subst b
        exact (hisol a hc'.1.symm).elim
end Oberwolfach
