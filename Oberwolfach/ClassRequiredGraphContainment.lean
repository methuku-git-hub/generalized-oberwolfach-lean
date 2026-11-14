module

public import Oberwolfach.LongActualPhysicalGraphsInHost
public import Oberwolfach.LongPreparationPhysicalContainment

@[expose] public section
/-! Required edges in the actual class differ from the sampled-class required
edges only by class edges inserted during regularisation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_required_graph_le_sampled_with_insertions
    {V:Type} [Fintype V] [LinearOrder V]
    (P S₀ S Used Sel:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D:V→V→Prop)
    (hSP:S≤P):
    longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)≤
      longRequiredPhysicalGraph P (S₀\Used) Sel π d I D (fun x y=>Used.Adj x y) ⊔
        spanningRestriction (S\S₀) I:=by
  intro x y h
  rcases (show (spanningRestriction ((S\Used)\Sel) I).Adj x y ∨
    (longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y)).Adj x y from h) with hinner|hclose
  · have hi:=(spanningRestriction_adj _ _ _ _).mp hinner
    by_cases hS₀:S₀.Adj x y
    · apply Or.inl
      apply Or.inl
      apply (spanningRestriction_adj _ _ _ _).mpr
      exact ⟨⟨⟨hS₀,hi.1.1.2⟩,hi.1.2⟩,hi.2⟩
    · apply Or.inr
      apply (spanningRestriction_adj _ _ _ _).mpr
      exact ⟨⟨hi.1.1.1,hS₀⟩,hi.2⟩
  · apply Or.inl
    apply Or.inr
    exact ⟨hSP hclose.1,hclose.2⟩

theorem class_required_graph_in_class
    {V:Type} [Fintype V] [LinearOrder V] (S Used Sel:SimpleGraph V)
    (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D:V→V→Prop):
    longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)≤S:=by
  exact long_required_physical_graph_le_host S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    (by intro x y h;exact h.1)
end Oberwolfach
