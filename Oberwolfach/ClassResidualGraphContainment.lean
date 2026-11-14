module

public import Oberwolfach.ClassRequiredGraphContainment

@[expose] public section
/-! The unused inner graph of the regularised class is contained in the
ambient residual graph used in the common-event estimates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_residual_graph_le_sampled
    {V:Type} [Fintype V] [LinearOrder V]
    (P S₀ S Used Sel:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (D:V→V→Prop)
    (hSP:S≤P):
    spanningRestriction (S\Used) I\
      longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y) ≤
    spanningRestriction (P\Used) I\
      longRequiredPhysicalGraph P (S₀\Used) Sel π d I D (fun x y=>Used.Adj x y):=by
  intro x y h
  have hi:=(spanningRestriction_adj _ _ _ _).mp h.1
  have hs:S.Adj x y:=hi.1.1
  have hsel:Sel.Adj x y:=by
    by_contra hnot
    apply h.2
    apply Or.inl
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨⟨hi.1,hnot⟩,hi.2⟩
  constructor
  · exact (spanningRestriction_adj _ _ _ _).mpr ⟨⟨hSP hs,hi.1.2⟩,hi.2⟩
  · intro hk
    rcases (show (spanningRestriction ((S₀\Used)\Sel) I).Adj x y ∨
      (longCloseRequiredGraph P π d D (fun x y=>Used.Adj x y)).Adj x y from hk) with hk|hk
    · exact ((spanningRestriction_adj _ _ _ _).mp hk).1.2 hsel
    · apply h.2
      exact Or.inr ⟨hs,hk.2⟩
end Oberwolfach
