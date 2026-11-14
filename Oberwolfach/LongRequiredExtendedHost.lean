module

public import Oberwolfach.LongRequiredAvoidsUsedPacking

@[expose] public section
/-! Add the required edges to the free directed host for prescribed pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_required_extended_host
    {V:Type} [Fintype V] [DecidableEq V]
    (P P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (D Dfree:V→V→Prop) (Pack:Finset (Sym2 V))
    (hP₀:P₀≤P\Used) (hPack:Pack⊆Used.edgeFinset)
    (hfree:∀x y,Dfree x y→P.Adj x y):
    let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d I D (fun x y=>Used.Adj x y)
    let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Kbad.Adj x y→Dstar x y ∨ Dstar y x) ∧
    (∀x y,Dstar x y→P.Adj x y) ∧ Disjoint Kbad.edgeFinset Pack:=by
  intro Kbad Dstar
  refine ⟨fun _ _ h=>Or.inl h,fun _ _ h=>Or.inl (Or.inr h),?_,?_⟩
  · intro x y h
    rcases h with h|h
    · exact hfree x y h
    · change (spanningRestriction (P₀\Sel) I ⊔ longCloseRequiredGraph P π d D (fun x y=>Used.Adj x y)).Adj x y at h
      simp only [SimpleGraph.sup_adj] at h
      rcases h with h|h
      · exact (hP₀ ((spanningRestriction_adj _ _ _ _).mp h).1.1).1
      · exact h.1
  · exact long_required_graph_avoids_used_packing P P₀ Sel Used π d I D Pack hP₀ hPack
end Oberwolfach
