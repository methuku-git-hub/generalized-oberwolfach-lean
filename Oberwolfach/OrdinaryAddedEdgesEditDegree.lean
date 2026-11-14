module

public import Oberwolfach.OrdinarySharedReferenceRobustness

@[expose] public section
/-! Every edge added relative to the sample is counted by the original
per-vertex symmetric-edit bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem added_graph_degree_le_symmetric_edit
    {V:Type} [Fintype V] [DecidableEq V]
    (S S₀:SimpleGraph V) (b:ℝ)
    (hedit:∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ)≤b):
    ∀x,((S\S₀).degree x:ℝ)≤b:=by
  intro x
  have hsub:(S\S₀).neighborFinset x⊆Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y)):=by
    intro y hy
    have hh:(S\S₀).Adj x y:=((S\S₀).mem_neighborFinset x y).mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (S.Adj x y ∧ ¬S₀.Adj x y) ∨ (S₀.Adj x y ∧ ¬S.Adj x y)
    exact Or.inl ⟨hh.1,hh.2⟩
  have hh:=Finset.card_le_card hsub
  have hh':(((S\S₀).degree x):ℝ)≤
      ((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ):=by exact_mod_cast hh
  exact hh'.trans (hedit x)
end Oberwolfach
