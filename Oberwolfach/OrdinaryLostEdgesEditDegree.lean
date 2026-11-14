module

public import Oberwolfach.OrdinaryAddedEdgesEditDegree

@[expose] public section
/-! The same symmetric-edit bound controls both lost and added edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem lost_graph_degree_le_symmetric_edit
    {V:Type} [Fintype V] [DecidableEq V]
    (S S₀:SimpleGraph V) (b:ℝ)
    (hedit:∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ)≤b):
    ∀x,((S₀\S).degree x:ℝ)≤b:=by
  have hswap:∀x,Finset.univ.filter (fun y=>Xor (S₀.Adj x y) (S.Adj x y))=
      Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y)):=by
    intro x
    apply Finset.ext
    intro y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change ((S₀.Adj x y ∧ ¬S.Adj x y) ∨ (S.Adj x y ∧ ¬S₀.Adj x y)) ↔
      ((S.Adj x y ∧ ¬S₀.Adj x y) ∨ (S₀.Adj x y ∧ ¬S.Adj x y))
    tauto
  apply added_graph_degree_le_symmetric_edit S₀ S b
  intro x
  simpa only [hswap x] using hedit x
end Oberwolfach
