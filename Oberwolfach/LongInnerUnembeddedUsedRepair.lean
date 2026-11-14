module

public import Oberwolfach.GraphSelectionDegrees
public import Oberwolfach.EndpointIndexDeletion
public import Oberwolfach.LongRequiredAvoidsUsedPacking

@[expose] public section
/-! The matching may use inner edges that the old packing has not embedded.
Adding those edges to the required graph covers the entire nonselected inner
residual.  The additional graph is supported on the inner set and its cost is
bounded solely in terms of that set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_inner_unembedded_used_repair
    (S Sel Used Old K:SimpleGraph V) (I:Finset V)
    (hKold:∀x y,K.Adj x y→¬Old.Adj x y)
    (hKcover:∀x y,x∈I→y∈I→S.Adj x y→¬Sel.Adj x y→¬Used.Adj x y→K.Adj x y)
    (hUsedSel:∀x y,Used.Adj x y→¬Sel.Adj x y) :
    let Extra:=spanningRestriction (Used\Old) I
    let Kplus:=K⊔Extra
    (∀x y,Kplus.Adj x y→¬Old.Adj x y) ∧
    (∀x y,x∈I→y∈I→S.Adj x y→¬Sel.Adj x y→¬Old.Adj x y→Kplus.Adj x y) ∧
    (∀x y,Extra.Adj x y→¬Sel.Adj x y) ∧
    (∀v,Kplus.degree v≤K.degree v+I.card) ∧
    ((Extra.edgeFinset.card:ℝ)≤(I.card:ℝ)^2) := by
  intro Extra Kplus
  have hdeg:∀v,Extra.degree v≤I.card:=by
    intro v
    dsimp only [Extra]
    rw [spanningRestriction_degree]
    split_ifs with hv
    · exact Finset.card_le_card Finset.inter_subset_right
    · exact Nat.zero_le _
  have hrestrict:spanningRestriction Extra I=Extra:=by
    ext x y
    simp only [spanningRestriction_adj,Extra,and_assoc,and_self]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x y h
    simp only [Kplus,SimpleGraph.sup_adj] at h
    rcases h with hk|he
    · exact hKold x y hk
    · exact ((spanningRestriction_adj _ _ _ _).mp he).1.2
  · intro x y hx hy hs hsel hold
    by_cases hu:Used.Adj x y
    · simp only [Kplus,SimpleGraph.sup_adj]
      exact Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨⟨hu,hold⟩,hx,hy⟩)
    · simp only [Kplus,SimpleGraph.sup_adj]
      exact Or.inl (hKcover x y hx hy hs hsel hu)
  · intro x y he
    exact hUsedSel x y ((spanningRestriction_adj _ _ _ _).mp he).1.1
  · intro v
    exact (graph_degree_sup_le K Extra v).trans (Nat.add_le_add_left (hdeg v) _)
  · have h:=internal_graph_edge_count Extra I (I.card:ℝ) (fun v _=>by exact_mod_cast hdeg v)
    rw [hrestrict] at h
    simpa only [pow_two] using h
end Oberwolfach
