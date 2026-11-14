module

public import Oberwolfach.OrdinaryProtectedRequiredEdges

@[expose] public section
/-! Quantitative comparison of the actual complement remainder with the
reference host, retaining separate edit, uncovered and used-reference costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_remainder_reference_edit_bound
    (Target Sample Reference Embedded:SimpleGraph V) (hRef:Reference≤Sample)
    (b κ loss:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)
    (hUncovered:∀v,(((Sample\Reference)\Embedded).degree v:ℝ)≤κ)
    (hUsed:∀v,((Reference⊓Embedded).degree v:ℝ)≤loss):
    ∀v,((Finset.univ.filter (fun w=>Xor ((Target\Embedded).Adj v w) (Reference.Adj v w))).card:ℝ)≤b+κ+loss:=by
  intro v
  let Change:=Finset.univ.filter (fun w=>Xor ((Target\Embedded).Adj v w) (Reference.Adj v w))
  let Edit:=Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))
  let Uncovered:=((Sample\Reference)\Embedded).neighborFinset v
  let Used:=(Reference⊓Embedded).neighborFinset v
  have hsub:Change⊆(Edit∪Uncovered)∪Used:=by
    intro w hw
    have hc:Xor ((Target\Embedded).Adj v w) (Reference.Adj v w):=(Finset.mem_filter.mp hw).2
    have href:Reference.Adj v w→Sample.Adj v w:=fun h=>hRef h
    have hlogic:Xor (Target.Adj v w) (Sample.Adj v w) ∨
        ((Sample.Adj v w ∧ ¬Reference.Adj v w) ∧ ¬Embedded.Adj v w) ∨
        (Reference.Adj v w ∧ Embedded.Adj v w):=by
      change Xor (Target.Adj v w ∧ ¬Embedded.Adj v w) (Reference.Adj v w) at hc
      simp only [Xor] at hc ⊢
      tauto
    rcases hlogic with he|hu|hr
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((((Sample\Reference)\Embedded).mem_neighborFinset v w).mpr hu))
    · exact Finset.mem_union_right _ (((Reference⊓Embedded).mem_neighborFinset v w).mpr hr)
  have hc:Change.card≤Edit.card+Uncovered.card+Used.card:=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc':(Change.card:ℝ)≤(Edit.card:ℝ)+(Uncovered.card:ℝ)+(Used.card:ℝ):=by exact_mod_cast hc
  have hU:(Uncovered.card:ℝ)≤κ:=by simpa only [Uncovered,SimpleGraph.card_neighborFinset_eq_degree] using hUncovered v
  have hR:(Used.card:ℝ)≤loss:=by simpa only [Used,SimpleGraph.card_neighborFinset_eq_degree] using hUsed v
  linarith [hEdit v]
end Oberwolfach
