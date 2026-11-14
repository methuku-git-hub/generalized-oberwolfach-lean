module

public import Oberwolfach.MarkedFiniteDeletionGraphBounds

@[expose] public section
/-! Translate the correction's endpoint counts into degree bounds for the
physical deletion graphs used by robustness hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_correction_physical_graph_degrees
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (δ:ℝ) (hδ:0≤δ)
    (hA:∀v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤δ)
    (hV:∀v,((S.filter (fun z=>v=z.1)).card:ℝ)≤δ)
    (hU:∀u,((S.filter (fun z=>u=z.2)).card:ℝ)≤δ):
    (∀v,((physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))).degree v:ℝ)≤2*δ) ∧
    (∀z,((markedFiniteSpokeGraph S).degree z:ℝ)≤δ):=by
  have hArc (v:V):((A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)).card:ℝ)≤2*δ:=by
    let R:=fun v a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a
    have hsub:A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)⊆
        A.filter (R v)∪A.filter (R (π.symm v)):=by
      intro a ha
      obtain ⟨hmem,hi⟩:=Finset.mem_filter.mp ha
      cases a with
      | inl a=>
        apply Finset.mem_union.mpr;left
        exact Finset.mem_filter.mpr ⟨hmem,by simpa only [R,markedPhysicalEdge,Finset.mem_insert,Finset.mem_singleton,Sum.elim_inl] using hi⟩
      | inr a=>
        have hh:v=ktail a∨v=π (khead a):=by simpa only [markedPhysicalEdge,Sum.elim_inr,Finset.mem_insert,Finset.mem_singleton] using hi
        rcases hh with ht|hh
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hmem,Or.inl ht⟩))
        · apply Finset.mem_union.mpr;right
          apply Finset.mem_filter.mpr;refine ⟨hmem,Or.inr ?_⟩
          change π.symm v=khead a
          rw [hh,π.symm_apply_apply]
    have hc:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hr:=Nat.cast_le (α:=ℝ).mpr hc
    simp only [Nat.cast_add] at hr
    linarith only [hr,hA v,hA (π.symm v)]
  constructor
  · intro v
    exact (Nat.cast_le.mpr (finite_physical_arc_graph_degree tail head ktail khead π A v)).trans (hArc v)
  · intro z
    cases z with
    | inl v=>
      have hv:=((finite_spoke_graph_degree_counts S).1 v)
      have hh:((S.filter (fun z=>z.1=v)).card:ℝ)≤δ:=by simpa only [eq_comm] using hV v
      exact (Nat.cast_le.mpr hv).trans hh
    | inr u=>
      have hu:=((finite_spoke_graph_degree_counts S).2 u)
      have hh:((S.filter (fun z=>z.2=u)).card:ℝ)≤δ:=by simpa only [eq_comm] using hU u
      exact (Nat.cast_le.mpr hu).trans hh
end Oberwolfach
