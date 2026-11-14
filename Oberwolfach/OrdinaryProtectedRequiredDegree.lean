module

public import Oberwolfach.OrdinaryProtectedRequiredEdges
public import Oberwolfach.OrdinaryLostEdgesEditDegree
public import Oberwolfach.ColourReorientation

@[expose] public section
/-! The extra required and deleted edges inside the protected inner set cost
at most its size per vertex, in addition to the original edit and reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_spanning_restriction_degree_card
    (G:SimpleGraph V) (I:Finset V) (v:V):
    (spanningRestriction G I).degree v≤I.card:=by
  have hsub:(spanningRestriction G I).neighborFinset v⊆I:=by
    intro w hw
    exact ((spanningRestriction_adj G I v w).mp (((spanningRestriction G I).mem_neighborFinset v w).mp hw)).2.2
  have hh:=Finset.card_le_card hsub
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh

theorem ordinary_protected_required_degree_bounds
    (Target Sample Reference Protect:SimpleGraph V) (Inner:Finset V) (b a:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)
    (hProtect:∀v,(Protect.degree v:ℝ)≤a):
    (∀v,((ordinaryProtectedRequired Target Sample Reference Inner).degree v:ℝ)≤b+Inner.card) ∧
    (∀v,((ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v:ℝ)≤b+a+Inner.card):=by
  have hAdded:=added_graph_degree_le_symmetric_edit Target Sample b hEdit
  have hLost:=lost_graph_degree_le_symmetric_edit Target Sample b hEdit
  constructor
  · intro v
    have hsup:=graph_sup_degree_le (Target\Sample) (spanningRestriction (Target\Reference) Inner) v
    have hs:( (spanningRestriction (Target\Reference) Inner).degree v:ℝ)≤Inner.card:=by
      exact_mod_cast ordinary_spanning_restriction_degree_card (Target\Reference) Inner v
    have hc:((ordinaryProtectedRequired Target Sample Reference Inner).degree v:ℝ)≤
        ((Target\Sample).degree v:ℝ)+(spanningRestriction (Target\Reference) Inner).degree v:=by
      simp only [←SimpleGraph.ncard_neighborSet] at hsup ⊢
      exact_mod_cast hsup
    linarith [hAdded v]
  · intro v
    have hsup₁:=graph_sup_degree_le (Sample\Target) Protect v
    have hsup₂:=graph_sup_degree_le ((Sample\Target)⊔Protect) (spanningRestriction (Sample\Reference) Inner) v
    have hs:((spanningRestriction (Sample\Reference) Inner).degree v:ℝ)≤Inner.card:=by
      exact_mod_cast ordinary_spanning_restriction_degree_card (Sample\Reference) Inner v
    have hc₁:(((Sample\Target)⊔Protect).degree v:ℝ)≤((Sample\Target).degree v:ℝ)+(Protect.degree v:ℝ):=by
      simp only [←SimpleGraph.ncard_neighborSet] at hsup₁ ⊢
      exact_mod_cast hsup₁
    have hc₂:((ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v:ℝ)≤
        (((Sample\Target)⊔Protect).degree v:ℝ)+(spanningRestriction (Sample\Reference) Inner).degree v:=by
      simp only [←SimpleGraph.ncard_neighborSet] at hsup₂ ⊢
      exact_mod_cast hsup₂
    linarith [hLost v,hProtect v]
end Oberwolfach
