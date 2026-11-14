module

public import Oberwolfach.OrdinaryBoundaryExtensionsSurvivePacking
public import Oberwolfach.OrdinaryBoundaryHubPairRetention

@[expose] public section
/-! Every sampled two-spoke hub choice survives a packing that preserves
the reserved boundary and inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_retained_hub_subset_choices_survive_packing
    (Q Q':SimpleGraph V) (H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (Zfree:Finset U) (hfree:Zfree⊆Z)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (β b:ℝ)
    (hinner:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hreserve:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ))
    (hkeep:ordinaryPhysicalGraph Q H\C≤ordinaryPhysicalGraph Q' H')
    (hgood:∀a c,β≤((Zfree.filter (fun u=>H a u∧H c u)).card:ℝ)→
      b≤((retainedPatternSet (Zfree.filter (fun u=>H a u∧H c u)) (ordinaryBoundaryHubPairCoins a c) σ).card:ℝ))
    (hparent:∀a∉X,∀c∉X,Q'.Adj a c→β≤((Zfree.filter (fun u=>H a u∧H c u)).card:ℝ)):
    ∀a∉X,∀c∉X,Q'.Adj a c→b≤((Zfree.filter (fun u=>H' a u∧H' c u)).card:ℝ):=by
  intro a ha c hc hq
  let A:=retainedPatternSet (Zfree.filter (fun u=>H a u∧H c u)) (ordinaryBoundaryHubPairCoins a c) σ
  have hsub:A⊆Zfree.filter (fun u=>H' a u∧H' c u):=by
    intro u hu
    have hu':(u∈Zfree ∧ H a u∧H c u) ∧ ∀e∈ordinaryBoundaryHubPairCoins a c u,σ e=true:=by
      simpa [A,retainedPatternSet] using hu
    have hi:Sum.inr u∈ordinaryInnerVertices X Z:=by simpa [ordinaryInnerVertices_right] using hfree hu'.1.1
    have h1:σ s(Sum.inl a,Sum.inr u)=true:=hu'.2 _ (by simp [ordinaryBoundaryHubPairCoins])
    have h2:σ s(Sum.inl c,Sum.inr u)=true:=hu'.2 _ (by simp [ordinaryBoundaryHubPairCoins])
    have he1:=ordinary_sampled_inner_incident_edge_survives Q H X Z C σ hinner hreserve
      (Sum.inl a) (Sum.inr u) hu'.1.2.1 (Or.inr hi) h1
    have he2:=ordinary_sampled_inner_incident_edge_survives Q H X Z C σ hinner hreserve
      (Sum.inl c) (Sum.inr u) hu'.1.2.2 (Or.inr hi) h2
    exact Finset.mem_filter.mpr ⟨hu'.1.1,hkeep he1,hkeep he2⟩
  exact (hgood a c (hparent a ha c hc hq)).trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
end Oberwolfach
