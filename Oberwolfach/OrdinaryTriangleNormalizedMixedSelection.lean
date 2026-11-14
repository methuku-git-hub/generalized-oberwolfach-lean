module

public import Oberwolfach.OrdinaryNormalizedHubFactorEventLift
public import Oberwolfach.EndpointTriangleNormalizedFactorFamily
public import Oberwolfach.MixedFreshBoundaryEventDefinition

@[expose] public section
/-! A hub event and an endpoint event on the same physical coins can be
combined by the mixed avoiding selection. The two input tolerances are
chosen on the actual inner domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_normalized_mixed_selection
    (ρ:ℝ) (hρ:0<ρ):∃N:ℕ,
    ∀(V U K:Type) [Fintype V] [Fintype U] [Fintype K]
      [DecidableEq V] [DecidableEq U] [DecidableEq K],
    ∀(Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
      (P B:SimpleGraph (V⊕U)) (S T:K→Finset (V⊕U))
      (g:K→(V⊕U)↪Sym2 (V⊕U)) (hST:∀k,Disjoint (S k) (T k))
      (p ζh ζe:ℝ) (hp:0≤p) (σ:Sym2 (V⊕U)→Bool),
    N≤Fintype.card V→
    (spanningRestriction Q A).map (Function.Embedding.inl:V↪V⊕U)≤P→
    OrdinaryNormalizedHubFactorEvent 2 Q F H A Z p ζh σ→
    EndpointTriangleNormalizedFactorEvent P B S T g p ζe σ→
    MixedFreshBoundaryAvoidingEvent p ρ (min ζh ζe) (spanningRestriction Q A) F P B
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z A) S T
      (fun j=>hubSpokeCoin j.val) g hST σ:=by
  obtain ⟨N,hN⟩:=select_mixed_boundary_factors_avoiding ρ hρ
  refine ⟨N,?_⟩
  intro V U K _ _ _ _ _ _ Q F H A Z P B S T g hST p ζh ζe hp σ hn hQ hh he
  intro Y D K₀ δ hK₀ hYT hdiv hDU hratio hchangeY hchangeD hinter hmem hbudgetY hbudgetD
  apply hN V (V⊕U) {u:U // u∉Z} K (by have hh:=Fintype.card_le_of_injective (Function.Embedding.inl:V↪V⊕U) Sum.inl_injective; omega) 3 (spanningRestriction Q A) F P B
    (Function.Embedding.inl:V↪V⊕U) hQ (ordinaryBoundaryHubSet H Z A) Y S T D hST K₀ δ
    hK₀ hinter hmem
  · intro j K' hK'
    have hscale:(min ζh ζe)*(p*(ordinaryBoundaryHubSet H Z A j).card)≤
        ζh*(p*(ordinaryBoundaryHubSet H Z A j).card):=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (mul_nonneg hp (Nat.cast_nonneg _))
    obtain ⟨M,hm,hcover,havoid⟩:=ordinary_normalized_hub_factor_event_lift 2 Q F H A Z p ζh σ hh j
      (Y j) (hYT j) (hdiv j) ((hchangeY j).trans hscale) K'
      (fun v=>(hK' v).trans ((hbudgetY j).trans hscale))
    exact ⟨M,⟨hm,hcover⟩,localOrdinaryFactorGraph_disjoint M K' havoid⟩
  · intro k K' hK'
    have hscale:(min ζh ζe)*(p*(T k).card)≤ζe*(p*(T k).card):=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (mul_nonneg hp (Nat.cast_nonneg _))
    have hdiff:(((((S k∪T k)∩bernoulliVertexSet (fun w=>σ (g k w)))\D k).card+
      (D k\((S k∪T k)∩bernoulliVertexSet (fun w=>σ (g k w)))).card:ℕ):ℝ)≤ζe*(p*(T k).card):=by
      simpa only [bernoulliVertexSet, Finset.inter_filter, Finset.inter_univ] using (hchangeD k).trans hscale
    obtain ⟨M,⟨hm,hcover⟩,havoid⟩:=he k (D k) (hDU k) (hratio k) hdiff K'
      (fun w=>(hK' w).trans ((hbudgetD k).trans hscale))
    exact ⟨M,⟨hm,hcover⟩,endpointFactorGraph_choice (hST k) M (D k) K' hm hcover havoid⟩
end Oberwolfach
