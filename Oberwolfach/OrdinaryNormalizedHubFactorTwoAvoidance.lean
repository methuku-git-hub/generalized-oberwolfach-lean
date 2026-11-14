module

public import Oberwolfach.OrdinaryNormalizedHubFactorEventLift
public import Oberwolfach.LocalFactorGraphChoice
public import Oberwolfach.MixedBoundarySelectionAvoidance

@[expose] public section
/-! A normalized hub factor can avoid both a local and an ambient graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W:Type} [Fintype V] [Fintype U] [Fintype W]
  [DecidableEq V] [DecidableEq U] [DecidableEq W]

theorem ordinary_normalized_hub_factor_two_avoidance
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (p ζ:ℝ) (σ:Sym2 (V⊕U)→Bool)
    (h:OrdinaryNormalizedHubFactorEvent m Q F H A Z p ζ σ)
    (j:{u:U // u∉Z}) (Y:Finset V) (hY:Y⊆ordinaryBoundaryHubSet H Z A j) (hdiv:(m+1)∣Y.card)
    (hchange:(((((ordinaryBoundaryHubSet H Z A j).filter (fun v=>σ (hubSpokeCoin j.val v)=true))\Y).card+
      (Y\((ordinaryBoundaryHubSet H Z A j).filter (fun v=>σ (hubSpokeCoin j.val v)=true))).card:ℕ):ℝ)≤
        ζ*(p*(ordinaryBoundaryHubSet H Z A j).card))
    (e:V↪W) (C:SimpleGraph V) (D:SimpleGraph W)
    (hdeg:∀v,((C⊔D.comap e).degree v:ℝ)≤ζ*(p*(ordinaryBoundaryHubSet H Z A j).card)):
    ∃M:Finset (LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) (m+1)),
      ((∀C∈M,∀C'∈M,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
        M.biUnion localOrdinaryVertices=Y) ∧
      Disjoint (localOrdinaryFactorGraph M) C ∧ Disjoint ((localOrdinaryFactorGraph M).map e) D:=by
  have hf:=ordinary_normalized_hub_factor_event_lift m Q F H A Z p ζ σ h j Y hY hdiv hchange (C⊔D.comap e)
    (by intro v;simpa only [←SimpleGraph.ncard_neighborSet] using hdeg v)
  obtain ⟨M,hM,hcover,havoid⟩:=hf
  obtain ⟨M,hM,_hs,_hd,ha⟩:=local_factor_graph_choice Y (C⊔D.comap e) ⟨M,⟨hM,hcover⟩,havoid⟩
  exact ⟨M,hM,ha.mono_right le_sup_left,
    graph_map_disjoint_of_comap _ D e (ha.mono_right le_sup_right)⟩
end Oberwolfach
