module

public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness
public import Oberwolfach.OrdinarySampleForcedSpokes

@[expose] public section
/-! The actual reservoir's spoke resources supply the finite absorber-label
sets used in the selected reserved-list placement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryReservoirSpokeLabels {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (K:Finset (Sym2 V⊕(V×U))) (u:U):Finset V :=
  Finset.univ.filter (fun v=>Sum.inr (v,u)∈K)

theorem ordinary_reservoir_spoke_labels_inputs
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Q:SimpleGraph V) (K:Finset (Sym2 V⊕(V×U)))
    (hK:K⊆ordinaryHostResources Q (rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false)):
    (∀u,ordinaryReservoirSpokeLabels K u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ∧
    (∀u,(ordinaryReservoirSpokeLabels K u).card≤(ordinaryResourceRows K).card) ∧
    (∀v,(Finset.univ.filter (fun u=>v∈ordinaryReservoirSpokeLabels K u)).card≤(ordinaryResourceHubs K).card) :=by
  constructor
  · intro u v hv
    have hk:Sum.inr (v,u)∈K:=(Finset.mem_filter.mp hv).2
    have hspoke:rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false v u:=
      (ordinaryHostResources_spoke Q _ v u).mp (hK hk)
    have hs:rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (v,u)=some (Sum.inr false):=
      (ordinary_reference_spoke_projection π d σ false v u).mp hspoke
    simpa only [rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hs
  constructor
  · intro u
    apply Finset.card_le_card
    intro v hv
    have hk:Sum.inr (v,u)∈K:=(Finset.mem_filter.mp hv).2
    exact Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),hk,by simp [ordinaryResourceRows]⟩
  · intro v
    apply Finset.card_le_card
    intro u hu
    have hv:(v∈ordinaryReservoirSpokeLabels K u):=(Finset.mem_filter.mp hu).2
    have hk:Sum.inr (v,u)∈K:=(Finset.mem_filter.mp hv).2
    exact Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),hk,by simp [ordinaryResourceHubs]⟩
end Oberwolfach
