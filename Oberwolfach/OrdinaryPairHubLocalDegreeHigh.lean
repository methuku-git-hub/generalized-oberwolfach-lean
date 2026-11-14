module

public import Oberwolfach.OrdinaryPatternLocalDegreeBridge
public import Oberwolfach.OrdinaryPatternConflictDeletionHigh
public import Oberwolfach.OrdinaryPairHubNormalizedCommonEvent

@[expose] public section
/-! On the realised two-hub common-spoke set, the degree of the fixed,
normalized parent cycle weight is the original-law omitted-spoke load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] {r:ℕ}
theorem ordinary_pair_hub_local_degree_identity_high
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (j:Color) (u u':U) (weight:OrdinaryCycle P r→ℝ) (D c:ℝ) (v:V):
    let Q:=rawWheelGraph P σ\F
    let H:=ordinaryPairHubSpokes π d σ j u u'
    let T:=Finset.univ.filter (fun z=>H z ())
    let hQP:Q≤P:=sdiff_le.trans (retainedGraph_le P (fun e=>σ (Sum.inl e)))
    H v () →
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C:LocalOrdinaryCycle Q F T r=>weight (localOrdinaryParent hQP C)/(D/2)/c) v =
    resourcePatternLoad ordinaryWheelResources (ordinaryCycleWheelWeight (U:=Unit) P F r weight (D/2))
      (fun _ _=>true) (Sum.inr (v,())) (ordinaryResourceState (rawWheelGraph P σ) H)/c := by
  intro Q H T hQP hv
  have hh:=ordinary_pattern_spoke_local_degree P Q F H hQP weight (D/2) c v hv
  have hd:=ordinary_pattern_load_delete_conflicts_high (P:=P) (F:=F) (Hbase:=fun (_:V) (_:Unit)=>True)
    (ordinaryCycleWheelWeight (U:=Unit) P F r weight (D/2)) (Sum.inr (v,())) (rawWheelGraph P σ) H
  dsimp only [Q] at hh
  rw [hd] at hh
  exact hh
end Oberwolfach
