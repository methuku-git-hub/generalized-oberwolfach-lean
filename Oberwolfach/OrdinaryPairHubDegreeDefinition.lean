module

public import Oberwolfach.OrdinaryPairHubLocalDegreeHigh

@[expose] public section
/-! Local degree on a realised two-hub class, using the fixed parent weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] {r:ℕ}
def ordinaryPairHubLocalDegree
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (j:Color) (u u':U) (weight:OrdinaryCycle P r→ℝ) (D c:ℝ) (v:V):ℝ :=
  let Q:=rawWheelGraph P σ\F
  let H:=ordinaryPairHubSpokes π d σ j u u'
  let T:=Finset.univ.filter (fun z=>H z ())
  let hQP:Q≤P:=sdiff_le.trans (retainedGraph_le P (fun e=>σ (Sum.inl e)))
  hypergraphWeightedDegree localOrdinaryVertices
    (fun C:LocalOrdinaryCycle Q F T r=>weight (localOrdinaryParent hQP C)/(D/2)/c) v

theorem ordinary_pair_hub_named_local_degree_identity
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (j:Color) (u u':U) (weight:OrdinaryCycle P r→ℝ) (D c:ℝ) (v:V)
    (hv:ordinaryPairHubSpokes π d σ j u u' v ()):
    ordinaryPairHubLocalDegree P F π d σ j u u' weight D c v =
    resourcePatternLoad ordinaryWheelResources (ordinaryCycleWheelWeight (U:=Unit) P F r weight (D/2))
      (fun _ _=>true) (Sum.inr (v,()))
      (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u'))/c := by
  exact ordinary_pair_hub_local_degree_identity_high P F π d σ j u u' weight D c v hv
end Oberwolfach
