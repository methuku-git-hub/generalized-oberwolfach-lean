module

public import Oberwolfach.MarkedActualParentCommonConfigurationEvent
public import Oberwolfach.MarkedParentConfigurationRecordInputs
public import Oberwolfach.MarkedCommonConfigurationParameterMono

@[expose] public section
/-! Parent common- and local-configuration inputs at the actual vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_parent_configuration_record_inputs
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r d L:ℕ) (a:Γ) (j:Color) (βCommon ζCommon βA κ t bC bP:ℝ)
    (hβ:βA≤βCommon) (hζ:ζCommon≤κ/4) (hC:3*βA≤bC) (hP:3*βA≤bP)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hcommon:∀ i≤L,MarkedCommonConfigurationsWithSpokes r (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hπ i) d βCommon ζCommon
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)))
    (hlocal:∀ i≤L,MarkedLocalConfigurationsWithSpokes r (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hπ i) d Finset.univ bC bP
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))):
    ∀ i≤L,
      let P:=G.comap (markedVortexVertexEmbedding Q i)
      let ρ:=markedVortexPermutation Q π hπ i
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u);
      MarkedCommonConfigurationsWithSpokes r P ρ d βA (κ/4) σ H ∧
      MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ (3*(min βA (t/4))) (3*(min βA (t/4))) σ H:=by
  intro i hi P ρ σ H
  constructor
  · exact marked_common_configuration_parameter_mono r P ρ d βCommon ζCommon βA (κ/4) hβ hζ σ H (hcommon i hi)
  · exact marked_parent_configuration_record_input r P ρ d bC bP βA t hC hP σ H (hlocal i hi)
end Oberwolfach
