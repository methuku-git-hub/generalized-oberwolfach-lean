module

public import Oberwolfach.MarkedVortexParentConfigurationRecordInputs
public import Oberwolfach.MarkedVortexNestedActiveConfigurationsInput

@[expose] public section
/-! Parent and next-active configuration fields on the same retained outcome.
The active field is restricted from all parent hubs to the non-deeper hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_joint_configuration_record_inputs
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r d L:ℕ) (a:Γ) (j:Color) (βCommon ζCommon βA βrec κ t bC bP:ℝ)
    (hβ:βA≤βCommon) (hζ:ζCommon≤κ/4)
    (hC:3*βA≤bC) (hP:3*βA≤bP) (hrec:βrec≤βA)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hcommon:∀ i≤L,MarkedCommonConfigurationsWithSpokes r (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hπ i) d βCommon ζCommon
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)))
    (hparent:∀ i≤L,MarkedLocalConfigurationsWithSpokes r (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hπ i) d Finset.univ bC bP
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)))
    (hactive:∀ i≤L,MarkedLocalConfigurationsWithSpokes r
      (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
      (markedVortexActivePermutation Q π hπ (i+1)) d Finset.univ bC bP
      (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q i) z.1)
      (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexHubEmbedding Q i u))):
    ∀ i≤L,
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:markedVortexNonDeeperHubType Q i→markedVortexHubType Q i:=Subtype.val
      let ρP:=markedVortexPermutation Q π hπ i
      let ρ:=markedVortexActivePermutation Q π hπ (i+1)
      let σP:=rawMarkedRestrictPair fP gP z.1
      let HP:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fP x) (gP u);
      MarkedCommonConfigurationsWithSpokes r (G.comap fP) ρP d βA (κ/4) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r (G.comap fP) ρP d Finset.univ
        (3*(min βA (t/4))) (3*(min βA (t/4))) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (f x))) ρ d Finset.univ
        (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
        (fun b x u=>HP b (fA (f x)) (gA u)):=by
  intro i hi fP gP fA f gA ρP ρ σP HP
  have hp:=marked_vortex_parent_configuration_record_inputs Q π hπ r d L a j βCommon ζCommon βA κ t bC bP
    hβ hζ hC hP z hcommon hparent i hi
  have hCr:3*βrec≤bC:=by linarith
  have hPr:3*βrec≤bP:=by linarith
  have ha:=marked_vortex_nested_active_configurations_input Q π hπ i d r bC bP βrec hCr hPr a j z (hactive i hi)
  exact ⟨hp.1,hp.2,ha⟩
end Oberwolfach
