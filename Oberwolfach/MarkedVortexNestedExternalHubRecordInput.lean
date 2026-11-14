module

public import Oberwolfach.MarkedVortexExternalHubConfigurationRecordInputs
public import Oberwolfach.MarkedVortexNonDeeperGeometry
public import Oberwolfach.RawMarkedPairNestedRims

@[expose] public section
/-! Identify the next active configuration input with the nested restriction
used by the parent level record, including hubs outside the next level. -/
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

theorem marked_vortex_nested_external_hub_record_input
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r d L:ℕ) (a:Γ) (j:Color) (bC bP βrec:ℝ)
    (hC:3*βrec≤bC) (hP:3*βrec≤bP)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hall:∀ i≤L,
      MarkedLocalConfigurationsWithSpokes r (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
        (markedVortexActivePermutation Q π hπ (i+1)) d Finset.univ bC bP
        (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
          (markedVortexActiveVertexEmbedding Q (i+1) x) (markedVortexHubEmbedding Q i u))):
    ∀ i≤L,
      let Z:=markedVortexHubType Q i
      let Zkeep:=↥(Finset.univ\markedVortexDeeperHubs Q i)
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:Zkeep→Z:=Subtype.val
      let ρ:=markedVortexActivePermutation Q π hπ (i+1)
      let σP:=rawMarkedRestrictPair fP gP z.1
      let HP:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fP x) (gP u);
      MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (f x))) ρ d Finset.univ (3*βrec) (3*βrec)
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
        (fun b x u=>HP b (fA (f x)) (gA u)):=by
  intro i hi Z Zkeep fP gP fA f gA ρ σP HP
  have hkeep:=marked_vortex_external_hub_configuration_record_inputs Q π hπ r d L a j bC bP βrec hC hP z hall i hi
  have hrim (e:Sym2 _):
      rawMarkedRestrictPair (fun x=>fA (f x)) gA σP (Sum.inl e)=
      rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (fun u:Zkeep=>gP u.val) z.1 (Sum.inl e):=by
    have hh:=rawMarked_pair_nested_rims fP (fun x=>fA (f x)) gP gA z.1 e
    exact hh
  have hc:=marked_local_configurations_hub_restriction r
    (G.comap (markedVortexActiveVertexEmbedding Q (i+1))) ρ d Finset.univ (3*βrec) (3*βrec)
    (rawMarkedRestrictPair (markedVortexActiveVertexEmbedding Q (i+1)) (fun u:Zkeep=>gP u.val) z.1)
    (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) id
    (fun b x (u:Zkeep)=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
          (markedVortexActiveVertexEmbedding Q (i+1) x) (gP u.val)) hrim hkeep
  exact hc
end Oberwolfach
