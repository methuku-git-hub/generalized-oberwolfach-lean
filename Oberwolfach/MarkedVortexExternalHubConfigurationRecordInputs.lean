module

public import Oberwolfach.MarkedActualNextActiveAllParentHubsConfigurationEvent
public import Oberwolfach.MarkedExternalHubConfigurationRecordInput

@[expose] public section
/-! Restrict the all-parent-hub estimate to the non-deeper hubs of each
parent level, retaining the next active vertex set and the same rim outcome. -/
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

theorem marked_vortex_external_hub_configuration_record_inputs
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
      let R:Finset Z:=markedVortexDeeperHubs Q i
      let Zkeep:=↥(Finset.univ\R)
      let f:=markedVortexActiveVertexEmbedding Q (i+1)
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexActivePermutation Q π hπ (i+1)
      MarkedLocalConfigurationsWithSpokes r (G.comap f) ρ d Finset.univ (3*βrec) (3*βrec)
        (rawMarkedRestrictPair f (fun u:Zkeep=>g u.val) z.1)
        (fun b x (u:Zkeep)=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u.val)):=by
  intro i hi Z R Zkeep f g ρ
  apply marked_external_hub_configuration_record_input r (G.comap f) ρ d bC bP βrec hC hP
    (rawMarkedRestrictPair f g z.1) (rawMarkedRestrictPair f (fun u:Zkeep=>g u.val) z.1) Subtype.val
    (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u))
  · intro e
    rfl
  · exact hall i hi
end Oberwolfach
