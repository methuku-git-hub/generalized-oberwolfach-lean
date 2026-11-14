module

public import Oberwolfach.LongCorrectionReserveUniversalEvent
public import Oberwolfach.LongSampleChainReserveEvents
public import Oberwolfach.MarkedVortexFiniteSampleChain

@[expose] public section
/-! Keep the corrected and reserve-deleted restrictions of one sample on
one coherent finite vortex chain, together with the terminal absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

def LongCorrectedReserveVortexChainEvent
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mm) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (gammaLoss sigmaLoss extra:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))):Prop :=
  let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
  let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
    (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false
  let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
  let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
  MarkedFixedTerminalAbsorber P π d (r+4) σ' H' C (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
  MarkedFixedTerminalAbsorber P π d (r+4) σ H C (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
  Nonempty (MarkedVortexFiniteSampleChain Q π hpres σ' H' Q.length Q.length_pos) ∧
  ∃D₂:MarkedReferenceDeletion P π d σ,
    D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) ((gammaLoss+extra)*n) ((sigmaLoss+extra)*n) ∧
    D₂.removed=D₀.removed∪C ∧ D₂.remaining H=D₀.remaining H\C ∧ Disjoint D₀.removed C ∧
    let σ₂:=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₂.arcs).edgeFinset
    let H₂:=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₂.spokes);
    Nonempty (MarkedVortexFiniteSampleChain Q π hpres σ₂ H₂ Q.length Q.length_pos)
end Oberwolfach
