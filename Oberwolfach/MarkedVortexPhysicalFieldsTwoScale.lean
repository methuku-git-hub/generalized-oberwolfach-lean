module

public import Oberwolfach.MarkedVortexCorrectedCompleteFromMatchingFieldsTwoScale
public import Oberwolfach.MarkedVortexCorrectedCompleteSeparateActiveSplit
public import Oberwolfach.MarkedVortexCorrectedCompleteFromMatchingFields
public import Oberwolfach.MarkedVortexCorrectedCompleteTerminalBudgetPhysicalLocal
public import Oberwolfach.MarkedVortexInitialLocalSpokeLoss
public import Oberwolfach.MarkedVortexFixedMarginLocalCorrectionCap
public import Oberwolfach.MarkedVortexInitialBalanceParentAmbientLocal
public import Oberwolfach.MarkedVortexCorrectedCompleteExactDeeper
public import Oberwolfach.MarkedVortexTerminalBudget
public import Oberwolfach.MarkedVortexTerminalDecompositionGeometry
public import Oberwolfach.MarkedVortexCorrectedCompleteFromReserved
public import Oberwolfach.MarkedVortexSmallerParentToRecordConsequences
public import Oberwolfach.MarkedVortexInitialInnerCutsFromRawAgreement
public import Oberwolfach.MarkedVortexInitialBalanceFromSelectedParent
public import Oberwolfach.MarkedVortexInitialPotentialFromParentRecord
public import Oberwolfach.MarkedVortexInitialBoundaryFromParentRecord
public import Oberwolfach.MarkedVortexInitialCommonFromParentRecord
public import Oberwolfach.MarkedVortexInitialDeepFromParentRecord
public import Oberwolfach.MarkedVortexActiveTransferFixedMargin
public import Oberwolfach.MarkedVortexFirstActiveExactRims
public import Oberwolfach.MarkedVortexProtectedDeeperEquality
public import Oberwolfach.MarkedVortexFixedMarginCorrectionCap
public import Oberwolfach.LongActualReferenceLevelDensities
public import Oberwolfach.MarkedLocalPrerequisiteMonotone
public import Oberwolfach.MarkedVortexInitialDeepFieldsForRecord
public import Oberwolfach.MarkedVortexInitialActiveFieldsForRecord
public import Oberwolfach.MarkedVortexInitialCommonFieldsForRecord
public import Oberwolfach.MarkedVortexInitialRecordFieldsOfTransfers
public import Oberwolfach.MarkedVortexRecordConsequencesBoundaryToleranceMono
public import Oberwolfach.MarkedVortexRecordConsequencesSpokeToleranceMono
public import Oberwolfach.MarkedVortexCorrectedReferenceChain
public import Oberwolfach.MarkedVortexCorrectedRecordFromStrongerPreciseParent
public import Oberwolfach.MarkedVortexWeightFamiliesWeakenMargin
public import Oberwolfach.MarkedFiniteReferenceChain
public import Oberwolfach.MarkedVortexFiniteSampleChain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_physical_fields_two_scale
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (d:ℕ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (Hordinary:V→U→Prop) (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (FSactive:SimpleGraph (↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))⊕markedVortexNonDeeperHubType Q 0))
    (ζchange ζactive cLocal:ℝ)
    (hData:MarkedVortexPhysicalCorrectionFields G D m β ε Q π d a j z σold σglobal Hold Hglobal Hordinary FR FS FSactive ζchange cLocal)
    (hActive:∀u,(FSactive.degree (Sum.inr u):ℝ) ≤ ζactive*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))):
    MarkedVortexPhysicalCorrectionFieldsTwoScale G D m β ε Q π d a j z σold σglobal Hold Hglobal Hordinary FR FS FSactive ζchange ζactive cLocal :=by
  exact ⟨hData.htypes,hData.hsep,hData.hinterval,hData.hR,hData.hS,hData.hFR,hData.hFS,hData.hHglobal,hData.hrawInner,hData.hOrdinary,hData.hSactive,hActive,hData.hLocalRimOutside,hData.hLocalSpokeOutside,hData.hPhysicalNoNew,hData.hPhysicalLoss⟩
end Oberwolfach
