module

public import Oberwolfach.OrdinaryReferenceSpokeProjection
public import Oberwolfach.OrdinaryDeepCoverSeparateLoadEvent
public import Oberwolfach.OrdinaryUniformProtectedReservoirEvent
public import Oberwolfach.OrdinaryShiftedMatchingCoreEvent

@[expose] public section
/-! The concrete selected raw sample carries the matching core, deep-cover
input, reference balance and protected terminal-reservoir event together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def OrdinaryMatchingReservoirBalanceBundle
    (P Fbad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d mMatch:ℕ)
    (p₂ k₂:ℝ) (q s:U→Bool→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd mMatch π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (t ξ balance:ℝ) (rRes mRes tRes fRes aRes bRes:ℕ) (εabs:ℝ)
    (mDeep KDeep:ℕ) (aDeep aLoadDeep ρDeep θDeep:ℝ) (JDeep:Finset U)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):Prop:=
  let raw:RawWheelOutcome (Fin n) U Bool Bool:=fun e=>expandedOrdinarySelectedCollapse e (σ e);
  OrdinaryDeepCoverSeparateLoadEvent mDeep KDeep aDeep aLoadDeep ρDeep θDeep P Fbad JDeep π d false raw ∧
  (∀v,|(((rawWheelGraph P raw)\Fbad).degree v:ℝ)-
    2*((Finset.univ.filter (fun u=>rawWheelSpokes π d raw false v u)).card:ℝ)|≤balance) ∧
  OrdinaryUniformProtectedReservoirEvent rRes mRes tRes fRes aRes bRes εabs
    (rawWheelGraph P raw\Fbad) Fbad (rawWheelSpokes π d raw false) ∧
  OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d mMatch p₂ k₂ q s wM wO t ξ σ
end Oberwolfach
