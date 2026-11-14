module

public import Oberwolfach.OrdinaryAssignedEligibleMatchingStartsBundle

@[expose] public section
/-! The exact joint sample event needed for deletion-uniform matching and
reserved source paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def OrdinaryShiftedMatchingCoreEvent
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (p k:ℝ)
    (q s:U→Bool→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (t ξ:ℝ) (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):Prop :=
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e);
    OrdinaryShiftedMixedLoadEvent P π d m (fun i:Fin K=>longPaddedSeedExponent i+1) p k q s
      (fun _ _=>True) (fun _ _=>True) (fun _:Unit=>wM) (fun _=>true) (fun _=>true)
      wO (fun _=>true) (fun _=>true) t (fun _=>t) σ ∧
    (∀g j v u,rawMarkedPairSpokes π d raw g j true v u→q u g≠0) ∧
    (∀h u,|rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) true true h u Finset.univ-
      (if h then q u true else s u true)*(n:ℝ)|<ξ*n) ∧
    (∀u g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) u-
      (n:ℝ)*q u g/d|<(n:ℝ)^(3/4:ℝ)/d)
end Oberwolfach
