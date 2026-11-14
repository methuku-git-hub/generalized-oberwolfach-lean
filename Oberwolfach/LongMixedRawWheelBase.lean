module

public import Oberwolfach.RawMarkedRealizationChoice
public import Oberwolfach.RawOrdinaryRestrictedCandidatePhysicalLift
public import Oberwolfach.MixedRestrictedPhysicalLift
public import Oberwolfach.LongAssignedMixedSeedFamilies

@[expose] public section
/-! Realize each component of the actual mixed raw candidate family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMixedRawWheelBaseDecidableEqFin1 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def LongRawRealizedWheel (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (d m:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    Option (Fin K)→Type
  | none =>
    let E:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) false
    let T:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) true
    let H:=rawMarkedPairSpokes π d raw g j
    MarkedWheel (fun x:E=>x.val.1) (fun x:E=>x.val.2)
      (fun x:T=>x.val.1) (fun x:T=>x.val.2) m π (3*d) (H false) (H true)
  | some i => OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ i)

def longRawRealizedPhysicalResources
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (d m:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    ∀i,LongRawRealizedWheel P π d m raw g j ℓ i→Finset (Finset (Fin n)⊕(Fin n×U))
  | none,W => markedWheelPhysicalResources W
  | some _,W => ordinaryWheelPhysicalResources W

def longRawSeedFamilies (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ):Option (Fin K)→Type:=
  LongMixedSeedFamily
    (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True))
    (fun i=>OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ i))

def longRawSeedResources (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ):
    ∀i,longRawSeedFamilies (U:=U) π d m ℓ i→
      Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)):=
  longMixedSeedResources (fun W=>typedMarkedOccurrenceResources W) (fun _ W=>orderedOrdinaryResources W)

end Oberwolfach
