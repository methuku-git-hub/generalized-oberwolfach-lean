module

public import Oberwolfach.LongMixedRawRealizationResources

@[expose] public section
/-! Realization does not change the hub attached to a selected candidate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMixedRawHubPreservationDecidableEqFin1 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def longRawSeedHub (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ):
    ∀i,longRawSeedFamilies (U:=U) π d m ℓ i→U
  | none,W=>W.2.val
  | some _,W=>W.2

def longRawRealizedHub (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (d m:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    ∀i,LongRawRealizedWheel P π d m raw g j ℓ i→U
  | none,W=>W.2.val
  | some _,W=>W.2

theorem long_raw_realize_component_hub
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀i W,longRawRealizedHub P π d m raw g j ℓ i (longRawRealizeComponent P π d m raw g j ℓ i W)=
      longRawSeedHub π d m ℓ i W.val :=by
  intro state e i W
  cases i with
  | none => exact (raw_marked_realization_properties P π d m raw g j (longRawMarkedComponent π d m ℓ e W)).2.1
  | some i => rfl
end Oberwolfach
