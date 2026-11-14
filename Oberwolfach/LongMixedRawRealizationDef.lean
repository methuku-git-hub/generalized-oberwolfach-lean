module

public import Oberwolfach.LongMixedRestrictedComponents

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def longRawRealizeComponent
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀i,RestrictedResource (longRawSeedResources (U:=U) π d m ℓ i) e→
      LongRawRealizedWheel P π d m raw g j ℓ i :=by
  intro state e i W
  cases i with
  | none => exact rawMarkedRealization P π d m raw g j (longRawMarkedComponent π d m ℓ e W)
  | some i => exact W.val

end Oberwolfach
