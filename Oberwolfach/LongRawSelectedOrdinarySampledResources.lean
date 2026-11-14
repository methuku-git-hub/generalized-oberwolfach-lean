module

public import Oberwolfach.RawOrdinaryRestrictedWheelResources
public import Oberwolfach.LongRawSelectedOrdinary

@[expose] public section
/-! The ordinary wheel extracted from the actual mixed matching retains all
its sampled rim arcs and ordinary spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_raw_selected_ordinary_sampled_resources
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    ∀a:LongRawSelectedOrdinary π d m ℓ e M,
      (∀k,rawMarkedPairSpokes π d raw g j false ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val k)
        ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2)) ∧
      (∀k,rawMarkedPairRims P π d raw (Sum.inl (((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val k),
        ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val (cycleNext k))))):=by
  intro state e M a
  exact raw_restricted_ordinary_wheel_sampled_resources P π d _ raw g j (longRawSelectedOrdinaryWheel π d m ℓ e M a)
end Oberwolfach
