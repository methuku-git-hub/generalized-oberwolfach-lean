module

public import Oberwolfach.LongRawHubContext
public import Oberwolfach.MixedRestrictedSomePayload
public import Oberwolfach.LongMixedRestrictedComponents

@[expose] public section
/-! Extract the ordinary restricted wheel carried by a selected mixed raw
candidate, retaining its index and its exact sampled resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

abbrev LongRawSelectedOrdinary (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):=
  {c:RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e //
    c∈M ∧ c.val.1.isSome}

def longRawSelectedOrdinaryPayload (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M):
    Σi,RestrictedResource (longRawSeedResources (U:=U) π d m ℓ (some i)) e :=
  mixedRestrictedSomePayload (longRawSeedResources (U:=U) π d m ℓ) e ⟨a.val,a.property.2⟩

def longRawSelectedOrdinaryWheel (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M):
    RestrictedResource (fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)=>
      (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e:=
  longRawOrdinaryComponent π d m ℓ _ e (longRawSelectedOrdinaryPayload π d m ℓ e M a).2

theorem long_raw_selected_ordinary_index (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M):
    some (longRawSelectedOrdinaryPayload π d m ℓ e M a).1=a.val.val.1:=by
  exact mixed_restricted_some_payload_index _ _ _

theorem long_raw_selected_ordinary_resources (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M):
    restrictedResourceSet (fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)=>
      (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e (longRawSelectedOrdinaryWheel π d m ℓ e M a)=
    restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e a.val :=by
  have h1:=long_raw_ordinary_component_resources π d m ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1 e
    (longRawSelectedOrdinaryPayload π d m ℓ e M a).2
  have h2:=mixed_restricted_some_payload_resources (longRawSeedResources (U:=U) π d m ℓ) e ⟨a.val,a.property.2⟩
  have h2' : restrictedResourceSet (longRawSeedResources (U:=U) π d m ℓ
      (some (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)) e
      (longRawSelectedOrdinaryPayload π d m ℓ e M a).2 =
      restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e a.val :=by
    convert h2 using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  calc
    _ = restrictedResourceSet (longRawSeedResources (U:=U) π d m ℓ
        (some (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)) e
        (longRawSelectedOrdinaryPayload π d m ℓ e M a).2 :=by
      convert h1.symm using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
    _ = _ :=h2' 
end Oberwolfach
