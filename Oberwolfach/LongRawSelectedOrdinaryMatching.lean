module

public import Oberwolfach.LongRawSelectedOrdinary

@[expose] public section
/-! Extracted ordinary wheels preserve the selected candidate's hub and
inherit the disjointness of the original mixed matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

theorem long_raw_selected_ordinary_hub (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (a:LongRawSelectedOrdinary π d m ℓ e M):
    (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2=
      longRawSeedHub π d m ℓ a.val.val.1 a.val.val.2:=by
  rcases a with ⟨⟨⟨i,v⟩,hv⟩,ha⟩
  cases i with
  | none => simp at ha
  | some i => rfl

theorem long_raw_selected_ordinary_restricted_matching (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (hmatch:∀c∈M,∀c'∈M,c≠c'→Disjoint
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e c)
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e c')):
    ∀a a':LongRawSelectedOrdinary π d m ℓ e M,a≠a'→Disjoint
      (restrictedResourceSet (fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)=>
        (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e (longRawSelectedOrdinaryWheel π d m ℓ e M a))
      (restrictedResourceSet (fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a').1)=>
        (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) e (longRawSelectedOrdinaryWheel π d m ℓ e M a')) :=by
  intro a a' hne
  have hne':a.val≠a'.val:=by intro h;exact hne (Subtype.ext h)
  have hh:=hmatch a.val a.property.1 a'.val a'.property.1 hne'
  rw [long_raw_selected_ordinary_resources, long_raw_selected_ordinary_resources]
  exact hh
end Oberwolfach
