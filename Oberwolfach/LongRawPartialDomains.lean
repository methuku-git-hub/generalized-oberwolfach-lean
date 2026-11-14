module

public import Oberwolfach.LongRawComponentMapsToPartialFactors

@[expose] public section
/-! Source domains used by the ordinary partial factor at a fixed hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

def LongRawSelectedAtHub (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (u:U):Type:=
  {a:LongRawSelectedOrdinary π d m ℓ e M // (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2=u}

def longRawComponentAtHub (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (C:∀a:LongRawSelectedOrdinary π d m ℓ e M,
      (F (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2).ConnectedComponent)
    (u:U) (a:LongRawSelectedAtHub π d m ℓ e M u):(F u).ConnectedComponent:=
  factorComponentAtAssignedHub F ⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a.val).val.2,C a.val⟩ u a.property

def longRawSourceDomain (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (C:∀a:LongRawSelectedOrdinary π d m ℓ e M,
      (F (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2).ConnectedComponent)
    (u:U):Set (Fin n):=
  {v | ∃a:LongRawSelectedAtHub π d m ℓ e M u,v∈(longRawComponentAtHub F π d m ℓ e M C u a).supp}
end Oberwolfach
