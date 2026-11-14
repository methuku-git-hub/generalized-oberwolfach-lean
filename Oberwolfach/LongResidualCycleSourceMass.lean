module

public import Oberwolfach.ResidualCycleHubMass
public import Oberwolfach.LongRawPartialDomainCard

@[expose] public section
/-! The cycle mass in the actual residual data equals the already estimated
ordinary source-domain mass for any compatible component assignment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

local instance longResidualCycleSelectedFinite (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    Fintype (LongRawSelectedOrdinary π d m ℓ e M):=by
  let f:(LongRawSelectedOrdinary π d m ℓ e M)→M:=fun a=>⟨a.val,a.property.1⟩
  have hf:Function.Injective f:=by intro a b h;apply Subtype.ext;exact congrArg (fun x:M=>x.val) h
  exact Fintype.ofInjective f hf

theorem long_residual_cycle_mass_eq_source_domain
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (assign₁ assign₂:LongRawSelectedOrdinary π d m ℓ e M↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign₁ a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2)
    (C:∀a:LongRawSelectedOrdinary π d m ℓ e M,(F (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2).ConnectedComponent)
    (hC:∀a,(⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign₂ a)
    (hsize:∀a,Fintype.card (C a)=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)
    (w:U) {L:Type} [DecidableEq L]
    (data:ActualResidualData (K:=L) (J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign₁ a).1=w}) (F w))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1):
    data.Cembed.card=Fintype.card (longRawSourceDomain F π d m ℓ e M C w):=by
  have hdata:=actual_residual_cycle_mass_by_matching_hub (fun a=>(assign₁ a).1)
    (fun a=>(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2) hhub w data ht hEmbed
    (fun a=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1) hlen
  have hsource:=long_raw_partial_domain_card_by_wheel_length F π d m ℓ e M assign₂ C hC hsize w
  apply hdata.trans
  convert hsource.symm using 1 <;> congr 1 <;> ext x <;> simp
end Oberwolfach
