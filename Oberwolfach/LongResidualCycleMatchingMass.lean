module

public import Oberwolfach.LongResidualCycleSourceMass
public import Oberwolfach.LongRawPartialDomainClassCard

@[expose] public section
/-! Count actual residual cycles by the same matching frequencies used in
the ordinary-source mass estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
local instance longCycleMatchSelectedFinite (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    Fintype (LongRawSelectedOrdinary π d m ℓ e M):=by
  let f:(LongRawSelectedOrdinary π d m ℓ e M)→M:=fun a=>⟨a.val,a.property.1⟩
  have hf:Function.Injective f:=by intro a b h;apply Subtype.ext;exact congrArg (fun x:M=>x.val) h
  exact Fintype.ofInjective f hf

theorem long_residual_cycle_mass_eq_matching_counts
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (hmaps:LongRawOrdinaryComponentMapsProperty F π d m ℓ e M)
    (assign₁:LongRawSelectedOrdinary π d m ℓ e M↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign₁ a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2)
    (w:U) {L:Type} [DecidableEq L]
    (data:ActualResidualData (K:=L) (J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign₁ a).1=w}) (F w))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1):
    data.Cembed.card=∑i:Fin K,(M.filter (fun c=>c.val.1=some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2=w)).card*ℓ i:=by
  obtain ⟨assign₂,C₂,hC₂,hsize₂⟩:=long_raw_component_sizes_of_maps F π d m ℓ e M hmaps
  have hh:=long_residual_cycle_mass_eq_source_domain F π d m ℓ e M assign₁ assign₂ hhub C₂ hC₂ hsize₂ w data ht hEmbed hlen
  have hc:=long_raw_partial_domain_card_by_matching_counts F π d m ℓ e M assign₂ C₂ hC₂ hsize₂ w
  exact hh.trans hc
end Oberwolfach
