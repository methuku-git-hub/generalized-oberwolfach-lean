module

public import Oberwolfach.LongRawPartialDomainCard
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! A source domain made from bounded-length components excludes every long component. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

theorem long_raw_partial_domain_excludes_long
    (hK:3≤K) (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m
      (fun i:Fin K=>longPaddedSeedExponent i+2))) e))
    (C:∀a:LongRawSelectedOrdinary π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M,
      (F (longRawSelectedOrdinaryWheel π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M a).val.2).ConnectedComponent)
    (hsize:∀a,Fintype.card (C a)=longPaddedSeedExponent
      (longRawSelectedOrdinaryPayload π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M a).1+2):
    ∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M C u :=by
  intro u v hv hm
  obtain ⟨a,ha⟩:=hm
  let ℓ:Fin K→ℕ:=fun i=>longPaddedSeedExponent i+2
  have hvcomp:(F u).connectedComponentMk v=longRawComponentAtHub F π d m ℓ e M C u a:=ha
  have heq:Fintype.card (longRawComponentAtHub F π d m ℓ e M C u a)=Fintype.card (C a.val):=
    Fintype.card_congr (factorComponentHubEquiv F
      ⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a.val).val.2,C a.val⟩ u a.property)
  have hb:longPaddedSeedExponent (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1+2≤K:=by
    rw [long_padded_seed_length_eq_exponent]
    exact long_assigned_padded_length_upper hK _
  rw [hvcomp,heq,hsize] at hv
  dsimp only [ℓ] at hb
  omega
theorem long_raw_partial_domain_contains_long_count
    (hK:3≤K) (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m
      (fun i:Fin K=>longPaddedSeedExponent i+2))) e))
    (C:∀a:LongRawSelectedOrdinary π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M,
      (F (longRawSelectedOrdinaryWheel π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M a).val.2).ConnectedComponent)
    (hsize:∀a,Fintype.card (C a)=longPaddedSeedExponent
      (longRawSelectedOrdinaryPayload π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M a).1+2):
    ∀u,(Finset.univ.filter (fun v:Fin n=>K<Fintype.card ((F u).connectedComponentMk v))).card ≤
      Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M C u} :=by
  intro u
  let L:=Finset.univ.filter (fun v:Fin n=>K<Fintype.card ((F u).connectedComponentMk v))
  let f:L→{v:Fin n // v∉longRawSourceDomain F π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M C u}:=
    fun v=>⟨v.val,long_raw_partial_domain_excludes_long hK F π d m e M C hsize u v.val (Finset.mem_filter.mp v.property).2⟩
  have hf:Function.Injective f:=by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun v:{v:Fin n // v∉longRawSourceDomain F π d m (fun i:Fin K=>longPaddedSeedExponent i+2) e M C u}=>v.val) h
  have hcard:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard

theorem long_raw_partial_domain_excludes_long_of_length_bound
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (hℓ:∀i,ℓ i≤K)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m
      ℓ)) e))
    (C:∀a:LongRawSelectedOrdinary π d m ℓ e M,
      (F (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2).ConnectedComponent)
    (hsize:∀a,Fintype.card (C a)=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1):
    ∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d m ℓ e M C u :=by
  intro u v hv hm
  obtain ⟨a,ha⟩:=hm
  have hvcomp:(F u).connectedComponentMk v=longRawComponentAtHub F π d m ℓ e M C u a:=ha
  have heq:Fintype.card (longRawComponentAtHub F π d m ℓ e M C u a)=Fintype.card (C a.val):=
    Fintype.card_congr (factorComponentHubEquiv F
      ⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a.val).val.2,C a.val⟩ u a.property)
  have hb:ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1≤K:=hℓ _
  rw [hvcomp,heq,hsize] at hv
  omega

end Oberwolfach
