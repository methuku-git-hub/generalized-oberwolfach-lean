module

public import Oberwolfach.ComponentFamilyDomainCard
public import Oberwolfach.LongRawPartialDomains
public import Oberwolfach.FixedHubAssignedComponents
public import Oberwolfach.LongRawComponentSizes

@[expose] public section
/-! Count the actual ordinary source domain at each hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

local instance (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    Fintype (LongRawSelectedOrdinary π d m ℓ e M):=by
  let f:(LongRawSelectedOrdinary π d m ℓ e M)→M:=fun a=>⟨a.val,a.property.1⟩
  have hf:Function.Injective f:=by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x:M=>x.val) h
  exact Fintype.ofInjective f hf

local instance (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (u:U):Fintype (LongRawSelectedAtHub π d m ℓ e M u):=by
  unfold LongRawSelectedAtHub
  exact Fintype.ofFinite _

theorem long_raw_partial_domain_card
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (assign:(LongRawSelectedOrdinary π d m ℓ e M)↪(Σu,(F u).ConnectedComponent))
    (C:∀a:LongRawSelectedOrdinary π d m ℓ e M,
      (F (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2).ConnectedComponent)
    (hC:∀a,(⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a)
    (u:U):
    Fintype.card (longRawSourceDomain F π d m ℓ e M C u) =
      ∑a:LongRawSelectedAtHub π d m ℓ e M u,
        Fintype.card (longRawComponentAtHub F π d m ℓ e M C u a) :=by
  have hi:=fixed_hub_assigned_components_injective F
    (fun a:LongRawSelectedOrdinary π d m ℓ e M => (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2)
    C assign hC u
  have hc:=component_family_domain_card (F u) (longRawComponentAtHub F π d m ℓ e M C u) hi
  convert hc using 1 <;> congr 3 <;> exact Subsingleton.elim _ _

theorem long_raw_partial_domain_card_by_wheel_length
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (assign:(LongRawSelectedOrdinary π d m ℓ e M)↪(Σu,(F u).ConnectedComponent))
    (C:∀a:LongRawSelectedOrdinary π d m ℓ e M,
      (F (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2).ConnectedComponent)
    (hC:∀a,(⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a)
    (hsize:∀a,Fintype.card (C a)=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)
    (u:U):
    Fintype.card (longRawSourceDomain F π d m ℓ e M C u) =
      ∑a:LongRawSelectedAtHub π d m ℓ e M u,
        ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1 :=by
  calc
    _ = ∑a:LongRawSelectedAtHub π d m ℓ e M u,
        Fintype.card (longRawComponentAtHub F π d m ℓ e M C u a) :=
      long_raw_partial_domain_card F π d m ℓ e M assign C hC u
    _ = _ :=by
      apply Finset.sum_congr rfl
      intro a ha
      rw [show Fintype.card (longRawComponentAtHub F π d m ℓ e M C u a)=Fintype.card (C a.val) from
        Fintype.card_congr (factorComponentHubEquiv F ⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a.val).val.2,C a.val⟩ u a.property)]
      exact hsize a.val


theorem long_raw_partial_domain_complement_card
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (assign:(LongRawSelectedOrdinary π d m ℓ e M)↪(Σu,(F u).ConnectedComponent))
    (C:∀a:LongRawSelectedOrdinary π d m ℓ e M,
      (F (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2).ConnectedComponent)
    (hC:∀a,(⟨(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a)
    (hsize:∀a,Fintype.card (C a)=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1)
    (u:U):
    Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ e M C u} =
      n - ∑a:LongRawSelectedAtHub π d m ℓ e M u,
        ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1 :=by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin,long_raw_partial_domain_card_by_wheel_length F π d m ℓ e M assign C hC hsize u]

theorem long_raw_partial_domain_count_from_component_maps
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (h:LongRawOrdinaryComponentMapsProperty F π d m ℓ e M):
    let A:=LongRawSelectedOrdinary π d m ℓ e M
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
      ∀u,Fintype.card (longRawSourceDomain F π d m ℓ e M C u) =
        ∑a:LongRawSelectedAtHub π d m ℓ e M u,
          ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1 :=by
  intro A Q
  obtain ⟨assign,C,hC,hsize⟩:=long_raw_component_sizes_of_maps F π d m ℓ e M h
  exact ⟨assign,C,hC,fun u=>long_raw_partial_domain_card_by_wheel_length F π d m ℓ e M assign C hC hsize u⟩

end Oberwolfach
