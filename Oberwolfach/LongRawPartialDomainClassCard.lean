module

public import Oberwolfach.FiniteLengthsByClass
public import Oberwolfach.LongRawPartialDomainCard
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

theorem long_raw_selected_hub_class_card
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (u:U) (i:Fin K):
    (Finset.univ.filter (fun a:LongRawSelectedAtHub π d m ℓ e M u=>
      (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1=i)).card =
    (M.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card :=by
  let B:Type:={a:LongRawSelectedAtHub π d m ℓ e M u //
      (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1=i}
  let S:=M.filter (fun c=>c.val.1=some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)
  let f:B→S:=fun a=>⟨a.val.val.val,Finset.mem_filter.mpr ⟨a.val.val.property.1,⟨by
    have h:=long_raw_selected_ordinary_index π d m ℓ e M a.val.val
    rw [a.property] at h
    exact h.symm,by
    rw [←long_raw_selected_ordinary_hub π d m ℓ e M a.val.val]
    exact a.val.property⟩⟩⟩
  have hf:Function.Injective f:=by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x:S=>x.val) h
  have hs:Function.Surjective f:=by
    intro c
    have hc:=Finset.mem_filter.mp c.property
    let a:LongRawSelectedOrdinary π d m ℓ e M:=⟨c.val,⟨hc.1,by rw [hc.2.1];rfl⟩⟩
    have hh:(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2=u:=by
      rw [long_raw_selected_ordinary_hub]
      exact hc.2.2
    let ah:LongRawSelectedAtHub π d m ℓ e M u:=⟨a,hh⟩
    have hi:(longRawSelectedOrdinaryPayload π d m ℓ e M a).1=i:=by
      apply Option.some.inj
      exact (long_raw_selected_ordinary_index π d m ℓ e M a).trans hc.2.1
    refine ⟨⟨ah,hi⟩,?_⟩
    apply Subtype.ext
    rfl
  have hcard:=Fintype.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)
  change (Finset.univ.filter (fun a:LongRawSelectedAtHub π d m ℓ e M u=>
    (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1=i)).card = S.card
  calc
    _ = Fintype.card B := by
      symm
      exact Fintype.card_subtype _
    _ = Fintype.card S := hcard
    _ = S.card := Fintype.card_coe S

theorem long_raw_partial_domain_card_by_wheel_class
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
      ∑i:Fin K,(Finset.univ.filter (fun a:LongRawSelectedAtHub π d m ℓ e M u=>
        (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1=i)).card * ℓ i :=by
  rw [long_raw_partial_domain_card_by_wheel_length F π d m ℓ e M assign C hC hsize u]
  exact finite_lengths_by_class (fun a:LongRawSelectedAtHub π d m ℓ e M u=>
    (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1) ℓ

theorem long_raw_partial_domain_card_by_matching_counts
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
      ∑i:Fin K,(M.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card * ℓ i :=by
  rw [long_raw_partial_domain_card_by_wheel_class F π d m ℓ e M assign C hC hsize u]
  apply Finset.sum_congr rfl
  intro i hi
  rw [long_raw_selected_hub_class_card π d m ℓ e M u i]

end Oberwolfach
