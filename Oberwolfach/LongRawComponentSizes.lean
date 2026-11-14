module

public import Oberwolfach.LongRawOrdinaryComponentMapsProperty

@[expose] public section
/-! The map onto an ordered rim certifies the size of its assigned component. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

theorem long_raw_component_sizes_from_rim_cover
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):
    let A:=LongRawSelectedOrdinary π d m ℓ e M
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M
    ∀(C:∀a:A,(F (Q a).val.2).ConnectedComponent)
      (f:∀a:A,C a↪Fin n),
      (∀a x,∃i:Fin (ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1),f a x=(Q a).val.1.val i) →
      (∀a,∀i:Fin (ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1),∃x:C a,f a x=(Q a).val.1.val i) →
      ∀a,Fintype.card (C a)=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1 :=by
  intro A Q C f hinto honto a
  have heq:Finset.univ.image (f a) = Finset.univ.image (Q a).val.1.val:=by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨i,hi⟩:=hinto a x
      exact ⟨i,hi.symm⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨x,hx⟩:=honto a i
      exact ⟨x,hx⟩
  have hc:=congrArg Finset.card heq
  rw [Finset.card_image_of_injective _ (f a).injective,
    Finset.card_image_of_injective _ (permutationSeparated_injective π (3*d) (Q a).val.1.val (Q a).val.1.property)] at hc
  simpa only [Finset.card_univ,Fintype.card_fin] using hc

theorem long_raw_component_sizes_of_maps
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (h:LongRawOrdinaryComponentMapsProperty F π d m ℓ e M):
    let A:=LongRawSelectedOrdinary π d m ℓ e M
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
      ∀a,Fintype.card (C a)=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1 :=by
  intro A Q
  obtain ⟨assign,C,hC,f,hinto,honto,_,_,_⟩:=h
  refine ⟨assign,C,hC,?_⟩
  intro a
  have heq:Finset.univ.image (f a) = Finset.univ.image (Q a).val.1.val:=by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨i,hi⟩:=hinto a x
      exact ⟨i,hi.symm⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨x,hx⟩:=honto a i
      exact ⟨x,hx⟩
  have hc:=congrArg Finset.card heq
  rw [Finset.card_image_of_injective _ (f a).injective,
    Finset.card_image_of_injective _ (permutationSeparated_injective π (3*d) (Q a).val.1.val (Q a).val.1.property)] at hc
  simpa only [Finset.card_univ,Fintype.card_fin] using hc
end Oberwolfach
