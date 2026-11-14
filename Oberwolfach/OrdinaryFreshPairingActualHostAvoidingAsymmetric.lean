module

public import Oberwolfach.MixedFreshPairingAsymmetricEvent
public import Oberwolfach.OrdinaryPairingFactorsActualHostAvoiding
public import Oberwolfach.OrdinaryPhysicalGraphDeletion

@[expose] public section
/-! A good fresh general-length pairing event supplies jointly selected
    factors in the actual post-deletion host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J E:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J] [Fintype E]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J] [DecidableEq E]

theorem ordinary_fresh_pairing_actual_host_avoiding_asymmetric
    (m:ℕ) (p ρ ζh ζe n:ℝ) (Q Q' F:SimpleGraph V) (H H':V→U→Prop)
    (T:J→Finset V) (S₀ T₀:I→Finset (V⊕U)) (f:J→V↪E) (g:I→(V⊕U)↪E) (σ:E→Bool)
    (hgood:MixedFreshPairingAsymmetricEvent m p ρ ζh ζe n Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U) T S₀ T₀ f g σ)
    (Y:J→Finset V) (A:I→Finset V) (B:I→Finset U)
    (hA:∀i,(A i).image Sum.inl⊆S₀ i) (hB:∀i,(B i).image Sum.inr⊆T₀ i)
    (K:SimpleGraph (V⊕U)) (δ:ℝ) (hK:∀w,(K.degree w:ℝ)≤δ)
    (hYT:∀j,Y j⊆T j) (hdiv:∀j,(m+1)∣(Y j).card) (hratio:∀i,(A i).card=2*(B i).card)
    (hchangeY:∀j,(((((T j).filter (fun v=>σ (f j v)=true))\Y j).card+
      (Y j\((T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζh*(p*(T j).card))
    (hchangeA:∀i,((changed ((A i).image Sum.inl) ((S₀ i).filter (fun w=>σ (g i w)=true))).card:ℝ)≤
      ζe*(p*n))
    (hchangeB:∀i,((changed ((B i).image Sum.inr) ((T₀ i).filter (fun w=>σ (g i w)=true))).card:ℝ)≤
      ζe*(p*n))
    (hinter:∀a b:J⊕I,a≠b→((Sum.elim (fun j=>(Y j).image (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr) a∩
      Sum.elim (fun j=>(Y j).image (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr) b).card:ℝ)≤ρ^2*Fintype.card (V⊕U))
    (hmem:∀w,((Finset.univ.filter (fun a:J⊕I=>w∈Sum.elim
      (fun j=>(Y j).image (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr) a)).card:ℝ)≤ρ*Fintype.card (V⊕U))
    (hbudgetY:∀j,2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζh*(p*(T j).card))
    (hbudget:2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζe*(p*n))
    (hkeepP:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H'):
    Nonempty (OrdinaryPairingSelectedFactorsAvoiding m Q' F H' A B T Y (2*(ρ*Fintype.card (V⊕U))) K):=by
  have hratio':∀i,((A i).image (Sum.inl:V→V⊕U)).card=2*((B i).image (Sum.inr:U→V⊕U)).card:=by
    intro i
    rw [Finset.card_image_of_injective _ Sum.inl_injective,Finset.card_image_of_injective _ Sum.inr_injective]
    exact hratio i
  obtain ⟨D,M,hD,_hsub,hdis,havoid,hdeg⟩:=hgood K δ hK Y
    (fun i=>(A i).image Sum.inl) (fun i=>(B i).image Sum.inr)
    hYT hdiv hA hB hratio' hchangeY hchangeA hchangeB hinter hmem hbudgetY hbudget
  apply ordinary_pairing_factors_actual_host_avoiding m Q Q' F H H' K A B T Y D M hD
  · intro j;exact havoid (Sum.inl j)
  · intro i;exact havoid (Sum.inr i)
  · exact ordinary_rim_survives_of_physical_survives Q Q' H H' K hkeepP
  · exact hkeepP
  · exact hdis
  · exact hdeg
end Oberwolfach
