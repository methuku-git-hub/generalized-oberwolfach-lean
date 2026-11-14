module

public import Oberwolfach.MixedFreshBoundaryEventDefinition
public import Oberwolfach.OrdinaryTriangleFreshFactorsActual
public import Oberwolfach.OrdinaryPhysicalGraphDeletion

@[expose] public section
/-! A good mixed fresh event supplies actual selected boundary factors after
an adaptive physical deletion and adaptive choice of surviving classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J E:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J] [Fintype E]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J] [DecidableEq E]

theorem ordinary_triangle_fresh_event_actual_host
    (p ρ ζ:ℝ) (Q Q' F:SimpleGraph V) (H H':V→U→Prop)
    (T:J→Finset V) (S₀ T₀:I→Finset (V⊕U)) (f:J→V↪E) (g:I→(V⊕U)↪E)
    (hST:∀i,Disjoint (S₀ i) (T₀ i)) (σ:E→Bool)
    (hgood:MixedFreshBoundaryAvoidingEvent p ρ ζ Q F (ordinaryPhysicalGraph Q H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U) T S₀ T₀ f g hST σ)
    (Y:J→Finset V) (A:I→Finset V) (B:I→Finset U)
    (hAB:∀i,Disjoint ((A i).image Sum.inl) ((B i).image Sum.inr))
    (hA:∀i,(A i).image Sum.inl⊆S₀ i) (hB:∀i,(B i).image Sum.inr⊆T₀ i)
    (K:SimpleGraph (V⊕U)) (δ:ℝ) (hK:∀w,(K.degree w:ℝ)≤δ)
    (hYT:∀j,Y j⊆T j) (hdiv:∀j,3∣(Y j).card)
    (hratio:∀i,(((A i).image Sum.inl∪(B i).image Sum.inr)∩S₀ i).card=
      2*((((A i).image Sum.inl∪(B i).image Sum.inr)∩T₀ i).card))
    (hchangeY:∀j,(((((T j).filter (fun v=>σ (f j v)=true))\Y j).card+
      (Y j\((T j).filter (fun v=>σ (f j v)=true))).card:ℕ):ℝ)≤ζ*(p*(T j).card))
    (hchangeZ:∀i,(((((S₀ i∪T₀ i).filter (fun w=>σ (g i w)=true))\
      ((A i).image Sum.inl∪(B i).image Sum.inr)).card+
      (((A i).image Sum.inl∪(B i).image Sum.inr)\((S₀ i∪T₀ i).filter (fun w=>σ (g i w)=true))).card:ℕ):ℝ)≤ζ*(p*(T₀ i).card))
    (hinter:∀a b:J⊕I,a≠b→((Sum.elim (fun j=>(Y j).image (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr) a∩
      Sum.elim (fun j=>(Y j).image (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr) b).card:ℝ)≤ρ^2*Fintype.card (V⊕U))
    (hmem:∀w,((Finset.univ.filter (fun a:J⊕I=>w∈Sum.elim
      (fun j=>(Y j).image (Function.Embedding.inl:V↪V⊕U))
      (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr) a)).card:ℝ)≤ρ*Fintype.card (V⊕U))
    (hbudgetY:∀j,2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(T j).card))
    (hbudgetZ:∀i,2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤ζ*(p*(T₀ i).card))
    (hkeepP:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H'):
    Nonempty (OrdinaryTriangleSelectedFactors Q' F H' A B T Y hAB (2*(ρ*Fintype.card (V⊕U)))):=by
  let Z:=fun i:I=>(A i).image Sum.inl∪(B i).image Sum.inr
  have hZU:∀i,Z i⊆S₀ i∪T₀ i:=by
    intro i w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · exact Finset.mem_union_left _ (hA i hw)
    · exact Finset.mem_union_right _ (hB i hw)
  obtain ⟨D,M,hD,hM,_hs,hdis,havoid,hdeg⟩:=
    hgood Y Z K δ hK hYT hdiv hZU hratio hchangeY hchangeZ hinter hmem hbudgetY hbudgetZ
  apply ordinary_triangle_fresh_factors_actual_host Q Q' F H H' K A B S₀ T₀ T Y hST hAB hA hB D M hD hM
  · intro j;exact havoid (Sum.inl j)
  · intro i;exact havoid (Sum.inr i)
  · exact ordinary_rim_survives_of_physical_survives Q Q' H H' K hkeepP
  · exact hkeepP
  · exact hdis
  · exact hdeg
end Oberwolfach
