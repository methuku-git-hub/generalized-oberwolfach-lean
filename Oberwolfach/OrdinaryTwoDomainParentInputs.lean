module

public import Oberwolfach.OrdinaryTwoDomainChangeGeometry

@[expose] public section
/-! Fixed triangle parent domains and their density assumptions transport
exactly to the auxiliary sum type before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_two_domain_parent_inputs (P:SimpleGraph V) (A X:Finset V) (B:Finset U)
    (K κ:ℝ) (hV:(Fintype.card V:ℝ)+Fintype.card U≤K*A.card)
    (hBA:κ*A.card≤(B.card:ℝ)) (hBA':B.card≤A.card)
    (hdeg:∀x∈X,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let A':=A.image (Sum.inl:V→V⊕U)
    let B':=ordinarySumHubSet (V:=V) B
    let X':=X.image (Sum.inl:V→V⊕U)
    let Y':=ordinarySumRimSet (V:=V) (U:=U);
    (Fintype.card (V⊕U):ℝ)≤K*A'.card ∧ A'⊆Y' ∧ X'⊆Y' ∧
    κ*A'.card≤(B'.card:ℝ) ∧ B'.card≤A'.card ∧
    (∀x∈X',∀v∈insert x A', (3/4:ℝ)*A'.card≤((A'∩(P.map e).neighborFinset v).card:ℝ)):=by
  intro e A' B' X' Y'
  have hA:A'.card=A.card:=Finset.card_image_of_injective _ Sum.inl_injective
  have hB:B'.card=B.card:=Finset.card_image_of_injective _ Sum.inr_injective
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hA,Fintype.card_sum,Nat.cast_add];exact hV
  · intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  · intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  · simpa only [hA,hB] using hBA
  · simpa only [hA,hB] using hBA'
  · intro z hz w hw
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    have hw':w∈(insert x A).image (Sum.inl:V→V⊕U):=by
      simpa only [Finset.image_insert] using hw
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw'
    have hh:=ordinary_sum_rim_neighbours (U:=U) P A v
    change A'∩(P.map e).neighborFinset (Sum.inl v)=(A∩P.neighborFinset v).image Sum.inl at hh
    have hc:((A∩P.neighborFinset v).image (Sum.inl:V→V⊕U)).card=(A∩P.neighborFinset v).card:=
      Finset.card_image_of_injective _ Sum.inl_injective
    rw [hh,hc,hA]
    exact hdeg x hx v hv
end Oberwolfach
