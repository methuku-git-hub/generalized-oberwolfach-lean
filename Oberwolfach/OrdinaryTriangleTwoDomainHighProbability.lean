module

public import Oberwolfach.OrdinaryTriangleTwoDomainEvent
public import Oberwolfach.TriangleRowCoverChangesNamedProbability
public import Oberwolfach.OrdinaryTwoDomainCommonEventTransfer
public import Oberwolfach.OrdinaryTwoDomainParentInputs

@[expose] public section
/-! One original two-domain sample supplies robust triangle row covers after
all permitted bounded edits. The auxiliary vertices and their random values
are projected out by the exact product-law identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_two_domain_rows_high_probability (K κ p:ℝ)
    (hK:1≤K) (hκ:0<κ) (hp:0<p) (hp1:p≤1):
    ∃η θ ρ:ℝ,0<η ∧ 0<θ ∧ 0<ρ ∧ ∀d q₀:ℕ,∀hd:2≤d,∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V) (A X:Finset V) (B:Finset U) (D:ℕ),
      N≤A.card → (Fintype.card V:ℝ)+Fintype.card U≤K*A.card →
      κ*A.card≤(B.card:ℝ) → B.card≤A.card → 2*d+1≤Fintype.card U →
      (∀x∈X,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      permutationConflictGraph π (3*d)≤F → (∀v,F.degree v≤D) →
      (∀v k,0<k→k<2*d+1→(π^k) v≠v) →
    ∀(pR pH:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
    ∀(q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀u a,0≤s u a)
      (hS:∀u,∑a,s u a≤ intervalUncoveredProbability d (∑a,q u a))
      (j:Color),(∀u,s u j=pH) →
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (OrdinaryTriangleTwoDomainRowEvent P F π d D A X B pR pH η θ ρ j):=by
  obtain ⟨η,θ,ρ,hη,hθ,hρ,h⟩:=triangle_row_cover_changes_named_high_probability K κ p hK hκ hp hp1
  refine ⟨η,θ,ρ,hη,hθ,hρ,?_⟩
  intro d q₀ hd
  obtain ⟨N,hN⟩:=h d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π A X B D hn hV hBA hBA' hU hdeg hF hD hπ
    pR pH hpR hpR1 hpH hpH1 q hq hQ s hs hS j hj
  obtain ⟨σ,hpow,hσ⟩:=ordinary_two_domain_permutation π (2*d+1) hU hπ
  have hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v):=by
    intro v
    simpa only [pow_one] using (hpow v 1).symm
  let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
  let P':=P.map e
  let F':=ordinaryTwoDomainConflict F σ (3*d)
  let A':=A.image (Sum.inl:V→V⊕U)
  let B':=ordinarySumHubSet (V:=V) B
  let X':=X.image (Sum.inl:V→V⊕U)
  let Y':=ordinarySumRimSet (V:=V) (U:=U)
  let Q:=ordinaryTwoDomainStart (V:=V) q
  let S:=ordinaryTwoDomainColour (V:=V) s j pH
  have hpH0:0≤pH:=(hp.trans_le hpH).le
  have hext:=ordinary_two_domain_sampling_extension (V:=V) d pH hpH0 hpH1 q hq hQ s hs hS j hj
  have hp0:0≤pR:=(hp.trans_le hpR).le
  have hparent:=ordinary_two_domain_parent_inputs P A X B K κ hV hBA hBA' hdeg
  have hconf:permutationConflictGraph σ (3*d)≤F':=
    (ordinary_two_domain_conflict_properties F π σ (3*d) D hcomm hF hD).1
  have hn':N≤A'.card:=by simpa only [A',Finset.card_image_of_injective _ Sum.inl_injective] using hn
  have hbig:=hN (V⊕U) Γ Color P' F' σ A' B' X' Y' hn' hparent.1 hparent.2.1 hparent.2.2.1
    (ordinary_sum_domains_disjoint B) hparent.2.2.2.1 hparent.2.2.2.2.1
    (by intro x hx v hv;convert hparent.2.2.2.2.2 x hx v hv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hconf hσ
    pR pH hpR hpR1 hpH hpH1 Q hext.1 hext.2.1 S hext.2.2.1 hext.2.2.2.1 j hext.2.2.2.2.1
  let E:RawWheelOutcome V U Γ Color→Prop:=OrdinaryTriangleTwoDomainRowEvent P F π d D A X B pR pH η θ ρ j
  let Ebig:RawWheelOutcome (V⊕U) (V⊕U) Γ Color→Prop:=TriangleRowCoverChangesEvent P' F' σ d A' B' X' Y' (ordinary_sum_domains_disjoint B) pR pH η θ ρ j
  have htransfer:=ordinary_two_domain_common_event_transfer d hd pR pH hp0 hpR1 hpH0 hpH1 q hq hQ s hs hS j hj
    (1-1/(A.card:ℝ)^q₀) E Ebig
  have hbig':(1-1/(A.card:ℝ)^q₀)≤
      (FiniteLaw.pi (rawWheelLaw (V:=V⊕U) (fun _=>pR) (fun _=>hp0) (fun _=>hpR1)
        d hd Q hext.1 hext.2.1 S hext.2.2.1 hext.2.2.2.1)).probability Ebig:=by
    convert hbig using 1 <;> simp only [Ebig,A',Finset.card_image_of_injective _ Sum.inl_injective] <;>
      congr! 10 <;> exact Subsingleton.elim _ _
  have hresult:=htransfer
    (by convert hbig' using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (fun sample hs=>
    ordinary_triangle_augmented_event_implies_two_domain P F π σ d D hcomm hF hD A X B pR pH η θ ρ j sample hs)
  convert hresult using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
