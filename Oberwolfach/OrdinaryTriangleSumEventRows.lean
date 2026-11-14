module

public import Oberwolfach.TriangleRowCoverChangesNamed
public import Oberwolfach.OrdinaryTriangleSumHostInputs
public import Oberwolfach.OrdinaryTriangleSumRootInputs

@[expose] public section
/-! Apply the robust triangle event to the exact rim, spoke and root data
constructed from the original projected sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_sum_event_rows
    (P F Q:SimpleGraph V) (J:V→U→Prop) (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U))
    (d D:ℕ) (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v))
    (hF:permutationConflictGraph π (3*d)≤F) (hD:∀v,F.degree v≤D) (hQ:Q≤P\F)
    (sample:RawWheelOutcome (V⊕U) (V⊕U) Γ Color) (j:Color)
    (A X Z:Finset V) (B:Finset U) (n:ℕ) (x:Fin n→V)
    (pR pH η θ ρ L:ℝ) (hL:0≤L) (hLρ:L+D+2*(3*d:ℕ)≤ρ*A.card)
    (hZA:Z⊆A) (hn:(n:ℝ)≤θ*A.card) (hx:Function.Injective x) (hX:∀i,x i∈X)
    (hZ:∀i,x i∉Z) (hroot:∀i,Q.neighborFinset (x i)⊆Z) (hJ:∀i u,J (x i) u→u∈B)
    (hbalance:∀i,|pR*(A∩P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η)
    (hbal:∀i,Q.degree (x i)=2*(Finset.univ.filter (J (x i))).card):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let f:U↪V⊕U:=⟨Sum.inr,Sum.inr_injective⟩
    let small:=ordinaryRawRestrictPair e f sample
    let R:=rawWheelGraph P small\F
    let H:=rawWheelSpokes π d small j;
    (∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
    (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L) →
    (∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L) →
    let P':=P.map e
    let F':=ordinaryTwoDomainConflict F σ (3*d)
    let Q':=Q.map e
    let J':=ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧J v u)
    let A':=A.image (Sum.inl:V→V⊕U)
    let B':=ordinarySumHubSet (V:=V) B
    let X':=X.image (Sum.inl:V→V⊕U)
    let Y':=ordinarySumRimSet (V:=V) (U:=U)
    let Z':=Z.image (Sum.inl:V→V⊕U)
    let x':Fin n→V⊕U:=fun i=>e (x i);
    TriangleRowCoverChangesEvent P' F' σ d A' B' X' Y' (ordinary_sum_domains_disjoint B) pR pH η θ ρ j sample →
    ∃ M:Fin n→Finset (OrdinaryWheel Q' F' J'.Adj 3),
      (∀i,OrdinaryRowCover (M i) (x' i) Z' 0) ∧
      (∀i k,i≠k→Disjoint ((M i).biUnion ordinaryWheelResources) ((M k).biUnion ordinaryWheelResources)):=by
  intro e f small R H hR hrow hcol P' F' Q' J' A' B' X' Y' Z' x' hBig
  let L':ℝ:=L+D+2*(3*d:ℕ)
  have hL':0≤L':=by dsimp [L'];positivity
  have hcap:L'≤ρ*A'.card:=by
    have hc:A'.card=A.card:=Finset.card_image_of_injective _ Sum.inl_injective
    rw [hc]
    exact hLρ
  have hhost:=ordinary_triangle_sum_host_inputs P F Q J π σ (3*d) D d hcomm hF hD hQ sample j A B L hL
    (by intro v;convert hR v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hrow v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hcol u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hroots:=ordinary_triangle_sum_root_inputs P Q J A X Z B n x pR pH η θ hZA hn hx hX hZ hroot hJ hbalance hbal
  obtain ⟨M,hM,hcross,_⟩:=hBig Q' J' L' hL' hcap hhost.1
    (by intro z;convert hhost.2.1 z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hhost.2.2.1 z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hhost.2.2.2.1 z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z hz;convert hhost.2.2.2.2.1 z hz using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hhost.2.2.2.2.2.1 z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hhost.2.2.2.2.2.2.1 z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hhost.2.2.2.2.2.2.2.1 z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hhost.2.2.2.2.2.2.2.2.1 z using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro z hz;convert hhost.2.2.2.2.2.2.2.2.2 z hz using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    Z' hroots.1 n x' hroots.2.1 hroots.2.2.1
    hroots.2.2.2.1 hroots.2.2.2.2.1
    (by intro i;convert hroots.2.2.2.2.2.1 i using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro i;convert hroots.2.2.2.2.2.2.1 i using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by intro i;convert hroots.2.2.2.2.2.2.2 i using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
  exact ⟨M,hM,hcross⟩
end Oberwolfach
