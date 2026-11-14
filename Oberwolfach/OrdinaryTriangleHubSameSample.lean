module

public import Oberwolfach.OrdinaryHubCoverNamed
public import Oberwolfach.OrdinaryTriangleAfterHubCover
public import Oberwolfach.OrdinaryForbiddenReferenceChanges

@[expose] public section
/-! On one sample, first apply the hub event and then the robust triangle
row event to its actual remainder, retaining physical disjointness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_hub_rows_same_sample
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d D nh nr:ℕ)
    (A:Finset V) (B:Finset U) (u:Fin nh→U) (x:Fin nr→V)
    (hu:Function.Injective u) (hx:Function.Injective x)
    (pR pH η θ ρ ρhub L:ℝ) (hL:0≤L) (hLhub:L≤ρhub*Fintype.card V)
    (hcap:2*L+nr+D+2*(3*d:ℕ)≤ρ*Fintype.card V)
    (hn:(nr:ℝ)≤θ*Fintype.card V) (hnh:(2*nh:ℝ)≤L)
    (hnotB:∀i,u i∉B) (hTX:∀i,Finset.univ.filter (fun v=>H v (u i))⊆A)
    (hdiv:∀i,3∣(Finset.univ.filter (fun v=>H v (u i))).card)
    (hxA:∀i,x i∉A) (hroot:∀i,Q.neighborFinset (x i)⊆A) (hrootB:∀i a,H (x i) a→a∈B)
    (hbalance:∀i,|pR*(P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η)
    (hbal:∀i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card)
    (hQ:Q≤P\F) (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (hHub:OrdinaryHubCoverEvent 2 P F π d ρhub j sample)
    (hTri:OrdinaryTriangleTwoDomainRowEvent P F π d D Finset.univ Finset.univ B pR pH η θ ρ j sample):
    let R:=rawWheelGraph P sample
    let H₀:=rawWheelSpokes π d sample j;
    (∀v,(F.degree v:ℝ)≤L) →
    (∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
    (∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
    (∀a,((changed (Finset.univ.filter (fun v=>H₀ v a)) (Finset.univ.filter (fun v=>H v a))).card:ℝ)≤L) →
    ∃ M:Finset (OrdinaryWheel Q F H 3),
      (∀W∈M,∀Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
        Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H v (u i))).image (fun v=>Sum.inr (v,u i))) ∧
      (∀v,(ordinaryWheelRimGraph M).degree v≤2*nh) ∧
      ∃ C:Fin nr→Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
        (fun v a=>H v a∧¬ordinaryPackingSpokes M v a) 3),
        (∀i,OrdinaryRowCover (C i) (x i) A 0) ∧
        (∀i k,i≠k→Disjoint ((C i).biUnion ordinaryWheelResources) ((C k).biUnion ordinaryWheelResources)) ∧
        (∀i,∀W∈C i,∀k,x k∈(ordinaryWheelRim W).support↔k=i) ∧
        (∀v∈A,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree v≤2*nr) ∧
        (∀v∈A,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) v)).card≤nr) ∧
        (∀a,(Finset.univ.filter (fun v=>ordinaryPackingSpokes (Finset.univ.biUnion C) v a)).card≤3*nr) ∧
        (∀i,Disjoint ((C i).biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources)):=by
  intro R H₀ hFL hQR hHr hHc
  have hinc (v:V):(2*(Finset.univ.filter (fun i=>H v (u i))).card:ℝ)≤ρhub*Fintype.card V:=by
    have hh:(Finset.univ.filter (fun i=>H v (u i))).card≤nh:=by simpa using Finset.card_filter_le (s:=Finset.univ) (fun i=>H v (u i))
    have hh':(2*(Finset.univ.filter (fun i=>H v (u i))).card:ℝ)≤2*nh:=by exact_mod_cast Nat.mul_le_mul_left 2 hh
    exact hh'.trans (hnh.trans hLhub)
  obtain ⟨M,hM,hunion,hdeg,_⟩:=hHub Q H L (hQ.trans sdiff_le) hL hLhub hFL hQR hHr hHc nh u hu hinc hdiv
  have hMdeg:∀v,(ordinaryWheelRimGraph M).degree v≤2*nh:=by
    intro v
    exact (hdeg v).trans (Nat.mul_le_mul_left 2 (by simpa using Finset.card_filter_le (s:=Finset.univ) (fun i=>H v (u i))))
  have hdis:Disjoint Q F:=by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact (hQ h.1).2 h.2
  have hrel:∀v,((changed ((R\F).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L:=by
    intro v
    have hh:=ordinary_forbidden_reference_change_le R Q F hdis v
    have hh':((changed ((R\F).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤
        ((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ):=by exact_mod_cast hh
    exact hh'.trans (hQR v)
  have hafter:=ordinary_triangle_event_after_hub_cover P F Q H π d D nh nr A B u x hu hx
    pR pH η θ ρ L hL hcap hn hnh hnotB hxA hroot hrootB hbalance hbal hQ j sample hTri
    (by intro v;convert hrel v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hHr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro a ha;convert hHc a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (fun i=>Finset.univ.filter (fun v=>H v (u i))) M hTX hMdeg hunion
  exact ⟨M,hM,hunion,hMdeg,hafter⟩
end Oberwolfach
