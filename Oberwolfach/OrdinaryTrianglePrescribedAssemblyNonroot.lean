module

public import Oberwolfach.OrdinaryPrescribedFamilyFromEvent
public import Oberwolfach.OrdinaryTrianglePrescribedRecombinationNonroot
public import Oberwolfach.OrdinaryLevelChangeBudget

@[expose] public section
/-! On one sample, choose the prescribed family, charge its actual deletions,
and cover the resulting protected stars with hub and triangle wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_prescribed_assembly_with_nonroot_union
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d D:ℕ)
    (a p γ L L' pR pH η θ ρ ρhub:ℝ) (ha:0≤a) (hL:0≤L) (hL':0≤L')
    (hLV:6*L≤(p^6*γ/4)*Fintype.card V) (hLU:6*L≤(p^6*γ/4)*Fintype.card U)
    (hbudget:L+12*a*Fintype.card V≤L') (hLhub:L'≤ρhub*Fintype.card V)
    (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (I:Finset V) (J:Finset U) (hI:(I.card:ℝ)≤p^6*γ*Fintype.card V/8)
    (hJ:(J.card:ℝ)≤p^6*γ*Fintype.card U/8)
    (hPre:OrdinaryPrescribedInnerEvent 3 P F π d a p γ Finset.univ Finset.univ j sample)
    (hHub:OrdinaryHubCoverEvent 2 P F π d ρhub j sample)
    (hTri:OrdinaryTriangleTwoDomainRowEvent P F π d D Finset.univ Finset.univ
      (Finset.univ\J) pR pH η θ ρ j sample)
    (hQ:Q≤P\F) (hFL:∀v,(F.degree v:ℝ)≤L)
    (hQR:∀v,((changed ((rawWheelGraph P sample).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d sample j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hHc:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d sample j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (Nr Ns D₀:ℕ) (v w:Fin Nr→V)
    (hv:∀i,v i∈I) (hw:∀i,w i∈I) (hvw:∀i,Q.Adj (v i) (w i)) (hFvw:∀i,¬F.Adj (v i) (w i))
    (hedge:∀i k,i≠k→¬((v i=v k∧w i=w k)∨(v i=w k∧w i=v k)))
    (hend:∀b,(Finset.univ.filter (fun i=>b=v i∨b=w i)).card≤D₀)
    (z:Fin Ns→V) (b:Fin Ns→U) (hz:∀i,z i∈I) (hb:∀i,b i∈J) (hH:∀i,H (z i) (b i))
    (hspoke:Function.Injective (fun i=>(z i,b i)))
    (hsend:∀t,(Finset.univ.filter (fun i=>t=z i)).card≤D₀)
    (hshub:∀t,(Finset.univ.filter (fun i=>b i=t)).card≤D₀)
    (hN:((Nr+Ns:ℕ):ℝ)≤a^2*(Fintype.card V:ℝ)^2) (hD₀:(D₀:ℝ)≤a*Fintype.card V)
    (nh nr:ℕ) (u:Fin nh→U) (x:Fin nr→V)
    (hu:Function.Injective u) (hx:Function.Injective x) (huJ:∀i,u i∈J) (hxI:∀i,x i∈I)
    (hcap:2*L'+nr+D+2*(3*d:ℕ)≤ρ*Fintype.card V)
    (hn:(nr:ℝ)≤θ*Fintype.card V) (hnh:(2*nh:ℝ)≤L')
    (hbalance:∀i,|pR*(P.neighborFinset (x i)).card/(2*(Finset.univ\J).card*pH)-1|≤η)
    (hbal:∀i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card)
    (hdiv:∀i,3∣(Finset.univ.filter (fun v=>H v (u i))).card)
    (hrim:∀i t,t∈I→Q.Adj (x i) t→Sum.inl s(x i,t)∈Finset.univ.image
      (Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i))))
    (hrow:∀i t,t∈J→H (x i) t→Sum.inr (x i,t)∈Finset.univ.image
      (Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i))))
    (hcol:∀i t,t∈I→H t (u i)→Sum.inr (t,u i)∈Finset.univ.image
      (Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i)))):
    let e:(Fin Nr⊕Fin Ns)→Sym2 V⊕(V×U):=Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i));
    ∃ C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H 3,
      (∀i k,i≠k→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C k))) ∧
      (∀i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
        (fun t u=>H t u∧t∈I∧u∈J)={e i}) ∧
      (∀t,((wheelFamilyRim C).degree t:ℝ)≤12*a*Fintype.card V) ∧
      (∀t,((Finset.univ.filter (wheelFamilySpokes C t)).card:ℝ)≤6*a*Fintype.card V) ∧
      (∀u,((Finset.univ.filter (fun t=>wheelFamilySpokes C t u)).card:ℝ)≤9*a*Fintype.card V) ∧
      ∃ M:Finset (OrdinaryWheel (Q\wheelFamilyRim C) F (fun v a=>H v a∧¬wheelFamilySpokes C v a) 3),
        (∀W∈M,∀T∈M,W≠T→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources T)) ∧
        (∀v,(∀i,v≠x i)→(ordinaryWheelRimGraph M).degree v≤2*nh+2*nr) ∧
        (∀v,(∀i,v≠x i)→(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr) ∧
        (∀a,(∀i,a≠u i)→(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v a)).card≤3*nr) ∧
        ∃ R:Finset (OrdinaryWheel Q F H 3),
          (∀W∈R,∀T∈R,W≠T→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources T)) ∧
          R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
            (fun v a=>H v a∧v∈I∧a∈J)=Finset.univ.image e ∧
          ordinaryWheelRimGraph R=wheelFamilyRim C⊔ordinaryWheelRimGraph M ∧
          (∀v a,ordinaryPackingSpokes R v a↔wheelFamilySpokes C v a∨ordinaryPackingSpokes M v a) ∧
          (∀i v,(ordinaryWheelRimGraph R).Adj (x i) v↔Q.Adj (x i) v) ∧
          (∀i t,ordinaryPackingSpokes R (x i) t↔H (x i) t) ∧
          (∀i v,ordinaryPackingSpokes R v (u i)↔H v (u i)):=by
  dsimp only
  obtain ⟨C,hC,hi,hd,hr,hc⟩:=ordinary_prescribed_family_from_event P F Q H π d a p γ L j sample hPre
    hL hLV hLU hQR hHr hHc I J hI hJ Nr Ns D₀ v w hv hw hvw hFvw hedge hend z b hz hb hH hspoke hsend hshub hN hD₀
  have hchanges:=ordinary_level_deletion_change_budget (rawWheelGraph P sample) Q F (rawWheelSpokes π d sample j) H 3 C
    L L L (12*a*Fintype.card V) (6*a*Fintype.card V) (9*a*Fintype.card V)
    (by intro t;convert hQR t using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro t;convert hHr t using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro t;convert hHc t using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro t;convert hd t using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro t;convert hr t using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro t;convert hc t using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hs:0≤a*Fintype.card V:=mul_nonneg ha (Nat.cast_nonneg _)
  obtain ⟨M,hM,hMd,hMr,hMc,R,hR,hRi,hRunion,hRsun,hRr,hRs,hRc⟩:=ordinary_triangle_prescribed_recombination_with_nonroot_union
    P F Q H π d D nh nr I J u x hu hx huJ hxI
    (Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i))) C hC hi hrim hrow hcol hbal hdiv
    pR pH η θ ρ ρhub L' hL' hLhub hcap hn hnh hbalance hQ j sample hHub hTri
    (fun t=>(hFL t).trans (by nlinarith only [hbudget,hs]))
    (by intro t;have hh:=hchanges.1 t;convert hh.trans hbudget using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro t;have hh:=hchanges.2.1 t;have ht:L+6*a*Fintype.card V≤L':=by nlinarith only [hbudget,hs];
        convert hh.trans ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro t;have hh:=hchanges.2.2 t;have ht:L+9*a*Fintype.card V≤L':=by nlinarith only [hbudget,hs];
        convert hh.trans ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  exact ⟨C,hC,hi,hd,hr,hc,M,hM,hMd,hMr,hMc,R,hR,hRi,hRunion,hRsun,hRr,hRs,hRc⟩
end Oberwolfach
