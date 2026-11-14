module

public import Oberwolfach.OrdinaryTriangleHubSameSample
public import Oberwolfach.HubRowPackingUnion
public import Oberwolfach.HubRowPackingSupport

@[expose] public section
/-! Convert the actual successive hub and triangle row covers into a single
physical packing on the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_hub_row_packing
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
    (hTri:OrdinaryTriangleTwoDomainRowEvent P F π d D Finset.univ Finset.univ B pR pH η θ ρ j sample)
    (hFL:∀v,(F.degree v:ℝ)≤L)
    (hQR:∀v,((changed ((rawWheelGraph P sample).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d sample j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hHc:∀a,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d sample j v a))
      (Finset.univ.filter (fun v=>H v a))).card:ℝ)≤L):
    ∃ M:Finset (OrdinaryWheel Q F H 3),
      (∀W∈M,∀Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      (∀i v,(ordinaryWheelRimGraph M).Adj (x i) v↔Q.Adj (x i) v) ∧
      (∀i a,ordinaryPackingSpokes M (x i) a↔H (x i) a) ∧
      (∀i v,ordinaryPackingSpokes M v (u i)↔H v (u i)) ∧
      (∀v∈A,(ordinaryWheelRimGraph M).degree v≤2*nh+2*nr) ∧
      (∀v∈A,(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr) ∧
      (∀a∈B,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v a)).card≤3*nr) ∧
      (∀W∈M,(∃i,ordinaryWheelHub W=u i ∧ ∀v∈(ordinaryWheelRim W).support,v∈A) ∨
        (∃i,x i∈(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∈B ∧
          ∀v∈(ordinaryWheelRim W).support,v=x i∨v∈A)):=by
  obtain ⟨Mh,hMh,hunion,hdeg,Cr,hCr,hcross,hunique,_,_,_,_⟩:=
    ordinary_triangle_hub_rows_same_sample P F Q H π d D nh nr A B u x hu hx
      pR pH η θ ρ ρhub L hL hLhub hcap hn hnh hnotB hTX hdiv hxA hroot hrootB hbalance hbal hQ j sample hHub hTri
      (by intro v;convert hFL v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
      (by intro v;convert hQR v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
      (by intro v;convert hHr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
      (by intro a;convert hHc a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  obtain ⟨M,hM,_,hr,hs,hc,hd,hdrow,hdcol,horigin⟩:=ordinary_hub_row_union_packing_with_origins
    Mh u (fun i=>Finset.univ.filter (fun v=>H v (u i)))
    (by convert hunion using 1 <;> congr!) (fun i=>rfl) hMh hdeg A B hnotB Cr x hxA hCr hcross
  have hsupport:=ordinary_hub_row_union_support (by omega) Mh u hu
    (fun i=>Finset.univ.filter (fun v=>H v (u i))) A B hTX
    (by convert hunion using 1 <;> congr!) Cr x hCr (fun i W hW=>(hunique i W hW i).mpr rfl)
    hrootB M horigin
  refine ⟨M,hM,hr,hs,hc,?_,?_,?_,hsupport⟩
  · intro v hv;convert hd v hv using 1 <;> simp <;> omega
  · intro v hv;convert hdrow v hv using 1 <;> simp
  · intro a ha;convert hdcol a ha using 1 <;> omega
end Oberwolfach
