module

public import Oberwolfach.OrdinaryTriangleHubRowPacking
public import Oberwolfach.PrescribedCoverRootInputs
public import Oberwolfach.DeepCoverInnerIntersection
public import Oberwolfach.PrescribedDeepPackingUnion

@[expose] public section
/-! Once a prescribed-edge family exists, apply hub and triangle row covers
in its actual remainder and recombine the physically disjoint wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color Z:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Z]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_prescribed_recombination_with_union
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d D nh nr:ℕ)
    (I:Finset V) (J:Finset U) (u:Fin nh→U) (x:Fin nr→V)
    (hu:Function.Injective u) (hx:Function.Injective x) (huJ:∀i,u i∈J) (hxI:∀i,x i∈I)
    (e:Z→Sym2 V⊕(V×U)) (C:Z→OrdinaryWheel Q F H 3)
    (hC:∀i k,i≠k→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C k)))
    (hinner:∀i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
      (fun v a=>H v a∧v∈I∧a∈J)={e i})
    (hrim:∀i v,v∈I→Q.Adj (x i) v→Sum.inl s(x i,v)∈Finset.univ.image e)
    (hrow:∀i a,a∈J→H (x i) a→Sum.inr (x i,a)∈Finset.univ.image e)
    (hcol:∀i v,v∈I→H v (u i)→Sum.inr (v,u i)∈Finset.univ.image e)
    (hbal:∀i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card)
    (hdiv:∀i,3∣(Finset.univ.filter (fun v=>H v (u i))).card)
    (pR pH η θ ρ ρhub L:ℝ) (hL:0≤L) (hLhub:L≤ρhub*Fintype.card V)
    (hcap:2*L+nr+D+2*(3*d:ℕ)≤ρ*Fintype.card V)
    (hn:(nr:ℝ)≤θ*Fintype.card V) (hnh:(2*nh:ℝ)≤L)
    (hbalance:∀i,|pR*(P.neighborFinset (x i)).card/(2*(Finset.univ\J).card*pH)-1|≤η)
    (hQ:Q≤P\F) (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (hHub:OrdinaryHubCoverEvent 2 P F π d ρhub j sample)
    (hTri:OrdinaryTriangleTwoDomainRowEvent P F π d D Finset.univ Finset.univ
      (Finset.univ\J) pR pH η θ ρ j sample)
    (hFL:∀v,(F.degree v:ℝ)≤L)
    (hQR:∀v,((changed ((rawWheelGraph P sample).neighborFinset v)
      ((Q\wheelFamilyRim C).neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d sample j v))
      (Finset.univ.filter (fun a=>H v a∧¬wheelFamilySpokes C v a))).card:ℝ)≤L)
    (hHc:∀a,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d sample j v a))
      (Finset.univ.filter (fun v=>H v a∧¬wheelFamilySpokes C v a))).card:ℝ)≤L):
    ∃ M:Finset (OrdinaryWheel (Q\wheelFamilyRim C) F
        (fun v a=>H v a∧¬wheelFamilySpokes C v a) 3),
      (∀W∈M,∀T∈M,W≠T→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources T)) ∧
      (∀v∉I,(ordinaryWheelRimGraph M).degree v≤2*nh+2*nr) ∧
      (∀v∉I,(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤nh+nr) ∧
      (∀a∉J,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v a)).card≤3*nr) ∧
      ∃ R:Finset (OrdinaryWheel Q F H 3),
        (∀W∈R,∀T∈R,W≠T→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources T)) ∧
        R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
          (fun v a=>H v a∧v∈I∧a∈J)=Finset.univ.image e ∧
        ordinaryWheelRimGraph R=wheelFamilyRim C⊔ordinaryWheelRimGraph M ∧
        (∀v a,ordinaryPackingSpokes R v a↔wheelFamilySpokes C v a∨ordinaryPackingSpokes M v a) ∧
        (∀i v,(ordinaryWheelRimGraph R).Adj (x i) v↔Q.Adj (x i) v) ∧
        (∀i a,ordinaryPackingSpokes R (x i) a↔H (x i) a) ∧
        (∀i v,ordinaryPackingSpokes R v (u i)↔H v (u i)):=by
  let A:=Finset.univ\I
  let B:=Finset.univ\J
  have hcovered:Finset.univ.image e⊆ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C):=by
    have hh:=(prescribed_wheel_family_exact_union C _ e hC hinner).2.1
    rw [←hh];exact Finset.inter_subset_left
  have hgeo:=prescribed_cover_root_geometry C I J (Finset.univ.image x) (Finset.univ.image u) (Finset.univ.image e) hcovered
    (by intro t ht v hv h;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hrim i v hv h)
    (by intro t ht a ha h;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hrow i a ha h)
    (by intro a ha v hv h;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha;exact hcol i v hv h)
  have hb:=prescribed_wheel_family_root_balance C hC (Finset.univ.image x) (Finset.univ.image u)
    (by intro t ht;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht;exact hbal i)
    (by intro a ha;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha;exact hdiv i)
  have hxA:∀i,x i∉A:=by intro i;simpa [A] using hxI i
  have huB:∀i,u i∉B:=by intro i;simpa [B] using huJ i
  obtain ⟨M,hM,hMr,hMs,hMc,hMd,hMrow,hMcol,hsupport⟩:=ordinary_triangle_hub_row_packing
    P F (Q\wheelFamilyRim C) (fun v a=>H v a∧¬wheelFamilySpokes C v a) π d D nh nr A B u x hu hx
    pR pH η θ ρ ρhub L hL hLhub hcap hn hnh huB
    (fun i=>by convert hgeo.2.2 (u i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    (fun i=>by convert hb.2 (u i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    hxA
    (fun i=>by convert hgeo.1 (x i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    (fun i=>hgeo.2.1 (x i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    hbalance
    (fun i=>by convert hb.1 (x i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) using 1 <;> congr!)
    (sdiff_le.trans hQ) j sample hHub hTri hFL
    (by intro v;convert hQR v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hHr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro a;convert hHc a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hME:=ordinary_deep_packing_avoids_inner M I J u x Q H (by
    intro W hW
    rcases hsupport W hW with ⟨i,hi,hv⟩|⟨i,_,hi,hv⟩
    · exact Or.inl ⟨i,hi,fun v hvW=>(Finset.mem_sdiff.mp (hv v hvW)).2⟩
    · exact Or.inr ⟨i,(Finset.mem_sdiff.mp hi).2,fun v hvW=>(hv v hvW).imp_right (fun h=>(Finset.mem_sdiff.mp h).2)⟩)
  obtain ⟨R,hR,_,hRinner,hRunion,hRsun,hRr,hRs,hRc⟩:=prescribed_deep_packing_union C hC _ e hinner M hM hME x u hMr hMs hMc
  refine ⟨M,hM,?_,?_,?_,R,hR,hRinner,hRunion,hRsun,hRr,hRs,hRc⟩
  · intro v hv;exact hMd v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩)
  · intro v hv;exact hMrow v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩)
  · intro a ha;exact hMcol a (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ha⟩)
end Oberwolfach
