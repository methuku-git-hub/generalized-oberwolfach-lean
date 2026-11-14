module

public import Oberwolfach.OrdinaryTrianglePrescribedAssemblyNonroot
public import Oberwolfach.OrdinaryTrianglePrescribedUnionBounds
public import Oberwolfach.PrescribedEdgeEnumeration

@[expose] public section
/-! Replace indexed prescribed edges and roots by the actual finite sets,
while retaining the same-sample event and all numerical hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_finite_packing_with_nonroot_degree
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
    (E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ)
    (hE:E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J))
    (hFE:∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w)
    (hDE:∀t,(E.filter (ordinaryResourceIncident t)).card≤D₀)
    (hEcard:(E.card:ℝ)≤a^2*(Fintype.card V:ℝ)^2) (hD₀:(D₀:ℝ)≤a*Fintype.card V)
    (T:Finset V) (W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hcap:2*L'+T.card+D+2*(3*d:ℕ)≤ρ*Fintype.card V)
    (hTcard:(T.card:ℝ)≤θ*Fintype.card V) (hWcard:(2*W.card:ℝ)≤L')
    (hbalance:∀v∈T,|pR*(P.neighborFinset v).card/(2*(Finset.univ\J).card*pH)-1|≤η)
    (hWdiv:∀u∈W,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hTbal:∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hErim:∀v∈T,∀w∈I,Q.Adj v w→Sum.inl s(v,w)∈E)
    (hErow:∀v∈T,∀u∈J,H v u→Sum.inr (v,u)∈E)
    (hEcol:∀u∈W,∀v∈I,H v u→Sum.inr (v,u)∈E):
    ∃ R:Finset (OrdinaryWheel Q F H 3),
      (∀A∈R,∀B∈R,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
        (fun v u=>H v u∧v∈I∧u∈J)=E ∧
      (∀v∈T,∀w,(ordinaryWheelRimGraph R).Adj v w↔Q.Adj v w) ∧
      (∀v∈T,∀u,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀u∈W,∀v,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀v∉T,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inl v):ℝ)≤
        18*a*Fintype.card V+3*((W.card:ℝ)+T.card)) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u):ℝ)≤
        9*a*Fintype.card V+3*(T.card:ℝ)):=by
  obtain ⟨Nr,Ns,v,w,z,b,hcard,hv,hw,hvw,hFvw,hedge,hend,hz,hb,hsp,hspinj,hsrow,hscol,heE⟩:=
    prescribed_inner_edge_enumeration Q F H I J E D₀ hE hFE hDE
  obtain ⟨x,hx,hxT⟩:=finset_injective_enumeration T
  obtain ⟨u,hu,huW⟩:=finset_injective_enumeration W
  have hxmem (i:Fin T.card):x i∈T:=hxT ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have humem (i:Fin W.card):u i∈W:=huW ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hxsur (v:V) (hv:v∈T):∃ i,x i=v:=by
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hxT.symm ▸ hv);exact ⟨i,hi⟩
  have husur (v:U) (hv:v∈W):∃ i,u i=v:=by
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (huW.symm ▸ hv);exact ⟨i,hi⟩
  have hNv:((Nr+Ns:ℕ):ℝ)≤a^2*(Fintype.card V:ℝ)^2:=by rw [hcard];exact hEcard
  have out:=ordinary_triangle_prescribed_assembly_with_nonroot_union P F Q H π d D a p γ L L' pR pH η θ ρ ρhub
    ha hL hL' hLV hLU hbudget hLhub j sample I J hI hJ hPre hHub hTri hQ hFL hQR hHr hHc
    Nr Ns D₀ v w hv hw hvw hFvw hedge hend z b hz hb hsp hspinj hsrow hscol hNv hD₀
    W.card T.card u x hu hx (fun i=>hWJ (humem i)) (fun i=>hTI (hxmem i))
    hcap hTcard hWcard (fun i=>hbalance _ (hxmem i)) (fun i=>hTbal _ (hxmem i)) (fun i=>hWdiv _ (humem i))
    (by intro i t ht hh;rw [heE];exact hErim _ (hxmem i) t ht hh)
    (by intro i t ht hh;rw [heE];exact hErow _ (hxmem i) t ht hh)
    (by intro i t ht hh;rw [heE];exact hEcol _ (humem i) t ht hh)
  dsimp only at out
  rw [heE] at out
  obtain ⟨C,hC,hi,hd,hr,hc,M,hM,hMd,hMr,hMc,R,hR,hRi,hRunion,hRsun,hRr,hRs,hRc⟩:=out
  have houter:=ordinary_triangle_prescribed_union_outer_bounds C M R T W a W.card T.card hRunion hRsun
    (by intro v;convert hd v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hc u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;have hh:=hMd v (by intro i he;apply hv;simpa [he] using hxmem i);convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;have hh:=hMr v (by intro i he;apply hv;simpa [he] using hxmem i);convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u hu;have hh:=hMc u (by intro i he;apply hu;simpa [he] using humem i);convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  refine ⟨R,hR,hRi,?_,?_,?_,houter.1,houter.2⟩
  · intro v hv;obtain ⟨i,rfl⟩:=hxsur v hv;exact hRr i
  · intro v hv;obtain ⟨i,rfl⟩:=hxsur v hv;exact hRs i
  · intro v hv;obtain ⟨i,rfl⟩:=husur v hv;exact hRc i
end Oberwolfach
