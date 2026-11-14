module

public import Oberwolfach.OrdinaryPrescribedHubRowSeparateLoad
public import Oberwolfach.PrescribedEdgeEnumeration
public import Oberwolfach.DeepWheelRoots

@[expose] public section

/-! The ordinary deep-cover event for actual finite edge and root sets.
The only enumeration in the proof counts each unordered rim edge once.
All root balances, host changes and inner incidences are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_cover_finite_sets_separate_load_event (m:ℕ) (hm:3≤m) (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ K:ℕ,0<K ∧ ∃ a ε₀ ρ θ:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θ ∧
    ∀ aLoad:ℝ,0<aLoad→aLoad≤a→∀ Dmax d q₀:ℕ,∀ hd:2≤d,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (J:Finset U),N≤Fintype.card V →
      (J.card:ℝ)≤a*Fintype.card V →
      ω*Fintype.card V≤((Finset.univ\J).card:ℝ) → Fintype.card U≤Fintype.card V →
      (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,F.degree v≤Dmax) → permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH D ε:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) → pR*D=2*Fintype.card U*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp.le.trans hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (Q:SimpleGraph V) (H:V→U→Prop) (L:ℝ),Q≤P → 0≤L → L≤ρ*Fintype.card V →
        (∀ v,(F.degree v:ℝ)≤L) →
        (∀ v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
        (∀ v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
        (∀ u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
          (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L) →
      ∀ I:Finset V,(I.card:ℝ)≤a*Fintype.card V →
      ∀ (E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ),
        E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J) →
        (∀ v w,Sum.inl s(v,w)∈E→¬F.Adj v w) →
        (∀ t,(E.filter (ordinaryResourceIncident t)).card≤D₀) →
        (E.card:ℝ)≤aLoad^2*(Fintype.card V:ℝ)^2 → (D₀:ℝ)≤aLoad*Fintype.card V →
      ∀ (T:Finset V) (W:Finset U),T⊆I → W⊆J →
        (T.card:ℝ)≤θ*Fintype.card V → (2*W.card:ℝ)≤L →
        (∀ u∈W,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card) →
        (∀ v∈T,∀ w,Q.Adj v w→¬F.Adj v w) →
        (∀ v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card) →
        (∀ v∈T,∀ w∈I,Q.Adj v w→Sum.inl s(v,w)∈E) →
        (∀ v∈T,∀ u∈J,H v u→Sum.inr (v,u)∈E) →
        (∀ u∈W,∀ v∈I,H v u→Sum.inr (v,u)∈E) →
      ∃ PE:Finset (OrdinaryWheel Q F H (m+1)),
        (∀ A∈PE,∀ B∈PE,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
        PE.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
          (fun v u=>H v u∧v∈I∧u∈J)=E ∧
        (∀ Y∈PE,(ordinaryWheelResources Y∩E).card=1) ∧
        (∀ v,((ordinaryWheelRimGraph PE).degree v:ℝ)≤12*aLoad*Fintype.card V) ∧
        (∀ v,((Finset.univ.filter (ordinaryPackingSpokes PE v)).card:ℝ)≤6*aLoad*Fintype.card V) ∧
        (∀ u,((Finset.univ.filter (fun v=>ordinaryPackingSpokes PE v u)).card:ℝ)≤3*aLoad*Fintype.card V*(m+1)) ∧
      ∃ M:Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph PE) F
          (fun v u=>H v u∧¬ordinaryPackingSpokes PE v u) (m+1)),
        (∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
        (∀ v∈T,∀ w,(ordinaryWheelRimGraph M).Adj v w↔(Q\ordinaryWheelRimGraph PE).Adj v w) ∧
        (∀ v∈T,∀ u,ordinaryPackingSpokes M v u↔H v u∧¬ordinaryPackingSpokes PE v u) ∧
        (∀ u∈W,∀ v,ordinaryPackingSpokes M v u↔H v u∧¬ordinaryPackingSpokes PE v u) ∧
        (∀ v∉I,(ordinaryWheelRimGraph M).degree v≤2*W.card+T.card*(2*(K+1))) ∧
        (∀ v∉I,(Finset.univ.filter (ordinaryPackingSpokes M v)).card≤W.card+T.card*(K+1)) ∧
        (∀ u∉J,(Finset.univ.filter (fun v=>ordinaryPackingSpokes M v u)).card≤T.card*(m+1)) ∧
        (∀ Y∈M,(ordinaryWheelVertices Y∩(T.image Sum.inl∪W.image Sum.inr)).card=1) ∧
        (∀ v∈I\T,∀ w,¬(ordinaryWheelRimGraph M).Adj v w) ∧
        (∀ v∈I\T,∀ u,¬ordinaryPackingSpokes M v u) ∧
        (∀ u∈J\W,∀ v,¬ordinaryPackingSpokes M v u) ∧
      ∃ P':Finset (OrdinaryWheel Q F H (m+1)),
        (∀ A∈P',∀ B∈P',A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
        P'.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
          (fun v u=>H v u∧v∈I∧u∈J)=E ∧
        (∀ v∈T,∀ w,(ordinaryWheelRimGraph P').Adj v w↔Q.Adj v w) ∧
        (∀ v∈T,∀ u,ordinaryPackingSpokes P' v u↔H v u) ∧
        (∀ u∈W,∀ v,ordinaryPackingSpokes P' v u↔H v u)):=by
  obtain ⟨K,hK,a,ε₀,ρ,θ,ha,hε₀,hρ,hθ,hmain⟩:=
    ordinary_prescribed_hub_row_common_event_separate_load m hm α p ω hα hp hp1 hω
  refine ⟨K,hK,a,ε₀,ρ,θ,ha,hε₀,hρ,hθ,?_⟩
  intro aLoad hloadPos hloadLe Dmax d q₀ hd
  obtain ⟨N,hN⟩:=hmain aLoad hloadPos hloadLe Dmax d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π J hn hJ hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  have hevent:=hN V U Γ Color P F π J hn hJ hB hU hP hF hclose hnoshort
    pR pH D ε hpR hpR1 hpH hpH1 hD hε hεsmall hreg hbalance q hq hQ s hs hS j hj
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ Q H L hQP hL hLρ hFL hQR hHr hHc I hI E D₀ hE hFE hDE hEcard hD₀
    T W hTI hWJ hTcard hWcard hWdiv hFT hTbal hErim hErow hEcol
  obtain ⟨Nr,Ns,v,w,z,b,hcard,hv,hw,hvw,hFvw,hedge,hend,hz,hb,hsp,hspinj,hsrow,hscol,heE⟩:=
    prescribed_inner_edge_enumeration Q F H I J E D₀ hE hFE hDE
  obtain ⟨x,hx,hxT⟩:=finset_injective_enumeration T
  obtain ⟨u,hu,huW⟩:=finset_injective_enumeration W
  have hxmem (i:Fin T.card):x i∈T:=hxT ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have humem (i:Fin W.card):u i∈W:=huW ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hxsur (v:V) (hv:v∈T):∃ i,x i=v:=by
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hxT.symm ▸ hv)
    exact ⟨i,hi⟩
  have husur (v:U) (hv:v∈W):∃ i,u i=v:=by
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (huW.symm ▸ hv)
    exact ⟨i,hi⟩
  have hNv:((Nr+Ns:ℕ):ℝ)≤aLoad^2*(Fintype.card V:ℝ)^2:=by rw [hcard];exact hEcard
  have out:=hσ Q H L hQP hL hLρ hFL hQR hHr hHc I hI Nr Ns D₀ v w hv hw hvw hFvw hedge hend
    z b hz hb hsp hspinj hsrow hscol hNv hD₀
  dsimp only at out
  rw [heE] at out
  obtain ⟨C,hC,hinner,hdeg,hrow,hcol,M,hM,hMr,hMs,hMu,hMd,hMrow,hMcol,hsupport,P',hP',hPI,hPr,hPs,hPu⟩:=
    out W.card u hu hWcard (fun i=>hWJ (humem i)) (fun i=>hWdiv _ (humem i))
      T.card x hTcard hx (fun i=>hTI (hxmem i)) (fun i=>hFT _ (hxmem i)) (fun i=>hTbal _ (hxmem i))
      (fun i=>hErim _ (hxmem i)) (fun i=>hErow _ (hxmem i)) (fun i=>hEcol _ (humem i))
  let e:(Fin Nr⊕Fin Ns)→Sym2 V⊕(V×U):=Sum.elim (fun i=>Sum.inl s(v i,w i)) (fun i=>Sum.inr (z i,b i))
  have hfamily:=prescribed_wheel_family_exact_union C
    (ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J)) e hC hinner
  have hfamilyE:ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C)∩
      ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J)=E:=hfamily.2.1.trans heE
  have hsingle (i:Fin Nr⊕Fin Ns):(ordinaryWheelResources (C i)∩E).card=1:=by
    rw [←heE,hfamily.2.2 i,Finset.card_singleton]
  have hother:=ordinary_packing_preserves_other_inner_stars M I J u x (by
    intro Y hY
    rcases hsupport Y hY with hh|⟨i,hx',hJ',hv'⟩
    · exact Or.inl hh
    · exact Or.inr ⟨i,hJ',hv'⟩)
  have hroots:Finset.univ.image (fun i=>Sum.inl (x i))∪Finset.univ.image (fun i=>Sum.inr (u i))=
      T.image Sum.inl∪W.image Sum.inr:=by
    have hleft:=congrArg (fun S:Finset V=>S.image (Sum.inl:V→V⊕U)) hxT
    have hright:=congrArg (fun S:Finset U=>S.image (Sum.inr:U→V⊕U)) huW
    simpa only [Finset.image_image,Function.comp_def] using congrArg₂ (fun S R:Finset (V⊕U)=>S∪R) hleft hright
  have hunique (Y) (hY:Y∈M):(ordinaryWheelVertices Y∩(T.image Sum.inl∪W.image Sum.inr)).card=1:=by
    rw [←hroots]
    exact ordinary_deep_wheel_unique_root Y I J u x (fun i=>hWJ (humem i)) (fun i=>hTI (hxmem i)) (hsupport Y hY)
  refine ⟨Finset.univ.image C,?_,?_,?_,?_,?_,?_,?_⟩
  · intro Y hY Z hZ hne
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hY
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hZ
    exact hC i j (fun hij=>hne (congrArg C hij))
  · rw [Finset.image_biUnion,←wheelFamily_resources];exact hfamilyE
  · intro Y hY
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hY
    exact hsingle i
  · rw [ordinary_family_image_rim];exact hdeg
  · rw [ordinary_family_image_spokes];exact hrow
  · rw [ordinary_family_image_spokes];exact hcol
  rw [ordinary_family_image_rim,ordinary_family_image_spokes]
  refine ⟨M,hM,?_,?_,?_,hMd,hMrow,hMcol,hunique,?_,?_,?_,P',hP',hPI,?_,?_,?_⟩
  · intro v hv
    obtain ⟨i,rfl⟩:=hxsur v hv
    exact hMr i
  · intro v hv
    obtain ⟨i,rfl⟩:=hxsur v hv
    exact hMs i
  · intro v hv
    obtain ⟨i,rfl⟩:=husur v hv
    exact hMu i
  · intro v hv
    exact hother.1 v (Finset.mem_sdiff.mp hv).1 (fun i he=>(Finset.mem_sdiff.mp hv).2 (he.symm ▸ hxmem i))
  · intro v hv
    exact hother.2.1 v (Finset.mem_sdiff.mp hv).1 (fun i he=>(Finset.mem_sdiff.mp hv).2 (he.symm ▸ hxmem i))
  · intro v hv
    exact hother.2.2 v (Finset.mem_sdiff.mp hv).1 (fun i he=>(Finset.mem_sdiff.mp hv).2 (he.symm ▸ humem i))
  · intro v hv
    obtain ⟨i,rfl⟩:=hxsur v hv
    exact hPr i
  · intro v hv
    obtain ⟨i,rfl⟩:=hxsur v hv
    exact hPs i
  · intro v hv
    obtain ⟨i,rfl⟩:=husur v hv
    exact hPu i

end Oberwolfach
