module

public import Oberwolfach.MarkedDeepHostEnumeratedRoots
public import Oberwolfach.MarkedDeepCoverReservedResources
public import Oberwolfach.MarkedReservedSampleDeepCover
public import Oberwolfach.MarkedReservedDeletedSampleAvoidance

@[expose] public section
/-! The sampled deep-cover theorem may reserve a bounded physical resource
set in addition to the previous deletion graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_sample_deep_cover_from_balanced_reserved_host
    (r:ℕ) (hr:1≤r) (omega t rho gamma eta:ℝ)
    (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1) (hg:0<gamma) (hg1:gamma≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1) (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/32)
    (β aLo B pstar:ℝ) (hβ:0<β) (hβt:β≤t/2) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar):
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∃ delta:ℝ,0<delta ∧ ∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→(Fintype.card U:ℝ)≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤eps*Fintype.card V)→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    (∀ u,q u g=t)→(∀ u,s u j=(((r+1)+3:ℕ):ℝ)*t)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d ((r+1)+11) Finset.univ (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d ((r+1)+11) Finset.univ q s g j (eps*Fintype.card V) σ H→
    ∀ (D τ p k s₀:ℝ),(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    ∀ weight:(Fin (r+4+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight→
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (2*β) (2*β) σ H→
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight (θ/2) σ H→
    ∀ (C:Finset (Finset V⊕(V×U))), (C.card:ℝ)≤delta*Fintype.card V→
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤delta*Fintype.card V)→
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤delta*Fintype.card V)→
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤delta*Fintype.card V)→
    let DRall:=DR⊔physicalEdgeGraph (markedReservedRimPairs C)
    let DSall:=DS⊔markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let edgeInst:Fintype DRall.edgeSet:=@SimpleGraph.fintypeEdgeSet V DRall (Sym2.instFintype)
      (fun x y=>Classical.propDecidable (DRall.Adj x y))
    let σ':=rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V DRall edgeInst)
    let H':=markedDeletePhysicalSpokes H DSall
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (I T:Finset V) (J W:Finset U),T⊆I→W⊆J→
    (∀ x,π x∈I↔x∈I)→(∀ x,π x∈T↔x∈T)→
    (I.card:ℝ)≤zeta*Fintype.card V→(J.card:ℝ)≤zeta*Fintype.card V→
    (∀ x u,¬(H false x u∧H true x u))→
    (∀ u x z,H false x u→H true z u→x≠π z)→
    MarkedDeepHostBalanced P π d (r+4) σ' H' I T J W→
    ∃ M_D:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H' false) (H' true)),
      (∀ X∈M_D,∀ Y∈M_D,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y)) ∧
      (∀ x∉I,(markedPackingRimGraph M_D).degree x≤2*W.card+T.card*(4*(K+4))+2*T.card) ∧
      (∀ x∉I,(Finset.univ.filter (markedPackingSpokes M_D x)).card≤W.card+T.card*(K+4)) ∧
      (∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes M_D x u)).card≤T.card*(r+5)) ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅ ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅ ∧
      (∀ X∈M_D,(X.2.val∈W∧markedWheelRows X⊆Iᶜ)∨
        (X.2.val∉J∧∃v∈T,markedWheelRows X⊆insert v Iᶜ∧v∈markedWheelRows X)) ∧
      (∀ a:E₀⊕E₁,markedStarResource T W
          (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
          Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M_D.biUnion markedWheelPhysicalResources) ∧
      (∀ x u,H' false x u∨H' true x u→markedStarResource T W (Sum.inr (x,u))→
          Sum.inr (x,u)∈M_D.biUnion markedWheelPhysicalResources) ∧
      Disjoint C (M_D.biUnion markedWheelPhysicalResources):=by
  obtain ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,delta,hdelta,hcover⟩:=
    marked_sample_deep_cover_preserving_reserved_resources r hr omega t rho gamma eta ho ht hrho hrho1 hg hg1
      hst heta hetaSmall β aLo B pstar hβ hβt haLo hB hpstar
  refine ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,delta,hdelta,?_⟩
  intro d hd
  obtain ⟨N,hN,hcover⟩:=hcover d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload C hCsize DR DS hDR hDSr hDSc DRall DSall edgeInst σ' H' E₀ E₁ tail head ktail khead
    I T J W hTI hWJ hI hT hIsize hJsize hH hshift hbal
  have hdis (x:V) (z:U):¬(H' false x z∧H' true x z):=fun h=>hH x z ⟨h.1.1,h.2.1⟩
  have hshift':∀ u x z,H' false x u→H' true z u→x≠π z:=fun u x z hx hz=>hshift u x z hx.1 hz.1
  obtain ⟨u,v,hu,hv,huimage,hvimage,huDis,huShift,huRatio,huSupport,hvNot,hvDis,hvIn,hvOut,hvBal,hvSpoke,hvMark,hY⟩:=
    marked_deep_host_enumerate_roots P π d (r+4) σ' H' I T J W hTI hWJ hdis hshift' hbal
  have hWsize:(W.card:ℝ)≤zeta*Fintype.card V:=(Nat.cast_le.mpr (Finset.card_le_card hWJ)).trans hJsize
  have hTsize:(T.card:ℝ)≤zeta*Fintype.card V:=(Nat.cast_le.mpr (Finset.card_le_card hTI)).trans hIsize
  have hYJ (i):Disjoint ((Finset.univ.filter (H' false (v i)))∪(Finset.univ.filter (H' true (v i)))) J:=by
    apply Finset.disjoint_left.mpr
    intro z hz hzJ
    have hs:H' false (v i) z∨H' true (v i) z:=by
      simpa only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using hz
    have hvT:v i∈T:=by
      rw [←hvimage]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    exact hbal.2.2.2.2.1 (v i) hvT z hs hzJ
  have huW (i):u i∈W:=by rw [←huimage];exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hvT (i):v i∈T:=by rw [←hvimage];exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  obtain ⟨MD,hMD,_,hrim,hspoke,hcol,hinside,hroots,hcovered,havoid⟩:=
    hcover V U Γ Color hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
      D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload C hCsize DR DS hDR hDSr hDSc
      Iᶜ (by intro x;simp only [Finset.mem_compl,hI]) (by simpa only [compl_compl] using hIsize)
      W.card hWsize u hu huDis huShift huRatio huSupport
      T.card v hv hTsize hvNot hvDis hvIn hvOut hvBal hvSpoke hvMark hY
  refine ⟨MD,hMD,(fun x hx=>hrim x (Finset.mem_compl.mpr hx)),
    (fun x hx=>hspoke x (Finset.mem_compl.mpr hx)),?_,?_,?_,?_,?_,?_,havoid⟩
  · simpa only [huimage] using hcol
  · exact hinside I J (Finset.disjoint_left.mpr (fun x hx hxi=>(Finset.mem_compl.mp hx) hxi)) hI hYJ
  · apply marked_hub_row_avoids_remaining_inner_star MD u v Iᶜ I T J W
      (fun i=>(Finset.univ.filter (H' false (v i)))∪(Finset.univ.filter (H' true (v i))))
    · intro X hX
      rcases hroots X hX with h|⟨i,hi,hrows,_⟩
      · exact Or.inl h
      · exact Or.inr ⟨i,hi,hrows⟩
    · exact Finset.disjoint_left.mpr (fun x hx hxi=>(Finset.mem_compl.mp hx) hxi)
    · exact hvT
    · exact hI
    · exact hT
    · exact huW
    · exact hYJ
  · intro X hX
    rcases hroots X hX with h|⟨i,hi,hrows,hmem⟩
    · exact Or.inl ⟨by simpa only [huimage] using h.1,h.2⟩
    · exact Or.inr ⟨fun hz=>Finset.disjoint_left.mp (hYJ i) hi hz,v i,hvT i,hrows,hmem⟩
  · simpa only [huimage] using (hcovered T (by rw [hvimage]) hT).1
  · simpa only [huimage] using (hcovered T (by rw [hvimage]) hT).2
end Oberwolfach
