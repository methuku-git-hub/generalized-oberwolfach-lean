module

public import Oberwolfach.MarkedSampleDeepCoverAfterDeletion
public import Oberwolfach.MarkedReservedDeepHost
public import Oberwolfach.MarkedReservedDeletionBudget
public import Oberwolfach.MarkedHubRowStarAvoidance

@[expose] public section

/-! Construct the deep-row and deep-hub packing in the actual host left by
an inner correction, reserved star and prescribed-edge packing. All local
balance and neighbour support hypotheses are derived from those objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reserved_sample_deep_cover
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
    (∀ x u,¬(H false x u∧H true x u))→
    (∀ u x z,H false x u→H true z u→x≠π z)→
    ∀ (I T:Finset V) (J W:Finset U),T⊆I→W⊆J→
    (∀ x,π x∈I↔x∈I)→(∀ x,π x∈T↔x∈T)→
    (I.card:ℝ)≤zeta*Fintype.card V→(J.card:ℝ)≤zeta*Fintype.card V→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    ∀ (DA:Finset (E₀⊕E₁)) (DS₀:Finset (V×U)),
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S)→
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S (r+4)→
    MarkedRemainderDivisible tail head ktail khead (H true) CA CS (r+4)→
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
    ∀ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    M.biUnion markedWheelArcs⊆Finset.univ\KA→
    M.biUnion markedWheelSpokePairs⊆S\KS→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)→
    ∀ etaE:ℝ,
    (∀ x,((markedPackingRimGraph M).degree x:ℝ)≤24*etaE*Fintype.card V)→
    (∀ x,((Finset.univ.filter (markedPackingSpokes M x)).card:ℝ)≤6*etaE*Fintype.card V)→
    (∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤3*(r+5)*etaE*Fintype.card V)→
    I.card+24*etaE*Fintype.card V≤delta*Fintype.card V→
    J.card+6*etaE*Fintype.card V≤delta*Fintype.card V→
    I.card+3*(r+5)*etaE*Fintype.card V≤delta*Fintype.card V→
    let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail':=fun e:E₀'=>e.val.1
    let head':=fun e:E₀'=>e.val.2
    let ktail':=fun e:E₁'=>e.val.1
    let khead':=fun e:E₁'=>e.val.2
    ∃ M_D:Finset (MarkedWheel tail' head' ktail' khead' (r+4) π (3*d) (H' false) (H' true)),
      (∀ X∈M_D,∀ Y∈M_D,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y)) ∧
      (∀ x∉I,(markedPackingRimGraph M_D).degree x≤2*W.card+T.card*(4*(K+4))+2*T.card) ∧
      (∀ x∉I,(Finset.univ.filter (markedPackingSpokes M_D x)).card≤W.card+T.card*(K+4)) ∧
      (∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes M_D x u)).card≤T.card*(r+5)) ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅ ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅ ∧
      (∀ X∈M_D,(X.2.val∈W∧markedWheelRows X⊆Iᶜ)∨
        (X.2.val∉J∧∃v∈T,markedWheelRows X⊆insert v Iᶜ∧v∈markedWheelRows X)) ∧
      (∀ a:E₀'⊕E₁',markedStarResource T W
          (Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))→
          Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a)∈M_D.biUnion markedWheelPhysicalResources) ∧
      (∀ x u,H' false x u∨H' true x u→markedStarResource T W (Sum.inr (x,u))→
          Sum.inr (x,u)∈M_D.biUnion markedWheelPhysicalResources):=by
  obtain ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,delta,hdelta,hcover⟩:=
    marked_sample_deep_cover_after_physical_deletion r hr omega t rho gamma eta ho ht hrho hrho1 hg hg1
      hst heta hetaSmall β aLo B pstar hβ hβt haLo hB hpstar
  refine ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,delta,hdelta,?_⟩
  intro d hd
  obtain ⟨N,hN,hcover⟩:=hcover d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload hH hshift I T J W hTI hWJ hI hT hIsize hJsize
  intro E₀ E₁ tail head ktail khead S DA DS₀ hDA hDS CA CS houter hinner KA KS M hM hMA hMS hexact
    etaE hErim hErow hEcol hnumR hnumV hnumU DR DS
  dsimp only
  have hKA (a) (ha:a∈KA):Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1).2
  have hKS (z) (hz:z∈KS):z.1∈I∧z.2∈J:=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1).2
  have hbudget:=marked_reserved_packing_deletion_bounds P π d (r+4) σ H I J hI KA KS hKA hKS M
    (24*etaE*Fintype.card V) (6*etaE*Fintype.card V) (3*(r+5)*etaE*Fintype.card V) hErim hErow hEcol
  have hDR (x:V):(DR.degree x:ℝ)≤delta*Fintype.card V:=(hbudget.1 x).trans hnumR
  have hDSr (x:V):(DS.degree (Sum.inl x):ℝ)≤delta*Fintype.card V:=(hbudget.2.1 x).trans hnumV
  have hDSc (u:U):(DS.degree (Sum.inr u):ℝ)≤delta*Fintype.card V:=(hbudget.2.2 u).trans hnumU
  have hinputs:=marked_reserved_deep_host_inputs P π d (r+4) σ H hH I T J W hTI hWJ hI hT
    DA DS₀ hDA hDS houter hinner M hM hMA hMS hexact
  obtain ⟨hbal,hratio,hinc,hout,hrowSupport,hhubSupport⟩:=hinputs
  let eu:Fin W.card≃W:=(Fintype.equivFinOfCardEq (Fintype.card_coe W)).symm
  let ev:Fin T.card≃T:=(Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let u:Fin W.card→U:=fun i=>(eu i).val
  let v:Fin T.card→V:=fun i=>(ev i).val
  have hu:Function.Injective u:=fun i j h=>eu.injective (Subtype.ext h)
  have hv:Function.Injective v:=fun i j h=>ev.injective (Subtype.ext h)
  have huW (i):u i∈W:=(eu i).property
  have hvT (i):v i∈T:=(ev i).property
  have huimage:Finset.univ.image u=W:=by
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩;exact huW i
    · intro hz
      obtain ⟨i,hi⟩:=eu.surjective ⟨z,hz⟩
      exact ⟨i,by simp only [u,hi]⟩
  have hvimage:Finset.univ.image v=T:=by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩;exact hvT i
    · intro hx
      obtain ⟨i,hi⟩:=ev.surjective ⟨x,hx⟩
      exact ⟨i,by simp only [v,hi]⟩
  have hWsize:(W.card:ℝ)≤zeta*Fintype.card V:=(Nat.cast_le.mpr (Finset.card_le_card hWJ)).trans hJsize
  have hTsize:(T.card:ℝ)≤zeta*Fintype.card V:=(Nat.cast_le.mpr (Finset.card_le_card hTI)).trans hIsize
  let H':=markedDeletePhysicalSpokes H DS
  have hdis (x:V) (z:U):¬(H' false x z∧H' true x z):=fun h=>hH x z ⟨h.1.1,h.2.1⟩
  have hY (i):Disjoint ((Finset.univ.filter (H' false (v i)))∪(Finset.univ.filter (H' true (v i)))) J:=by
    apply Finset.disjoint_left.mpr
    intro z hz hzJ
    have hs:H' false (v i) z∨H' true (v i) z:=by
      simpa only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and] using hz
    exact hrowSupport (v i) (hvT i) z hs hzJ
  have hYW (i):Disjoint ((Finset.univ.filter (H' false (v i)))∪(Finset.univ.filter (H' true (v i))))
      (Finset.univ.image u):=by
    rw [huimage]
    exact (hY i).mono_right hWJ
  obtain ⟨MD,hMD,_,hrim,hspoke,hcol,hinside,hroots,hcovered⟩:=
    hcover V U Γ Color hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
      D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload DR DS hDR hDSr hDSc
      Iᶜ (by intro x;simp only [Finset.mem_compl,hI]) (by simpa only [compl_compl] using hIsize)
      W.card hWsize u hu (fun i x=>hdis x (u i))
      (fun i x z hx hz=>hshift (u i) x z hx.1 hz.1)
      (fun i=>hratio (u i) (huW i))
      (fun i x hx=>Finset.mem_compl.mpr (hhubSupport (u i) (huW i) x hx))
      T.card v hv hTsize (fun i=>by simpa only [Finset.mem_compl,not_not] using hTI (hvT i))
      (fun i z=>hdis (v i) z)
      (fun i a ha=>Finset.mem_compl.mpr (hinc a (ha.symm ▸ hvT i)))
      (fun i a ha=>Finset.mem_compl.mpr (hout a (ha.symm ▸ hvT i)))
      (fun i=>(hbal (v i) (hvT i)).1) (fun i=>(hbal (v i) (hvT i)).2.1)
      (fun i=>(hbal (v i) (hvT i)).2.2) hYW
  refine ⟨MD,hMD,(fun x hx=>hrim x (Finset.mem_compl.mpr hx)),
    (fun x hx=>hspoke x (Finset.mem_compl.mpr hx)),?_,?_,?_,?_,?_⟩
  · simpa only [huimage] using hcol
  · exact hinside I J (Finset.disjoint_left.mpr (fun x hx hxi=>(Finset.mem_compl.mp hx) hxi)) hI hY
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
    · exact hY
  · intro X hX
    rcases hroots X hX with h|⟨i,hi,hrows,hmem⟩
    · exact Or.inl ⟨by simpa only [huimage] using h.1,h.2⟩
    · exact Or.inr ⟨fun hz=>Finset.disjoint_left.mp (hY i) hi hz,v i,hvT i,hrows,hmem⟩
  · simpa only [huimage] using hcovered T (by rw [hvimage]) hT

end Oberwolfach
