module

public import Oberwolfach.MarkedReferenceSupportedTwoStageCover
public import Oberwolfach.MarkedReservedUnionCoverProtection
public import Oberwolfach.MarkedTwoStageTerminalAbsorber
public import Oberwolfach.MarkedPreselectedAbsorberProtectedDecomposition
public import Oberwolfach.MarkedSupportedReserveAvoidsInnerSubset
public import Oberwolfach.MarkedTwoStageCompactCaller
public import Oberwolfach.MarkedReferenceTwoStageCanonicalDeletion

@[expose] public section
/-! Apply both sampled cover-down stages to any bounded deletion of a
parent-level reference sample. The remaining inputs are the actual
reserved resource, divisibility and prescribed-resource hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 48000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
theorem marked_reference_preselected_absorber_and_two_stage_cover
    (r size a₀ b₀ e₀ f:ℕ) (hr:2≤r) (gamma omega t rho eta betaA aLoA BA betaCap εAbs:ℝ)
    (hg:0<gamma) (hg1:gamma≤1) (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1) (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/32)
    (hbetaA:0<betaA) (haLoA:0<aLoA) (hBA:0≤BA) (hbetaCap:0<betaCap):
    ∃ β beta eps₁ delta₁ eta₀:ℝ,0<β∧β≤t/2∧β≤betaCap∧0<beta∧0<eps₁∧0<delta₁∧0<eta₀∧
    ∃ eps₂:ℝ,0<eps₂∧∃ K:ℕ,0<K∧∃ zeta:ℝ,0<zeta∧∃ θ:ℝ,0<θ∧∃ delta₂:ℝ,0<delta₂∧
    ∃ xi etaE:ℝ,0<xi∧0<etaE∧
    ∀ cap:ℝ,0<cap→∃ kappa thetaDeep ζ:ℝ,0<kappa∧0<thetaDeep∧0<ζ∧kappa≤cap∧thetaDeep≤cap∧ζ≤cap∧
    ∀ d:ℕ,2≤d→∃ N:ℕ,1≤N∧
    ∀ (NI Kgeom:ℕ) (p0 ξ alphaInner omegaInner iota aLo B η x omegaI hIcut deltaI etaBal:ℝ)
      (L:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
        kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal),
    letI:Fintype L.VP:=L.inst7
    letI:Fintype L.UP:=L.inst8
    letI:LinearOrder L.VP:=L.inst9
    letI:DecidableEq L.UP:=L.inst10
    let V:=L.VP
    let U:=L.UP
    let P:=L.PP
    let π:=L.πP
    let Eold:=MarkedSampleArc P π (3*d) (fun e=>L.σBase (Sum.inl e)) false
    let Kold:=MarkedSampleArc P π (3*d) (fun e=>L.σBase (Sum.inl e)) true
    let told:=fun e:Eold=>e.val.1
    let hold:=fun e:Eold=>e.val.2
    let ktold:=fun e:Kold=>e.val.1
    let khold:=fun e:Kold=>e.val.2;
    MarkedReservedTerminalAbsorberProperty told hold ktold khold (L.HBase false) (L.HBase true) π (3*d) r size a₀ b₀ e₀ f εAbs→
    ∀ (Xterm Wres:Finset V) (Zterm Bres:Finset U),Xterm.card+Zterm.card≤size→Xterm⊆Wres→Zterm⊆Bres→
    (Wres.card:ℝ)≤εAbs*Fintype.card V+f→(Bres.card:ℝ)≤εAbs*Fintype.card V+f→
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f→(e₀:ℝ)≤min delta₁ delta₂*Fintype.card V→
    ∃ C₀:MarkedSupportedEdgeSet told hold ktold khold π U,
      Disjoint C₀.edges F₀∧C₀.edges.card≤e₀∧C₀.rows.card≤a₀∧C₀.hubs.card≤b₀∧
      (∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
        (∀ x y,Sum.inl ({x,y}:Finset V)∈C₀.edges→¬DR.Adj x y)→
        (∀ v u,Sum.inr (v,u)∈C₀.edges→¬DS.Adj (Sum.inl v) (Sum.inr u))→
        (∀ v∈Xterm,∀ u∈Zterm,¬DS.Adj (Sum.inl v) (Sum.inr u))→
        let L.σBase':=rawMarkedDeleteRims L.σBase DR.edgeFinset
        let L.HBase':=markedDeletePhysicalSpokes L.HBase DS
        let E':=MarkedSampleArc P π (3*d) (fun e=>L.σBase' (Sum.inl e)) false
        let K':=MarkedSampleArc P π (3*d) (fun e=>L.σBase' (Sum.inl e)) true
        let t':=fun e:E'=>e.val.1
        let h':=fun e:E'=>e.val.2
        let kt':=fun e:K'=>e.val.1
        let kh':=fun e:K'=>e.val.2;
        ∀ (A:Finset (E'⊕K')) (S:Finset (V×U)),
        (∀ a∈A,Sum.elim t' kt' a∈Xterm∧Sum.elim h' kh' a∈Xterm)→
        (∀ z∈S,z.1∈Xterm∧z.2∈Zterm∧(L.HBase' false z.1 z.2∨L.HBase' true z.1 z.2))→
        MarkedRemainderDivisible t' h' kt' kh' (L.HBase' true) A S (r+4)→
        IsResourceAbsorber
          (fun Q:MarkedWheel t' h' kt' kh' (r+4) π (3*d) (L.HBase' false) (L.HBase' true)=>markedWheelPhysicalResources Q)
          (A.image (fun a=>Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))∪S.image Sum.inr) C₀.edges)∧
      ∀ (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
      (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
      (∀ x y,Sum.inl ({x,y}:Finset V)∈C₀.edges→¬FR.Adj x y)→
      (∀ v u,Sum.inr (v,u)∈C₀.edges→¬FS.Adj (Sum.inl v) (Sum.inr u))→
      let C:=C₀.edges
      let σ:=rawMarkedDeleteRims L.σBase FR.edgeFinset
      let H:=markedDeletePhysicalSpokes L.HBase FS
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (X T:Finset V) (J W:Finset U),(∀ x,π x∈X↔x∈X)→(∀ x,π x∈T↔x∈T)→T⊆Xᶜ→W⊆J→
    ((Xᶜ).card:ℝ)≤xi*Fintype.card V→(J.card:ℝ)≤xi*Fintype.card V→
    Xᶜ⊆Wres→J⊆Bres→
    ∀ (DA:Finset (E₀⊕E₁)) (DS₀:Finset (V×U)),
    let A:=DA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let S:=DS₀.filter (fun z=>z.1∈T∨z.2∈W);
    (A.card:ℝ)≤etaE^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤etaE^2*(Fintype.card V:ℝ)^2→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤etaE^2*Fintype.card V)→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤etaE^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤etaE^2*Fintype.card V)→
    let Full:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈Xᶜ∧Sum.elim head khead a∈Xᶜ))\DA
    let CS:=(Full.filter (fun z=>z.1∈Xᶜ∧z.2∈J))\DS₀
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W);
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ Full (r+4)→
    MarkedRemainderDivisible tail head ktail khead (H true) CA CS (r+4)→
    (∀ a∈DA,Sum.elim tail ktail a∈Xᶜ∧Sum.elim head khead a∈Xᶜ)→
    (∀ z∈DS₀,z.1∈Xᶜ∧z.2∈J∧z∈Full)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
      (∀ Y∈M,∀ Z∈M,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))∧
      Disjoint C (M.biUnion markedWheelPhysicalResources)∧
      (∀ x,((markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)).degree x:ℝ)≤(Xᶜ).card+24*etaE*Fintype.card V)∧
      (∀ x,((markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)).degree (Sum.inl x):ℝ)≤J.card+6*etaE*Fintype.card V)∧
      (∀ u,((markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)).degree (Sum.inr u):ℝ)≤(Xᶜ).card+3*(r+5)*etaE*Fintype.card V)∧
      (∀ x,((markedPackingRimGraph M).degree x:ℝ)≤24*etaE*Fintype.card V)∧
      (∀ x,((Finset.univ.filter (markedPackingSpokes M x)).card:ℝ)≤6*etaE*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤3*(r+5)*etaE*Fintype.card V)∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) J)=
        (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)∧
      let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
      let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
      let DRall:=DR⊔physicalEdgeGraph (markedReservedRimPairs C)
      let DSall:=DS⊔markedFiniteSpokeGraph (markedReservedSpokePairs C)
      let edgeInst:Fintype DRall.edgeSet:=@SimpleGraph.fintypeEdgeSet V DRall (Sym2.instFintype)
        (fun x y=>Classical.propDecidable (DRall.Adj x y))
      let σ':=rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V DRall edgeInst)
      let H':=markedDeletePhysicalSpokes H DSall
      let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
      let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
      let t':=fun e:E'=>e.val.1
      let h':=fun e:E'=>e.val.2
      let kt':=fun e:K'=>e.val.1
      let kh':=fun e:K'=>e.val.2;
      ∃ MD:Finset (MarkedWheel t' h' kt' kh' (r+4) π (3*d) (H' false) (H' true)),
        (∀ Y∈MD,∀ Z∈MD,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))∧
        Disjoint C (MD.biUnion markedWheelPhysicalResources)∧
        Disjoint (M.biUnion markedWheelPhysicalResources) (MD.biUnion markedWheelPhysicalResources)∧
        (∀ x∈X,(markedPackingRimGraph MD).degree x≤2*W.card+T.card*(4*(K+4))+2*T.card)∧
        (∀ x∈X,(Finset.univ.filter (markedPackingSpokes MD x)).card≤W.card+T.card*(K+4))∧
        (∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes MD x u)).card≤T.card*(r+5))∧
        (MD.biUnion markedWheelPhysicalResources).filter (markedInnerResource Xᶜ J)=∅ ∧
        (MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (Xᶜ\T) (J\W))=∅ ∧
        (∀ Y∈MD,(Y.2.val∈W∧markedWheelRows Y⊆X)∨
          (Y.2.val∉J∧∃ v∈T,markedWheelRows Y⊆insert v X∧v∈markedWheelRows Y))∧
        (∀ a:E'⊕K',markedStarResource T W (Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))→
          Sum.inl (markedPhysicalEdge t' h' kt' kh' π a)∈MD.biUnion markedWheelPhysicalResources) ∧
        (∀ x u,H' false x u∨H' true x u→markedStarResource T W (Sum.inr (x,u))→
          Sum.inr (x,u)∈MD.biUnion markedWheelPhysicalResources) ∧
        let σfirst:=rawMarkedDeleteRims σ DR.edgeFinset
        let Hfirst:=markedDeletePhysicalSpokes H DS
        let Efirst:=MarkedSampleArc P π (3*d) (fun e=>σfirst (Sum.inl e)) false
        let Kfirst:=MarkedSampleArc P π (3*d) (fun e=>σfirst (Sum.inl e)) true;
        ∃ Ndeep:Finset (MarkedWheel (fun e:Efirst=>e.val.1) (fun e=>e.val.2)
          (fun e:Kfirst=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hfirst false) (Hfirst true)),
          (∀ Y∈Ndeep,∀ Z∈Ndeep,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))∧
          Ndeep.biUnion markedWheelPhysicalResources=MD.biUnion markedWheelPhysicalResources∧
          Disjoint C (Ndeep.biUnion markedWheelPhysicalResources)∧
          let σfinal:=rawMarkedDeleteRims σfirst (markedPackingRimGraph Ndeep).edgeFinset
          let Hfinal:=markedDeletePhysicalSpokes Hfirst (markedFiniteSpokeGraph (Ndeep.biUnion markedWheelSpokePairs))
          let Efinal:=MarkedSampleArc P π (3*d) (fun e=>σfinal (Sum.inl e)) false
          let Kfinal:=MarkedSampleArc P π (3*d) (fun e=>σfinal (Sum.inl e)) true;
          (∀ mark x y,x∈Xᶜ\T→y∈Xᶜ\T→
            (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1↔
             markedPhysicalRim P π (3*d) (fun e=>σfinal (Sum.inl e)) mark x y=1))∧
          (∀ b v u,v∈Xᶜ\T→u∈J\W→(H b v u↔Hfinal b v u))∧
          (∀ e:E₀,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':Efinal,e'.val=e.val)∧
          (∀ e:E₁,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':Kfinal,e'.val=e.val)∧
          (∀ b v u,Sum.inr (v,u)∈C→H b v u→Hfinal b v u)∧
          (Xterm⊆Xᶜ\T→Zterm⊆J\W→
            (∀ v∈Xterm,∀ u∈Zterm,¬FS.Adj (Sum.inl v) (Sum.inr u))→
            MarkedTerminalAbsorberForGraphs P π d (r+4) L.σBase L.HBase C Xterm Zterm
              (FR⊔(DR⊔markedPackingRimGraph Ndeep))
              (FS⊔(DS⊔markedFiniteSpokeGraph (Ndeep.biUnion markedWheelSpokePairs)))) :=by
  obtain ⟨β,beta,eps₁,delta₁,eta₀,hβ,hβt,hβcap,hbeta,heps₁,hdelta₁,heta₀,eps₂,heps₂,K,hK,zeta,hzeta,θ,hθ,delta₂,hdelta₂,xi,etaE,hxi,hetaE,hcover⟩:=
    marked_reference_two_stage_cover_with_supported_reserve (Gamma:=Gamma) (Color:=Color) r hr gamma omega t rho eta betaA aLoA BA betaCap
      hg hg1 ho ht hrho hrho1 hst heta hetaSmall hbetaA haLoA hBA hbetaCap
  refine ⟨β,beta,eps₁,delta₁,eta₀,hβ,hβt,hβcap,hbeta,heps₁,hdelta₁,heta₀,eps₂,heps₂,K,hK,zeta,hzeta,θ,hθ,delta₂,hdelta₂,xi,etaE,hxi,hetaE,?_⟩
  intro cap hcap
  obtain ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,hcover⟩:=hcover cap hcap
  refine ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,?_⟩
  intro d hd
  obtain ⟨N,hN,hcover⟩:=hcover d hd
  refine ⟨N,hN,?_⟩
  intro NI Kgeom p0 ξ alphaInner omegaInner iota aLo B η x omegaI hIcut deltaI etaBal L
  letI:Fintype L.VP:=L.inst7
  letI:Fintype L.UP:=L.inst8
  letI:LinearOrder L.VP:=L.inst9
  letI:DecidableEq L.UP:=L.inst10
  intro V U P π Eold Kold told hold ktold khold habs Xterm Wres Zterm Bres hsize hX hZ hW hB F₀ hF hsizeC
  obtain ⟨C₀,hF₀,hCe,hCr,hCu,hCold,hinner,hdec,hdecAfter,htransfer⟩:=
    marked_preselected_absorber_decomposes_and_avoids_inner_after_deletions P π d r size a₀ b₀ e₀ f εAbs L.σBase L.HBase habs Xterm Wres Zterm Bres hsize hX hZ hW hB F₀ hF
  have hCsize:(C₀.edges.card:ℝ)≤min delta₁ delta₂*Fintype.card V:=
    (Nat.cast_le.mpr hCe).trans hsizeC
  refine ⟨C₀,hF₀,hCe,hCr,hCu,htransfer,?_⟩
  intro FR FS hdegR hdegS hAvoidR hAvoidS C σ H E₀ E₁ tail head ktail khead
    X T J W hX' hT hTI hWJ hXI hJ hIW hJB DA DS₀ A S hA hS hAdeg hSrow hScol Full CA CS KA KS hOuter hInner hDA hDS
  obtain ⟨M,hM,hMC,hbr,hbv,hbu,hrim1,hrow1,hcol1,hMinner,MD,hMD,hMDC,hMM,hrim2,hrow2,hcol2,hMDinner,hactive,hroots,hcoverR,hcoverS⟩:=
    hcover NI Kgeom p0 ξ alphaInner omegaInner iota aLo B η x omegaI hIcut deltaI etaBal L
      FR FS hdegR hdegS C₀ Wres Bres hCold hCsize hAvoidR hAvoidS
      X T J W hX' hT hTI hWJ hXI hJ hIW hJB DA DS₀ hA hS hAdeg hSrow hScol hOuter hdec hInner hDA hDS
  have hI:∀ v,π v∈Xᶜ↔v∈Xᶜ:=by intro v;simpa only [Finset.mem_compl] using not_congr (hX' v)
  have hCavoid:∀ e∈C,¬markedInnerResource Xᶜ J e:=hinner Xᶜ J hI hIW hJB
  have hCA:∀ a∈CA,Sum.elim tail ktail a∈Xᶜ∧Sum.elim head khead a∈Xᶜ:=by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2
  have hCS:∀ z∈CS,z.1∈Xᶜ∧z.2∈J:=by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
  obtain ⟨Ndeep,hNd,hNres,hNC,hprotect⟩:=
    marked_reserved_union_cover_protects_active_pair_and_absorber P π d (r+4) (by omega) (by omega) σ H C Xᶜ T J W hI hT hCavoid
      CA CS M (markedFiniteResources tail head ktail khead π DA DS₀) hCA hCS hMC hMinner MD hMD hMDinner
  obtain ⟨hprotR,hprotS,hprotE,hprotK,hprotSpoke⟩:=hprotect
  refine ⟨M,hM,hMC,hbr,hbv,hbu,hrim1,hrow1,hcol1,hMinner,MD,hMD,hMDC,hMM,hrim2,hrow2,hcol2,hMDinner,hactive,hroots,hcoverR,hcoverS,Ndeep,hNd,hNres,hNC,hprotR,hprotS,hprotE,hprotK,hprotSpoke,?_⟩
  intro hXterm hZterm hpriorTerm
  have hNinner:(Ndeep.biUnion markedWheelPhysicalResources).filter (markedInnerResource Xᶜ J)=∅:=by
    rw [hNres]
    exact hMDinner
  have habs:MarkedUniversalTerminalDeletionAbsorber P π d (r+4) L.σBase L.HBase C Xterm Zterm:=htransfer
  exact marked_two_stage_preserves_terminal_absorption P π d (r+4) L.σBase L.HBase C Xterm Zterm
    FR FS hAvoidR hAvoidS hpriorTerm habs Xᶜ T J W hI hXterm hZterm hCavoid
    CA CS M (markedFiniteResources tail head ktail khead π DA DS₀) hCA hCS hMC hMinner Ndeep hNC hNinner
end Oberwolfach
