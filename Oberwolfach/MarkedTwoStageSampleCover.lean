module

public import Oberwolfach.MarkedSamplePrescribedToBalancedHost
public import Oberwolfach.MarkedBalancedReservedSampleDeepCover

@[expose] public section
/-! The prescribed first packing and the deep packing are chosen on one
sample, with the fixed reserved resources removed before the deep cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_two_stage_sample_cover_with_reserve
    (r:ℕ) (hr:2≤r) (pstar₁ gamma omega t rho eta:ℝ)
    (hpstar₁:0<pstar₁) (hpstar₁1:pstar₁≤1) (hg:0<gamma) (hg1:gamma≤1) (ho:0<omega)
    (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1) (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/32)
    (β aLo B pstar₂:ℝ) (hβ:0<β) (hβt:β≤t/2) (haLo:0<aLo) (hB:0≤B) (hpstar₂:0<pstar₂):
    ∃ beta eps₁ delta₁ eta₀:ℝ,0<beta ∧ 0<eps₁ ∧ 0<delta₁ ∧ 0<eta₀ ∧
    ∃ eps₂:ℝ,0<eps₂ ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∃ delta₂:ℝ,0<delta₂ ∧
    ∀ etaE:ℝ,0<etaE→etaE≤eta₀→∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→(Fintype.card U:ℝ)≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤eps₂*Fintype.card V)→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    pstar₁≤rho*((((r+1)+3:ℕ):ℝ)*t)/2→pstar₁≤rho*t/2→
    (∀ u,pstar₁≤q u g)→(∀ u,pstar₁≤s u j)→
    (∀ u,q u g=t)→(∀ u,s u j=(((r+1)+3:ℕ):ℝ)*t)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d (r+12) Finset.univ (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eps₁*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d (r+12) Finset.univ q s g j (eps₁*Fintype.card V) σ H→
    MarkedRowsWithSpokes P π d ((r+1)+11) Finset.univ (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eps₂*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d ((r+1)+11) Finset.univ q s g j (eps₂*Fintype.card V) σ H→
    ∀ (D τ p k s₀:ℝ),(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
    pstar₂≤p→pstar₂≤k→pstar₂≤s₀→p≤1→k≤1→s₀≤1→
    ∀ weight:(Fin (r+4+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight→
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (2*β) (2*β) σ H→
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight (θ/2) σ H→
    ∀ C:Finset (Finset V⊕(V×U)),(C.card:ℝ)≤delta₁*Fintype.card V→(C.card:ℝ)≤delta₂*Fintype.card V→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (X T:Finset V) (J W:Finset U),(∀ x,π x∈X↔x∈X)→(∀ x,π x∈T↔x∈T)→T⊆Xᶜ→W⊆J→
    ((Xᶜ).card:ℝ)≤beta*Fintype.card V/10→(J.card:ℝ)≤beta*Fintype.card V/10→
    ((Xᶜ).card:ℝ)≤zeta*Fintype.card V→(J.card:ℝ)≤zeta*Fintype.card V→
    (Xᶜ).card+24*etaE*Fintype.card V≤delta₂*Fintype.card V→
    J.card+6*etaE*Fintype.card V≤delta₂*Fintype.card V→
    (Xᶜ).card+3*(r+5)*etaE*Fintype.card V≤delta₂*Fintype.card V→
    (∀ e∈C,¬markedInnerResource (Xᶜ) J e)→
    ∀ (DA:Finset (E₀⊕E₁)) (DS₀:Finset (V×U)),
    let A:=DA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let S:=DS₀.filter (fun z=>z.1∈T∨z.2∈W);
    (A.card:ℝ)≤etaE^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤etaE^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤etaE^2*Fintype.card V)→
    (∀ z∈S,z.1∉X∧z.2∈J∧(H false z.1 z.2∨H true z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤etaE^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤etaE^2*Fintype.card V)→
    let Full:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈Xᶜ∧Sum.elim head khead a∈Xᶜ))\DA
    let CS:=(Full.filter (fun z=>z.1∈Xᶜ∧z.2∈J))\DS₀
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W);
    (∀ v u,¬(H false v u∧H true v u))→
    (∀ u x z,H false x u→H true z u→x≠π z)→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ Full (r+4)→
    HasResourceDecomposition (fun Y:MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources Y) C→
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
          Sum.inr (x,u)∈MD.biUnion markedWheelPhysicalResources):=by
  obtain ⟨beta,eps₁,delta₁,eta₀,hbeta,heps₁,hdelta₁,heta₀,hfirst⟩:=
    marked_sample_prescribed_star_to_balanced_deep_host r hr pstar₁ gamma omega hpstar₁ hpstar₁1 hg hg1 ho
  obtain ⟨eps₂,heps₂,K,hK,zeta,hzeta,θ,hθ,delta₂,hdelta₂,hdeep⟩:=
    marked_sample_deep_cover_from_balanced_reserved_host r (by omega) omega t rho gamma eta ho ht hrho hrho1 hg hg1 hst heta hetaSmall β aLo B pstar₂ hβ hβt haLo hB hpstar₂
  refine ⟨beta,eps₁,delta₁,eta₀,hbeta,heps₁,hdelta₁,heta₀,eps₂,heps₂,K,hK,zeta,hzeta,θ,hθ,delta₂,hdelta₂,?_⟩
  intro etaE hetaE hetaE₀ d hd
  obtain ⟨N₁,hN₁,hfirst⟩:=hfirst etaE hetaE hetaE₀ d hd
  obtain ⟨N₂,hN₂,hdeep⟩:=hdeep d hd
  refine ⟨max N₁ N₂,le_trans hN₁ (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hp1 hk1 hq1 hs1 hq hs σ H hrows1 hindices1 hrows2 hindices2
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1' hk1' hs₁ weight hw hconfigs hload C hC1 hC2
  intro E₀ E₁ tail head ktail khead X T J W hX hT hTI hWJ hXI hJ hIz hJz hnumR hnumV hnumU hC DA DS₀ A S
    hAcard hScard hArows hAdeg hS hSrow hScol Full CA CS KA KS hH hshift hOuter hDec hInner hDA hDS
  have hn₁:N₁≤Fintype.card V:=(le_max_left _ _).trans hn
  have hn₂:N₂≤Fintype.card V:=(le_max_right _ _).trans hn
  obtain ⟨M,hM,hbr,hbv,hbu,hrim1,hrow1,hcol1,hdis,hfirstInner,M',_,_,_,_,_,_,_,_,_,_,_,_,_,hcombined⟩:=
    hfirst V U Γ Color hn₁ hU P π hdeg _ _ q s g j hp1 hk1 hq1 hs1 σ H hrows1 hindices1 C hC1 X T J W hX hT hTI hWJ hXI hJ hC DA DS₀ hAcard hScard hArows hAdeg hS hSrow hScol hH hOuter hDec hInner hDA hDS
  let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
  let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
  have hDR:∀ x,(DR.degree x:ℝ)≤delta₂*Fintype.card V:=fun x=>(hbr x).trans hnumR
  have hDSr:∀ x,(DS.degree (Sum.inl x):ℝ)≤delta₂*Fintype.card V:=fun x=>(hbv x).trans hnumV
  have hDSc:∀ u,(DS.degree (Sum.inr u):ℝ)≤delta₂*Fintype.card V:=fun u=>(hbu u).trans hnumU
  have hI:∀ x,π x∈Xᶜ↔x∈Xᶜ:=by intro x;simpa only [Finset.mem_compl] using not_congr (hX x)
  obtain ⟨MD,hMD,hrim,hrow,hcol,hinner,hactive,hroots,hcoverR,hcoverS,havoid⟩:=
    hdeep V U Γ Color hn₂ hUn hU P π hdeg hparent q s g j hq hs σ H hrows2 hindices2
      D τ p k s₀ hDlo hDhi hp hk hs₀ hp1' hk1' hs₁ weight hw hconfigs hload C hC2 DR DS hDR hDSr hDSc
      Xᶜ T J W hTI hWJ hI hT hIz hJz hH hshift hcombined
  let DRall:=DR⊔physicalEdgeGraph (markedReservedRimPairs C)
  let DSall:=DS⊔markedFiniteSpokeGraph (markedReservedSpokePairs C)
  have hgraphs:=marked_reserved_graphs_of_packing (M.biUnion markedWheelPhysicalResources) M rfl
  have hR:physicalEdgeGraph (markedReservedRimPairs (M.biUnion markedWheelPhysicalResources))≤DRall:=by
    rw [←hgraphs.1,←markedSampleArcSetGraph_packing P π d (r+4) σ H M]
    calc
      markedSampleArcSetGraph P π d σ (M.biUnion markedWheelArcs) ≤ DR := by
        dsimp only [DR]
        rw [markedSampleArcSetGraph_union]
        exact le_sup_right
      _ ≤ DRall := le_sup_left
  have hSgraph:markedFiniteSpokeGraph (markedReservedSpokePairs (M.biUnion markedWheelPhysicalResources))≤DSall:=by
    rw [←hgraphs.2]
    calc
      markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs) ≤ DS := by
        dsimp only [DS]
        rw [markedFiniteSpokeGraph_union]
        exact le_sup_right
      _ ≤ DSall := le_sup_left
  have hMM:=marked_deleted_sample_packing_avoids_reserved_resources P π d (r+4) (by omega) (by omega) σ H
    (M.biUnion markedWheelPhysicalResources) DRall DSall hR hSgraph MD
  refine ⟨M,hM,hdis,hbr,hbv,hbu,hrim1,hrow1,hcol1,hfirstInner,MD,hMD,havoid,hMM,?_,?_,hcol,hinner,hactive,?_,hcoverR,hcoverS⟩
  · simpa only [Finset.mem_compl,not_not] using hrim
  · simpa only [Finset.mem_compl,not_not] using hrow
  · simpa only [compl_compl] using hroots
end Oberwolfach
