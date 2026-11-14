module

public import Oberwolfach.MarkedReservedDecompositionAfterDeletion
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
theorem marked_reference_two_stage_cover_with_supported_reserve
    (r:ℕ) (hr:2≤r) (gamma omega t rho eta betaA aLoA BA betaCap:ℝ)
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
    ∀ (FR:SimpleGraph L.VP) (FS:SimpleGraph (L.VP⊕L.UP)),
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card L.VP)→(∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card L.VP)→
    let V:=L.VP
    let U:=L.UP
    let P:=L.PP
    let π:=L.πP
    let σ:=rawMarkedDeleteRims L.σBase FR.edgeFinset
    let H:=markedDeletePhysicalSpokes L.HBase FS
    let Eold:=MarkedSampleArc P π (3*d) (fun e=>L.σBase (Sum.inl e)) false
    let Kold:=MarkedSampleArc P π (3*d) (fun e=>L.σBase (Sum.inl e)) true
    let told:=fun e:Eold=>e.val.1
    let hold:=fun e:Eold=>e.val.2
    let ktold:=fun e:Kold=>e.val.1
    let khold:=fun e:Kold=>e.val.2;
    ∀ (C₀:MarkedSupportedEdgeSet told hold ktold khold π U) (Wres:Finset V) (Bres:Finset U),
    let C:=C₀.edges;
    (∀ e∈C,¬MarkedOldResource told hold ktold khold π Wres Bres e)→
    (C.card:ℝ)≤min delta₁ delta₂*Fintype.card V→
    (∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬FR.Adj x y)→
    (∀ v u,Sum.inr (v,u)∈C→¬FS.Adj (Sum.inl v) (Sum.inr u))→
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
    HasResourceDecomposition (fun Y:MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>L.σBase (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>L.σBase (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (r+4) π (3*d) (L.HBase false) (L.HBase true)=>markedWheelPhysicalResources Y) C→
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
          Sum.inr (x,u)∈MD.biUnion markedWheelPhysicalResources) :=by
  have hρt:=marked_two_stage_complete_density_bounds r t rho ht hrho hrho1 hst
  obtain ⟨β,hβ,hβt,hβcap,hmargin⟩:=
    marked_reference_choose_uniform_change_margins r betaA t betaCap hbetaA ht hbetaCap
  obtain ⟨beta,eps₁,delta₁,eta₀,hbeta,heps₁,hdelta₁,heta₀,eps₂,heps₂,K,hK,zeta,hzeta,θ,hθ,delta₂,hdelta₂,xi,etaE,hxi,hetaE,hcover⟩:=
    marked_two_stage_sample_cover_compact_caller r hr gamma omega t rho eta hg hg1 ho ht hrho hrho1 hst heta hetaSmall
      β aLoA BA (rho*t/2) hβ hβt haLoA hBA hρt.1
  refine ⟨β,beta,eps₁,delta₁,eta₀,hβ,hβt,hβcap,hbeta,heps₁,hdelta₁,heta₀,eps₂,heps₂,K,hK,zeta,hzeta,θ,hθ,delta₂,hdelta₂,xi,etaE,hxi,hetaE,?_⟩
  intro cap hcap
  let coeff:ℝ:=15*((r+4:ℝ)+1)^4*(2*BA/(rho*t/2)^(2*(r+4)+1))
  have hc:0≤coeff:=marked_reference_weighted_change_coefficient_nonnegative r BA (rho*t/2) hBA hρt.1
  obtain ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,hreg,hR,hI,hC,hP,hload⟩:=
    hmargin eps₁ eps₂ θ coeff cap heps₁ heps₂ hθ hc hcap
  refine ⟨kappa,thetaDeep,ζ,hκ,hθD,hζ,hκcap,hθcap,hζcap,?_⟩
  intro d hd
  obtain ⟨N,hN,hcover⟩:=hcover d (by omega)
  refine ⟨N,hN,?_⟩
  intro NI Kgeom p0 ξ alphaInner omegaInner iota aLo B η x omegaI hIcut deltaI etaBal L
  letI:Fintype L.VP:=L.inst7
  letI:Fintype L.UP:=L.inst8
  letI:LinearOrder L.VP:=L.inst9
  letI:DecidableEq L.UP:=L.inst10
  intro FR FS hdegR hdegS V U P π σ H Eold Kold told hold ktold khold
  let p:ℝ:=rho*(r+4:ℝ)*t/2
  let k:ℝ:=rho*t/2
  let sr:ℝ:=(r+4:ℝ)*t
  let D:ℝ:=2*Fintype.card U/rho
  have hn:0<Fintype.card V:=lt_of_lt_of_le (by omega) L.hnP
  have hscaled:=marked_reference_scale_neighbourhood_margins r kappa ζ eps₁ eps₂ (Fintype.card V) (Nat.cast_nonneg _) hR hI
  have hp:rho*t/2≤p:=by dsimp [p];push_cast;have h:=hρt.2.1;push_cast at h;nlinarith [h]
  have hk:rho*t/2≤k:=le_refl _
  have hs:rho*t/2≤sr:=by dsimp [sr];push_cast;have h:=hρt.2.2.2.1;push_cast at h;nlinarith [h]
  have hp1:p≤1:=by dsimp [p];push_cast;have h:=hρt.2.2.2.2.1;push_cast at h;nlinarith [h]
  have hk1:k≤1:=hρt.2.2.2.2.2.1
  have hs1:sr≤1:=by dsimp [sr];push_cast;have h:=hρt.2.2.2.2.2.2;push_cast at h;nlinarith [h]
  have inputs:=marked_reference_two_stage_inputs_after_deletions L eps₁ eps₂ θ (rho*t/2) ζ hreg hζ.le hρt.1 hBA
    hn hp hk hs hp1 hk1 hs1 hscaled.1 hscaled.2 hC hP hload FR FS hdegR hdegS
  obtain ⟨hparent,hq,hsq,hrows,hindices,hw,hconfigs,hloads,hH,hshift⟩:=inputs
  have hsamp:∀ u,L.sP u L.cP=(((r+1)+3:ℕ):ℝ)*t:=by
    intro u
    rw [L.hsP]
    push_cast
    ring
  have hpform:rho*((((r+1)+3:ℕ):ℝ)*t)/2=p:=by dsimp [p];push_cast;ring
  change MarkedRowsWithSpokes P π d (r+12) Finset.univ p k L.qP L.sP L.aP L.cP
    (min eps₁ eps₂*Fintype.card V) σ H at hrows
  rw [←hpform] at hrows
  have hUP:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast L.hUP
  have hmain:=hcover V U Gamma Color L.hnP hUP L.hUPlow P π L.hPdeg hparent L.qP L.sP L.aP L.cP hq hsamp σ H hrows hindices
    D L.tauRef p k sr L.hDloP L.hDhiP hp hk hs hp1 hk1 hs1 L.weightRef hw hconfigs hloads
  intro C₀ Wres Bres C hCold hC hAvoidR hAvoidS E₀ E₁ tail head ktail khead X T J W hX hT hTI hWJ hXI hJ hIW hJB DA DS₀ A S hA hS hAdeg hSrow hScol Full CA CS KA KS hOuter hDec hInner hDA hDS
  have hI:∀ v,π v∈Xᶜ↔v∈Xᶜ:=by intro v;simpa only [Finset.mem_compl] using not_congr (hX v)
  have hCavoid:=marked_supported_reserve_avoids_inner_subset C₀ Xᶜ Wres J Bres hI hIW hJB hCold
  have hDec':=marked_reserved_decomposition_after_avoiding_deletions P π d (r+4) L.σBase L.HBase C FR FS hAvoidR hAvoidS hDec
  exact hmain C hC X T J W hX hT hTI hWJ hXI hJ hCavoid DA DS₀ hA hS hAdeg hSrow hScol hH hshift hOuter hDec' hInner hDA hDS
end Oberwolfach
