module

public import Oberwolfach.MarkedReferenceLevelStepXiMonotonicity
public import Oberwolfach.MarkedTypedLossFromSymmetricChanges
public import Oberwolfach.MarkedReferenceCompletionTypedChangeGraphs
public import Oberwolfach.MarkedSpokeDeletionRepresentation
public import Oberwolfach.MarkedReferenceCompletionPhysicalRims
public import Oberwolfach.MarkedReferenceCompletionAfterPhysicalDeletion
public import Oberwolfach.MarkedUniformReferenceLevelStep
public import Oberwolfach.MarkedReferenceReservedCompletion
public import Oberwolfach.MarkedReferenceLevelStepProperty
public import Oberwolfach.MarkedReferenceStateStepDecomposition
public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedNextSampleCanonicalRemainder
public import Oberwolfach.MarkedDeletedCoverFixedRemainder
public import Oberwolfach.MarkedReferenceInputStability
public import Oberwolfach.MarkedGlobalCoverInputMargins
public import Oberwolfach.MarkedLocalCoverInputMargins
public import Oberwolfach.MarkedNestedIterationBalanceInputs
public import Oberwolfach.MarkedResourceDomainMonotonicity
public import Oberwolfach.MarkedIterationNeighbourhoodFromResources
public import Oberwolfach.MarkedIterationToleranceChoices

@[expose] public section

/-! Uniform level-step completion using the same physical change graphs,
with additions and deletions and agreement on the protected inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_uniform_reference_completion_with_xi_cap (gamma pA0:ℝ)
    (hg:0< gamma) (hg1:gamma≤   1) (hpA0:0< pA0) (hpA01:pA0≤   1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤   r →            c₀≤   r+5 →            ∀ rho omega t p0 betaA aLoA BA:ℝ,
    0< rho →            rho≤   1 →            0< omega →            omega≤   1 →            0< t →            (r+4:ℝ)*t≤   1 →            
    pA0≤   rho*(r+4:ℝ)*t/2 →            0< p0 →            p0≤   rho*(r+4:ℝ)*t/2 →            p0≤   rho*t/2 →            p0≤   t →            0< betaA →            0< aLoA →            0< BA → ∀ xiCap:ℝ,0<xiCap →
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   ξ≤xiCap∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa →            kappa≤   kappa0 →            
    ∀ alphaInner omegaInner:ℝ,0< alphaInner →         0< omegaInner →         omegaInner≤   1 →         
    ∃ betaExt epsilonExt:ℝ,0< betaExt∧   0< epsilonExt∧   
    ∃ gammaMax:ℝ,0<gammaMax ∧ ∀ gammaLoss iota β aLo B:ℝ,0<gammaLoss → gammaLoss≤gammaMax →   0< iota →        0<β →        β≤   betaExt →        0< aLo →        0≤   B →        
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ) (hp:0< p) (hp1:p≤   1),p≤   pmax →            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x →    x≤   delta →    
    ∃ sigmaMax:ℝ,0<sigmaMax ∧ ∀ sigmaLoss:ℝ,0<sigmaLoss → sigmaLoss≤sigmaMax →  ∀ omegaI hIcut deltaI:ℝ,0< omegaI →    0< hIcut →    0< deltaI →    deltaI<1/4 →    
    ∃ etaBal:ℝ,0< etaBal∧   ∃ NI:ℕ,∀ d:ℕ,1≤   d →            ∃ N:ℕ,1≤   N∧   
    ∀ (ε:ℝ),ξ≤ε → ∀ (s a₀ b₀ e₀ f:ℕ),∃ N₀:ℕ,
    ∀ (Gamma Color:Type) [Fintype Gamma] [Fintype Color],
    ∀ (levels:ℕ → MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal),
    letI : ∀ i,Fintype (levels i).VP:=fun i=>(levels i).inst7
    letI : ∀ i,Fintype (levels i).UP:=fun i=>(levels i).inst8
    letI : ∀ i,LinearOrder (levels i).VP:=fun i=>(levels i).inst9
    letI : ∀ i,DecidableEq (levels i).UP:=fun i=>(levels i).inst10;
    N₀≤Fintype.card (levels 0).VP →
    ∀ (count:ℕ),0<count → ∀ chain:MarkedReferenceLevelChain levels count,
    let VP:=(levels 0).VP
    let UP:=(levels 0).UP
    let E:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) false
    let K:=MarkedSampleArc (levels 0).PP (levels 0).πP (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let H₀:=(levels 0).HBase false
    let HK:=(levels 0).HBase true
    let π:=(levels 0).πP
    let R:=fun W:MarkedWheel tail head ktail khead (r+4) π (3*d) H₀ HK=>markedWheelPhysicalResources W
    let S:=Finset.univ.filter (fun z:VP×UP=>H₀ z.1 z.2∨HK z.1 z.2)
    let Full:=markedFiniteResources tail head ktail khead π Finset.univ S
    let last:=count-1
    let X:=(levels last).I.image (chain.intoV last)
    let Y:=(levels last).J.image (chain.intoU last);
    ∀ (σOriginal:RawMarkedOutcome VP UP Gamma Color) (HOriginal:Bool→VP→UP→Prop)
      (ζ:ℝ),
    (∀ mark x y,x∈(levels 0).I→y∈(levels 0).I→
      (markedPhysicalRim (levels 0).PP π (3*d) (fun e=>σOriginal (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim (levels 0).PP π (3*d) (fun e=>(levels 0).σBase (Sum.inl e)) mark x y=1)) →
    (∀ b v u,v∈(levels 0).I→u∈(levels 0).J→
      (HOriginal b v u↔(levels 0).HBase b v u)) →
    (∀ v u,¬(HOriginal false v u∧HOriginal true v u)) →
    ∀ (FR:SimpleGraph VP) (FS:SimpleGraph (VP⊕UP)),
    (∀ a,¬(rawMarkedPairRims (levels 0).PP π d σOriginal a↔
      rawMarkedPairRims (levels 0).PP π d (levels 0).σBase a)→
      markedPairPhysical π a∈FR.edgeFinset) →
    (∀ b v u,¬(HOriginal b v u↔(levels 0).HBase b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ x,(FR.degree x:ℝ)≤ζ*Fintype.card VP) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card VP) →
    (∀ (DR':SimpleGraph VP) (DS':SimpleGraph (VP⊕UP)),
      (∀ x,(DR'.degree x:ℝ)≤ζ*Fintype.card VP) → (∀ z,(DS'.degree z:ℝ)≤ζ*Fintype.card VP) →
      let σ':=rawMarkedDeleteRims σOriginal DR'.edgeFinset
      let H':=markedDeletePhysicalSpokes HOriginal DS'
      let E':=MarkedSampleArc (levels 0).PP π (3*d) (fun e=>σ' (Sum.inl e)) false
      let K':=MarkedSampleArc (levels 0).PP π (3*d) (fun e=>σ' (Sum.inl e)) true;
      MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r s a₀ b₀ e₀ f ε) →
    MarkedRemainderDivisible tail head ktail khead HK Finset.univ S (r+4) →
    X.card+Y.card≤s →
    HasResourceDecomposition R Full := by
  obtain ⟨c₀,hcover⟩ := marked_uniform_reference_level_step gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA xiCap hCap
  obtain ⟨Kgeom,hKgeom,kappa0,xiOld,thetaDeep,hkappa0,hXiOld,hΘDeep,hcover⟩ :=
    hcover r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  let ξ:=min xiOld xiCap
  have hξ:0<ξ:=lt_min hXiOld hCap
  have hξOld:ξ≤xiOld:=min_le_left _ _
  refine ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,min_le_right _ _,hΘDeep,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩ := hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨gammaMax,hGammaMax,hcover⟩ := hcover
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,gammaMax,hGammaMax,?_⟩
  intro gammaLoss iota β aLo B hGammaLoss hGammaBound hIota hβ hBetaSmall haLo hB
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩ :=
    hcover gammaLoss iota β aLo B hGammaLoss hGammaBound hIota hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,delta,hdelta,hcover⟩ := hcover p hp hp1 hpp
  refine ⟨θ,hθ,delta,hdelta,?_⟩
  intro x hx hxdelta
  obtain ⟨sigmaMax,hSigmaMax,hcover⟩ := hcover x hx hxdelta
  refine ⟨sigmaMax,hSigmaMax,?_⟩
  intro sigmaLoss hSigmaLoss hSigmaBound omegaI hIcut deltaI hoI hhI hdI hdIs
  obtain ⟨etaBal,hetaBal,NI,hcover⟩ := hcover sigmaLoss hSigmaLoss hSigmaBound omegaI hIcut deltaI hoI hhI hdI hdIs
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨NN,hNN,hcover⟩ := hcover d hd
  refine ⟨NN,hNN,?_⟩
  intro ε hξε s a₀ b₀ e₀ f
  obtain ⟨Ng,hNg⟩:=exists_nat_gt ((e₀:ℝ)/gammaLoss)
  obtain ⟨Ns,hNs⟩:=exists_nat_gt ((e₀:ℝ)/sigmaLoss)
  refine ⟨max Ng Ns,?_⟩
  intro Gamma Color _ _ levels hn count hcount chain
  intro VP UP E K tail head ktail khead H₀ HK π R S Full last X Y
    σOriginal HOriginal ζ hprotectedR hprotectedS htypes FR FS hchangeR hchangeS hdegR hdegS hrob hdiv hs
  letI:Fintype (levels 0).VP:=(levels 0).inst7
  letI:Fintype (levels 0).UP:=(levels 0).inst8
  letI:LinearOrder (levels 0).VP:=(levels 0).inst9
  letI:DecidableEq (levels 0).UP:=(levels 0).inst10
  have hnG:Ng≤Fintype.card VP:=(le_max_left _ _).trans hn
  have hnS:Ns≤Fintype.card VP:=(le_max_right _ _).trans hn
  have hI:((levels 0).I.card:ℝ)≤ε*Fintype.card VP+f:=by
    have hh:=mul_le_mul_of_nonneg_right hξε (Nat.cast_nonneg (Fintype.card VP))
    have hi:((levels 0).I.card:ℝ)≤ξ*Fintype.card VP:=(levels 0).hIsize
    have hf:0≤(f:ℝ):=by positivity
    linarith
  have hJ:((levels 0).J.card:ℝ)≤ε*Fintype.card VP+f:=by
    have hh:=mul_le_mul_of_nonneg_right hξε (Nat.cast_nonneg (Fintype.card VP))
    have hi:((levels 0).J.card:ℝ)≤ξ*Fintype.card VP:=(levels 0).hJsize
    have hf:0≤(f:ℝ):=by positivity
    linarith
  have hG:(e₀:ℝ)≤gammaLoss*Fintype.card VP:=by
    have hn':(Ng:ℝ)≤Fintype.card VP:=by exact_mod_cast hnG
    have hh:((e₀:ℝ)/gammaLoss)*gammaLoss<(Fintype.card VP:ℝ)*gammaLoss:=
      mul_lt_mul_of_pos_right (hNg.trans_le hn') hGammaLoss
    have he:(e₀:ℝ)/gammaLoss*gammaLoss=e₀:=div_mul_cancel₀ _ (ne_of_gt hGammaLoss)
    rw [he] at hh
    linarith
  have hStar:(e₀:ℝ)≤sigmaLoss*Fintype.card VP:=by
    have hn':(Ns:ℝ)≤Fintype.card VP:=by exact_mod_cast hnS
    have hh:((e₀:ℝ)/sigmaLoss)*sigmaLoss<(Fintype.card VP:ℝ)*sigmaLoss:=
      mul_lt_mul_of_pos_right (hNs.trans_le hn') hSigmaLoss
    have he:(e₀:ℝ)/sigmaLoss*sigmaLoss=e₀:=div_mul_cancel₀ _ (ne_of_gt hSigmaLoss)
    rw [he] at hh
    linarith
  exact marked_reference_completion_from_typed_change_graphs levels count hcount gammaLoss sigmaLoss ε s a₀ b₀ e₀ f chain
    (fun i _=>marked_reference_step_from_larger_xi (levels i) hξOld gammaLoss sigmaLoss
      (hcover Gamma Color (marked_reference_level_increase_xi (levels i) hξOld))) σOriginal HOriginal ζ hprotectedR hprotectedS htypes FR FS
    (marked_removed_typed_rim_from_pair_change (levels 0).PP FR π d σOriginal (levels 0).σBase hchangeR)
    (marked_missing_spoke_from_pair_change FS HOriginal (levels 0).HBase hchangeS)
    hdegR hdegS hrob hs hI hJ hG hStar hdiv
end Oberwolfach
