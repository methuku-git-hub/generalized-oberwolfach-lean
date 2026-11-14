module

public import Oberwolfach.OrdinaryInitialReservoirSharpReferenceEnvelopedScaledProfile
public import Oberwolfach.OrdinaryInitialNumericFromShared
public import Oberwolfach.OrdinaryVortexInitialEditEnvelope
public import Oberwolfach.OrdinaryVortexUniformEditCostEvents
public import Oberwolfach.OrdinaryVortexAsymmetricPairingGeometryProp
public import Oberwolfach.OrdinaryInitialReservoirFineCoverSeparatedProfile
public import Oberwolfach.OrdinaryVortexInitialFineSharpReferenceGeneralLoad
public import Oberwolfach.OrdinaryInitialReservoirBufferedEditBothBalanceCoverAndParentAtTolerance
public import Oberwolfach.OrdinaryVortexInitialBufferedReferenceFromCover
public import Oberwolfach.OrdinaryInitialEditBothBalanceProfileWithReservoir
public import Oberwolfach.OrdinaryVortexPairingParentFromProfileAt
public import Oberwolfach.OrdinaryInitialProfileWithCorrectedReservoir
public import Oberwolfach.OrdinaryVortexInitialBufferedNonrootCover
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! Retain the same selected absorber and correction when deriving the
initial local profile and adaptive hub weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_reservoir_sharp_reference_shared_numeric_scaled_profile
    (mWheel loadK d:ℕ) (hm:3≤mWheel) (ρ₀ α pmin δcut:ℝ)
    (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hδcut:0<δcut) (hδsmall:δcut<1/4):
    ∃cProfile:ℝ,0<cProfile ∧
    ∀(ε:ℝ) (hε:0<ε) (hε1:ε<1/4)
    (ξroot:ℝ) (hξroot:0<ξroot) (hξε:ξroot≤ε/100)
    (ηlimit:ℝ) (hηlimit:0<ηlimit)
    (βH ηH BHost pstar βparent εparent ζparent rate:ℝ) (N₀:ℕ)
    (hBHost:0≤BHost) (hpstar:0<pstar) (hζparent:0≤ζparent) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH BHost (ρ₀/16) pstar βparent εparent ζparent rate N₀)
    (k:ℕ) (hk:4≤k) (c h δref gap lamroot:ℝ)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (by omega) α βparent c
      (BHost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*h-ζparent) δref εparent (ρ₀/16) gap lamroot),
    ∃η₀:ℝ,0<η₀ ∧ η₀≤ηlimit ∧ ∃n₀:ℕ,∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(Kdom ηf b Binner βe βh:ℝ),0<ηf→0≤b→0≤Binner→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→
    ∀(ζ δcap capEdit:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→ζ≤rate→0<δcap→0<capEdit→δcap≤capEdit/2→
    ∀(a aLoad ρ θdeep ζlimit ζcut εcut href εsample εvortex:ℝ),
    0<aLoad→ε≤εvortex→capEdit≤ζlimit→
    OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href a ρ θdeep δcut ζcut εcut ζlimit εsample εvortex→
    ∀ξlimit:ℝ,0<ξlimit→∃ξ:ℝ,0<ξ ∧ ξ≤ξlimit ∧
    ∀m t aK bK:ℕ,∀β:ℝ,0≤β→β≤1/4→β≤δ→∃v₀ N:ℕ,1≤v₀ ∧ 1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→N≤Fintype.card V→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (j:Color) (σ:RawWheelOutcome V U Γ Color) (s:U→Color→ℝ)
      (pR pH θ εR εH:ℝ),
      pmin≤pR→pR≤1→pmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→εR≤εsample→0≤εH→εH≤δ→εH≤εsample→0≤βe→βe≤cProfile*ε→0≤βh→βh≤cProfile*ε→
    ∀(A Z Wterm:Finset V) (Bterm Bprotect:Finset U)
      (coins:Sym2 V→Bool) (αcut:ℝ),
    letI : DecidableEq (markedVortexVertexType Q 0):=Classical.decEq _;
    letI : DecidableEq (markedVortexHubType Q 0):=Classical.decEq _;
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    ∀(weight:OrdinaryCycle (P.comap f) (mWheel+1)→ℝ) (βP ηP row εTri:ℝ),
    OrdinaryFixedVortexDeepCoverEvent mWheel loadK d a aLoad ρ θdeep P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<aLoad→aLoad≤1→80*ξroot≤aLoad^2→
    OrdinaryCorrectedProtectedReservoir (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryUniformEditWeightEvents Q π hπ mWheel d pR pH capEdit βe βh b Binner ηf
      (fun _=>θ+α-β/2) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) s j σ→
    N₀≤Fintype.card (markedVortexVertexType Q 0)→pstar≤pR→pstar≤pH→0≤c→
    (∀C,c/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((mWheel+1)-2)≤weight C ∧
      weight C≤BHost/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((mWheel+1)-2))→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri (P.comap f) (F.comap f) ρi
      B pR pH (2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D) β→
    ordinaryCombinedHostEvent mWheel d k hm (P.comap f) (F.comap f) ρi (max (1/2) (cycleThreshold (mWheel+1)))
      α pstar βP ηP row ηH βH c BHost pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts (P.comap f) (F.comap f) ρi d j δref h raw
      (fun e:Sym2 (markedVortexVertexType Q 0)=>coins (Sym2.map f.toEmbedding e))→
    ∀(βout εstar ηpack ξgeom ζout p εout:ℝ),
    let T:=ordinaryVortexBufferedVertices Q 0 2;let W:=ordinaryVortexBufferedHubs Q 0 2;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q 0)+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q 0)*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let bin:=η₀*I.card;
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L;
    let cover:=10*ξroot*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Q 0);
    let Aroot:=Finset.univ\T;let Croot:=Finset.univ\W;
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈B);
    (T.card:ℝ)+W.card≤lamroot*Fintype.card (markedVortexVertexType Q 0)→0≤deep→
    OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) (βparent/2) βout (c*(1-δref)^mWheel)
      (BHost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (εparent+gap) εstar ηpack ξgeom ζout p εout
      (deep+2*cover) (bin+deep+4*cover) (bin+deep+loss) Xf Zf→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Aroot→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Croot→
    ∀(Ncert N:ℕ) (δend ζh ζe γ eCoeff:ℝ),
    0≤δend → 0<ζh → 0<ζe → 0<γ → γ≤eCoeff →
    Ncert≤N → 2/ε≤N → (N:ℝ)≤ε*vsize/2 → 0≤rate →
    εR≤δend/4 → εH≤δend/4 → rate≤δend*ε/8 →
    ∃(K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop),
    OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect K JQ JH ∧
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    (G≤P ∧ Disjoint G F ∧
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card) ∧
    0≤L ∧ L≤ζ*I.card ∧
    (∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρi d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset w)).card:ℝ)≤L) ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) ρi d I B
      pR pH (θ+α-β/2) (εR*I.card) (εH*B.card) L βe βh (fun u=>s (g u)) j raw ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η₀*I.card) ∧
    (∀v∉I,|(((G.comap f).neighborFinset v∩I).card:ℝ)-2*(B.filter (fun u=>Hs (f v) (g u))).card|≤η₀*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel b Binner ηf (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B)) ∧
    OrdinaryFineWheelCoverResult mWheel loadK ξroot aLoad (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I (ordinaryVortexBufferedVertices Q 0 2) B (ordinaryVortexBufferedHubs Q 0 2) ∧
    ∃Droot:OrdinaryRootCoverNonrootData (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) I T B W
      (mWheel+1) (10*ξroot*I.card) ell,
    Nonempty (OrdinaryRootCoverSharpReferenceData (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      I T B W (mWheel+1) k (by omega) (10*ξroot*I.card) ell bin bin deep loss Droot α (ρ₀/16) (βparent/2) βout
      (c*(1-δref)^((mWheel+1)-1)) (BHost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζparent) (δref/2) (εparent+gap) εstar ηpack ξgeom ζout p εout (deep+2*cover) (bin+deep+4*cover) (bin+deep+loss)) ∧
    OrdinaryVortexAsymmetricPairingGeometryAt Q 0 Ncert ρ₀ δend εR εH L ζh ζe γ eCoeff :=by
  obtain ⟨cProfile,hProfile,hmain⟩:=
    ordinary_initial_reservoir_sharp_reference_enveloped_scaled_profile mWheel loadK d hm ρ₀ α pmin δcut
      hρ₀ hα hpmin hδcut hδsmall
  refine ⟨cProfile,hProfile,?_⟩
  intro ε hε hε1 ξroot hξroot hξε ηlimit hηlimit βH ηH BHost pstar βparent εparent ζparent rate N₀
    hBHost hpstar hζparent hN₀ hscale k hk c h δref gap lamroot hroot
  obtain ⟨η₀,hη₀,hηcap,n₀,δ,hδ,hδα,hmain⟩:=hmain ε hε hε1 ξroot hξroot hξε ηlimit hηlimit
    βH ηH BHost pstar βparent εparent ζparent rate N₀ hBHost hpstar hζparent hN₀ hscale k hk c h δref gap lamroot hroot
  refine ⟨η₀,hη₀,hηcap,n₀,δ,hδ,hδα,?_⟩
  intro Kdom ηf b Binner βe βh hηf hb hBinner hKdom
  intro ζ δcap capEdit hζ hδcap0 hδcapζ hζδ hζB hζrate hδcap hcapEdit hδcapEdit
  intro a aLoad ρ θdeep ζlimit ζcut εcut href εsample εvortex haLoad hεv hcapLimit hNumeric
  intro ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlimit,hmain⟩:=hmain Kdom ηf b Binner βe βh hηf hb hBinner hKdom
    ζ δcap capEdit hζ hδcap0 hδcapζ hζδ hζB hζrate hδcap hcapEdit hδcapEdit ξlimit hξlimit
  refine ⟨ξ,hξ,hξlimit,?_⟩
  intro m t aK bK β hβ hβ1 hβδ
  obtain ⟨v₀,N,hv₀,hN,hmain⟩:=hmain m t aK bK β hβ hβ1 hβδ
  obtain ⟨vNum,hvNum,hnum⟩:=ordinary_initial_numeric_from_shared ρ₀ pmin href a ρ θdeep δcut ζcut εcut ζlimit εsample εvortex
    hNumeric ε hε hεv aLoad haLoad β hβ hβ1 d n₀
  obtain ⟨vEnv,hvEnv,henv⟩:=ordinary_vortex_initial_edit_envelope ε ρ₀ capEdit d hε hε1 hρ₀ hcapEdit β hβ hβ1
  refine ⟨max v₀ (max vNum vEnv),N,by omega,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεRsample hεH0 hεH hεHsample hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins αcut F R J f g ρi I B raw L weight βP ηP row εTri
  have hL:=henv V U P D vsize hreg hn hD hρlo hρhi (by omega) Q 0 Q.length_pos δcap hδcap0 hδcapEdit
  have hL0:0≤L:=by convert hL.1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hLcap:L≤ζlimit*I.card:=by
    have hx:=mul_le_mul_of_nonneg_right hcapLimit (show (0:ℝ)≤I.card by positivity)
    have hy:L≤capEdit*I.card:=by convert hL.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact hy.trans hx
  have hnums:=hnum V U P D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ pH εR εH L hpH hεR0 hεRsample hεH0 hεHsample hL0 hLcap
  apply hmain V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) hnN Q π hπ j σ s
    pR pH θ εR εH hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins a aLoad ρ θdeep ζlimit ζcut εcut href αcut weight βP ηP row εTri
  convert hnums using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
