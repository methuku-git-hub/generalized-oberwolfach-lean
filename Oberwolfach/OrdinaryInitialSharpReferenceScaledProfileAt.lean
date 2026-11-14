module

public import Oberwolfach.OrdinaryInitialReservoirSharpReferenceSharedNumericScaledProfile

@[expose] public section
/-! Name the early, scale-uniform initial reference callback for use in
parameter selectors without repeating its host-level proof. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryInitialSharpReferenceScaledProfileAt
    (mWheel loadK d:ℕ) (hm:3≤mWheel) (ρ₀ α pmin δcut cProfile:ℝ):Prop:=
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
    OrdinaryVortexAsymmetricPairingGeometryAt Q 0 Ncert ρ₀ δend εR εH L ζh ζe γ eCoeff
end Oberwolfach
