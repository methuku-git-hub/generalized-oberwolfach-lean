module

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
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_reservoir_buffered_reference_and_pairing
    (mWheel buffer d:ℕ) (hm:3≤mWheel) (hbuffer:2≤buffer) (ε ρ₀ α pmin δcut ξroot:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hδcut:0<δcut) (hδsmall:δcut<1/4) (hξroot:0<ξroot) (hξε:ξroot≤ε/100)
    (ηlimit:ℝ) (hηlimit:0<ηlimit)
    (βH ηH BHost pstar βparent εparent ζparent rate:ℝ) (N₀:ℕ)
    (hBHost:0≤BHost) (hpstar:0<pstar) (hζparent:0≤ζparent) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH BHost (ρ₀/16) pstar βparent εparent ζparent rate N₀)
    (k:ℕ) (hk:4≤k) (c h δref gap lamroot:ℝ)
    (hroot:OrdinaryUniformDeepRootReferenceAtScale (mWheel+1) (by omega) k α βparent c
      (BHost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*h-ζparent) δref εparent (ρ₀/16) gap lamroot):
    ∃η₀:ℝ,0<η₀ ∧ η₀≤ηlimit ∧ ∃n₀:ℕ,∃δ:ℝ,0<δ ∧ δ≤α ∧
    ∀(Kdom ηf εf γ κ aPair lam b Bweight βe βh:ℝ),
      0<ηf→0<εf→0≤γ→0≤κ→0<aPair→0<lam→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→
      aPair*(2*Kdom)+2*lam≤pmin/2→aPair*(2*Kdom)+2*lam≤pmin*(ρ₀/8)→
      6*lam≤ηf*aPair→γ≤βe→κ≤βe→
    ∀(ζ δcap:ℝ),0<ζ→0≤δcap→δcap≤ζ/2→ζ≤δ→ζ≤δ*(ρ₀/8)→ζ≤lam→ζ≤rate→0<δcap→
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
      0≤εR→εR≤δ→εR≤lam→0≤εH→εH≤δ→εH≤lam→0≤βe→βe≤δ→0≤βh→βh≤δ→
    ∀(A Z Wterm:Finset V) (Bterm Bprotect:Finset U)
      (coins:Sym2 V→Bool) (a aLoad ρ θdeep ζlimit ζcut εcut href αcut:ℝ),
    letI : DecidableEq (markedVortexVertexType Q 0):=Classical.decEq _;
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let raw:=ordinaryRawRestrictPair f g σ;let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    ∀(weight:OrdinaryCycle (P.comap f) (mWheel+1)→ℝ) (βP ηP row εTri:ℝ),
    OrdinaryNonrootNumericInputs (F.comap f) I (ordinaryVortexBufferedVertices Q 0 buffer) B (ordinaryVortexBufferedHubs Q 0 buffer)
      n₀ d (ρ₀/8) a ρ θdeep aLoad ζlimit ε δcut ζcut εcut pH εR εH L href→
    OrdinaryFixedVortexDeepCoverEvent mWheel 0 d a aLoad ρ θdeep P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    0<aLoad→aLoad≤1→80*ξroot≤aLoad^2→
    OrdinaryCorrectedProtectedReservoir (mWheel+1) m t aK bK ξ (R\F) F J A Z Wterm Bterm Bprotect→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D vsize β ε Q π hπ pR pH s j σ→
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel (P.comap f) (F.comap f) I B ρi d pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh b Bweight ηf (fun u=>s (g u)) j raw→
    N₀≤Fintype.card (markedVortexVertexType Q 0)→pstar≤pR→pstar≤pH→0≤c→
    (∀C,c/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((mWheel+1)-2)≤weight C ∧
      weight C≤BHost/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((mWheel+1)-2))→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri (P.comap f) (F.comap f) ρi
      B pR pH (2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D) β→
    ordinaryCombinedHostEvent mWheel d k hm (P.comap f) (F.comap f) ρi (max (1/2) (cycleThreshold (mWheel+1)))
      α pstar βP ηP row ηH βH c BHost pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts (P.comap f) (F.comap f) ρi d j δref h raw
      (fun e:Sym2 (markedVortexVertexType Q 0)=>coins (Sym2.map f.toEmbedding e))→
    ∀(βout extraGap η ξgeom ζout p εout γgeom:ℝ),
    OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale mWheel k buffer ρ₀ (βparent/2)
      (c*(1-δref)^((mWheel+1)-1)) (BHost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gap) extraGap η βout ξgeom ζout p εout γgeom→
    0≤lamroot→lamroot≤1/4→lamroot≤(ρ₀/8)/2→lamroot≤γgeom/(1000*((mWheel:ℝ)+2))→
    ε≤ξgeom/2→ε≤ξgeom*(ρ₀/8)/2→2*ε^buffer≤lamroot→
    aLoad≤γgeom/(1000*((mWheel:ℝ)+2))→ηlimit*ε≤γgeom/8→
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
    Nonempty (OrdinaryMixedHubWeightsOfLength mWheel b Bweight ηf (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B)) ∧
    OrdinaryNonrootWheelCoverResult mWheel 0 ξroot aLoad (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I (ordinaryVortexBufferedVertices Q 0 buffer) B (ordinaryVortexBufferedHubs Q 0 buffer) ∧
    Nonempty (MixedFreshPairingParentInsideRoots mWheel (2*(3*d)) γ κ b Bweight pmin aPair εf ηf
      (spanningRestriction (G.comap f) I) (F.comap f)
      (ordinaryPhysicalGraph (spanningRestriction (G.comap f) I) (fun v u=>Hs (f v) (g u)∧v∈I∧u∈B))
      (ordinaryPhysicalGraph (F.comap f) (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q 0↪_)
      (ordinaryBoundaryHubSet (fun v u=>Hs (f v) (g u)) B I)
      (fun k=>(ordinaryBoundaryRimSet (G.comap f) I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet (fun v u=>Hs (f v) (g u)) I B k).image Sum.inr) (fun _=>pH)) ∧
    let T:=ordinaryVortexBufferedVertices Q 0 buffer;let W:=ordinaryVortexBufferedHubs Q 0 buffer;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q 0)+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q 0)*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let bin:=η₀*I.card;let deep:ℝ:=T.card+2*W.card;
    let fout:=deep+3*ell;let binner:=bin+3*ell+fout;
    ∃Droot:OrdinaryRootCoverNonrootData (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u)) I T B W
      (mWheel+1) (10*ξroot*I.card) ell,
    Nonempty (OrdinaryRootCoverDeepReferenceData (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      I T B W (mWheel+1) k (by omega) (10*ξroot*I.card) ell bin bin deep Droot α (ρ₀/16) (βparent/2) βout
      (c*(1-δref)^((mWheel+1)-1)) (BHost/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζparent) (δref/2) (εparent+gap) (εparent+gap+extraGap) η ξgeom ζout p εout fout binner binner) :=by
  obtain ⟨η₀,hη₀,hηcap,n₀,δ,hδ,hδα,hmain⟩:=
    ordinary_initial_reservoir_buffered_edit_both_balance_cover_and_parent_at_tolerance mWheel 0 buffer d hm ε ρ₀ α pmin δcut ξroot
      hε hε1 hρ₀ hα hpmin hδcut hδsmall hξroot hξε ηlimit hηlimit
  refine ⟨η₀,hη₀,hηcap,n₀,δ,hδ,hδα,?_⟩
  intro Kdom ηf εf γ κ aPair lam b Bweight βe βh hηf hεf hγ hκ haPair hlam hKdom hRrate hHrate herr hγβ hκβ
  intro ζ δcap hζ hδcap0 hδcapζ hζδ hζB hζlam hζrate hδcap ξlimit hξlimit
  obtain ⟨ξ,hξ,hξlimit,hmain⟩:=hmain Kdom ηf εf γ κ aPair lam b Bweight βe βh hηf hεf hγ hκ haPair hlam hKdom hRrate hHrate herr hγβ hκβ
    ζ δcap hζ hδcap0 hδcapζ hζδ hζB hζlam hδcap ξlimit hξlimit
  refine ⟨ξ,hξ,hξlimit,?_⟩
  intro m t aK bK β hβ hβ1 hβδ
  obtain ⟨v₀,N,hv₀,hN,hmain⟩:=hmain m t aK bK β hβ hβ1 hβδ
  refine ⟨v₀,N,hv₀,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεRlam hεH0 hεH hεHlam hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins a aLoad ρ θdeep ζlimit ζcut εcut href αcut F R J f g ρi I B raw L weight βP ηP row εTri
    hnums hDeep hRim hpH1 hεcut hζcut hζlimit hδlim hhref haLoad haLoad1 hξsmall hRes hgood hevent
    hN₀local hpRstar hpHstar hc hweight hinputs event cuts
    βout extraGap η ξgeom ζout p εout γgeom hgeometry hlamroot hlamroot1 hlamrootρ hlamrootγ hεξ hερ hεroot haLoadγ hηlimitγ
  obtain ⟨K,JQ,JH,hw,hprofile,hcover,hpair⟩:=hmain V U Γ Color P D vsize hreg hn hD hρlo hρhi hv hnN Q π hπ j σ s
    pR pH θ εR εH hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεRlam hεH0 hεH hεHlam hβe0 hβe hβh0 hβh
    A Z Wterm Bterm Bprotect coins a aLoad ρ θdeep ζlimit ζcut εcut href αcut pstar
    hnums hDeep hRim hpH1 hεcut hζcut hζlimit hδlim hhref haLoad haLoad1 hξsmall hRes hgood hevent
  let Qcorr:=(R\F)\JQ
  let Hcorr:=fun v u=>J v u∧¬JH v u
  let G:=Qcorr\ordinaryResourceRim Qcorr K
  let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K)
  have hprofile':=hprofile
  rcases hprofile' with ⟨hGP,hdis,hbal,hdiv,hL0,hLζ,hphysical,hlocal,hnear,hcross,hHub⟩
  have hIle:(I.card:ℝ)≤Fintype.card (markedVortexVertexType Q 0):=by exact_mod_cast Finset.card_le_univ I
  have hLrate:L≤rate*Fintype.card (markedVortexVertexType Q 0):=by
    have h1:=mul_le_mul_of_nonneg_left hIle hζ.le
    have h2:=mul_le_mul_of_nonneg_right hζrate (show (0:ℝ)≤Fintype.card (markedVortexVertexType Q 0) by positivity)
    linarith
  have hbalcap:η₀*ε≤γgeom/8:=(mul_le_mul_of_nonneg_right hηcap hε.le).trans hηlimitγ
  have href:=ordinary_vortex_initial_buffered_reference_from_cover mWheel buffer hm hbuffer βH ηH BHost ρ₀ pstar βparent εparent ζparent rate N₀
    hBHost hρ₀ hpstar hζparent hN₀ hscale k hk α c h δref gap lamroot hroot P G Hs D vsize β ε Q π hπ d j σ coins s
    βP ηP row εTri pR pH η₀ L weight hreg hn hD hρlo hρhi hβ hβ1 hε (by omega) hN₀local hL0 hLrate hGP hdis
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hinputs
    hpRstar hpR1 hpHstar hpH1 hc hweight event cuts
    (by intro w;convert hphysical w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hη₀.le (by intro v;convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hcross v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    βout extraGap η ξgeom ζout p εout γgeom ξroot aLoad hgeometry hlamroot hlamroot1 hlamrootρ hlamrootγ hεξ hερ hεroot haLoad.le haLoadγ hbalcap hcover
  refine ⟨K,JQ,JH,hw,?_,?_,?_,?_⟩
  · convert hprofile using 1 <;> congr! 40
  · convert hcover using 1 <;> congr! 40
  · convert hpair using 1 <;> congr! 40
  · convert href using 1 <;> congr! 40
end Oberwolfach
