module

public import Oberwolfach.OrdinaryVortexHistoryWindowLocalBalance
public import Oberwolfach.OrdinaryVortexHistoryLocalCrossBalance
public import Oberwolfach.OrdinaryDeepTraceCommonCoverProfileLocalBalance
public import Oberwolfach.OrdinaryVortexDeepTraceBufferedCoverToReferenceLocalBalance
public import Oberwolfach.OrdinaryDeepTracePairingParentAt
public import Oberwolfach.OrdinaryVortexDeepTraceBufferedCoverToReference
public import Oberwolfach.OrdinaryDeepTraceCommonCoverSeparatedBalance
public import Oberwolfach.OrdinaryVortexTraceFullParentGeneralBufferedDeepReferenceCoarseBalance
public import Oberwolfach.OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale
public import Oberwolfach.OrdinaryCrossBalanceCardBound
public import Oberwolfach.OrdinaryVortexTraceFullParentGeneralDeepRootReference
public import Oberwolfach.OrdinaryFixedVortexCleanupBothBalance
public import Oberwolfach.OrdinaryVortexTraceFullParentTriangleAtScale
public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance
public import Oberwolfach.OrdinaryTriangleParentRootScaleChoice
public import Oberwolfach.OrdinaryTriangleEditedParentScaled
public import Oberwolfach.OrdinaryVortexTraceParentDirectEdits
public import Oberwolfach.OrdinaryTriangleDeepInputsFixedDomain
public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryVortexTraceNondeeperHost
public import Oberwolfach.OrdinaryVortexNondeeperTriangleInputs

@[expose] public section
/-! Construct the ordinary triangle edited parent from the actual protected
trace and the common local sample tests, with a single edit-rate condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_deep_trace_buffered_same_sample_history_balance_pairing
    (mWheel buffer:ℕ) (hmWheel:3≤mWheel) (hbuffer:2≤buffer) (βH ηH B ρ₀ pstar βparent εparent ζ rate:ℝ) (N₀:ℕ)
    (hB:0≤B) (hρ₀:0<ρ₀) (hp:0<pstar) (hζ:0≤ζ) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B (ρ₀/16) pstar βparent εparent ζ rate N₀)
    (k:ℕ) (hk:4≤k) (α c h δ gap lam:ℝ)
    (hroot:OrdinaryUniformDeepRootReferenceAtScale (mWheel+1) (by omega) k α βparent c (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) δ εparent (ρ₀/16) gap lam):
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ)
      (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
      (K:Finset (Sym2 V⊕(V×U)))
      (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
      (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
      (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
      (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
      (βP ηP row εTri pR pH θ εR εH βe βh ηbal ηProfile:ℝ) (s:U→Color→ℝ)
      (pmin href δcut ζcut εcut ζlimit εsample ξroot aLoad a ρ configθ ζe cBoundary δe rateC C αcut:ℝ)
      (ηf εf γpair κpair aPair lamPair bPair Bweight:ℝ) (mBalance mCover mPair:ℕ)
      (Rhist:ℕ→SimpleGraph V) (Shist:ℕ→V→U→Prop) (bInner bCross:ℝ) (boundary cross:ℕ→ℝ)
      (hpairAt:OrdinaryDeepTracePairingParentAt ε ρ₀ α pmin ηProfile ζe cBoundary δe rateC ηf εf γpair κpair aPair lamPair bPair Bweight βe βh d mWheel buffer β C mPair)
      (hselectBalance:OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin pmin ηProfile ζe cBoundary δe rateC d buffer β C mBalance)
      (hselectCover:OrdinaryDeepTraceCoverAtLocalBalance mWheel 0 buffer ρ₀ pmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ configθ β ηbal d mCover)
      (hζlim:ζe≤ζlimit) (hζrate:ζe≤rate) (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit),
    let W:=markedVortexVertexType Q (i+1)
    let Z:=markedVortexHubType Q (i+1)
    letI : DecidableEq W:=Classical.decEq W
    let f:W↪V:=(markedVortexVertexEmbedding Q (i+1)).toEmbedding
    let g:=markedVortexHubEmbedding Q (i+1)
    let ρ₂:=markedVortexPermutation Q π hπ (i+1)
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer)
    let Zs:=fun k=>Q.extendedIndices (k+1);let Ws:=fun k=>Q.extendedIndices (k+buffer)
    let raw:=ordinaryRawRestrictPair f g σ
    let localCoins:=fun e:Sym2 W=>coins (Sym2.map f e)
    let Hlocal:=fun v u=>Hs (f v) (g u)
    let localP:=P.comap f;let localG:=G.comap f;let localF:=F.comap f
    let Jwin:=Finset.Icc (i+2-buffer) i;
    let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j;
    ∀weight:OrdinaryCycle localP (mWheel+1)→ℝ,
    i+1<Q.length→P.IsRegularOfDegree D→0<Fintype.card V→0< initialIndexDensity U D→0≤β→0≤pH→0≤εR→0≤εH→
    (θ+α)*Fintype.card V≤D→pR=initialIndexDensity U D*pH→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ→
    OrdinaryProtectedTrace S₀ H₀ X T Zs Ws cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    N₀≤Fintype.card W→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri localP localF ρ₂
      (markedVortexInnerHubs Q (i+1)) pR pH (2*(Fintype.card Z:ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→
    (∀C,c/(Fintype.card W:ℝ)^((mWheel+1)-2)≤weight C ∧ weight C≤B/(Fintype.card W:ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel localP localF ρ₂ (max (1/2) (cycleThreshold (mWheel+1))) α pstar βP ηP row ηH βH c B pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts localP localF ρ₂ d j δ h raw localCoins→
    ∀(βout extraGap η ξ ζout p εout γgeom κ:ℝ),
    OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale mWheel k buffer ρ₀ (βparent/2)
      (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gap) extraGap η βout ξ ζout p εout γgeom→
    0<ε→0<m→β≤1/4→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    (Fintype.card V:ℝ)/2≤D→0≤lam→lam≤1/4→lam≤(ρ₀/8)/2→
    lam≤γgeom/(1000*((mWheel:ℝ)+2))→ε≤ξ/2→ε≤ξ*(ρ₀/8)/2→2*ε^buffer≤lam→
    0≤κ→κ≤γgeom/(1000*((mWheel:ℝ)+2))→0≤ηbal→ηbal*ε≤γgeom/8→
    let Xr:=markedVortexInnerVertices Q (i+1);let Tr:=ordinaryVortexBufferedVertices Q (i+1) buffer
    let Zr:=markedVortexInnerHubs Q (i+1);let Wr:=ordinaryVortexBufferedHubs Q (i+1) buffer
    let ell:=max (18*κ*Fintype.card W+3*((Wr.card:ℝ)+Tr.card))
      (3*κ*Fintype.card W*((mWheel:ℝ)+1)+(Tr.card:ℝ)*((mWheel:ℝ)+1))
    let bin:=ηbal*Xr.card;let deep:ℝ:=Tr.card+2*Wr.card
    let fout:=deep+3*ell;let binner:=bin+3*ell+fout;
    mBalance≤m→mCover≤m→mPair≤m→pmin≤pR→pmin≤pH→1/2≤θ→(∀u,s u j=pH)→
    εR≤δe→εR≤εsample→εR≤lamPair→εH≤δe→εH≤εsample→εH≤lamPair→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    (∀t∈Jwin,0≤cost t ∧ cost t≤4*rateC*Fintype.card (markedVortexVertexType Q t⊕markedVortexHubType Q t)+C)→
    ordinaryHostResources (ordinaryHistoryRim S₀ Rhist Shist (i+1))
      (ordinaryHistorySpokes H₀ Rhist Shist (i+1))=A→
    (∀v∈Q.extendedVertices (i+2),|((spanningRestriction S₀ (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤bInner)→
    (∀v∉Q.extendedVertices (i+2),|((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
      2*((Q.extendedIndices (i+2)).filter (H₀ v)).card|≤bCross)→
    (∀t < i+1,Rhist t≤ordinaryHistoryRim S₀ Rhist Shist t ∧
      ∀v u,Shist t v u→ ordinaryHistorySpokes H₀ Rhist Shist t v u)→
    (∀t < i+1,HasOrdinaryWheelDecomposition (Rhist t) (Shist t) (mWheel+1))→
    (∀t < i+1,Disjoint (ordinaryPhysicalGraph (Rhist t) (Shist t))
      (ordinaryDeepBlocker (Q.extendedVertices (t+buffer)) (Q.extendedIndices (t+buffer))))→
    (∀t∈Finset.Icc (i+3-buffer) i,∀v∈Q.extendedVertices (i+2),
      |(((Rhist t)\spanningRestriction (Rhist t) (Q.extendedVertices (i+2))).degree v:ℝ)-
        2*(Finset.univ.filter (fun u=>Shist t v u∧¬(v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2)))).card|≤boundary t)→
    (∀t < i+1,∀v∉Q.extendedVertices (i+2),
      |(((Rhist t).neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
        2*((Q.extendedIndices (i+2)).filter (Shist t v)).card|≤cross t)→
    bInner+∑t∈Finset.Icc (i+3-buffer) i,boundary t≤ηbal*(markedVortexInnerVertices Q (i+1)).card→
    bCross+∑t∈Finset.range (i+1),cross t≤ηbal*(markedVortexInnerVertices Q (i+1)).card→
    OrdinaryAdaptiveHubWeightsLevelEvent mWheel localP localF Xr Zr ρ₂ d pR pH (θ+α-β/2)
      (εR*Xr.card) (εH*Zr.card) Ledit βe βh bPair Bweight ηf (fun u=>s (g u)) j raw→
    OrdinaryFixedVortexDeepCoverEvent mWheel 0 d a aLoad ρ configθ P D m β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→κ=aLoad→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    ∃Droot:OrdinaryRootCoverNonrootData localG localF Hlocal Xr Tr Zr Wr (mWheel+1) (10*ξroot*Xr.card) ell,
    Nonempty (OrdinaryRootCoverDeepReferenceData localP localG localF Hlocal Xr Tr Zr Wr (mWheel+1) k (by omega)
      (10*ξroot*Xr.card) ell bin bin deep Droot α (ρ₀/16) (βparent/2) βout
      (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) (δ/2) (εparent+gap) (εparent+gap+extraGap) η ξ ζout p εout fout binner binner) ∧
    Nonempty (MixedFreshPairingParentInsideRoots mWheel (2*(3*d)) γpair κpair bPair Bweight pmin aPair εf ηf
      (spanningRestriction localG Xr) localF
      (ordinaryPhysicalGraph (spanningRestriction localG Xr) (fun v u=>Hlocal v u∧v∈Xr∧u∈Zr))
      (ordinaryPhysicalGraph localF (fun _ _=>False)) (Function.Embedding.inl:W↪_)
      (ordinaryBoundaryHubSet Hlocal Zr Xr) (fun t=>(ordinaryBoundaryRimSet localG Xr t).image Sum.inl)
      (fun t=>(ordinaryBoundaryRowSet Hlocal Xr Zr t).image Sum.inr) (fun _=>pH)) :=by
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs βP ηP row εTri pR pH θ εR εH βe βh ηbal ηProfile s
    pmin href δcut ζcut εcut ζlimit εsample ξroot aLoad a ρ configθ ζe cBoundary δe rateC C αcut ηf εf γpair κpair aPair lamPair bPair Bweight mBalance mCover mPair Rhist Shist bInner bCross boundary cross
    hpairAt hselectBalance hselectCover hζlim hζrate hζcut hεcut hζlimit
    W Z f g ρ₂ F R J S H S₀ H₀ X T Zs Ws raw localCoins Hlocal localP localG localF Jwin Ledit
    weight hi hreg hn hρ hβ hpH hεR hεH hdegree hpEq hgood htrace hstate hN hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    βout extraGap η ξ ζout p εout γgeom κ hgeometry hε hm hβ1 hρlo hρhi hD hlam hlam1 hlamρ hlamγ hεξ hερ hεroot hκ hκcap hηbal hbalcap
    Xr Tr Zr Wr ell bin deep fout binner hmB hmC hmPair hpRlo hpHlo hθ hs hεRδ hεRsample hεRlam hεHδ hεHsample hεHlam hβe0 hβeδ hβh0 hβhδ
    hcost hhist hinitInner hinitCross hsubHist hdecHist hprotectHist hboundaryHist hcrossHist hbudgetInner hbudgetCross hevent hdeep hrim hpHpos hcut hhref hκeq hbal hdiv
  have hnear:=ordinary_vortex_history_window_local_balance P S₀ G H₀ Hs Rhist Shist D m β ε Q buffer i (mWheel+1) hbuffer A bInner ηbal boundary
    hhist hstate (by intro v hv;convert hinitInner v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hsubHist hdecHist hprotectHist hboundaryHist hbudgetInner
  have hcrossRaw:=ordinary_vortex_history_local_cross_balance P S₀ G H₀ Hs Rhist Shist D m β ε Q i A bCross cross
    hhist hstate (by intro v hv;convert hinitCross v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hsubHist hcrossHist
  have hcrossInput:∀v,v∉markedVortexInnerVertices Q (i+1)→
      |((localG.neighborFinset v∩markedVortexInnerVertices Q (i+1)).card:ℝ)-
        2*((markedVortexInnerHubs Q (i+1)).filter (Hlocal v)).card|≤ηbal*(markedVortexInnerVertices Q (i+1)).card:=by
    intro v hv
    exact (hcrossRaw v hv).trans hbudgetCross
  obtain ⟨hwin0,hprofile,hnearOut,hLrate,hcover⟩:=
    ordinary_deep_trace_common_cover_profile_local_balance mWheel d buffer ρ₀ pmin pmin href δcut ζcut εcut ζlimit εsample
      ε ξroot aLoad a ρ configθ β ηbal ηProfile α ζe cBoundary δe rateC C rate mBalance mCover
      hselectBalance hselectCover hζlim hζrate hζcut hεcut hζlimit
      V U Γ Color P JQ G JH Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s K cost deepCost i hi
      A pR pH θ εR εH βe βh αcut pstar hpRlo hRhi hpHlo hHhi hθ hdegree hpEq hs
      hεR hεRδ hεRsample hεH hεHδ hεHsample hβe0 hβeδ hβh0 hβhδ hJQ hJH havoid hgood htrace hstate hcost hnear
      hbal hdiv hdeep hrim hpHpos hcut hhref
  have hcover':OrdinaryNonrootWheelCoverResult mWheel 0 ξroot κ localG localF Hlocal Xr Tr Zr Wr:=by
    subst κ
    convert hcover using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hreference:=ordinary_vortex_deep_trace_buffered_cover_to_reference_local_balance mWheel buffer hmWheel hbuffer βH ηH B ρ₀ pstar βparent εparent ζ rate N₀
    hB hρ₀ hp hζ hN₀ hscale k hk α c h δ gap lam hroot V U Γ Color P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs βP ηP row εTri pR pH θ εR εH βe βh ηbal s weight hi hreg hn hρ hβ hpH hεR hεH hdegree hpEq hgood
    (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hnearOut (by intro v hv;convert hcrossInput v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) htrace hstate hN hwin0 hLrate hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    βout extraGap η ξ ζout p εout γgeom ξroot κ hgeometry hε hm hβ1 hρlo hρhi hD hlam hlam1 hlamρ hlamγ hεξ hερ hεroot hκ hκcap hηbal hbalcap hcover' hbal hdiv
  obtain ⟨Droot,hRef⟩:=hreference
  have hpair:=hpairAt V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi hmPair Q π hπ s j σ
    pR pH θ εR εH hpRlo hRhi hpHlo hHhi hθ hdegree hpEq hs hεR hεRδ hεRlam hεH hεHδ hεHlam
    K hJQ hJH havoid hgood cost deepCost i hi A G Hs htrace hstate hcost
    (by convert hevent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  exact ⟨Droot,hRef,by convert hpair using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _⟩
end Oberwolfach
