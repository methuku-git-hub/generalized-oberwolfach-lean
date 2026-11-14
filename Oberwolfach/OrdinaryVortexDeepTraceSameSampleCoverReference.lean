module

public import Oberwolfach.OrdinaryVortexDeepTraceThreeStepCoverToReference
public import Oberwolfach.OrdinaryDeepTraceCommonCoverBalance
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

theorem ordinary_vortex_deep_trace_same_sample_cover_reference
    (mWheel:ℕ) (hmWheel:3≤mWheel) (βH ηH B ρ₀ pstar βparent εparent ζ rate:ℝ) (N₀:ℕ)
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
      (βP ηP row εTri pR pH θ εR εH βe βh ηbal:ℝ) (s:U→Color→ℝ)
      (pmin hmin href δcut ζcut εcut ζlimit εsample ξroot aLoad a ρ configθ ζe δe rateC C αcut:ℝ)
      (mBalance mCover:ℕ)
      (hselectBalance:OrdinaryDeepTraceBalanceAt ε ρ₀ α pmin hmin ηbal ζe δe rateC d 3 β C mBalance)
      (hselectCover:OrdinaryDeepTraceCoverAt mWheel 0 3 ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρ configθ β ηbal d mCover)
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
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+3)
    let Zs:=fun k=>Q.extendedIndices (k+1);let Ws:=fun k=>Q.extendedIndices (k+3)
    let raw:=ordinaryRawRestrictPair f g σ
    let localCoins:=fun e:Sym2 W=>coins (Sym2.map f e)
    let Hlocal:=fun v u=>Hs (f v) (g u)
    let localP:=P.comap f;let localG:=G.comap f;let localF:=F.comap f
    let Jwin:=Finset.Icc (i+2-3) i;
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
    OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale mWheel k 3 ρ₀ (βparent/2)
      (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gap) extraGap η βout ξ ζout p εout γgeom→
    0<ε→0<m→β≤1/4→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    (Fintype.card V:ℝ)/2≤D→0≤lam→lam≤1/4→lam≤(ρ₀/8)/2→
    lam≤γgeom/(1000*((mWheel:ℝ)+2))→ε≤ξ/2→ε≤ξ*(ρ₀/8)/2→2*ε^3≤lam→
    0≤κ→κ≤γgeom/(1000*((mWheel:ℝ)+2))→0≤ηbal→ηbal*ε≤γgeom/8→
    let Xr:=markedVortexInnerVertices Q (i+1);let Tr:=ordinaryVortexBufferedVertices Q (i+1) 3
    let Zr:=markedVortexInnerHubs Q (i+1);let Wr:=ordinaryVortexBufferedHubs Q (i+1) 3
    let ell:=max (18*κ*Fintype.card W+3*((Wr.card:ℝ)+Tr.card))
      (3*κ*Fintype.card W*((mWheel:ℝ)+1)+(Tr.card:ℝ)*((mWheel:ℝ)+1))
    let bin:=ηbal*Xr.card;let deep:ℝ:=Tr.card+2*Wr.card
    let fout:=deep+3*ell;let binner:=bin+3*ell+fout;
    mBalance≤m→mCover≤m→pmin≤pR→hmin≤pH→1/2≤θ→(∀u,s u j=pH)→
    εR≤δe→εR≤εsample→εH≤δe→εH≤εsample→0≤βe→βe≤δe→0≤βh→βh≤δe→
    (∀t∈Jwin,0≤cost t ∧ cost t≤4*rateC*Fintype.card (markedVortexVertexType Q t⊕markedVortexHubType Q t)+C)→
    OrdinaryFixedVortexDeepCoverEvent mWheel 0 d a aLoad ρ configθ P D m β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→κ=aLoad→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    ∃Droot:OrdinaryRootCoverNonrootData localG localF Hlocal Xr Tr Zr Wr (mWheel+1) (10*ξroot*Xr.card) ell,
    Nonempty (OrdinaryRootCoverDeepReferenceData localP localG localF Hlocal Xr Tr Zr Wr (mWheel+1) k (by omega)
      (10*ξroot*Xr.card) ell bin bin deep Droot α (ρ₀/16) (βparent/2) βout
      (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) (δ/2) (εparent+gap) (εparent+gap+extraGap) η ξ ζout p εout fout binner binner) :=by
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs βP ηP row εTri pR pH θ εR εH βe βh ηbal s
    pmin hmin href δcut ζcut εcut ζlimit εsample ξroot aLoad a ρ configθ ζe δe rateC C αcut mBalance mCover
    hselectBalance hselectCover hζlim hζrate hζcut hεcut hζlimit
    W Z f g ρ₂ F R J S H S₀ H₀ X T Zs Ws raw localCoins Hlocal localP localG localF Jwin Ledit
    weight hi hreg hn hρ hβ hpH hεR hεH hdegree hpEq hgood htrace hstate hN hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    βout extraGap η ξ ζout p εout γgeom κ hgeometry hε hm hβ1 hρlo hρhi hD hlam hlam1 hlamρ hlamγ hεξ hερ hεroot hκ hκcap hηbal hbalcap
    Xr Tr Zr Wr ell bin deep fout binner hmB hmC hpRlo hpHlo hθ hs hεRδ hεRsample hεHδ hεHsample hβe0 hβeδ hβh0 hβhδ
    hcost hdeep hrim hpHpos hcut hhref hκeq hbal hdiv
  obtain ⟨hwin0,hprofile,hmargin,hLrate,hcover⟩:=
    ordinary_deep_trace_common_cover_balance mWheel d 3 ρ₀ pmin hmin href δcut ζcut εcut ζlimit εsample
      ε ξroot aLoad a ρ configθ β ηbal α ζe δe rateC C rate mBalance mCover
      hselectBalance hselectCover hζlim hζrate hζcut hεcut hζlimit
      V U Γ Color P JQ G JH Hs D m hreg hn hD hρlo hρhi hmB hmC Q π hπ σ coins j s K cost deepCost i hi
      A pR pH θ εR εH βe βh αcut pstar hpRlo hRhi hpHlo hHhi hθ hdegree hpEq hs
      hεR hεRδ hεRsample hεH hεHδ hεHsample hβe0 hβeδ hβh0 hβhδ hJQ hJH havoid hgood htrace hstate hcost
      hbal hdiv hdeep hrim hpHpos hcut hhref
  have hcover':OrdinaryNonrootWheelCoverResult mWheel 0 ξroot κ localG localF Hlocal Xr Tr Zr Wr:=by
    subst κ
    convert hcover using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact ordinary_vortex_deep_trace_three_step_cover_to_reference mWheel hmWheel βH ηH B ρ₀ pstar βparent εparent ζ rate N₀
    hB hρ₀ hp hζ hN₀ hscale k hk α c h δ gap lam hroot V U Γ Color P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs βP ηP row εTri pR pH θ εR εH βe βh ηbal s weight hi hreg hn hρ hβ hpH hεR hεH hdegree hpEq hgood
    (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hmargin htrace hstate hN hwin0 hLrate hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    βout extraGap η ξ ζout p εout γgeom ξroot κ hgeometry hε hm hβ1 hρlo hρhi hD hlam hlam1 hlamρ hlamγ hεξ hερ hεroot hκ hκcap hηbal hbalcap hcover' hbal hdiv
end Oberwolfach
