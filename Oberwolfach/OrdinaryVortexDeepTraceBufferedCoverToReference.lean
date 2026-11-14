module

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

theorem ordinary_vortex_deep_trace_buffered_cover_to_reference
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
      (βP ηP row εTri pR pH θ εR εH βe βh ηbal:ℝ) (s:U→Color→ℝ),
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
    OrdinaryCleanupParentProfiles localP localG localF Hlocal ρ₂ d
      (markedVortexInnerVertices Q (i+1)) (markedVortexInnerHubs Q (i+1))
      pR pH (θ+α-β/2) (εR*(markedVortexInnerVertices Q (i+1)).card)
      (εH*(markedVortexInnerHubs Q (i+1)).card) Ledit βe βh (fun u=>s (g u)) j raw→
    (initialIndexDensity U D*pH)*β*(markedVortexInnerVertices Q (i+1)).card+
      εR*(markedVortexInnerVertices Q (i+1)).card+2*(εH*(markedVortexInnerHubs Q (i+1)).card)+3*Ledit≤
      ηbal*(markedVortexInnerVertices Q (i+1)).card→
    OrdinaryProtectedTrace S₀ H₀ X T Zs Ws cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    N₀≤Fintype.card W→0≤(∑j∈Jwin,cost j)→Ledit≤rate*Fintype.card W→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri localP localF ρ₂
      (markedVortexInnerHubs Q (i+1)) pR pH (2*(Fintype.card Z:ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→
    (∀C,c/(Fintype.card W:ℝ)^((mWheel+1)-2)≤weight C ∧ weight C≤B/(Fintype.card W:ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel localP localF ρ₂ (max (1/2) (cycleThreshold (mWheel+1))) α pstar βP ηP row ηH βH c B pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts localP localF ρ₂ d j δ h raw localCoins→
    ∀(βout extraGap η ξ ζout p εout γgeom ξroot κ:ℝ),
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
    OrdinaryNonrootWheelCoverResult mWheel 0 ξroot κ localG localF Hlocal Xr Tr Zr Wr→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    ∃Droot:OrdinaryRootCoverNonrootData localG localF Hlocal Xr Tr Zr Wr (mWheel+1) (10*ξroot*Xr.card) ell,
    Nonempty (OrdinaryRootCoverDeepReferenceData localP localG localF Hlocal Xr Tr Zr Wr (mWheel+1) k (by omega)
      (10*ξroot*Xr.card) ell bin bin deep Droot α (ρ₀/16) (βparent/2) βout
      (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) (δ/2) (εparent+gap) (εparent+gap+extraGap) η ξ ζout p εout fout binner binner) :=by
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs βP ηP row εTri pR pH θ εR εH βe βh ηbal s W Z f g ρ₂ F R J S H S₀ H₀ X T Zs Ws raw localCoins Hlocal localP localG localF Jwin Ledit
    weight hi hreg hn hρ hβ hpH hεR hεH hdegree hpEq hgood hprofile hmargin
    htrace hstate hN hcost hLrate hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    βout extraGap η ξ ζout p εout γgeom ξroot κ hgeometry hε hm hβ1 hρlo hρhi hD hlam hlam1 hlamρ hlamγ hεξ hερ hεroot hκ hκcap hηbal hbalcap
    Xr Tr Zr Wr ell bin deep fout binner hcover hbal hdiv
  letI : DecidableEq W := Classical.decEq W
  have hgeo:=hgeometry V U P D m β ε lam Q hreg hn hD hρlo hρhi hβ hβ1 hε hm
    hlam hlam1 hlamρ hlamγ hεξ hερ hεroot (i+1) hi localG localF Hlocal ξroot κ ηbal hκ hκcap hηbal hbalcap hcover
  obtain ⟨Droot0,hsize,hell,hbin,hf,hbinner,hstatic,hscaleV,hscaleU⟩:=hgeo
  have Droot:OrdinaryRootCoverNonrootData localG localF Hlocal Xr Tr Zr Wr (mWheel+1) (10*ξroot*Xr.card) ell:=by
    convert Droot0 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  refine ⟨Droot,?_⟩
  exact ordinary_vortex_trace_full_parent_general_buffered_deep_reference_coarse_balance mWheel hmWheel βH ηH B ρ₀ pstar βparent εparent ζ rate N₀
    hB hρ₀ hp hζ hN₀ hscale k hk α c h δ gap lam hroot V U Γ Color P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i buffer hbuffer A G Hs βP ηP row εTri pR pH θ εR εH βe βh ηbal s weight hi hreg hn hρ hβ hpH hεR hεH hdegree hpEq hgood hprofile hmargin
    htrace hstate hN hcost hLrate hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    Xr Tr Zr Wr (10*ξroot*Xr.card) ell bin bin deep Droot (ρ₀/16) βout (εparent+gap+extraGap) η ξ ζout p εout fout binner binner
    hsize hell hbal hdiv rfl rfl rfl rfl (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _)
    (by convert hstatic using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hscaleV using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | (ext x; simp [Tr,Wr]))
    (by convert hscaleU using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | (ext x; simp [Tr,Wr]))
end Oberwolfach
