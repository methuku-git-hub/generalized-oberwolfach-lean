module

public import Oberwolfach.OrdinaryVortexTraceDeepSampleBalance
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

theorem ordinary_vortex_trace_full_parent_general_deep_root_reference_all_balance
    (mWheel:ℕ) (hmWheel:3≤mWheel) (βH ηH B ρ₀ pstar βparent εparent ζ rate:ℝ) (N₀:ℕ)
    (hB:0≤B) (hρ₀:0<ρ₀) (hp:0<pstar) (hζ:0≤ζ) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B (ρ₀/16) pstar βparent εparent ζ rate N₀)
    (k:ℕ) (hk:4≤k) (α c h δ gap lam:ℝ)
    (hroot:OrdinaryUniformDeepRootReferenceAtScale (mWheel+1) (by omega) k α βparent c (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) δ εparent (ρ₀/16) gap lam):
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ)
      (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
      (K:Finset (Sym2 V⊕(V×U)))
      (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
      (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
      (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
      (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
      (βP ηP row εTri pR pH θ εR εH βe βh ηbal εRdeep εHdeep:ℝ) (s:U→Color→ℝ),
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
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Zs:=fun k=>Q.extendedIndices (k+1);let Ws:=fun k=>Q.extendedIndices (k+2)
    let raw:=ordinaryRawRestrictPair f g σ
    let localCoins:=fun e:Sym2 W=>coins (Sym2.map f e)
    let Hlocal:=fun v u=>Hs (f v) (g u)
    let localP:=P.comap f;let localG:=G.comap f;let localF:=F.comap f
    let Ledit:=2*((3*d:ℕ):ℝ)+cost i;
    ∀weight:OrdinaryCycle localP (mWheel+1)→ℝ,
    i+1<Q.length→P.IsRegularOfDegree D→0<Fintype.card V→0< initialIndexDensity U D→0≤β→0≤pH→0≤εR→0≤εH→
    (θ+α)*Fintype.card V≤D→pR=initialIndexDensity U D*pH→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ→
    0≤εRdeep→0≤εHdeep→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εRdeep εHdeep P F D m β ε Q π hπ pR pH s j σ→
    OrdinaryCleanupParentProfiles localP localG localF Hlocal ρ₂ d
      (markedVortexInnerVertices Q (i+1)) (markedVortexInnerHubs Q (i+1))
      pR pH (θ+α-β/2) (εR*(markedVortexInnerVertices Q (i+1)).card)
      (εH*(markedVortexInnerHubs Q (i+1)).card) Ledit βe βh (fun u=>s (g u)) j raw→
    (initialIndexDensity U D*pH)*β*(markedVortexInnerVertices Q (i+1)).card+
      εR*(markedVortexInnerVertices Q (i+1)).card+2*(εH*(markedVortexInnerHubs Q (i+1)).card)+3*Ledit≤
      ηbal*(markedVortexInnerVertices Q (i+1)).card→
    OrdinaryProtectedTrace S₀ H₀ X T Zs Ws cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    N₀≤Fintype.card W→0≤cost i→Ledit≤rate*Fintype.card W→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri localP localF ρ₂
      (markedVortexInnerHubs Q (i+1)) pR pH (2*(Fintype.card Z:ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→
    (∀C,c/(Fintype.card W:ℝ)^((mWheel+1)-2)≤weight C ∧ weight C≤B/(Fintype.card W:ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel localP localF ρ₂ (max (1/2) (cycleThreshold (mWheel+1))) α pstar βP ηP row ηH βH c B pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts localP localF ρ₂ d j δ h raw localCoins→
    ∀(Xr Tr:Finset W) (Zr Wr:Finset Z) (ηcover ell bin cin deep:ℝ)
      (Droot:OrdinaryRootCoverNonrootData localG localF Hlocal Xr Tr Zr Wr (mWheel+1) ηcover ell)
      (ω βout εstar η ξ ζout p εout fout binner cross:ℝ),
    (Tr.card:ℝ)+Wr.card≤lam*Fintype.card W→0≤ell→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    Xr=markedVortexInnerVertices Q (i+1)→Zr=markedVortexInnerHubs Q (i+1)→
    Tr=ordinaryVortexBufferedVertices Q (i+1) 2→Wr=ordinaryVortexBufferedHubs Q (i+1) 2→
    (initialIndexDensity U D*pH)*β*Tr.card+εRdeep*Tr.card+2*(εHdeep*Wr.card)+3*Ledit≤deep→
    ηbal*(markedVortexInnerVertices Q (i+1)).card≤bin→
    ηbal*(markedVortexInnerVertices Q (i+1)).card≤cin→
    deep+3*ell≤fout→bin+3*ell+(deep+3*ell)≤binner→
    cin+3*ell+(deep+3*ell)≤cross→
    let Aroot:=Finset.univ\Tr;let Croot:=Finset.univ\Wr
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈Xr)
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈Zr);
    OrdinaryNonrootGeometryStatic (mWheel+1) k ω (βparent/2) βout (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gap) εstar η ξ ζout p εout fout binner cross Xf Zf→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Aroot→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Croot→
    Nonempty (OrdinaryRootCoverDeepReferenceData localP localG localF Hlocal Xr Tr Zr Wr (mWheel+1) k (by omega)
      ηcover ell bin cin deep Droot α ω (βparent/2) βout (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) (δ/2) (εparent+gap) εstar η ξ ζout p εout fout binner cross) :=by
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs βP ηP row εTri pR pH θ εR εH βe βh ηbal εRdeep εHdeep s W Z f g ρ₂ F R J S H S₀ H₀ X T Zs Ws raw localCoins Hlocal localP localG localF Ledit
    weight hi hreg hn hρ hβ hpH hεR hεH hdegree hpEq hgood hεRdeep hεHdeep hgoodDeep hprofile hmargin
    htrace hstate hN hcost hLrate hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    Xr Tr Zr Wr ηcover ell bin cin deep Droot ω βout εstar η ξ ζout p εout fout binner cross
    hsize hell hbal hdiv hX hZ hT hW hdeepmargin hbin hcin hcross hfull hinnermargin Aroot Croot Xf Zf hstatic hscaleV hscaleU
  have hL:0≤Ledit:=by dsimp [Ledit];positivity
  have hboth:=ordinary_fixed_vortex_cleanup_both_balance P F D m β ε θ α pR pH εR εH Ledit βe βh ηbal
    Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hdegree hpEq hgood (i+1) hi localG Hlocal (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hmargin
  have hinner:∀v,|((spanningRestriction localG Xr).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hlocal v u∧v∈Xr∧u∈Zr)).card|≤bin:=by
    subst Xr;subst Zr
    intro v
    have hh:=(hboth.1 v).trans hbin
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hcrossbal:∀v∉Xr,|((localG.neighborFinset v∩Xr).card:ℝ)-2*(Zr.filter (Hlocal v)).card|≤cin:=by
    subst Xr;subst Zr
    intro v hv
    have hh:=(hboth.2 v hv).trans hcin
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hTX:Tr⊆Xr:=by
    rw [hT,hX]
    exact (ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.1
  have hWZ:Wr⊆Zr:=by
    rw [hW,hZ]
    exact (ordinary_vortex_buffered_nested Q (i+1) 2 (by omega)).2.2.2
  have hdeepbal:∀v∉Tr,|((localG.neighborFinset v∩Tr).card:ℝ)-2*(Wr.filter (Hlocal v)).card|≤deep:=by
    rw [hT,hW] at hdeepmargin ⊢
    intro v hv
    have hh:=ordinary_vortex_trace_deep_sample_balance P JQ JH D m β ε pR pH εRdeep εHdeep
      Q π hπ d s j σ K hn hreg hρ hβ hpH hεRdeep hεHdeep hpEq hJQ hJH havoid hgoodDeep
      cost deepCost i hi hcost A G Hs htrace hstate v
    exact hh.trans hdeepmargin
  exact ordinary_vortex_trace_full_parent_general_deep_root_reference_at_scale mWheel hmWheel βH ηH B ρ₀ pstar βparent εparent ζ rate N₀
    hB hρ₀ hp hζ hN₀ hscale k hk α c h δ gap lam hroot V U Γ Color P JQ JH D m β ε Q π hπ d s j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs βP ηP row εTri pR pH weight htrace hstate hN hcost hLrate hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    Xr Tr Zr Wr ηcover ell bin cin deep Droot ω βout εstar η ξ ζout p εout fout binner cross
    hsize hell hbal hdiv hTX hWZ
    (by convert hdeepbal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hinner using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hcrossbal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hcross hfull hinnermargin hstatic hscaleV hscaleU
end Oberwolfach
