module

public import Oberwolfach.OrdinaryVortexTraceTriangleParentAtScale
public import Oberwolfach.OrdinaryTriangleParentRootScaleChoice
public import Oberwolfach.OrdinaryTriangleEditedParentScaled
public import Oberwolfach.OrdinaryVortexTraceNondeeperDirectEdits
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

theorem ordinary_vortex_trace_triangle_root_reference_at_scale
    (βH ηH B ρ₀ pstar βparent εparent ζ rate:ℝ) (N₀:ℕ)
    (hB:0≤B) (hρ₀:0<ρ₀) (hp:0<pstar) (hζ:0≤ζ) (hN₀:1≤N₀)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B (ρ₀/4) pstar βparent εparent ζ rate N₀)
    (k:ℕ) (hk:4≤k) (α c h δ gap lam:ℝ)
    (hroot:OrdinaryUniformRootReferenceAtScale 3 (by omega) k α βparent c (B/((ρ₀/4)*pstar^(2*3-1)))
      (2*h-ζ) δ εparent (ρ₀/4) gap lam):
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
      (ρ₂:Equiv.Perm (ordinaryVortexNondeeperVertexType Q (i+1)))
      (hcomm₂:∀x,(ρ₂ x).val=π x.val)
      (βP ηP εTri pR pH:ℝ),
    let W:=ordinaryVortexNondeeperVertexType Q (i+1)
    let Z:=ordinaryVortexNondeeperHubType Q (i+1)
    letI : DecidableEq W:=Classical.decEq W
    let f:=ordinaryVortexNondeeperVertexEmbedding Q (i+1)
    let g:=ordinaryVortexNondeeperHubEmbedding Q (i+1)
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
    ∀weight:OrdinaryCycle localP 3→ℝ,
    OrdinaryProtectedTrace S₀ H₀ X T Zs Ws cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    N₀≤Fintype.card W→0≤cost i→Ledit≤rate*Fintype.card W→
    OrdinaryNondeeperTriangleLocalInputs P D m d β ε ρ₀ (max (1/2) (cycleThreshold 3)) α εTri pR pH Q π (i+1) ρ₂→
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→
    (∀C,c/(Fintype.card W:ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card W:ℝ)^(3-2))→
    ordinaryCombinedTriangleEvent d k localP localF ρ₂ (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH weight j raw→
    OrdinaryTriangleReferenceNormalizedCuts localP localF ρ₂ d j δ h raw localCoins→
    ∀(Xr Tr:Finset W) (Zr Wr:Finset Z) (ηcover ell bin cin:ℝ)
      (Droot:OrdinaryRootCoverNonrootData localG localF Hlocal Xr Tr Zr Wr 3 ηcover ell)
      (ω βout εstar η ξ ζout p εout fout binner cross:ℝ),
    (Tr.card:ℝ)+Wr.card≤lam*Fintype.card W→0≤ell→
    (∀v,localG.degree v=2*(Finset.univ.filter (Hlocal v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>Hlocal v u)).card)→
    (∀v,|((spanningRestriction localG Xr).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hlocal v u∧v∈Xr∧u∈Zr)).card|≤bin)→
    (∀v∉Xr,|((localG.neighborFinset v∩Xr).card:ℝ)-2*(Zr.filter (Hlocal v)).card|≤cin)→
    (Tr.card:ℝ)+2*Wr.card≤fout→bin+3*ell+Tr.card+2*Wr.card≤binner→
    cin+3*ell+Tr.card+2*Wr.card≤cross→
    let Aroot:=Finset.univ\Tr;let Croot:=Finset.univ\Wr
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈Xr)
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈Zr);
    OrdinaryNonrootGeometryStatic 3 k ω (βparent/2) βout (c*(1-δ)^(3-1)) (B/((ρ₀/4)*pstar^(2*3-1)))
      (εparent+gap) εstar η ξ ζout p εout fout binner cross Xf Zf→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Aroot→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Croot→
    Nonempty (OrdinaryRootCoverReferenceData localP localG localF Hlocal Xr Tr Zr Wr 3 k (by omega)
      ηcover ell bin cin Droot α ω (βparent/2) βout (c*(1-δ)^(3-1)) (B/((ρ₀/4)*pstar^(2*3-1)))
      (2*h-ζ) (δ/2) (εparent+gap) εstar η ξ ζout p εout fout binner cross) :=by
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m β ε Q π hπ d j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs ρ₂ hcomm₂ βP ηP εTri pR pH W Z f g F R J S H S₀ H₀ X T Zs Ws raw localCoins Hlocal localP localG localF Ledit
    weight htrace hstate hN hcost hLrate hinputs hRlo hRhi hHlo hHhi hc hweight event cuts
    Xr Tr Zr Wr ηcover ell bin cin Droot ω βout εstar η ξ ζout p εout fout binner cross
    hsize hell hbal hdiv hinner hcross hfull hinnermargin hcrossmargin Aroot Croot Xf Zf hstatic hscaleV hscaleU
  have hW:0<Fintype.card W:=by omega
  have hU:0<Fintype.card Z:=by
    have hWr:(0:ℝ)<Fintype.card W:=by exact_mod_cast hW
    have hh:0<(Fintype.card Z:ℝ):=(mul_pos (by positivity : (0:ℝ)<ρ₀/4) hWr).trans_le hinputs.hub_lower
    exact_mod_cast hh
  have hParent:=ordinary_vortex_trace_triangle_edited_parent_at_scale βH ηH B ρ₀ pstar βparent εparent ζ rate N₀
    hB hρ₀ hp hζ hN₀ hscale V U Γ Color P JQ JH D m β ε Q π hπ d k hk j σ coins K hJQ hJH havoid
    cost deepCost i A G Hs ρ₂ hcomm₂ α βP ηP εTri pR pH c h δ weight htrace hstate hN hcost hLrate hinputs
    hRlo hRhi hHlo hHhi hc hweight
    (by convert event using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert cuts using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
  obtain ⟨parent⟩:=hParent
  have hHost:=ordinary_vortex_trace_nondeeper_host_subgraph P JQ JH D m β ε Q π d j σ K cost deepCost i A G Hs htrace hstate
  exact hroot W Z localP localG localF Hlocal parent Xr Tr Zr Wr ηcover ell bin cin Droot
    ω βout εstar η ξ ζout p εout fout binner cross hW hU hinputs.hub_upper hinputs.hub_lower hsize hell hHost.2
    hbal hdiv hinner hcross hfull hinnermargin hcrossmargin hstatic hscaleV hscaleU
end Oberwolfach
