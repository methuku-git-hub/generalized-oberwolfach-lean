module

public import Oberwolfach.OrdinaryVortexInitialBufferedReferenceFromCover
public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.OrdinaryGeneralPhysicalParentDeepReference
public import Oberwolfach.OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale
public import Oberwolfach.OrdinaryGeneralDeepInputsFixedDomain
public import Oberwolfach.OrdinaryVortexSupportedLocalExactBalance

@[expose] public section
/-! At level zero, actual corrected-sample edits and both local balances
combine with the buffered cover into the general-wheel reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_vortex_initial_buffered_reference_and_pairing
    (mWheel buffer:ℕ) (hmWheel:3≤mWheel) (hbuffer:2≤buffer)
    (βH ηH B ρ₀ pstar βparent εparent ζ rate:ℝ) (N₀:ℕ)
    (hB:0≤B) (hρ₀:0<ρ₀) (hp:0<pstar) (hζ:0≤ζ) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B (ρ₀/16) pstar βparent εparent ζ rate N₀)
    (k:ℕ) (hk:4≤k) (α c h δ gap lam:ℝ)
    (hroot:OrdinaryUniformDeepRootReferenceAtScale (mWheel+1) (by omega) k α βparent c (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) δ εparent (ρ₀/16) gap lam)
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (s:U→Color→ℝ)
    (βP ηP row εTri pR pH ηbal Ledit:ℝ):
    let W:=markedVortexVertexType Q 0;let Z:=markedVortexHubType Q 0;
    letI : DecidableEq W:=Classical.decEq W;
    let f:W↪V:=(markedVortexVertexEmbedding Q 0).toEmbedding;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let F:=permutationConflictGraph π (3*d);
    let raw:=ordinaryRawRestrictPair f g σ;let localCoins:=fun e:Sym2 W=>coins (Sym2.map f e);
    let Hlocal:=fun v u=>Hs (f v) (g u);let localP:=P.comap f;let localG:=G.comap f;let localF:=F.comap f;
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 buffer;
    let J:=markedVortexInnerHubs Q 0;let Wdeep:=ordinaryVortexBufferedHubs Q 0 buffer;
    ∀weight:OrdinaryCycle localP (mWheel+1)→ℝ,
    P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
    ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<ε→0<m→
    N₀≤Fintype.card W→0≤Ledit→Ledit≤rate*Fintype.card W→G≤P→Disjoint G F→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri localP localF ρi
      J pR pH (2*(Fintype.card Z:ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→
    (∀C,c/(Fintype.card W:ℝ)^((mWheel+1)-2)≤weight C ∧ weight C≤B/(Fintype.card W:ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel localP localF ρi (max (1/2) (cycleThreshold (mWheel+1))) α pstar βP ηP row ηH βH c B pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts localP localF ρi d j δ h raw localCoins→
    (∀z:W⊕Z,((changed ((ordinaryPhysicalGraph (rawWheelGraph localP raw) (rawWheelSpokes ρi d raw j)).neighborFinset z)
      ((ordinaryPhysicalGraph localG Hlocal).neighborFinset z)).card:ℝ)≤Ledit)→
    0≤ηbal→
    (∀v:I,|((localG.induce (I:Set W)).degree v:ℝ)-2*(Finset.univ.filter (fun u:J=>Hlocal v.val u.val)).card|≤ηbal*I.card)→
    (∀v∉I,|((localG.neighborFinset v∩I).card:ℝ)-2*(J.filter (Hlocal v)).card|≤ηbal*I.card)→
    ∀(βout extraGap η ξ ζout p εout γgeom ξroot κ:ℝ),
    OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale mWheel k buffer ρ₀ (βparent/2)
      (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (εparent+gap) extraGap η βout ξ ζout p εout γgeom→
    0≤lam→lam≤1/4→lam≤(ρ₀/8)/2→lam≤γgeom/(1000*((mWheel:ℝ)+2))→
    ε≤ξ/2→ε≤ξ*(ρ₀/8)/2→2*ε^buffer≤lam→
    0≤κ→κ≤γgeom/(1000*((mWheel:ℝ)+2))→ηbal*ε≤γgeom/8→
    let ell:=max (18*κ*Fintype.card W+3*((Wdeep.card:ℝ)+T.card))
      (3*κ*Fintype.card W*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let bin:=ηbal*I.card;let deep:ℝ:=T.card+2*Wdeep.card;
    let fout:=deep+3*ell;let binner:=bin+3*ell+fout;
    ∀(γpair κpair bPair Bweight pmin aPair εf ηf:ℝ),
    let Pair:Prop:=Nonempty (MixedFreshPairingParentInsideRoots mWheel (2*(3*d)) γpair κpair bPair Bweight pmin aPair εf ηf
      (spanningRestriction localG I) localF
      (ordinaryPhysicalGraph (spanningRestriction localG I) (fun v u=>Hlocal v u∧v∈I∧u∈J))
      (ordinaryPhysicalGraph localF (fun _ _=>False)) (Function.Embedding.inl:W↪_)
      (ordinaryBoundaryHubSet Hlocal J I) (fun t=>(ordinaryBoundaryRimSet localG I t).image Sum.inl)
      (fun t=>(ordinaryBoundaryRowSet Hlocal I J t).image Sum.inr) (fun _=>pH));
    OrdinaryNonrootWheelCoverResult mWheel 0 ξroot κ localG localF Hlocal I T J Wdeep→ Pair→
    ∃Droot:OrdinaryRootCoverNonrootData localG localF Hlocal I T J Wdeep (mWheel+1) (10*ξroot*I.card) ell,
    Nonempty (OrdinaryRootCoverDeepReferenceData localP localG localF Hlocal I T J Wdeep (mWheel+1) k (by omega)
      (10*ξroot*I.card) ell bin bin deep Droot α (ρ₀/16) (βparent/2) βout
      (c*(1-δ)^((mWheel+1)-1)) (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) (δ/2) (εparent+gap) (εparent+gap+extraGap) η ξ ζout p εout fout binner binner) ∧
    Pair :=by
  intro W Z f g ρi F raw localCoins Hlocal localP localG localF I T J Wdeep weight
    hreg hn hD hρlo hρhi hβ hβ1 hε hm hN hL hLrate hGP hdis hbal hdiv hinputs
    hRlo hRhi hHlo hHhi hc hweight event cuts hphysical hηbal hnear hcross
    βout extraGap η ξ ζout p εout γgeom ξroot κ hgeometry hlam hlam1 hlamρ hlamγ hεξ hερ hεroot hκ hκcap hbalcap
    ell bin deep fout binner γpair κpair bPair Bweight pmin aPair εf ηf Pair hcover hpair
  have href:=ordinary_vortex_initial_buffered_reference_from_cover mWheel buffer hmWheel hbuffer βH ηH B ρ₀ pstar βparent εparent ζ rate N₀
    hB hρ₀ hp hζ hN₀ hscale k hk α c h δ gap lam hroot P G Hs D m β ε Q π hπ d j σ coins s
    βP ηP row εTri pR pH ηbal Ledit weight hreg hn hD hρlo hρhi hβ hβ1 hε hm hN hL hLrate hGP hdis hbal hdiv hinputs
    hRlo hRhi hHlo hHhi hc hweight event cuts hphysical hηbal hnear hcross
    βout extraGap η ξ ζout p εout γgeom ξroot κ hgeometry hlam hlam1 hlamρ hlamγ hεξ hερ hεroot hκ hκcap hbalcap hcover
  obtain ⟨Droot,hRef⟩:=href
  exact ⟨Droot,hRef,hpair⟩
end Oberwolfach
