module

public import Oberwolfach.OrdinaryInitialActualHostPhysicalBundle
public import Oberwolfach.OrdinaryVortexLocalFineSharpReferenceGeneralLoad

@[expose] public section
/-! The initial sharp reference is built in the actual edited remainder,
using the same physical sample, hub event, fine cover and reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_actual_host_sharp_from_physical
    {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [LinearOrder U]
    (mWheel loadK : ℕ) (hmWheel : 3≤mWheel)
    (βH ηH Bhost ρ₀ pstar βparent εparent ζ rate : ℝ) (N₀ : ℕ)
    (hB : 0≤Bhost) (hρ₀ : 0<ρ₀) (hp : 0<pstar) (hζ : 0≤ζ) (hN₀ : 1≤N₀)
    (hscale : OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH Bhost (ρ₀/16) pstar βparent εparent ζ rate N₀)
    (k : ℕ) (hk : 4≤k) (α c h δ gap lam : ℝ)
    (hroot : OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (by omega) α βparent c
      (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*h-ζ) δ εparent (ρ₀/16) gap lam)
    (P G : SimpleGraph V) (Hs : V→U→Prop) (D m : ℕ) (β ε : ℝ)
    (Q : Vortex U P D β ε m) (π : Equiv.Perm V)
    (hπ : ∀ i x, π x∈Q.extendedVertices i ↔ x∈Q.extendedVertices i)
    (d : ℕ) (j : Color) (σ : RawWheelOutcome V U Γ Color) (coins : Sym2 V→Bool) (s : U→Color→ℝ)
    (βP ηP row εTri pR pH ηbal Ledit θhost εR εH βe βh bHub Bweight ηHub capHub : ℝ)
    (weight : OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q 0)) (mWheel+1)→ℝ)
    (hreg : P.IsRegularOfDegree D) (hn : 0<Fintype.card V) (hD : (Fintype.card V:ℝ)/2≤D)
    (hρlo : ρ₀≤ initialIndexDensity U D) (hρhi : initialIndexDensity U D≤1)
    (hβ : 0≤β) (hβ1 : β≤1/4) (hε : 0<ε) (hm : 0<m)
    (hN : N₀≤Fintype.card (markedVortexVertexType Q 0))
    (hL : 0≤Ledit) (hLrate : Ledit≤rate*Fintype.card (markedVortexVertexType Q 0))
    (hG : G≤P\permutationConflictGraph π (3*d))
    (hbal : ∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv : ∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)
    (hpR0 : 0≤pR) (hpR1 : pR≤1) (hpH0 : 0≤pH) (hpH1 : pH≤1)
    (hεR : 0≤εR) (hεH : 0≤εH) (hθ : 1/2≤θhost) (hβα : β≤2*α)
    (hdegree : (θhost+α)*Fintype.card V≤D) (hpEq : pR=initialIndexDensity U D*pH) (hs : ∀u,s u j=pH)
    (hgood : OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (hgood2 : OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (hfamily : OrdinaryUniformInnerHubEvent mWheel P D m d β ε Q π hπ pR pH βe βh bHub Bweight ηHub capHub
      (fun _=>θhost+α-β/2) (fun i=>εR*(markedVortexInnerVertices Q i).card)
      (fun i=>εH*(markedVortexInnerHubs Q i).card) s j σ) :
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2
    let J:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 2
    let ρi:=markedVortexPermutation Q π hπ 0;let Ploc:=P.comap f
    let Floc:=(permutationConflictGraph π (3*d)).comap f;let Gloc:=G.comap f
    let Hloc:=fun v u=>Hs (f v) (g u);let raw:=ordinaryRawRestrictPair f g σ;
    Ledit≤capHub*I.card→
    (∀z:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph Ploc raw) (rawWheelSpokes ρi d raw j)).neighborFinset z)
        ((ordinaryPhysicalGraph Gloc Hloc).neighborFinset z)).card:ℝ)≤Ledit)→
    βe*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)+εR*I.card+3*Ledit≤
      pR^2*pH*(2*(θhost+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)+εH*J.card+2*Ledit≤pH^2*J.card→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*Ledit≤ηbal*I.card→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri Ploc Floc ρi
      J pR pH (2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pstar≤pH→0≤c→
    (∀C,c/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((mWheel+1)-2)≤weight C ∧
      weight C≤Bhost/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel Ploc Floc ρi (max (1/2) (cycleThreshold (mWheel+1))) α pstar
      βP ηP row ηH βH c Bhost pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts Ploc Floc ρi d j δ h raw
      (fun e=>coins (Sym2.map f.toEmbedding e))→
    ∀(ξroot κ bin cin deep ω βout εstar η ξ ζout p εout : ℝ),
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q 0)→
    0≤ξroot→0≤κ→0≤bin→0≤deep→0≤ηbal→ηbal*I.card≤bin→ηbal*I.card≤cin→
    (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*Ledit≤deep→
    OrdinaryFineWheelCoverResult mWheel loadK ξroot κ Gloc Floc Hloc I T J W→
    letI : DecidableEq (markedVortexVertexType Q 0):=Classical.decEq _
    letI : DecidableEq (markedVortexHubType Q 0):=Classical.decEq _
    let ell:=max (18*κ*Fintype.card (markedVortexVertexType Q 0)+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card (markedVortexVertexType Q 0)*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let cover:=10*ξroot*I.card;let loss:=12*κ*Fintype.card (markedVortexVertexType Q 0);
    let fout:=deep+2*cover;let binner:=bin+deep+4*cover;let cross:=cin+deep+loss;
    let Aroot:=Finset.univ\T;let Croot:=Finset.univ\W;
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈J);
    OrdinaryNonrootGeometryStatic (mWheel+1) k ω (βparent/2) βout (c*(1-δ)^mWheel)
      (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (εparent+gap) εstar η ξ ζout p εout fout binner cross Xf Zf→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Aroot→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Croot→
    (∃Droot:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T J W (mWheel+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData Ploc Gloc Floc Hloc I T J W (mWheel+1) k (by omega)
        cover ell bin cin deep loss Droot α ω (βparent/2) βout (c*(1-δ)^mWheel)
        (Bhost/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*h-ζ) (δ/2) (εparent+gap)
        εstar η ξ ζout p εout fout binner cross)) ∧
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I J pR pH (θhost+α-β/2)
      (εR*I.card) (εH*J.card) Ledit βe βh (fun u=>s (g u)) j raw ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bHub Bweight ηHub Gloc Floc Hloc I J) :=by
  intro f g I T J W ρi Ploc Floc Gloc Hloc raw hcap hphysical hext hhub hmargin hinputs
    hpRstar hpHstar hc hweight hevent hcuts ξroot κ bin cin deep ω βout εstar η ξ ζout p εout
    hsize hξroot hκ hbin hdeep0 hηbal hbinMargin hcinMargin hdeepMargin hcover
    ell cover loss fout binner cross Aroot Croot Xf Zf hstatic hscaleV hscaleU
  have hρpos:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hρlo
  have hBundle:=ordinary_initial_actual_host_physical_bundle mWheel P G Hs D m β ε θhost α pR pH εR εH Ledit βe βh ηbal bHub Bweight ηHub capHub
    Q π hπ d s j σ hn hreg hρpos hβ hpR0 hpR1 hpH0 hεR hεH hL hθ hβα hdegree hpEq hs hG hbal hdiv hgood hgood2 hfamily
    hcap hphysical hext hhub hmargin
  obtain ⟨hprofile,hlocal,hlocalbal,hlocaldiv,hnear,hcross,hdeep,hweights⟩:=hBundle
  have hRef:=ordinary_vortex_local_fine_sharp_reference_general_load mWheel loadK 2 hmWheel (by omega)
    βH ηH Bhost ρ₀ pstar βparent εparent ζ rate N₀ hB hρ₀ hp hζ hN₀ hscale
    k hk α c h δ gap lam hroot P G Hs D m β ε Q 0 Q.length_pos π hπ d j σ coins s
    βP ηP row εTri pR pH ηbal Ledit weight hreg hn hD hρlo hρhi hβ hβ1 hε hm hN hL hLrate
    (by convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hlocalbal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hlocaldiv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hinputs using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hpRstar hpR1 hpHstar hpH1 hc hweight
    (by convert hevent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hcuts using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hphysical z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hηbal (by intro v;convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hcross v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    ξroot κ bin cin deep ω βout εstar η ξ ζout p εout hsize hξroot hκ hbin hdeep0 hbinMargin hcinMargin
    (by convert hcover using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert (hdeep v hv).trans hdeepMargin using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hstatic using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | (ext x;simp))
    (by convert hscaleV using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | ring | (ext x;simp [Aroot,Croot]))
    (by convert hscaleU using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | ring | (ext x;simp [Aroot,Croot]))
  exact ⟨(by convert hRef using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _),
    (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _),
    (by convert hweights using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)⟩
end Oberwolfach
