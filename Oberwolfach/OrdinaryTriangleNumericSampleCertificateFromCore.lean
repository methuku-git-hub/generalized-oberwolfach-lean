module

public import Oberwolfach.OrdinaryTriangleLocalSharpInputs

@[expose] public section
/-! The common sample and a local sharp-input package give the selected
root-free certificate at each level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_numeric_sample_level_certificate_from_core
    (β ε ρ₀ α pmin Kdom ηend εf γold κold δ εrows tpot lamInner bold Bold:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hε:0<ε) (hε1:ε<1/4)
    (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)
    (deepNum:OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηend εf (2*Kdom)
      γold κold δ εrows tpot lamInner bold Bold)
    (innerNum:OrdinaryTriangleInnerNumericParameters pmin (ρ₀/8) εf ηend εrows δ εrows tpot lamInner)
    (hβbalance:β≤2*δ*(ρ₀/8)*pmin) (d k:ℕ) (hk:4≤k)
    (ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub ζfresh:ℝ)
    (p βeGeo βhGeo ν cap εsup δsample τ eps:ℝ)
    (hfixed:OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b Bweight hpack δpack εstar cLinear (ρ₀/8) pmin
      bHub BHub εf ηhub ηend ζfresh εrows p βeGeo βhGeo ν cap εsup δsample τ)
    (heps:0<eps) (hp:0<p) (hp1:p≤1) (hτ:0≤τ) (hζfresh:0<ζfresh)
    (hεsup:εsup≤p^2/4) (hsupport:τ+ν≤p^2/4)
    (ellCap:ℝ)
    (hclass:τ+ν+(p*ellCap+δsample)≤ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε*p/4)
    (hblock:ν+cap≤ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε*p/4)
    (hpκ:p≤4*(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε))
    (hsqrt:20*Real.sqrt (2*p)≤(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε)/2)
    (Norder:ℕ) (horder:∀n:ℕ,Norder≤n→
      2≤(ζfresh*(min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε)*p*n/4):
    ∃M v₀:ℕ,64≤M ∧ 1≤v₀ ∧
    ∀(n q D mv:ℕ) (P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→0<n→
      (n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity (Fin q) D→initialIndexDensity (Fin q) D≤1→v₀≤mv→
      (M:ℝ)≤ε*mv/2→
    ∀(Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (θhost pR pH εR εH Ledit rateParent βeParent βhParent:ℝ),cycleThreshold 3≤θhost→
      (θhost+α)*(n:ℝ)≤D→pmin≤pR→pR≤1→pmin≤pH→pH≤1→
      pR=initialIndexDensity (Fin q) D*pH→0≤εR→2*εR≤εrows→0≤εH→2*εH≤εrows→0≤Ledit→
      rateParent≤lamInner*ε/4→
    ∀(i:ℕ),i<Q.length→
    ∀(pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner:ℝ)
      (density tR tH:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
      (raw:RawWheelOutcome (Fin n) (Fin q) Bool Bool) (coins:Sym2 (Fin n)→Bool)
      (weightTri:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) 3→ℝ),
    OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Q π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href pR pH pmin κ aLoad εR εH
      bInner BInner ηInner capInner βeInner βhInner density tR tH s j raw coins i weightTri→
    ∀(G:SimpleGraph (markedVortexVertexType Q i)) (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
      (weight:markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
      (ξroot rate:ℝ),
    let Ploc:=P.comap (markedVortexVertexEmbedding Q i);
    let Floc:=(permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i);
    let I:=markedVortexInnerVertices Q i;let T:=ordinaryVortexBufferedVertices Q i 2;
    let B:=markedVortexInnerHubs Q i;let W:=ordinaryVortexBufferedHubs Q i 2;
    let perm:=markedVortexPermutation Q π hπ i;let sloc:=fun u=>s (markedVortexHubEmbedding Q i u);
    let rawloc:=ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw;
    EndpointPhysicalParentWeights Ploc I Iᶜ weight→
    EndpointPhysicalPotentialEvent Ploc Floc I B Iᶜ perm d j weight pR pH tpot rawloc→
    OrdinaryTriangleLocalSharpInputs Ploc G Floc H I T B W perm d k (by omega) sloc j rawloc
      α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub
      pR pH (θhost+α-β/2) (εR*I.card) (εH*B.card) Ledit rateParent βeParent βhParent
      ξroot aLoad ellCap cap βeGeo βhGeo→
    βeGeo+3*max cap ellCap≤βeParent→βhGeo+2*ellCap≤βhParent→ν+cap+4*p≤rate→
    OrdinaryWheelLikelySeparateCostsCertificate G Floc H I T B W 3
      (rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)) (10*ξroot*I.card) :=by
  obtain ⟨M,v₀,hM,hv₀,hcert⟩:=ordinary_triangle_numeric_sample_level_certificate β ε ρ₀ α pmin Kdom ηend εf γold κold δ εrows tpot lamInner bold Bold
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin hKdom deepNum innerNum hβbalance d k hk
    ω βout b Bweight hpack δpack εstar cLinear bHub BHub ηhub ζfresh p βeGeo βhGeo ν cap εsup δsample τ eps
    hfixed heps hp hp1 hτ hζfresh hεsup hsupport ellCap hclass hblock hpκ hsqrt Norder horder
  refine ⟨M,v₀,hM,hv₀,?_⟩
  intro n q D mv P hreg hn hD hρlo hρhi hv hterminal Q π hπ θhost pR pH εR εH Ledit rateParent βeParent βhParent
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hE hrate i hi
    pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH s j raw coins weightTri hsample G H weight ξroot rate Ploc Floc I T B W perm sloc rawloc parent event hcore hbudgetE hbudgetH hfinish
  dsimp only [OrdinaryTriangleLocalSharpInputs] at hcore
  obtain ⟨lam,b₁,c₁,deep,crossLoss,βparent,h,εparent,ξ,ζ,f,binner,c,
    hEdit,hhost,profile,hub,hbal,hdiv,hroot,hlam4,hξroot,ha,hlam,hellCap,hcap,hell,hξcap,hrefsharp,hpackcut,hT,hW⟩:=hcore
  obtain ⟨hub⟩:=hub
  have hh:=hcert n q D mv P hreg hn hD hρlo hρhi hv hterminal Q π hπ θhost pR pH εR εH Ledit rateParent βeParent βhParent
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hE hrate i hi
    pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH s j raw coins weightTri hsample G H weight ξroot lam b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c rate
    hEdit hhost
    (by convert profile using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    parent event
    (by convert hub using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro v; convert hbal v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro u; convert hdiv u using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hroot hlam4 hξroot ha hlam hellCap hcap hell hξcap
    (by convert hrefsharp using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hpackcut hT hW
    hbudgetE hbudgetH hfinish
  convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
