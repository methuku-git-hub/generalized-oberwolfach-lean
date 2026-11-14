module

public import Oberwolfach.OrdinaryTriangleSampleLevelNumericInputs
public import Oberwolfach.OrdinaryTriangleRootFreeUniformSharpCertificate
public import Oberwolfach.OrdinaryTriangleInnerTerminalThreshold
public import Oberwolfach.OrdinaryVortexBufferedDomains

@[expose] public section
/-! One preselected threshold and the selected numerical hierarchy give the
root-free wheel certificate at any level of the same sampled vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_numeric_sample_level_certificate
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
      (ξroot lam b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c rate:ℝ),
    let Ploc:=P.comap (markedVortexVertexEmbedding Q i);
    let Floc:=(permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i);
    let I:=markedVortexInnerVertices Q i;let T:=ordinaryVortexBufferedVertices Q i 2;
    let B:=markedVortexInnerHubs Q i;let W:=ordinaryVortexBufferedHubs Q i 2;
    let perm:=markedVortexPermutation Q π hπ i;let sloc:=fun u=>s (markedVortexHubEmbedding Q i u);
    let rawloc:=ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw;
    let cover:=10*ξroot*I.card;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q i)+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q i)*3+(T.card:ℝ)*3);
    Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)→
    G≤Ploc\Floc→
    OrdinaryCleanupParentProfiles Ploc G Floc H perm d I B pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) Ledit βeParent βhParent sloc j rawloc→
    EndpointPhysicalParentWeights Ploc I Iᶜ weight→
    EndpointPhysicalPotentialEvent Ploc Floc I B Iᶜ perm d j weight pR pH tpot rawloc→
    OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub G Floc H I B→
    (∀v,G.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i)→lam≤1/4→
    0≤ξroot→0≤aLoad→0≤lam→0≤ellCap→0≤cap→
    max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap→10*ξroot≤cap→
    OrdinaryRootCoverSharpReferenceExists Ploc G Floc H I T B W 3 k (by omega)
      cover ell b₁ c₁ deep crossLoss α ω βparent βout b Bweight h δpack εparent εstar (cLinear*τ) ξ ζ p eps f binner c→
    hpack≤h-ξ-ζ→
    (T.card:ℝ)≤(βeGeo/2)*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)→
    (W.card:ℝ)≤(βhGeo/2)*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)→
    βeGeo+3*max cap ellCap≤βeParent→βhGeo+2*ellCap≤βhParent→ν+cap+4*p≤rate→
    OrdinaryWheelLikelySeparateCostsCertificate G Floc H I T B W 3
      (rate*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)) cover :=by
  obtain ⟨Mbase,hbase64,hcert⟩:=ordinary_triangle_root_free_uniform_sharp_certificate α k hk ω βout b Bweight hpack δpack εstar cLinear (ρ₀/8) pmin
    bHub BHub εf ηhub ηend ζfresh εrows p βeGeo βhGeo ν cap εsup δsample τ hfixed (2*(3*d)) (2*((3*d:ℕ):ℝ)) (by positivity) eps heps
  obtain ⟨M,hMbase,hM32,hMε,hMb⟩:=ordinary_triangle_inner_terminal_threshold ε lamInner hε innerNum.lambda_pos (2*(3*d)) (max Mbase Norder)
  obtain ⟨v₀,hv₀,hnumeric⟩:=ordinary_triangle_sample_level_numeric_inputs β ε ρ₀ α pmin Kdom ηend εf γold κold δ εrows tpot lamInner bold Bold
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin hKdom deepNum innerNum hβbalance d M hM32 hMε hMb
  refine ⟨M,v₀,by omega,hv₀,?_⟩
  intro n q D mv P hreg hn hD hρlo hρhi hv hterminal Q π hπ θhost pR pH εR εH Ledit rateParent βeParent βhParent
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hE hrate i hi
    pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH s j raw coins weightTri hsample G H weight ξroot lam b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c rate
    Ploc Floc I T B W perm sloc rawloc cover ell hEdit hhost profile parent event hub hbal hdiv hroot hlam4
    hξroot ha hlam hellCap hcap hell hξcap hrefsharp hpackcut hT hW hbudgetE hbudgetH hfinish
  have hI:M≤I.card:=by
    have ht:=Q.extended_card_at_least_threshold hterminal (by omega:i+1≤Q.length)
    have heq:=(marked_vortex_inner_cardinalities Q i).1
    exact heq.symm ▸ ht
  have hIV:I.card≤Fintype.card (markedVortexVertexType Q i):=Finset.card_le_univ I
  have hVN:Fintype.card (markedVortexVertexType Q i)≤Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):=
    Fintype.card_le_of_injective (Sum.inl:markedVortexVertexType Q i→markedVortexVertexType Q i⊕markedVortexHubType Q i) Sum.inl_injective
  have horder':=horder (Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)) (by omega)
  have hnum:=hnumeric n q D mv k P hreg hn hD hρlo hρhi hv hterminal Q π hπ θhost pR pH εR εH Ledit rateParent βeParent βhParent
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hE hrate i hi
    pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH s j raw coins weightTri hsample G H weight hEdit hhost profile parent event
    p εsup τ ν cap (p*ellCap+δsample) ζfresh hp hp1 hτ hζfresh hεsup hsupport hclass hblock hpκ hsqrt horder'
  obtain ⟨hd,hscaled,hsize,hJv,hJu,hF,hLf⟩:=hnum
  have hdis:Disjoint G Floc:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hhost hvw.1).2 hvw.2
  have hnested:=ordinary_vortex_buffered_nested Q i 2 (by omega)
  have hV:0<Fintype.card (markedVortexVertexType Q i):=by omega
  have hh:=hcert (markedVortexVertexType Q i) (markedVortexHubType Q i) Bool Bool
    Ploc G Floc H perm d I T B W ξroot aLoad lam ellCap cap b₁ c₁ deep crossLoss
    βparent h εparent ξ ζ f binner c pR pH (θhost+α-β/2) (εR*I.card) (εH*B.card) tpot Ledit βeParent βhParent δ (2*Kdom) γold κold bold Bold εf
    sloc j weight rawloc (by omega) hV hroot hlam4 hξroot ha hlam hellCap hcap hell hξcap hrefsharp hpackcut
    hnested.2.2.1 hnested.2.2.2 hT hW hdis
    (by convert hJv using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hJu using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hd using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hub using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro v; convert hF v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hLf
    (by intro v; convert hbal v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro u; convert hdiv u using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    ((min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4)/4)*ε) rate
    (by convert hscaled using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hbudgetE hbudgetH hfinish
  convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
