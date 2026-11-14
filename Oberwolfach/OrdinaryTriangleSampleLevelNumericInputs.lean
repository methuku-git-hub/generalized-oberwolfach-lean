module

public import Oberwolfach.OrdinaryTriangleDeepInputsFromSelectedNumeric
public import Oberwolfach.OrdinaryTriangleLevelInnerParentConditionsFromSample
public import Oberwolfach.OrdinaryVortexTriangleInnerEditBudget

@[expose] public section
/-! The same selected row and endpoint tests supply the deep-parent inputs,
scaled triangle conditions and all local conflict/index bounds together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_sample_level_numeric_inputs
    (β ε ρ₀ α pmin Kdom ηend εf γold κold δ εrows tpot lamInner bold Bold:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hε:0<ε) (hε1:ε<1/4)
    (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)
    (deepNum:OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηend εf (2*Kdom)
      γold κold δ εrows tpot lamInner bold Bold)
    (innerNum:OrdinaryTriangleInnerNumericParameters pmin (ρ₀/8) εf ηend εrows δ εrows tpot lamInner)
    (hβbalance:β≤2*δ*(ρ₀/8)*pmin) (d M:ℕ) (hM:32≤M) (hMε:4/ε≤(M:ℝ))
    (hMb:((2*(3*d):ℕ):ℝ)≤lamInner*M):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(n q D mv k:ℕ) (P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→0<n→
      (n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity (Fin q) D→initialIndexDensity (Fin q) D≤1→v₀≤mv→
      (M:ℝ)≤ε*mv/2→
    ∀(Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (θhost pR pH εR εH Ledit rateParent βe βh:ℝ),cycleThreshold 3≤θhost→
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
      (weight:markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ),
    let Ploc:=P.comap (markedVortexVertexEmbedding Q i);
    let Floc:=(permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i);
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let perm:=markedVortexPermutation Q π hπ i;let sloc:=fun u=>s (markedVortexHubEmbedding Q i u);
    let rawloc:=ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw;
    let L:ℝ:=2*((3*d:ℕ):ℝ);
    Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)→
    G≤Ploc\Floc→
    OrdinaryCleanupParentProfiles Ploc G Floc H perm d I B pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) Ledit βe βh sloc j rawloc→
    EndpointPhysicalParentWeights Ploc I Iᶜ weight→
    EndpointPhysicalPotentialEvent Ploc Floc I B Iᶜ perm d j weight pR pH tpot rawloc→
    ∀(p εsup τ ν η ell ζfresh:ℝ),0<p→p≤1→0≤τ→0<ζfresh→
    let γ:=min (pmin^4/32) (endpointCountCoefficient pmin (ρ₀/8)/4);
    let θmatch:=ζfresh*(γ/4)*ε;
    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+ell≤θmatch*p/4→ν+η≤θmatch*p/4→p≤4*θmatch→
    20*Real.sqrt (2*p)≤θmatch/2→
    2≤θmatch*p*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)/4→
    OrdinaryDeepParentIngredients Ploc G Floc H I B perm d j sloc weight γold κold bold Bold εf ηend (ρ₀/8) pmin
      pR pH (θhost+α-β/2) (εR*I.card) (εH*B.card) L Ledit βe βh δ εrows tpot (2*Kdom) rawloc ∧
    OrdinaryTriangleRootFirstScaledConditions G H I B p εsup τ ν η ell ((γ/4)*ε) ζfresh ∧
    M≤I.card ∧ Fintype.card {v:markedVortexVertexType Q i // v∉I}≤I.card^2 ∧
    Fintype.card {u:markedVortexHubType Q i // u∉B}≤I.card^2 ∧
    (∀v,Floc.degree v≤2*(3*d)) ∧ L≤εf*I.card :=by
  obtain ⟨v₀,hv₀,hdeep⟩:=ordinary_triangle_deep_inputs_from_selected_numeric β ε ρ₀ α pmin Kdom ηend εf γold κold δ εrows tpot lamInner bold Bold
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin hKdom deepNum hβbalance d
  refine ⟨v₀,hv₀,?_⟩
  intro n q D mv k P hreg hn hD hρlo hρhi hv hterminal Q π hπ θhost pR pH εR εH Ledit rateParent βe βh
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hE hrate i hi
    pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH s j raw coins weightTri hlevel G H weight Ploc Floc I B perm sloc rawloc L hEdit hhost profile parent event
    p εsup τ ν η ell ζfresh hp hp1 hτ hζfresh γ θmatch hεsup hsupport hclass hblock hpκ hsqrt horder
  have hm:0<mv:=by omega
  have hEditInner:=ordinary_vortex_triangle_inner_edit_budget Q hreg (by simpa using hn) (by simpa using hD)
    hρ₀ hρlo hρhi hβ hβ1 hε hm i hi lamInner rateParent Ledit innerNum.lambda_pos.le hrate hEdit
  have hd:=hdeep n q D mv k P hreg hn hD hρlo hρhi hv Q π hπ θhost pR pH εR εH Ledit βe βh
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hE i hi
    pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH s j raw coins weightTri hlevel G H weight hEditInner hhost profile parent event
  have hgeneral:=ordinary_triangle_selected_sample_level_general_of_fin n q D mv k d β ε P Q π hπ
    α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href pR pH pmin κ aLoad εR εH
    bInner BInner ηInner capInner βeInner βhInner density tR tH s j raw coins i weightTri hlevel
  have hnumer:=ordinary_triangle_level_inner_parent_conditions_from_sample P D mv β ε ρ₀ Q hreg (by simpa using hn)
    (by simpa using hD) hρ₀ hρlo hρhi hβ hβ1 hε hm i hi π hπ d α pmin εf ηend εrows δ εrows tpot lamInner
    hα hβα hpmin innerNum hβbalance M hM hMε hMb hterminal θhost pR pH εR εH Ledit tpot rateParent βe βh
    hθ (by simpa using hdegree) hpR hpR1 hpH hpH1 hpEq hεRsmall hεHsmall hE hrate le_rfl s j raw
    k pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH coins weightTri hgeneral G H p εsup τ ν η ell ζfresh hp hp1 hτ hζfresh
    (by convert profile using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hhost hEdit hεsup hsupport hclass hblock hpκ hsqrt horder
  obtain ⟨_,hscaled,_,hsize,hJv,hJu,hF,_,_,_,_,hLf,_,_,_⟩:=hnumer
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · convert hd using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hscaled using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hsize using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hJv using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hJu using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · intro v; convert hF v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hLf using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
