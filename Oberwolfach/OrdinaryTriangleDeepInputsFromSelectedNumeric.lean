module

public import Oberwolfach.OrdinaryFixedVortexDeepParentMargins
public import Oberwolfach.OrdinaryTriangleDeepIngredientsFromSampleLevel

@[expose] public section
/-! The preselected numerical hierarchy, the common sample's row and
endpoint tests, and the actual cleanup profile give the deep-parent inputs
at every admissible vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_deep_inputs_from_selected_numeric
    (β ε ρ₀ α pmin Kdom ηend εf γold κold δ εrows tpot lam bold Bold:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8) (hε:0<ε) (hε1:ε<1/4)
    (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom)
    (num:OrdinaryDeepNumericParameters pmin (ρ₀/8) (1/Kdom) ηend εf (2*Kdom)
      γold κold δ εrows tpot lam bold Bold)
    (hβbalance:β≤2*δ*(ρ₀/8)*pmin) (d:ℕ):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(n q D mv k:ℕ) (P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→0<n→
      (n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity (Fin q) D→initialIndexDensity (Fin q) D≤1→v₀≤mv→
    ∀(Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (θhost pR pH εR εH Ledit βe βh:ℝ),cycleThreshold 3≤θhost→
      (θhost+α)*(n:ℝ)≤D→pmin≤pR→pR≤1→pmin≤pH→pH≤1→
      pR=initialIndexDensity (Fin q) D*pH→0≤εR→2*εR≤εrows→0≤εH→2*εH≤εrows→0≤Ledit→
    ∀(i:ℕ),i<Q.length→
    ∀(pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner:ℝ)
      (density tR tH:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
      (raw:RawWheelOutcome (Fin n) (Fin q) Bool Bool) (coins:Sym2 (Fin n)→Bool)
      (weightTri:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) 3→ℝ),
    OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Q π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href pR pH pmin κ aLoad εR εH
      bInner BInner ηInner capInner βeInner βhInner density tR tH s j raw coins i weightTri→
    ∀(G:SimpleGraph (markedVortexVertexType Q i)) (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
      (endpointWeight:markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ),
    let Ploc:=P.comap (markedVortexVertexEmbedding Q i);
    let Floc:=(permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i);
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let perm:=markedVortexPermutation Q π hπ i;
    let sloc:=fun u=>s (markedVortexHubEmbedding Q i u);
    let rawloc:=ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw;
    Ledit≤lam*I.card→G≤Ploc\Floc→
    OrdinaryCleanupParentProfiles Ploc G Floc H perm d I B pR pH (θhost+α-β/2)
      (εR*I.card) (εH*B.card) Ledit βe βh sloc j rawloc→
    EndpointPhysicalParentWeights Ploc I Iᶜ endpointWeight→
    EndpointPhysicalPotentialEvent Ploc Floc I B Iᶜ perm d j endpointWeight pR pH tpot rawloc→
    OrdinaryDeepParentIngredients Ploc G Floc H I B perm d j sloc endpointWeight γold κold bold Bold εf ηend (ρ₀/8) pmin
      pR pH (θhost+α-β/2) (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)) Ledit βe βh δ εrows tpot (2*Kdom) rawloc :=by
  obtain ⟨v₀,hv₀,hmargin⟩:=ordinary_fixed_vortex_deep_parent_margins β ε ρ₀ α pmin Kdom ηend εf γold κold δ εrows tpot lam bold Bold
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin hKdom num hβbalance d
  refine ⟨v₀,hv₀,?_⟩
  intro n q D mv k P hreg hn hD hρlo hρhi hv Q π hπ θhost pR pH εR εH Ledit βe βh
    hθ hdegree hpR hpR1 hpH hpH1 hpEq hεR hεRsmall hεH hεHsmall hE i hi
    pstar βP ηP ηH βH cParent Bparent εTri δref href κ aLoad bInner BInner ηInner capInner βeInner βhInner
    density tR tH s j raw coins weightTri hlevel G H endpointWeight Ploc Floc I B perm sloc rawloc hEdit hhost profile parent event
  have hmarg:=hmargin (Fin n) (Fin q) P D mv hreg (by simpa using hn) (by simpa using hD) hρlo hρhi hv
    Q π hπ θhost pR pH εR εH Ledit hθ (by simpa using hdegree) hpR hpR1 hpH hpH1 hpEq
    hεR hεRsmall hεH hεHsmall hE i hi hEdit
  exact ordinary_triangle_deep_ingredients_from_sample_level n q D mv k d β ε P Q π hπ
    α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href pR pH pmin κ aLoad εR εH
    bInner BInner ηInner capInner βeInner βhInner density tR tH s j raw coins i weightTri hi hlevel G H endpointWeight
    γold κold bold Bold εf ηend (ρ₀/8) (θhost+α-β/2) (2*((3*d:ℕ):ℝ)) Ledit βe βh δ εrows tpot (2*Kdom)
    (pR*β*I.card) (by convert hmarg using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) hhost profile parent event
end Oberwolfach
