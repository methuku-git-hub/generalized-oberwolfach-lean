module

public import Oberwolfach.OrdinaryTriangleSelectedSampleLevelWithEndpoint
public import Oberwolfach.OrdinaryDeepIngredientsFromCommon

@[expose] public section
/-! Build the inner certificate's deep-parent ingredients from a selected
level of the common sample and the cleanup profile of the actual local host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_deep_ingredients_from_sample_level
    (n q D mv k d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href:ℝ)
    (pR pH pmin κ aLoad εR εH bInner BInner ηInner capInner βeInner βhInner:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
    (raw:RawWheelOutcome (Fin n) (Fin q) Bool Bool) (coins:Sym2 (Fin n)→Bool) (i:ℕ)
    (weightTri:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i)) 3→ℝ)
    (hi:i<Q.length)
    (hlevel:OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Q π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href
      pR pH pmin κ aLoad εR εH bInner BInner ηInner capInner βeInner βhInner
      density tR tH s j raw coins i weightTri)
    (G:SimpleGraph (markedVortexVertexType Q i))
    (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
    (endpointWeight:markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ)
    (γold κold bold Bold εold ηend κe dens L Ledit βe βh δbal εrows tpot K escale:ℝ):
    let Ploc:=P.comap (markedVortexVertexEmbedding Q i);
    let Floc:=(permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i);
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let perm:=markedVortexPermutation Q π hπ i;
    let sloc:=fun u=>s (markedVortexHubEmbedding Q i u);
    let rawloc:=ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) raw;
    OrdinaryDeepParentMargins Ploc Floc I B γold κold bold Bold εold ηend κe pmin pR pH dens
      (εR*I.card) (εH*B.card) L Ledit δbal εrows tpot K escale→
    G≤Ploc\Floc→
    OrdinaryCleanupParentProfiles Ploc G Floc H perm d I B pR pH dens (εR*I.card) (εH*B.card)
      Ledit βe βh sloc j rawloc→
    EndpointPhysicalParentWeights Ploc I Iᶜ endpointWeight→
    EndpointPhysicalPotentialEvent Ploc Floc I B Iᶜ perm d j endpointWeight pR pH tpot rawloc→
    OrdinaryDeepParentIngredients Ploc G Floc H I B perm d j sloc endpointWeight γold κold bold Bold εold ηend κe pmin
      pR pH dens (εR*I.card) (εH*B.card) L Ledit βe βh δbal εrows tpot K rawloc :=by
  intro Ploc Floc I B perm sloc rawloc margins hG profile parent event
  have hrow:=hlevel.2.2.1 i hi
  exact ordinary_deep_ingredients_from_common Ploc G Floc H I B perm d j sloc endpointWeight
    γold κold bold Bold εold ηend κe pmin pR pH dens (εR*I.card) (εH*B.card) L Ledit βe βh
    δbal εrows tpot K escale rawloc margins hG profile (by convert hrow.1 using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) parent event
end Oberwolfach
