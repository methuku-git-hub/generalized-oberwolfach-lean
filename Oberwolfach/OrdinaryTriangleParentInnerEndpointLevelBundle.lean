module

public import Oberwolfach.OrdinaryTriangleInnerEndpointExtension

@[expose] public section
/-! A high-probability triangle parent, inner-hub and endpoint event gives
all level packages on the very same sample and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_parent_inner_endpoint_level_bundle
    (n q D mv k d:ℕ) (hd:2≤d) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri χhost δref href:ℝ) (hpstar:0<pstar)
    (selection:OrdinaryTriangleFullDomainSelection k d hd
      (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16) βP ηP ηH βH cParent Bparent εTri χhost (2*(3*d)) hpstar
      (Fin n) (Fin q) Bool Bool (markedVortexVertexType Q) (markedVortexHubType Q) P (permutationConflictGraph π (3*d))
      (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding) (fun i=>markedVortexHubEmbedding Q i) (markedVortexPermutation Q π hπ) (Q.length-1))
    (κ aLoad p pH pmin εR εH δcap b Bweight ηHub:ℝ)
    (density tR tH βe βh:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e))
    (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (loss χdeep χHub χone χtwo χcut:ℝ)
    (hinputs:∀i,i<Q.length→OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap (markedVortexVertexEmbedding Q i).toEmbedding)
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i).toEmbedding)
      (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i) (2*p) pH
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin q) D) β)
    (κcoins:FiniteLaw (Sym2 (Fin n)→Bool))
    (tpot bInner BInner ηInner capInner βeInner βhInner a χinner χendpoint:ℝ):
    let Good:=OrdinaryTriangleHubProductEvent n q D mv d β ε α κ aLoad p pH pmin εR εH δcap b Bweight ηHub
      P Q π hπ density tR tH βe βh s j R μ ν E loss χdeep χHub χone χtwo χcut
    let All:=OrdinaryTriangleParentProductEvent n q D mv k d (Q.length-1) hd β ε α pstar βP ηP ηH βH cParent Bparent δref href
      P Q π hπ selection.weight p pH s j R Good
    OrdinaryTriangleInnerEndpointExtension n q D mv d β ε P Q π hπ
      p pH βeInner βhInner bInner BInner ηInner capInner tpot χinner χendpoint density tR tH s j R μ ν κcoins→
    1-a≤((μ.sigma ν).prod κcoins).probability All→
    ∃endpointWeight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
    1-a-χinner-χendpoint≤((μ.sigma ν).prod κcoins).probability (fun z=> E z ∧ ∀i,i<Q.length→
      OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Q π hπ
        α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href
        (2*p) pH pmin κ aLoad εR εH bInner BInner ηInner capInner βeInner βhInner
        density tR tH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) z.2 i (selection.weight i) ∧
      EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (endpointWeight i) ∧
      EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d j (endpointWeight i) (2*p) pH tpot
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))) :=by
  intro Good All hselected hAll
  obtain ⟨endpointWeight,hweight,hattach⟩:=hselected
  have hevent:=hattach All a hAll
  have hevent':1-(a+χinner+χendpoint)≤((μ.sigma ν).prod κcoins).probability (fun z=>
      (All z ∧ OrdinaryUniformInnerHubEvent 2 P D mv d β ε Q π hπ (2*p) pH βeInner βhInner
        bInner BInner ηInner capInner density tR tH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d j (endpointWeight i) (2*p) pH tpot
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))):=by linarith only [hevent]
  have hb:=ordinary_triangle_sample_levels_endpoint_exists_probability n q D mv k d hd β ε P Q π hπ
    α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri χhost δref href hpstar selection
    κ aLoad p pH pmin εR εH δcap b Bweight ηHub density tR tH βe βh s j R μ ν E
    loss χdeep χHub χone χtwo χcut hinputs κcoins tpot bInner BInner ηInner capInner βeInner βhInner (a+χinner+χendpoint)
    ⟨endpointWeight,hweight,hevent'⟩
  obtain ⟨weight,hprob⟩:=hb
  refine ⟨weight,?_⟩
  linarith only [hprob]
end Oberwolfach
