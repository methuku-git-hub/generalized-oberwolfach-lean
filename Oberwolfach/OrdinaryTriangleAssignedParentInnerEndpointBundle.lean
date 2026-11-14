module

public import Oberwolfach.OrdinaryTriangleAssignedInnerEndpointSelectedHostGeneric
public import Oberwolfach.OrdinaryTriangleParentInnerEndpointLevelBundle

@[expose] public section
/-! Attach the selected inner-hub and endpoint events to a triangle parent
prior on the actual assigned expanded law and the same direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_assigned_parent_inner_endpoint_bundle
    (n q D mv k d K:ℕ) (hd:2≤d) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri χhost δref href:ℝ) (hpstar:0<pstar)
    (selection:OrdinaryTriangleFullDomainSelection k d hd
      (max (1/2) (cycleThreshold 3)) α pstar (ρ₀/16) βP ηP ηH βH cParent Bparent εTri χhost (2*(3*d)) hpstar
      (Fin n) (Fin q) Bool Bool (markedVortexVertexType Q) (markedVortexHubType Q) P (permutationConflictGraph π (3*d))
      (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding) (fun i=>markedVortexHubEmbedding Q i) (markedVortexPermutation Q π hπ) (Q.length-1))
    (cInner CInner ξInner bInner BInner ηInner Kdom eParent hParent capInner χinner χendpoint tpot:ℝ) (v₀:ℕ)
    (hselect:OrdinaryTriangleInnerEndpointHostSelector α cInner CInner ε ρ₀ pstar ξInner bInner BInner ηInner Kdom
      eParent hParent capInner χinner χendpoint tpot d hd β v₀)
    (hρ:0<ρ₀) (hreg:P.IsRegularOfDegree D) (hn:0<n) (hhalf:(n:ℝ)/2≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1) (hv:v₀≤mv)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (θhost:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold 3≤θhost) (hdegree:(θhost+α)*(n:ℝ)≤D)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θfreq cAux smin:ℝ) (hsmin:0<smin) (hstar:pstar≤ρ₀*smin/2)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θfreq cAux ρ₀ smin d)
    (κ aLoad εR εH δcap b Bweight ηHub:ℝ) (density tR tH βe βh:ℕ→ℝ)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (loss χdeep χHub χone χtwo χcut a:ℝ)
    (hinputs:∀i,i<Q.length→OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap (markedVortexVertexEmbedding Q i).toEmbedding)
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i).toEmbedding)
      (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i)
      (2*(initialIndexDensity (Fin q) D*rsv/2)) rsv
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin q) D) β)
    (κcoins:FiniteLaw (Sym2 (Fin n)→Bool)):
    let p:=initialIndexDensity (Fin q) D*rsv/2;
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θfreq cAux;
    let μ:=ordinaryAssignedExpandedLaw F hF i₀ rsv θfreq cAux ρ₀ smin d hd sampling;
    let Good:=OrdinaryTriangleHubProductEvent n q D mv d β ε α κ aLoad p rsv pstar εR εH δcap b Bweight ηHub
      P Q π hπ density tR tH βe βh s false R μ ν E loss χdeep χHub χone χtwo χcut;
    let All:=OrdinaryTriangleParentProductEvent n q D mv k d (Q.length-1) hd β ε α pstar βP ηP ηH βH cParent Bparent δref href
      P Q π hπ selection.weight p rsv s false R Good;
    1-a≤((μ.sigma ν).prod κcoins).probability All→
    ∃endpointWeight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
    1-a-χinner-χendpoint≤((μ.sigma ν).prod κcoins).probability (fun z=> E z ∧ ∀i,i<Q.length→
      OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Q π hπ
        α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href
        (2*p) rsv pstar κ aLoad εR εH cInner (4*CInner/pstar^7) ηInner capInner (eParent*ε) (hParent*ε)
        density tR tH s false (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) z.2 i (selection.weight i) ∧
      EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (endpointWeight i) ∧
      EndpointPhysicalPotentialEvent (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d false (endpointWeight i) (2*p) rsv tpot
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))) :=by
  intro p s μ Good All hAll
  have hext:=ordinary_triangle_assigned_inner_endpoint_selected_host_generic α cInner CInner ε ρ₀ pstar ξInner bInner BInner ηInner Kdom
    eParent hParent capInner χinner χendpoint tpot d hd β v₀ hselect hρ n q D mv K P hreg hn hhalf hρlo hρhi hv Q π hπ hnoshort
    θhost hθ hthreshold hdegree F hF i₀ rsv θfreq cAux smin hsmin hstar sampling density tR tH ν κcoins
  exact ordinary_triangle_parent_inner_endpoint_level_bundle n q D mv k d hd β ε P Q π hπ
    α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri χhost δref href hpstar selection
    κ aLoad p rsv pstar εR εH δcap b Bweight ηHub density tR tH βe βh s false R μ ν E
    loss χdeep χHub χone χtwo χcut hinputs κcoins tpot cInner (4*CInner/pstar^7) ηInner capInner
    (eParent*ε) (hParent*ε) a χinner χendpoint hext hAll
end Oberwolfach
