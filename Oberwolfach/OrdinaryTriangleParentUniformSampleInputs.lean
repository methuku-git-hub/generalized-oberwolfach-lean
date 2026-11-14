module

public import Oberwolfach.OrdinaryTriangleParentEventLevelTests
public import Oberwolfach.OrdinaryTriangleHubProductEvent
public import Oberwolfach.OrdinaryTriangleFullDomainSelection
public import Oberwolfach.OrdinaryOriginalParentLevelInputs

@[expose] public section
/-! Extract all initial and later triangle tests from one selected parent,
matching and correction outcome. The level inputs are supplied separately by
the original host selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_parent_uniform_sample_inputs
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
    (z:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool))
    (hinputs:∀i,i<Q.length→OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap (markedVortexVertexEmbedding Q i).toEmbedding)
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i).toEmbedding)
      (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i) (2*p) pH
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin q) D) β):
    let Good:=OrdinaryTriangleHubProductEvent n q D mv d β ε α κ aLoad p pH pmin εR εH δcap b Bweight ηHub
      P Q π hπ density tR tH βe βh s j R μ ν E loss χdeep χHub χone χtwo χcut
    let All:=OrdinaryTriangleParentProductEvent n q D mv k d (Q.length-1) hd β ε α pstar βP ηP ηH βH cParent Bparent δref href
      P Q π hπ selection.weight p pH s j R Good
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
    let Fconf:=permutationConflictGraph π (3*d)
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ;
    All z→E z ∧
      OrdinaryVortexAdaptiveHubAllLevelsEvent 2 d D mv β ε p pH δcap b Bweight ηHub density tR tH βe βh P Q π hπ s j raw ∧
      OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D mv β ε Q π hπ j raw ∧
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      ∀i,i<Q.length→
        OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1)) (sampledOrientation (rawWheelGraph P raw) z.2) (min (α/4) (1/4:ℝ)) pmin ∧
        ordinaryCombinedTriangleEvent d k (P.comap (f i)) (Fconf.comap (f i)) (ρi i)
          (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH cParent Bparent (2*p) pH (selection.weight i)
          j (ordinaryRawRestrictPair (f i) (g i) raw) ∧
        OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (Fconf.comap (f i)) (ρi i) d j δref href
          (ordinaryRawRestrictPair (f i) (g i) raw) (fun e=>z.2 (Sym2.map (f i) e)) ∧
        OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
          (P.comap (f i)) (Fconf.comap (f i)) (ρi i) (markedVortexInnerHubs Q i) (2*p) pH
          (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin q) D) β ∧
        (∀C,cParent/(Fintype.card (markedVortexVertexType Q i):ℝ)^(3-2)≤selection.weight i C ∧
          selection.weight i C≤Bparent/(Fintype.card (markedVortexVertexType Q i):ℝ)^(3-2)) :=by
  intro Good All raw Fconf f g ρi hz
  obtain ⟨⟨⟨⟨hE,hFine⟩,hRow⟩,hTwo⟩,hRim⟩:=hz.1.1
  have hHub:=hz.1.2
  refine ⟨hE,hHub,hFine,?_,?_,?_⟩
  · convert hRow using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hTwo using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  intro i hi
  have hle:i≤Q.length-1:=by omega
  refine ⟨by simpa using hRim i hi,hz.2.1 i hle,hz.2.2 i hle,?_,?_⟩
  · convert hinputs i hi using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · exact (selection.bounds i hle).1
end Oberwolfach
