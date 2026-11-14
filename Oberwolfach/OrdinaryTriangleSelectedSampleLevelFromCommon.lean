module

public import Oberwolfach.OrdinaryTriangleSelectedSampleLevelData

@[expose] public section
/-! The actual triangle parent event and an attached inner-scale event yield
one per-level package, including level zero, on the same physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_selected_sample_level_from_common
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
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    All z→
    ∀(bInner BInner ηInner capInner βeInner βhInner:ℝ),
    OrdinaryUniformInnerHubEvent 2 P D mv d β ε Q π hπ (2*p) pH βeInner βhInner
      bInner BInner ηInner capInner density tR tH s j raw→
    E z ∧ ∀i,i<Q.length→
      OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Q π hπ
        α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δref href
        (2*p) pH pmin κ aLoad εR εH bInner BInner ηInner capInner βeInner βhInner
        density tR tH s j raw z.2 i (selection.weight i) :=by
  intro Good All raw hz bInner BInner ηInner capInner βeInner βhInner hInner
  have h:=ordinary_triangle_parent_uniform_sample_inputs n q D mv k d hd β ε P Q π hπ
    α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri χhost δref href hpstar selection
    κ aLoad p pH pmin εR εH δcap b Bweight ηHub density tR tH βe βh s j R μ ν E
    loss χdeep χHub χone χtwo χcut z hinputs hz
  obtain ⟨hE,_hHub,hFine,hRow,hTwo,hlevels⟩:=h
  refine ⟨hE,?_⟩
  intro i hi
  obtain ⟨hRim,hParent,hCuts,hInputs,hWeight⟩:=hlevels i hi
  dsimp only [OrdinaryTriangleSelectedSampleLevelData]
  exact ⟨hInner,hFine,hRow,hTwo,hRim,hParent,hCuts,hInputs,hWeight⟩
end Oberwolfach
