module

public import Oberwolfach.OrdinaryWheelSelectedSampleLevelData

@[expose] public section
/-! Every level-data package comes from the same parent and deep event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_wheel_selected_sample_level_from_common
    (n qCount D mv m K k d:ℕ) (hm:3≤m) (hd:2≤d) (β ε:ℝ) (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin qCount) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri χhost δref href:ℝ) (hpstar:0<pstar)
    (selection:OrdinaryGeneralFullDomainSelection m k d hm hd
      (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16) βP ηP row ηH βH cParent Bparent εTri χhost (2*(3*d)) hpstar
      (Fin n) (Fin qCount) Bool Bool (markedVortexVertexType Q) (markedVortexHubType Q) P (permutationConflictGraph π (3*d))
      (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding) (fun i=>markedVortexHubEmbedding Q i) (markedVortexPermutation Q π hπ) (Q.length-1))
    (p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH:ℝ)
    (density tR tH:ℕ→ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e))
    (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (loss χinner χdeep χone χtwo χcut:ℝ)
    (z:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool))
    (hinputs:∀i,i<Q.length→OrdinaryDeepCoverLevelInputs m (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
      (P.comap (markedVortexVertexEmbedding Q i).toEmbedding)
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i).toEmbedding)
      (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i) (2*p) pH
      (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity (Fin qCount) D) β):
    let Good:=OrdinaryDeepRowsCutsEvent n qCount D mv m K d β ε P Q π hπ p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut
    let All:=OrdinaryVortexParentProductEvent n qCount D mv m k d (Q.length-1) hm hd β ε α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri χhost δref href hpstar
      P Q π hπ selection p pH s j R Good
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
    let Fconf:=permutationConflictGraph π (3*d)
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ;
    All z→E z ∧ ∀i,i<Q.length→
      OrdinaryWheelSelectedSampleLevelData n qCount D mv m K k d hm β ε P Q π hπ
        α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri δref href
        (2*p) pH pmin αcut c C ηHub a aLoad ρdeep θdeep cap eParent hParent εR εH
        density tR tH s j raw z.2 i (selection.weight i) :=by
  intro Good All raw Fconf f g ρi hz
  have h:=ordinary_deep_parent_uniform_sample_inputs n qCount D mv m K k d hm hd β ε P Q π hπ
    α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri χhost δref href hpstar selection
    p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH
    density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut z hinputs hz
  obtain ⟨hE,hInner,hDeep,hRow,hTwo,hlevels⟩:=h
  refine ⟨hE,?_⟩
  intro i hi
  obtain ⟨hRim,hEvent,hCuts,hIn,hWeight⟩:=hlevels i hi
  dsimp only [OrdinaryWheelSelectedSampleLevelData]
  exact ⟨hInner,hDeep,hRow,hTwo,hRim,hEvent,hCuts,hIn,hWeight⟩
end Oberwolfach
