module

public import Oberwolfach.OrdinaryDeepParentInitialSelectedInputs
public import Oberwolfach.OrdinaryDeepParentLevelSelectedInputs

@[expose] public section
/-! Initial and every later selected parent input are read from the same
sample and the same selected weight family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_all_level_selected_inputs
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
    All z→((E z ∧
      OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ (2*p) pH (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j raw ∧
      OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρdeep θdeep P D mv β ε Q π hπ j raw ∧
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P raw) z.2) αcut pmin ∧
      ordinaryCombinedHostEvent m d k hm (P.comap (f 0)) (Fconf.comap (f 0)) (ρi 0)
        (max (1/2) (cycleThreshold (m+1))) α pstar βP ηP row ηH βH cParent Bparent (2*p) pH (selection.weight 0)
        (fun u=>s (g 0 u)) j (ordinaryRawRestrictPair (f 0) (g 0) raw) ∧
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f 0)) (Fconf.comap (f 0)) (ρi 0) d j δref href
        (ordinaryRawRestrictPair (f 0) (g 0) raw) (fun e=>z.2 (Sym2.map (f 0) e))) ∧
      OrdinaryDeepCoverLevelInputs m (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
        (P.comap (f 0)) (Fconf.comap (f 0)) (ρi 0) (markedVortexInnerHubs Q 0) (2*p) pH
        (2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity (Fin qCount) D) β ∧
      (∀C,cParent/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((m+1)-2)≤selection.weight 0 C ∧
        selection.weight 0 C≤Bparent/(Fintype.card (markedVortexVertexType Q 0):ℝ)^((m+1)-2))) ∧ (E z ∧
      OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ (2*p) pH (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j raw ∧
      OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρdeep θdeep P D mv β ε Q π hπ j raw ∧
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      ∀i,i+1<Q.length→
        OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2))
          (sampledOrientation (rawWheelGraph P raw) z.2) αcut pmin ∧
        ordinaryCombinedHostEvent m d k hm (P.comap (f (i+1))) (Fconf.comap (f (i+1))) (ρi (i+1))
          (max (1/2) (cycleThreshold (m+1))) α pstar βP ηP row ηH βH cParent Bparent (2*p) pH (selection.weight (i+1))
          (fun u=>s (g (i+1) u)) j (ordinaryRawRestrictPair (f (i+1)) (g (i+1)) raw) ∧
        OrdinaryTriangleReferenceNormalizedCuts (P.comap (f (i+1))) (Fconf.comap (f (i+1))) (ρi (i+1)) d j δref href
          (ordinaryRawRestrictPair (f (i+1)) (g (i+1)) raw) (fun e=>z.2 (Sym2.map (f (i+1)) e)) ∧
        OrdinaryDeepCoverLevelInputs m (2*(3*d)) d α pstar (ρ₀/16) 1 εTri
          (P.comap (f (i+1))) (Fconf.comap (f (i+1))) (ρi (i+1)) (markedVortexInnerHubs Q (i+1)) (2*p) pH
          (2*(Fintype.card (markedVortexHubType Q (i+1)):ℝ)/initialIndexDensity (Fin qCount) D) β ∧
        (∀C,cParent/(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)^((m+1)-2)≤selection.weight (i+1) C ∧
          selection.weight (i+1) C≤Bparent/(Fintype.card (markedVortexVertexType Q (i+1)):ℝ)^((m+1)-2))) :=by
  intro Good All raw Fconf f g ρi hz
  constructor
  · exact ordinary_deep_parent_initial_selected_inputs n qCount D mv m K k d hm hd β ε P Q π hπ
      α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri χhost δref href hpstar selection
      p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH
      density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut z (hinputs 0 Q.length_pos) hz
  · exact ordinary_deep_parent_level_selected_inputs n qCount D mv m K k d hm hd β ε P Q π hπ
      α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri χhost δref href hpstar selection
      p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH
      density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut z hinputs hz
end Oberwolfach
