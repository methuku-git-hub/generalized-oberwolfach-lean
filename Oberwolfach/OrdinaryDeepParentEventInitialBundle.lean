module

public import Oberwolfach.OrdinaryParentEventLevelTests
public import Oberwolfach.OrdinaryDeepRowsCutsEvent

@[expose] public section
/-! Read the actual deeper-level inputs simultaneously from the common
sample: the prior, inner weights, deep cover, row tests and both parent cuts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_event_initial_bundle
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
    (z:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)):
    let Good:=OrdinaryDeepRowsCutsEvent n qCount D mv m K d β ε P Q π hπ p pH pmin αcut c C b Bweight ξ ηHub Kdom a aLoad ρdeep θdeep cap eParent hParent εR εH density tR tH s j R μ ν E loss χinner χdeep χone χtwo χcut
    let All:=OrdinaryVortexParentProductEvent n qCount D mv m k d (Q.length-1) hm hd β ε α ρ₀ pstar βP ηP row ηH βH cParent Bparent εTri χhost δref href hpstar
      P Q π hπ selection p pH s j R Good
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
    let Fconf:=permutationConflictGraph π (3*d)
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ;
    All z→E z ∧
      OrdinaryUniformInnerHubEvent m P D mv d β ε Q π hπ (2*p) pH (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j raw ∧
      OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρdeep θdeep P D mv β ε Q π hπ j raw ∧
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Fconf D mv β ε Q π hπ (2*p) pH s j raw ∧
      OrdinaryInducedRimCutEvent (Q.extendedVertices 1) (sampledOrientation (rawWheelGraph P raw) z.2) αcut pmin ∧
      ordinaryCombinedHostEvent m d k hm (P.comap (f 0)) (Fconf.comap (f 0)) (ρi 0)
        (max (1/2) (cycleThreshold (m+1))) α pstar βP ηP row ηH βH cParent Bparent (2*p) pH (selection.weight 0)
        (fun u=>s (g 0 u)) j (ordinaryRawRestrictPair (f 0) (g 0) raw) ∧
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f 0)) (Fconf.comap (f 0)) (ρi 0) d j δref href
        (ordinaryRawRestrictPair (f 0) (g 0) raw) (fun e=>z.2 (Sym2.map (f 0) e)) :=by
  intro Good All raw Fconf f g ρi hz
  obtain ⟨⟨⟨⟨⟨hE,hInner⟩,hDeep⟩,hRow⟩,hTwo⟩,hRim⟩:=hz.1
  exact ⟨hE,hInner,hDeep,hRow,hTwo,by simpa using hRim 0 Q.length_pos,hz.2.1 0 (by omega),hz.2.2 0 (by omega)⟩
end Oberwolfach
