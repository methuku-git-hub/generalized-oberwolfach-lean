module

public import Oberwolfach.OrdinaryTriangleParentProductEvent

@[expose] public section
/-! A named product-sample event retaining its prior and all selected parent
and reference-direction tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_parent_event_level_tests
    (n qCount D mv k d L:ℕ) (hd:2≤d) (β ε α pstar βP ηP ηH βH c B δref href:ℝ)
    (P:SimpleGraph (Fin n)) (Q:Vortex (Fin qCount) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (weight:∀i,OrdinaryCycle (P.comap (markedVortexVertexEmbedding Q i).toEmbedding) 3→ℝ)
    (p pH:ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (Good:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop):
    ∀z,OrdinaryTriangleParentProductEvent n qCount D mv k d L hd β ε α pstar βP ηP ηH βH c B δref href
      P Q π hπ weight p pH s j R Good z→
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ
    let Fconf:=permutationConflictGraph π (3*d)
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    Good z ∧ ∀i≤L,
      ordinaryCombinedTriangleEvent d k (P.comap (f i)) (Fconf.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B (2*p) pH (weight i)
        j (ordinaryRawRestrictPair (f i) (g i) raw) ∧
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (Fconf.comap (f i)) (ρi i) d j δref href
        (ordinaryRawRestrictPair (f i) (g i) raw) (fun e=>z.2 (Sym2.map (f i) e)) :=by
  intro z hz f g ρi Fconf raw
  exact ⟨hz.1,fun i hi=>⟨hz.2.1 i hi,hz.2.2 i hi⟩⟩
end Oberwolfach
