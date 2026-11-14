module

public import Oberwolfach.OrdinaryVortexParentProductEvent

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

theorem ordinary_parent_event_level_tests
    (n qCount D mv m k d L:ℕ) (hm:3≤m) (hd:2≤d) (β ε α ρ₀ pstar βP ηP row ηH βH c B εTri χhost δref href:ℝ)
    (hpstar:0<pstar) (P:SimpleGraph (Fin n)) (Q:Vortex (Fin qCount) P D β ε mv)
    (π:Equiv.Perm (Fin n)) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (selection:OrdinaryGeneralFullDomainSelection m k d hm hd
      (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16) βP ηP row ηH βH c B εTri χhost (2*(3*d)) hpstar
      (Fin n) (Fin qCount) Bool Bool (markedVortexVertexType Q) (markedVortexHubType Q) P (permutationConflictGraph π (3*d))
      (fun i=>(markedVortexVertexEmbedding Q i).toEmbedding) (fun i=>markedVortexHubEmbedding Q i) (markedVortexPermutation Q π hπ) L)
    (p pH:ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (Good:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop):
    ∀z,OrdinaryVortexParentProductEvent n qCount D mv m k d L hm hd β ε α ρ₀ pstar βP ηP row ηH βH c B εTri χhost δref href hpstar
      P Q π hπ selection p pH s j R Good z→
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
    let g:=fun i=>markedVortexHubEmbedding Q i
    let ρi:=markedVortexPermutation Q π hπ
    let Fconf:=permutationConflictGraph π (3*d)
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    Good z ∧ ∀i≤L,
      ordinaryCombinedHostEvent m d k hm (P.comap (f i)) (Fconf.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold (m+1))) α pstar βP ηP row ηH βH c B (2*p) pH (selection.weight i)
        (fun u=>s (g i u)) j (ordinaryRawRestrictPair (f i) (g i) raw) ∧
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (Fconf.comap (f i)) (ρi i) d j δref href
        (ordinaryRawRestrictPair (f i) (g i) raw) (fun e=>z.2 (Sym2.map (f i) e)) :=by
  intro z hz f g ρi Fconf raw
  exact ⟨hz.1,fun i hi=>⟨hz.2.1 i hi,hz.2.2 i hi⟩⟩
end Oberwolfach
