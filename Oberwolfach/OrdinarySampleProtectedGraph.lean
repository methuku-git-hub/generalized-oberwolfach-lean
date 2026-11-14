module

public import Oberwolfach.OrdinaryReservoirProtectedGraph
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! The reservoir selects a bounded protected graph inside the actual
expanded sample and avoids the entire prescribed inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) ordinarySampleProtectedGraphSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem ordinary_sample_reservoir_protected_graph
    {n:ℕ} {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P Fbad:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
    (A:Finset (Sym2 (Fin n)⊕(Fin n×U))) (Inner:Finset (Fin n)) (B:Finset U)
    (a b:ℕ) (hrow:(ordinaryResourceRows A).card≤a) (hhub:(ordinaryResourceHubs A).card≤b)
    (hInner:Disjoint A (ordinaryRootResources Inner B)):
    let R:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Fbad
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Protect:=ordinaryResourceRim R A;
    Protect≤S₀ ∧ Protect.edgeFinset.card≤a*a+a*b ∧
      (∀v∈Inner,∀w∈Inner,¬Protect.Adj v w):=by
  intro R S₀ Protect
  have hR:R≤S₀:=by
    exact (show R≤rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e)) from sdiff_le).trans
      (ordinary_shared_sample_reference_graph_le_class P σ)
  exact ordinary_reservoir_protected_graph R S₀ A Inner B a b hR hrow hhub hInner
end Oberwolfach
