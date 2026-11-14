module

public import Oberwolfach.OrdinaryTrackedComplementInitialVortexInputs

@[expose] public section
/-! The matching remainder and the fixed reservoir satisfy the local
reference-agreement inputs for the later actual-host trace lemmas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_local_trace_inputs {n q r mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Z Wterm A:Finset (Fin n)) (B Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hw:OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ
      (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\permutationConflictGraph π (3*d))
      (permutationConflictGraph π (3*d)) (rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false)
      A Z Wterm Bterm B K JQ JH)
    (hf:OrdinaryTrackedComplementFor P S π d σ Fs C Z B K cost f):
    (∀v∈Z,∀w∈Z,(rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\permutationConflictGraph π (3*d)).Adj v w ↔
      (S\ordinaryEmbeddedComplements Fs C f).Adj v w) ∧
    (∀v∈Z,∀u∈B,rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false v u ↔ v∉Set.range (f u)) ∧
    Disjoint K (ordinaryRootResources Z B) :=by
  unfold OrdinaryTrackedComplementFor at hf
  obtain ⟨_,_,_,hQ,hH,_,_⟩:=hf
  exact ⟨fun v hv w hw=>(hQ v hv w hw).symm,fun v hv u hu=>(hH v hv u hu).symm,hw.2.1⟩
end Oberwolfach
