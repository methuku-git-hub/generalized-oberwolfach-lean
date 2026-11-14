module

public import Oberwolfach.OrdinaryTrackedComplementWitness
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! A wheel decomposition of this exact matching remainder completes the
factor decomposition of the edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_wheel_to_factor {n q r:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hr:0<r)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r) (hS:S.IsRegularOfDegree (2*q))
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q)) (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hf:OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f)
    (hWheel:HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements Fs C f) (fun v u=>v∉Set.range (f u)) r):
    HasFactorDecomposition S Fs :=by
  unfold OrdinaryTrackedComplementFor at hf
  obtain ⟨hC,hCC,_,_,_,_,_⟩:=hf
  exact ordinary_complement_remainder_decomposition S hS hr Fs hFs C hsize f hC hCC hWheel
end Oberwolfach
