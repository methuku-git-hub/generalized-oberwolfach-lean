module

public import Oberwolfach.OrdinaryTrackedComplementWitness

@[expose] public section
/-! A tracked complement on a nonempty vertex set has a nonnegative edit
budget, directly from the physical discrepancy it bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_tracked_cost_nonnegative_from_witness {n q:ℕ}
    (hn:0<n) (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (cost:ℝ)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (h:OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs cost f):
    0≤cost :=by
  obtain ⟨_,_,_,_,_,_,hcost⟩:=h
  have hh:=hcost (Sum.inl ⟨0,hn⟩)
  exact le_trans (by positivity) hh
end Oberwolfach
