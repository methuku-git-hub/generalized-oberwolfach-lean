module

public import Oberwolfach.OrdinaryTrackedComplementWitness

@[expose] public section
/-! Increase the explicit physical error budget without changing the
matching embedding, fixed absorber or protected pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_cost_monotone {n q:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q)) (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (cost cost':ℝ) (hcost:cost≤cost')
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hf:OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f):
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost' f :=by
  unfold OrdinaryTrackedComplementFor at hf ⊢
  obtain ⟨hC,hCC,hK,hpair,hspoke,hbad,hphysical⟩:=hf
  exact ⟨hC,hCC,hK,hpair,hspoke,hbad,fun w=>(hphysical w).trans hcost⟩
end Oberwolfach
