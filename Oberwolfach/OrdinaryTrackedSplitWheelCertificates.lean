module

public import Oberwolfach.OrdinaryTrackedSplitWheelCertificatesAt
public import Oberwolfach.OrdinaryTrackedLocalCertificatesFromSplit

@[expose] public section
/-! Reassemble the fixed initial and adaptive later certificates on the
same tracked complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_split_wheel_certificates {n q:ℕ}
    (P S Bad:SimpleGraph (Fin n)) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent) (r:ℕ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (D mv:ℕ) (β ε:ℝ)
    (Vor:Vortex (Fin q) P D β ε mv) (L:ℕ) (cost deepCost:ℕ→ℝ)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hsplit:OrdinaryTrackedSplitWheelCertificatesAt P S Bad Fs C r Kabs D mv β ε Vor L cost deepCost f):
    OrdinaryTrackedWheelLocalCertificates P S Bad Fs C r Kabs D mv β ε Vor L cost deepCost f :=by
  obtain ⟨hInitial,hLater⟩:=hsplit
  exact ordinary_tracked_local_certificates_from_split P S Bad Fs C r Kabs D mv β ε Vor L cost deepCost f hInitial hLater
end Oberwolfach
