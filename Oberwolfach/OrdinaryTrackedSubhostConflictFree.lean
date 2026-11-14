module

public import Oberwolfach.OrdinaryTrackedComplementWitness

@[expose] public section
/-! Every later host retained from the actual matching remainder lies in the
original host and avoids the same conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_subhost_conflict_free {n q:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q)) (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hf:OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f)
    (hQP:(S\ordinaryEmbeddedComplements Fs C f)≤P)
    (G:SimpleGraph (Fin n)) (hG:G≤S\ordinaryEmbeddedComplements Fs C f):
    G≤P\permutationConflictGraph π (3*d) :=by
  have hcopy:=hf
  unfold OrdinaryTrackedComplementFor at hcopy
  obtain ⟨_,_,_,_,_,hBad,_⟩:=hcopy
  intro v w h
  have hQ:=hG h
  exact ⟨hQP hQ,fun hb=>(disjoint_iff_inf_le.mp hBad) ⟨hQ,hb⟩⟩
end Oberwolfach
