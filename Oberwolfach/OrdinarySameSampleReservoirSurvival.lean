module

public import Oberwolfach.OrdinaryReservoirSurvivesComplement
public import Oberwolfach.OrdinaryReferenceSpokeProjection

@[expose] public section
/-! The reservoir and the complement embedding are interpreted in the same
expanded sample; no separate sample or independence is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_reservoir_survives_complement {n q:ℕ}
    (P Fbad Target:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (fC:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Ref:=rawWheelGraph P raw\Fbad
    let Href:=rawWheelSpokes π d raw false
    let Protect:=ordinaryResourceRim Ref A;
    A⊆ordinaryHostResources Ref Href → Protect≤Target →
    (∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (fC u x) (fC u y)) →
    (∀u x,¬Href (fC u x) u) →
    A⊆ordinaryHostResources (Target\ordinaryEmbeddedComplements Fs C fC)
      (fun v u=>v∉Set.range (fC u)):=by
  intro raw Ref Href Protect hA hProtect hRim hSpoke
  exact ordinary_protected_reservoir_survives_complement Ref Target Fs C fC Href A hA hProtect hRim hSpoke
end Oberwolfach
