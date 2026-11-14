module

public import Oberwolfach.OrdinaryTrackedComplementWitness
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! The same actual remainder and fixed corrected reservoir provide all
root-agreement inputs for the edited-target trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_root_agreement {n q r mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner Z Wterm A:Finset (Fin n)) (Hubs B Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hZ:Z⊆Inner) (hB:B⊆Hubs):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u);
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→
    (∀v∈Z,∀w∈Z,Reference.Adj v w↔Q.Adj v w) ∧
    (∀v∈Z,∀u∈B,Href v u↔H v u) ∧
    Disjoint K (ordinaryRootResources Z B) ∧ K⊆ordinaryHostResources Q H ∧
    (∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Reference Href).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q K)
        (fun v u=>H v u∧¬(Sum.inr (v,u)∈K))).neighborFinset w)).card:ℝ)≤cost) :=by
  intro raw Bad Reference Href Q H hw hf
  have havoid:=hw.2.1
  unfold OrdinaryTrackedComplementFor at hf
  obtain ⟨_,_,hK,hpair,hspoke,_,hphysical⟩:=hf
  refine ⟨?_,?_,havoid,hK,hphysical⟩
  · intro v hv w hw'
    exact (hpair v (hZ hv) w (hZ hw')).symm
  · intro v hv u hu
    exact (hspoke v (hZ hv) u (hB hu)).symm
end Oberwolfach
