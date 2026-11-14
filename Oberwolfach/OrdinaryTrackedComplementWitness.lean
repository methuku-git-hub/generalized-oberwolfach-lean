module

public import Oberwolfach.OrdinaryTrackedComplementOutcome
public import Oberwolfach.OrdinaryForbiddenComplementLocalAbsorber
public import Oberwolfach.OrdinaryComplementPhysicalEditWithSpokeLoss

@[expose] public section
/-! The actual embedded complement, its fixed absorber, protected pair and
physical comparison with the reference, on one expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTrackedComplementFor {n q:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (cost:ℝ)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):Prop :=
  let Bad:=permutationConflictGraph π (3*d)
  let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
  let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    (∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→S.Adj (f u x) (f u y)) ∧
    (∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (f u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (f v))) ∧
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u);
    Kabs⊆ordinaryHostResources Q H ∧
    (∀v∈Inner,∀w∈Inner,Q.Adj v w↔Reference.Adj v w) ∧
    (∀v∈Inner,∀u∈Hubs,H v u↔Href v u) ∧ Disjoint Q Bad ∧
    ∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Reference Href).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\ordinaryResourceRim Q Kabs)
        (fun v u=>H v u∧¬(Sum.inr (v,u)∈Kabs))).neighborFinset w)).card:ℝ)≤cost
theorem ordinary_tracked_complement_outcome_has_witness {n q:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (cost:ℝ)
    (h:OrdinaryTrackedComplementOutcome P S π d σ Fs C Inner Hubs Kabs cost):
    ∃f,OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs cost f :=by
  unfold OrdinaryTrackedComplementOutcome at h
  unfold OrdinaryTrackedComplementFor
  exact h
end Oberwolfach
