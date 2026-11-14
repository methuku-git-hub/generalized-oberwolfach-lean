module

public import Oberwolfach.OrdinaryTrackedReservoirToNaturalCertificate
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! The fixed absorber and every edited-target completion are witnesses on
one expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTrackedSampleCompletion {n q r:ℕ}
    (P:SimpleGraph (Fin n)) (I Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (ξ:ℝ) (a b:ℕ) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent):Prop :=
  let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
  let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\permutationConflictGraph π (3*d);
  ∃K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)),
    (ordinaryResourceRows K).card≤a ∧ (ordinaryResourceHubs K).card≤b ∧
    ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→ ordinaryResourceRim Reference K≤S→
      (∀x∈I,∀y∈I,S.Adj x y↔Sample.Adj x y)→
      (∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (Sample.Adj x y))).card:ℝ)≤ξ*n)→
      ∃cost:ℝ,∃f:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n,
        OrdinaryTrackedComplementFor P S π d σ F C Inner Hubs K cost f ∧
        HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements F C f)
          (fun v u=>v∉Set.range (f u)) r

theorem ordinary_tracked_sample_completion_certificate {n q r:ℕ}
    (P:SimpleGraph (Fin n)) (I Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (ξ:ℝ) (a b:ℕ) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (h:OrdinaryTrackedSampleCompletion (r:=r) P I Inner Hubs ξ a b π d σ F C):
    OrdinaryNaturalPreparationCertificate (r:=r) P (longPhysicalStateGraph P σ {0,1,2,3,4}) I ξ (a*a+a*b) F C :=by
  unfold OrdinaryTrackedSampleCompletion at h
  obtain ⟨K,hrow,hhub,hcomplete⟩:=h
  let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
  let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\permutationConflictGraph π (3*d)
  have hRef:Reference≤Sample:=sdiff_le.trans (ordinary_shared_sample_reference_graph_le_class P σ)
  exact ordinary_tracked_reservoir_completion_to_natural_certificate P Sample Reference I Inner Hubs ξ π d σ F C K a b hRef hrow hhub hcomplete
end Oberwolfach
