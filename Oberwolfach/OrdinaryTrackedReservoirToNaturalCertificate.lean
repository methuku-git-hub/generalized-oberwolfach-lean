module

public import Oberwolfach.OrdinaryTrackedToNaturalCertificate
public import Oberwolfach.OrdinaryReservoirProtectedGraph

@[expose] public section
/-! Use the rim of the same fixed absorber as the bounded protected graph
in the ordinary natural preparation certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_reservoir_completion_to_natural_certificate {n q r:ℕ}
    (P S₀ Reference:SimpleGraph (Fin n)) (I Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (ξ:ℝ) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (a b:ℕ)
    (hRef:Reference≤S₀) (hrow:(ordinaryResourceRows K).card≤a) (hhub:(ordinaryResourceHubs K).card≤b):
    let A:=ordinaryResourceRim Reference K;
    (∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→A≤S→
      (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→
      (∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ)≤ξ*n)→
      ∃cost:ℝ,∃f:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n,
        OrdinaryTrackedComplementFor P S π d σ F C Inner Hubs K cost f ∧
        HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements F C f)
          (fun v u=>v∉Set.range (f u)) r)→
    OrdinaryNaturalPreparationCertificate (r:=r) P S₀ I ξ (a*a+a*b) F C :=by
  intro A hcomplete
  have hA:A≤S₀:=by intro v w h;exact hRef h.1
  have hB:A.edgeFinset.card≤a*a+a*b:=
    (ordinary_reservoir_rim_edge_card_le Reference K).trans (ordinary_reservoir_resource_card_bound K a b hrow hhub)
  exact ordinary_tracked_uniform_completion_to_natural_certificate P S₀ A I Inner Hubs ξ (a*a+a*b) π d σ F C K hA hB hcomplete
end Oberwolfach
