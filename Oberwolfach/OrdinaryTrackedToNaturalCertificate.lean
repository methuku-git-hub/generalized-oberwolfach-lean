module

public import Oberwolfach.OrdinaryNaturalPreparationCertificate
public import Oberwolfach.OrdinaryTrackedComplementWitness

@[expose] public section
/-! Uniform completion of the same tracked remainder yields the natural
preparation certificate with the protected graph fixed before the edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_uniform_completion_to_natural_certificate {n q r:ℕ}
    (P S₀ A:SimpleGraph (Fin n)) (I Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (ξ:ℝ) (B:ℕ) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hA:A≤S₀) (hB:A.edgeFinset.card≤B)
    (hcomplete:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→A≤S→
      (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→
      (∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) (S₀.Adj x y))).card:ℝ)≤ξ*n)→
      ∃cost:ℝ,∃f:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n,
        OrdinaryTrackedComplementFor P S π d σ F C Inner Hubs K cost f ∧
        HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements F C f)
          (fun v u=>v∉Set.range (f u)) r):
    OrdinaryNaturalPreparationCertificate (r:=r) P S₀ I ξ B F C :=by
  refine ⟨A,hA,hB,?_⟩
  intro S hSP hS hAS hI hchange
  obtain ⟨cost,f,hf,hwheel⟩:=hcomplete S hSP hS hAS hI hchange
  unfold OrdinaryTrackedComplementFor at hf
  obtain ⟨hC,hCC,_,_,_,_,_⟩:=hf
  exact ⟨f,hC,hCC,hwheel⟩
end Oberwolfach
