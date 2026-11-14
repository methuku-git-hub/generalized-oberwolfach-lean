module

public import Oberwolfach.OrdinaryTrackedReservoirToNaturalCertificate

@[expose] public section
/-! A high-probability event with one fixed absorber per sample and uniform
completion of all allowed target edits implies the natural certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_to_natural_probability {n q r:ℕ} {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (P:SimpleGraph (Fin n)) (Sample Reference:Ω→SimpleGraph (Fin n))
    (I Inner:Finset (Fin n)) (Hubs:Finset (Fin q)) (ξ:ℝ) (a b:ℕ)
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:Ω→∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (E:Ω→Prop) (p:ℝ) (hprob:p≤μ.probability E)
    (hcomplete:∀z,E z→∃K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)),
      Reference z≤Sample z ∧ (ordinaryResourceRows K).card≤a ∧ (ordinaryResourceHubs K).card≤b ∧
      ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→ ordinaryResourceRim (Reference z) K≤S→
        (∀x∈I,∀y∈I,S.Adj x y↔(Sample z).Adj x y)→
        (∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y) ((Sample z).Adj x y))).card:ℝ)≤ξ*n)→
        ∃cost:ℝ,∃f:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n,
          OrdinaryTrackedComplementFor P S π d (σ z) F C Inner Hubs K cost f ∧
          HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements F C f)
            (fun v u=>v∉Set.range (f u)) r):
    p≤μ.probability (fun z=>OrdinaryNaturalPreparationCertificate (r:=r) P (Sample z) I ξ (a*a+a*b) F C) :=by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨K,hRef,hrow,hhub,hcompletion⟩:=hcomplete z hz
  exact ordinary_tracked_reservoir_completion_to_natural_certificate P (Sample z) (Reference z) I Inner Hubs ξ π d
    (σ z) F C K a b hRef hrow hhub hcompletion
end Oberwolfach
