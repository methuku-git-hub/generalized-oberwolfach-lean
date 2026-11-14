module

public import Oberwolfach.OrdinaryEdgeAssignmentBeforeSpacing
public import Oberwolfach.OrdinaryPairAssignmentCommonEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The bad-edge assignments may be chosen after observing any event on the
same expanded sample; no additional probability loss is incurred. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_pair_assignment_on_same_event_before_spacing
    (θ ρ₀:ℝ) (hθ:0<θ) (hρ₀:0<ρ₀):
    ∃a:ℝ,0<a ∧ ∀(d:ℕ),0<d→1/(4*(d:ℝ))≤5*θ^2/256→∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(U:Type) [Fintype U] [DecidableEq U]
    (ρ D:ℝ),ρ₀≤ρ→0<D→(n:ℝ)/2≤D→ρ*D=2*(Fintype.card U:ℝ)→
    ∀(π:Equiv.Perm (Fin n)) (q:U→Bool→ℝ), (∀u,∑g,q u g≤1/8)→
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (μ:FiniteLaw (Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ))
      (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (ε:ℝ),
      1-ε≤μ.probability (fun z=>E z ∧ OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1)→
      1-ε≤μ.probability (fun z=>E z ∧ OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧
        OrdinaryProtectedBadEdgeAssignments π d z.1 a):=by
  obtain ⟨a,ha,hN⟩:=ordinary_bad_edge_assignment_before_spacing θ ρ₀ hθ hρ₀
  refine ⟨a,ha,?_⟩
  intro d hd hspacing
  obtain ⟨N,hN⟩:=hN d hd hspacing
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ ρ D hρ hD hDlo hsize π q hQ R _ μ E ε hE
  apply hE.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,hz.2,?_⟩
  exact hN n hn hn0 U ρ D hρ hD hDlo hsize π z.1 q hQ hz.2
end Oberwolfach
