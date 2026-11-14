module

public import Oberwolfach.OrdinaryEdgeAssignmentFromPairEvent
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

def OrdinaryProtectedBadEdgeAssignments {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (a:ℝ):Prop :=
    ∀(t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
      (G:SimpleGraph (Fin n)) (Dstar:Fin n→Fin n→Prop),
      (∀x y,G.Adj x y→Dstar x y∨Dstar y x)→
    ∀(Old:U→Finset (Fin n)),
      (∀u,Disjoint (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u) (Old u))→
    ∀b:ℝ,0≤b→b≤a/16→(∀v,(G.degree v:ℝ)≤b*n)→
    let Kload:=⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊;
    ∃(assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n),
      (∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e ∧ Dstar (orient e).1 (orient e).2) ∧
      (∀e∈G.edgeFinset,assign e∈protectedPairEdgeHubs
        (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret) ∅ e) ∧
      (∀u,Disjoint (Old u) (prescribedMatchingEndpoints (prescribedAssignedArcs G assign orient u))) ∧
      (∀u,IsPrescribedOrientedMatching (prescribedAssignedArcs G assign orient u)) ∧
      (∀u,(prescribedAssignedArcs G assign orient u).card≤Kload)

theorem ordinary_pair_assignment_on_same_event
    (θ ρ₀:ℝ) (hθ:0<θ) (hρ₀:0<ρ₀) (d:ℕ) (hd:0<d)
    (hspacing:1/(4*(d:ℝ))≤5*θ^2/256):
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(U:Type) [Fintype U] [DecidableEq U]
    (ρ D:ℝ),ρ₀≤ρ→0<D→(n:ℝ)/2≤D→ρ*D=2*(Fintype.card U:ℝ)→
    ∀(π:Equiv.Perm (Fin n)) (q:U→Bool→ℝ), (∀u,∑g,q u g≤1/8)→
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (μ:FiniteLaw (Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ))
      (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (ε:ℝ),
      1-ε≤μ.probability (fun z=>E z ∧ OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1)→
      1-ε≤μ.probability (fun z=>E z ∧ OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧
        OrdinaryProtectedBadEdgeAssignments π d z.1 a):=by
  obtain ⟨a,ha,N,hN⟩:=ordinary_bad_edge_assignment_from_pair_event θ ρ₀ hθ hρ₀ d hd hspacing
  refine ⟨a,ha,N,?_⟩
  intro n hn hn0 U _ _ ρ D hρ hD hDlo hsize π q hQ R _ μ E ε hE
  apply hE.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,hz.2,?_⟩
  exact hN n hn hn0 U ρ D hρ hD hDlo hsize π z.1 q hQ hz.2
end Oberwolfach
