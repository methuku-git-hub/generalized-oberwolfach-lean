module

public import Oberwolfach.OrdinaryProtectedEdgeAssignmentFromCounts
public import Oberwolfach.OrdinaryProtectedPairDensityBeforeSpacing
public import Oberwolfach.OrdinaryUnassignedPairsStartsEvent

@[expose] public section
/-! The original density identity and same-sample unassigned-pair event give
protected matchings of bad edges for all sufficiently large orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_bad_edge_assignment_before_spacing
    (θ ρ₀:ℝ) (hθ:0<θ) (hρ₀:0<ρ₀):
    ∃a:ℝ,0<a ∧ ∀(d:ℕ),0<d→1/(4*(d:ℝ))≤5*θ^2/256→∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(U:Type) [Fintype U] [DecidableEq U]
    (ρ D:ℝ),ρ₀≤ρ→0<D→(n:ℝ)/2≤D→ρ*D=2*(Fintype.card U:ℝ)→
    ∀(π:Equiv.Perm (Fin n))
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (q:U→Bool→ℝ), (∀u,∑g,q u g≤1/8)→
      OrdinaryUnassignedPairsStartsEvent π d (θ/2) q σ→
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
      (∀u,(prescribedAssignedArcs G assign orient u).card≤Kload):=by
  obtain ⟨a,ha,hN⟩:=ordinary_protected_pair_budget_density_before_spacing θ ρ₀ hθ hρ₀
  refine ⟨a,ha,?_⟩
  intro d hd hspacing
  obtain ⟨N,hN⟩:=hN d hd hspacing
  refine ⟨N,?_⟩
  intro n hnN hn U _ _ ρ D hρ hD hDlo hsize π σ q hQ hEvent t Jret G Dstar hDstar Old hOld b hb hbsmall hdegree Kload
  letI:Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hU0:0<Fintype.card U:=by
    have hρpos:0<ρ:=lt_of_lt_of_le hρ₀ hρ
    have hh:0<(Fintype.card U:ℝ):=by nlinarith [mul_pos hρpos hD]
    exact_mod_cast hh
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU0
  have hbudget:=hN n hnN U ρ D hρ hD hDlo hsize
  have hinst : (fun a b : Fin n => Classical.propDecidable (a = b)) = instDecidableEqFin n := Subsingleton.elim _ _
  have hEvent' := hEvent
  unfold OrdinaryUnassignedPairsStartsEvent at hEvent'
  rw [hinst] at hEvent'
  have hpair:∀x y,x≠y→(5/32:ℝ)*(θ/2)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      rawIntervalUnassignedPairColumnCount π d (fun e=>σ (Sum.inr e)) x y Finset.univ:=by
    simpa only [OrdinaryUnassignedPairsStartsEvent,Fintype.card_fin] using hEvent'.1
  have hstarts:∀v g,|rawIntervalStartColumnCount π d (fun e=>σ (Sum.inr e)) v g Finset.univ-
      ∑u,q u g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ):=by
    simpa only [OrdinaryUnassignedPairsStartsEvent,Fintype.card_fin] using hEvent'.2
  exact ordinary_protected_bad_edge_assignment_from_counts π d hd (fun e=>σ (Sum.inr e)) t Jret G Dstar hDstar Old hOld
    a b ha hb hbsmall hn q hQ (θ/2) ((n:ℝ)^(3/4:ℝ)) hpair hstarts hbudget hdegree
end Oberwolfach
