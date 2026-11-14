module

public import Oberwolfach.OrdinaryProtectedEdgeAssignment
public import Oberwolfach.AssignedEdgePreparationShielded

@[expose] public section
/-! Assign the actual bad edges to protected unassigned lists while avoiding
all previously embedded vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_bad_edge_assignment_from_counts
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty U] [Nonempty (Fin n)]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:0<d)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (G:SimpleGraph (Fin n)) (Dstar:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (Old:U→Finset (Fin n))
    (hOld:∀u,Disjoint (rawIntervalProtectedUnassignedList π d σ false true t Jret u) (Old u))
    (a b:ℝ) (ha:0<a) (hb:0≤b) (hbsmall:b≤a/16) (hn:0<n)
    (q:U→Bool→ℝ) (hQ:∀u,∑g,q u g≤1/8) (θ err:ℝ)
    (hpair:∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-err≤rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ)
    (hstarts:∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<err)
    (hbudget:a*n+5*err≤((5/32:ℝ)*θ^2-1/(4*(d:ℝ)))*Fintype.card U)
    (hdegree:∀v,(G.degree v:ℝ)≤b*n):
    let Kload:=⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊;
    ∃(assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n),
      (∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e ∧ Dstar (orient e).1 (orient e).2) ∧
      (∀e∈G.edgeFinset,assign e∈protectedPairEdgeHubs (rawIntervalProtectedUnassignedList π d σ false true t Jret) ∅ e) ∧
      (∀u,Disjoint (Old u) (prescribedMatchingEndpoints (prescribedAssignedArcs G assign orient u))) ∧
      (∀u,IsPrescribedOrientedMatching (prescribedAssignedArcs G assign orient u)) ∧
      (∀u,(prescribedAssignedArcs G assign orient u).card≤Kload):=by
  intro Kload
  have hlabels:=ordinary_protected_pair_edge_labels π d hd σ t Jret q hQ θ err a hpair hstarts hbudget G
  exact ordinary_protected_bad_edge_assignment π d σ t Jret G Dstar hDstar Old hOld a b ha hb hbsmall hn hlabels hdegree
end Oberwolfach
