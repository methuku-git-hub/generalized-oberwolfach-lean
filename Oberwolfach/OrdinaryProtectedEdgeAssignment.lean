module

public import Oberwolfach.OrdinaryProtectedPairLabels
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

theorem ordinary_protected_bad_edge_assignment
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty U] [Nonempty (Fin n)]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (G:SimpleGraph (Fin n)) (Dstar:Fin n→Fin n→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (Old:U→Finset (Fin n))
    (hOld:∀u,Disjoint (rawIntervalProtectedUnassignedList π d σ false true t Jret u) (Old u))
    (a b:ℝ) (ha:0<a) (hb:0≤b) (hbsmall:b≤a/16) (hn:0<n)
    (hlabels:∀e∈G.edgeFinset,a*n≤((protectedPairEdgeHubs
      (rawIntervalProtectedUnassignedList π d σ false true t Jret) ∅ e).card:ℝ))
    (hdegree:∀v,(G.degree v:ℝ)≤b*n):
    let Kload:=⌈4*(G.edgeFinset.card:ℝ)/(a*n)⌉₊;
    ∃(assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n),
      (∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e ∧ Dstar (orient e).1 (orient e).2) ∧
      (∀e∈G.edgeFinset,assign e∈protectedPairEdgeHubs (rawIntervalProtectedUnassignedList π d σ false true t Jret) ∅ e) ∧
      (∀u,Disjoint (Old u) (prescribedMatchingEndpoints (prescribedAssignedArcs G assign orient u))) ∧
      (∀u,IsPrescribedOrientedMatching (prescribedAssignedArcs G assign orient u)) ∧
      (∀u,(prescribedAssignedArcs G assign orient u).card≤Kload):=by
  intro Kload
  let Lists:=rawIntervalProtectedUnassignedList π d σ false true t Jret
  let labels:=protectedPairEdgeHubs Lists ∅
  let Bad:Fin n→Finset U:=fun _=>∅
  have hshield:∀i e v,e∈G.edgeFinset→v∈e.toFinset→v∈Old i→i∈labels e→i∈Bad v:=by
    intro i e v he hv ho hi
    have hnone:False:=(protected_pair_edge_hubs_avoid_old_images Lists Old ∅ hOld).2 i e v hv ho hi
    exact False.elim hnone
  have hOutside:∀e∈G.edgeFinset,Disjoint (labels e) (∅:Finset U):=by simp
  have hB:∀v,((Bad v).card:ℝ)≤b*Fintype.card (Fin n):=by
    intro v
    simp only [Bad,Finset.card_empty,Nat.cast_zero,Fintype.card_fin]
    positivity
  have hnV:0<Fintype.card (Fin n):=by simpa using hn
  obtain ⟨assign,orient,horient,hallowed,hmatching,hcap,hold,hinner,hmatch,hcard⟩:=
    prepare_assigned_bad_edges_with_shield G Dstar hDstar labels Bad Old ∅ hshield hOutside a b ha hb hbsmall hnV
      (by simpa only [Fintype.card_fin,labels,Lists] using hlabels) hB
      (by simpa only [Fintype.card_fin] using hdegree)
  refine ⟨assign,orient,horient,?_,hold,hmatch,?_⟩
  · intro e he
    exact (hallowed e he).1
  · simpa only [Kload,Fintype.card_fin] using hcard
end Oberwolfach
