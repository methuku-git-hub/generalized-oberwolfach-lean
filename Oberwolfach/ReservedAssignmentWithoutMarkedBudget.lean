module

public import Oberwolfach.ReservedSpokeAvoidsRetainedMarked
public import Oberwolfach.AssignedEdgePreparationShielded

@[expose] public section
/-! Reserved-pair labels avoid retained marked spokes automatically. Thus the
edge assignment needs no global bound on the marked labels at a vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prepare_reserved_edges_without_marked_budget
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Nonempty V] [Nonempty U]
    (G:SimpleGraph V) (Dstar:V→V→Prop) (hDstar:∀x y,G.Adj x y→Dstar x y∨Dstar y x)
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (Old:U→Finset V) (inner:Finset U)
    (hOld:∀w,Disjoint (rawReservedSpokeList π d σ w) (Old w))
    (a b:ℝ) (ha:0<a) (hb:0≤b) (hbsmall:b≤a/16) (hn:0<Fintype.card V)
    (hLabels:∀e∈G.edgeFinset,a*Fintype.card V≤
      ((protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner e).card:ℝ))
    (hG:∀v,(G.degree v:ℝ)≤b*Fintype.card V):
    let L:=protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner
    let K:=⌈4*(G.edgeFinset.card:ℝ)/(a*Fintype.card V)⌉₊;
    ∃(assign:Sym2 V→U) (orient:Sym2 V→V×V),
      (∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e ∧ Dstar (orient e).1 (orient e).2) ∧
      (∀e∈G.edgeFinset,assign e∈L e ∧ ∀v∈e.toFinset,v∉retainedFinalMarkedAt π d σ t J (assign e)) ∧
      (∀w,∀e∈G.edgeFinset,∀e'∈G.edgeFinset,assign e=w→assign e'=w→e≠e'→Disjoint e.toFinset e'.toFinset) ∧
      (∀w,(G.edgeFinset.filter (fun e=>assign e=w)).card≤K) ∧
      (∀w,Disjoint (Old w) (prescribedMatchingEndpoints (prescribedAssignedArcs G assign orient w))) ∧
      (∀w,w∈inner→prescribedAssignedArcs G assign orient w=∅) ∧
      (∀w,IsPrescribedOrientedMatching (prescribedAssignedArcs G assign orient w)) ∧
      (∀w,(prescribedAssignedArcs G assign orient w).card≤K):=by
  intro L K
  let B:V→Finset U:=fun _=>∅
  obtain ⟨hOutside,hShield⟩:=protected_pair_edge_hubs_avoid_old_images (rawReservedSpokeList π d σ) Old inner hOld
  have hOldB:∀w e v,e∈G.edgeFinset→v∈e.toFinset→v∈Old w→w∈L e→w∈B v:=by
    intro w e v he hv ho hl
    exact False.elim (hShield w e v hv ho hl)
  have hB:∀v,((B v).card:ℝ)≤b*Fintype.card V:=by
    intro v
    simp only [B,Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨assign,orient,horient,hallowed,hmatch,hload,hold,hinner,hmatching,hcard⟩:=
    prepare_assigned_bad_edges_with_shield G Dstar hDstar L B Old inner hOldB
      (fun e _=>hOutside e) a b ha hb hbsmall hn hLabels hB hG
  refine ⟨assign,orient,horient,?_,hmatch,hload,hold,hinner,hmatching,hcard⟩
  intro e he
  have hl:assign e∈L e:=(hallowed e he).1
  refine ⟨hl,?_⟩
  intro v hv hvMarked
  have hvReserved:v∈rawReservedSpokeList π d σ (assign e):=(Finset.mem_filter.mp hl).2.2 v hv
  exact Finset.disjoint_left.mp (reserved_spoke_avoids_retained_marked π d σ t J (assign e)) hvReserved hvMarked
end Oberwolfach
