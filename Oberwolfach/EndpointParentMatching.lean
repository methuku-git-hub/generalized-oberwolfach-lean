module

public import Oberwolfach.GraphEdgeWeightExtension
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Weights supplied on the parent induced graph have the ambient
representation used in the endpoint estimates. No new edge weights are
chosen when the rim or spoke subgraphs change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_parent_matching_extension (P F : SimpleGraph V) (Px : Finset V) (x : V)
    (a c C : ℝ) (ha : 0<a) (hc : 0≤c) (hC : 0≤C)
    (weight : (spanningRestriction P Px).edgeSet→ℝ)
    (hweight : ∀ e,c/a≤weight e ∧ weight e≤C/a)
    (hsum : ∀ v∈Px,(∑ e:(spanningRestriction P Px).edgeSet,if v∈e.val then weight e else 0)=1) :
    let w:=graphEdgeWeightExtension (spanningRestriction P Px) weight
    (∀ v∈Px,∀ u∈Px,0≤w s(v,u) ∧ w s(v,u)≤C/a) ∧
    (∀ v∈Px,∑ u∈Px,w s(v,u)=1) ∧
    (∀ v∈Px,∀ u∈Px,¬P.Adj v u → w s(v,u)=0) ∧
    (∀ e∈(endpointEligibleGraph P F Px x).edgeSet,c/a≤w e ∧ w e≤C/a) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv u hu
    by_cases he:s(v,u)∈(spanningRestriction P Px).edgeSet
    · rw [graphEdgeWeightExtension_edge _ _ _ he]
      exact ⟨(div_nonneg hc ha.le).trans (hweight ⟨_,he⟩).1,(hweight ⟨_,he⟩).2⟩
    · rw [graphEdgeWeightExtension_nonedge _ _ _ he]
      exact ⟨le_refl _,div_nonneg hC ha.le⟩
  · intro v hv
    calc
      _ = ∑ u,graphEdgeWeightExtension (spanningRestriction P Px) weight s(v,u) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro u hu hnot
        apply graphEdgeWeightExtension_nonedge
        intro he
        exact hnot ((spanningRestriction_adj P Px v u).mp he).2.2
      _ = _ := (graphEdgeWeightExtension_incident _ weight v).trans (hsum v hv)
  · intro v hv u hu hnot
    apply graphEdgeWeightExtension_nonedge
    intro he
    exact hnot ((spanningRestriction_adj P Px v u).mp he).1
  · intro e he
    have he' : e∈(spanningRestriction P Px).edgeSet := by
      induction e using Sym2.ind with
      | _ v u => exact (spanningRestriction_adj P Px v u).mpr ⟨he.2.2.2.2.1,he.1,he.2.1⟩
    rw [graphEdgeWeightExtension_edge _ _ _ he']
    exact hweight ⟨_,he'⟩

theorem endpoint_row_target_as_edges (P F : SimpleGraph V) (Px : Finset V) (x v : V)
    (hv : v∈Px) (hFx : ¬F.Adj x v) (weight : Sym2 V→ℝ)
    (hzero : ∀ u∈Px,¬P.Adj v u → weight s(v,u)=0) :
    endpointEligibleRowWeight F Px x v (fun v u=>weight s(v,u))=
      ∑ e∈(endpointEligibleGraph P F Px x).edgeFinset,if v∈e then weight e else 0 := by
  rw [←graph_weighted_incidence_sum]
  unfold endpointEligibleRowWeight
  have hexpand : (∑ u∈Px,if ¬F.Adj x u ∧ ¬F.Adj v u then weight s(v,u) else 0)=
      ∑ u,if u∈Px then (if ¬F.Adj x u ∧ ¬F.Adj v u then weight s(v,u) else 0) else 0 := by simp
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huP:u∈Px <;> by_cases hxu:F.Adj x u <;> by_cases hvu:F.Adj v u <;>
    by_cases hP:P.Adj v u <;> simp_all [endpointEligibleGraph]

end Oberwolfach
