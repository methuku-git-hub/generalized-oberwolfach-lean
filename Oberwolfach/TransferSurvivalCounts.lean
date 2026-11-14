module

public import Oberwolfach.TransferPhysicalRetention
public import Oberwolfach.TransferCandidates
public import Oberwolfach.EdgeRetention

@[expose] public section

/-! Surviving physical patterns correspond exactly to transfer
configurations in the sampled graph; root spokes are restored separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (hr : 3 ≤ r) (P F : SimpleGraph V) (H : V → U → Prop) (v : V) (u u' : U)

def transferRetainedEquiv (σ : Sym2 V → Bool) :
    {T : OrdinaryTransferConfiguration hr P F H v u u' // ∀ e∈transferRequiredEdges T,σ e=true} ≃
    OrdinaryTransferConfiguration hr (retainedGraph P σ) F H v u u' where
  toFun T := {
    labels := T.val.labels
    omitted := T.val.omitted
    rim_edges := by
      intro j x y hxy
      refine ⟨T.val.rim_edges j hxy,?_⟩
      apply T.property s(x,y)
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,by
        rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
        exact hxy⟩
    spokes := T.val.spokes
    independent := T.val.independent }
  invFun T := ⟨{
    labels := T.labels
    omitted := T.omitted
    rim_edges := fun j _ _ hxy=>(T.rim_edges j hxy).1
    spokes := T.spokes
    independent := T.independent },by
      intro e he
      obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
      induction e using Sym2.ind with
      | _ x y=>
        rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at he
        exact (T.rim_edges j he).2⟩
  left_inv T := by
    apply Subtype.ext
    apply OrdinaryTransferConfiguration.labels_injective
    rfl
  right_inv T := by
    apply OrdinaryTransferConfiguration.labels_injective
    rfl

theorem transferSurvivalSum_card (σ : Sym2 V → Bool) :
    transferSurvivalSum r hr P F H v u u' σ=
      (Fintype.card (OrdinaryTransferConfiguration hr (retainedGraph P σ) F H v u u'):ℝ)/
        (Fintype.card V:ℝ)^(r^2) := by
  have hcard := Fintype.card_congr (transferRetainedEquiv r hr P F H v u u' σ)
  rw [← hcard]
  unfold transferSurvivalSum
  simp_rw [patternValue_indicator]
  rw [← Finset.mul_sum,Fintype.card_subtype]
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [div_eq_mul_inv,mul_comm]
  simp only [one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> rfl

def transferRootSpokesEquiv (hroot : H v u ∧ H v u') :
    OrdinaryTransferCandidate hr P F H v u u' ≃ OrdinaryTransferConfiguration hr P F H v u u' where
  toFun T := {
    labels := T.labels
    omitted := T.omitted
    rim_edges := T.rim_edges
    spokes := by
      intro z hz
      have hh := T.spokes z hz
      by_cases he : z=v
      · simpa only [he] using hroot
      · exact ⟨hh.1.resolve_left he,hh.2.resolve_left he⟩
    independent := T.independent }
  invFun T := {
    labels := T.labels
    omitted := T.omitted
    rim_edges := T.rim_edges
    spokes := fun z hz=>⟨Or.inr (T.spokes z hz).1,Or.inr (T.spokes z hz).2⟩
    independent := T.independent }
  left_inv T := by apply OrdinaryTransferConfiguration.labels_injective;rfl
  right_inv T := by apply OrdinaryTransferConfiguration.labels_injective;rfl

theorem transfer_candidate_survival_actual_count (σ : Sym2 V → Bool) (hroot : H v u ∧ H v u') :
    transferSurvivalSum r hr P F (transferRootCompletedSpokes H v) v u u' σ=
      (Fintype.card (OrdinaryTransferConfiguration hr (retainedGraph P σ) F H v u u'):ℝ)/
        (Fintype.card V:ℝ)^(r^2) := by
  rw [transferSurvivalSum_card]
  congr 1
  exact_mod_cast Fintype.card_congr (transferRootSpokesEquiv r hr (retainedGraph P σ) F H v u u' hroot)

def transferDeleteConflictsEquiv :
    OrdinaryTransferConfiguration hr P F H v u u' ≃ OrdinaryTransferConfiguration hr (P\F) F H v u u' where
  toFun T := {
    labels := T.labels
    omitted := T.omitted
    rim_edges := by
      intro j x y hxy
      refine ⟨T.rim_edges j hxy,?_⟩
      exact T.independent x (transferCycleGraph_support_subset hr T.labels v T.omitted j hxy.mem_support_left)
        y (transferCycleGraph_support_subset hr T.labels v T.omitted j hxy.mem_support_right)
    spokes := T.spokes
    independent := T.independent }
  invFun T := {
    labels := T.labels
    omitted := T.omitted
    rim_edges := fun j _ _ hxy=>(T.rim_edges j hxy).1
    spokes := T.spokes
    independent := T.independent }
  left_inv T := by apply OrdinaryTransferConfiguration.labels_injective;rfl
  right_inv T := by apply OrdinaryTransferConfiguration.labels_injective;rfl

theorem transfer_candidate_survival_deleted_count (σ : Sym2 V → Bool) (hroot : H v u ∧ H v u') :
    transferSurvivalSum r hr P F (transferRootCompletedSpokes H v) v u u' σ=
      (Fintype.card (OrdinaryTransferConfiguration hr (retainedGraph P σ\F) F H v u u'):ℝ)/
        (Fintype.card V:ℝ)^(r^2) := by
  rw [transfer_candidate_survival_actual_count r hr P F H v u u' σ hroot]
  congr 1
  exact_mod_cast Fintype.card_congr (transferDeleteConflictsEquiv r hr (retainedGraph P σ) F H v u u')

end Oberwolfach
