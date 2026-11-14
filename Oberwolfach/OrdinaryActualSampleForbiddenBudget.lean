module

public import Oberwolfach.OrdinaryForbiddenSelectedMatchingBundle
public import Oberwolfach.OrdinaryMatchingProtectChoice
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion
public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! Instantiate the enlarged matching input with the selected reference,
permutation conflict graph and protected reservoir from the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_sample_forbidden_matching_budget
    {V U : Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (P Target Host : SimpleGraph V) (hHost : Host ≤ P) (π : Equiv.Perm V) (d : ℕ)
    (σ : ∀ e : RawWheelCoordinate V U, RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner : Finset V) (Hubs : Finset U) (K : Finset (Sym2 V ⊕ (V × U))) (b : ℝ) :
    let Sample := longPhysicalStateGraph P σ {0,1,2,3,4}
    let F := permutationConflictGraph π (3*d)
    let Reference := rawWheelGraph P (fun e => expandedOrdinarySelectedCollapse e (σ e)) \ F
    let Protect := ordinaryMatchingProtect Reference Inner K
    let G := ordinaryForbiddenRequired Target Sample Reference F Inner
    let Del := ordinaryForbiddenSampleDeletion Sample Target Reference Protect F Inner
    let Dfree := fun x y => rawSelectedPhysicalRelation P π d (fun e => σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar := fun x y => Dfree x y ∨ G.Adj x y
    let Href := rawWheelSpokes π d (fun e => expandedOrdinarySelectedCollapse e (σ e)) false
    let T := ordinaryInnerSpokeTargets Inner Hubs Href
    let Budget : ℝ := b + 2*Inner.card + (ordinaryResourceRows K).card + 2*((3*d:ℕ):ℝ);
    (∀ v, ((Finset.univ.filter (fun w => Xor (Target.Adj v w) (Sample.Adj v w))).card : ℝ) ≤ b) →
    Reference ≤ Sample ∧ Disjoint Reference F ∧ Protect ≤ Reference ∧
    spanningRestriction Reference Inner ≤ Protect ∧ ordinaryResourceRim Reference K ≤ Protect ∧
    Sample \ (Target \ Protect) ≤ Del ∧ G ≤ Target \ Protect ∧
    (∀ x y, G.Adj x y → ¬(Sample \ Del).Adj x y) ∧
    (∀ v, (G.degree v : ℝ) ≤ Budget) ∧ (∀ v, (Del.degree v : ℝ) ≤ Budget) ∧
    (∀ x y, rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e => rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y →
      (Target \ Protect).Adj x y) ∧
    (∀ x y, G.Adj x y → Dstar x y ∨ Dstar y x) ∧
    (∀ x y, Dfree x y → Dstar x y) ∧ (∀ x y, Dstar x y → (Target \ Protect).Adj x y) ∧
    (∀ u, T u ⊆ Inner ∧ (T u ≠ ∅ → u ∈ Hubs)) ∧
    Target ⊓ F ≤ G ∧ ordinaryProtectedRequired Target Sample Reference Inner ≤ G := by
  intro Sample F Reference Protect G Del Dfree Dstar Href T Budget hEdit
  have hRef : Reference ≤ Sample := sdiff_le.trans (ordinary_shared_sample_reference_graph_le_class P σ)
  have hRefF : Disjoint Reference F := by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact h.1.2 h.2
  have hprotect := ordinary_matching_protect_choice Reference Inner K
  have hPdegree : ∀ v, (Protect.degree v : ℝ) ≤ (Inner.card : ℝ)+(ordinaryResourceRows K).card := by
    intro v
    have hh := hprotect.2.2.2 v
    exact_mod_cast hh
  have hFdegree : ∀ v, (F.degree v : ℝ) ≤ 2*((3*d:ℕ):ℝ) := by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) v
  have hGbudget : b + Inner.card + 2*((3*d:ℕ):ℝ) ≤ Budget := by
    dsimp [Budget]
    have : 0 ≤ ((Inner.card + (ordinaryResourceRows K).card : ℕ) : ℝ) := by positivity
    push_cast at this
    linarith
  have hDelbudget : b + ((Inner.card : ℝ)+(ordinaryResourceRows K).card) + Inner.card + 2*((3*d:ℕ):ℝ) ≤ Budget := by
    dsimp [Budget]
    ring_nf
    exact le_rfl
  have hb := ordinary_forbidden_selected_matching_bundle P Target Host Reference Protect F hHost π d σ Inner Hubs
    b ((Inner.card : ℝ)+(ordinaryResourceRows K).card) (2*((3*d:ℕ):ℝ)) Budget
    hRef hprotect.1 hRefF hEdit hPdegree hFdegree hGbudget hDelbudget
  exact ⟨hRef,hRefF,hprotect.1,hprotect.2.1,hprotect.2.2.1,hb⟩
end Oberwolfach
