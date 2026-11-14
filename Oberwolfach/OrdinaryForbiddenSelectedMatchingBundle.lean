module

public import Oberwolfach.OrdinaryForbiddenMatchingInputs
public import Oberwolfach.OrdinarySelectedRequiredDirectedTarget
public import Oberwolfach.OrdinarySampleForcedSpokes

@[expose] public section
/-! Assemble the required/deleted edge inputs, selected directed host and
forced non-reference spoke targets on one expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_forbidden_selected_matching_bundle
    {V U : Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (P Target Host Reference Protect Bad : SimpleGraph V) (hHost : Host ≤ P)
    (π : Equiv.Perm V) (d : ℕ)
    (σ : ∀ e : RawWheelCoordinate V U, RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner : Finset V) (Hubs : Finset U) (b a f B : ℝ) :
    let Sample := longPhysicalStateGraph P σ {0,1,2,3,4}
    let G := ordinaryForbiddenRequired Target Sample Reference Bad Inner
    let Del := ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner
    let Dfree := fun x y => rawSelectedPhysicalRelation P π d (fun e => σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar := fun x y => Dfree x y ∨ G.Adj x y
    let Href := rawWheelSpokes π d (fun e => expandedOrdinarySelectedCollapse e (σ e)) false
    let T := ordinaryInnerSpokeTargets Inner Hubs Href;
    Reference ≤ Sample → Protect ≤ Reference → Disjoint Reference Bad →
    (∀ v, ((Finset.univ.filter (fun w => Xor (Target.Adj v w) (Sample.Adj v w))).card : ℝ) ≤ b) →
    (∀ v, (Protect.degree v : ℝ) ≤ a) → (∀ v, (Bad.degree v : ℝ) ≤ f) →
    b + Inner.card + f ≤ B → b + a + Inner.card + f ≤ B →
    Sample \ (Target \ Protect) ≤ Del ∧ G ≤ Target \ Protect ∧
    (∀ x y, G.Adj x y → ¬(Sample \ Del).Adj x y) ∧
    (∀ v, (G.degree v : ℝ) ≤ B) ∧ (∀ v, (Del.degree v : ℝ) ≤ B) ∧
    (∀ x y, rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e => rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y →
      (Target \ Protect).Adj x y) ∧
    (∀ x y, G.Adj x y → Dstar x y ∨ Dstar y x) ∧
    (∀ x y, Dfree x y → Dstar x y) ∧ (∀ x y, Dstar x y → (Target \ Protect).Adj x y) ∧
    (∀ u, T u ⊆ Inner ∧ (T u ≠ ∅ → u ∈ Hubs)) ∧
    Target ⊓ Bad ≤ G ∧ ordinaryProtectedRequired Target Sample Reference Inner ≤ G := by
  intro Sample G Del Dfree Dstar Href T hRef hProtectRef hBadRef hEdit hProtect hBad hGbudget hDelbudget
  have hm := ordinary_forbidden_matching_inputs Target Sample Reference Protect Bad Inner b a f B
    hRef hProtectRef hBadRef hEdit hProtect hBad hGbudget hDelbudget
  obtain ⟨hDel,hG,hsep,hGdegree,hDeldegree,hBadCover,hProtectedCover⟩ := hm
  have hs := ordinary_selected_required_directed_target P (Target \ Protect) Host Del G hHost hG π d σ hDel
  obtain ⟨hOld,hGstar,hfree,hstar,hselected⟩ := hs
  refine ⟨hDel,hG,hsep,hGdegree,hDeldegree,hOld,hGstar,hfree,hstar,?_,hBadCover,hProtectedCover⟩
  intro u
  have ht := ordinary_sample_inner_targets_avoid_reserved π d σ Inner Hubs u
  exact ⟨ht.2.1,ht.2.2⟩
end Oberwolfach
