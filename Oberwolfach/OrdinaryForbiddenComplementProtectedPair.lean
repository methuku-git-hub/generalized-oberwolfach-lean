module

public import Oberwolfach.OrdinaryComplementSampleAgreementAndReserve
public import Oberwolfach.OrdinaryForbiddenCompletionInputs

@[expose] public section
/-! Covering the enlarged required graph gives both exact protected-pair
agreement and a forbidden-edge-free complement, on the same embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_forbidden_complement_protected_pair_and_reservoir {n q : ℕ}
    (Target Sample Reference Protect Bad : SimpleGraph (Fin n)) (Inner : Finset (Fin n)) (Hubs : Finset (Fin q))
    (Href : Fin n → Fin q → Prop) (Fs : Fin q → SimpleGraph (Fin n))
    (C : ∀ u, Finset (Fs u).ConnectedComponent)
    (f : ∀ u, {x : Fin n // (Fs u).connectedComponentMk x ∉ C u} ↪ Fin n)
    (Old New : Fin q → Finset (Sym2 (Fin n)))
    (A : Finset (Sym2 (Fin n) ⊕ (Fin n × Fin q)))
    (hRef : Reference ≤ Sample)
    (hAgreement : ∀ v ∈ Inner, ∀ w ∈ Inner, (Target.Adj v w ↔ Sample.Adj v w))
    (hProtect : Protect ≤ Reference) (hInnerProtect : spanningRestriction Reference Inner ≤ Protect)
    (hA : A ⊆ ordinaryHostResources Reference Href)
    (hReserveProtect : ordinaryResourceRim Reference A ≤ Protect)
    (hReserveTarget : ordinaryResourceRim Reference A ≤ Target)
    (hRim : ∀ u x y, ((Fs u).induce {x | (Fs u).connectedComponentMk x ∉ C u}).Adj x y →
      (Target \ Protect).Adj (f u x) (f u y))
    (hpartition : ∀ u, (((Fs u).induce {x | (Fs u).connectedComponentMk x ∉ C u}).edgeFinset).image
      (Sym2.map (f u)) = Old u ∪ New u)
    (hcover : ∀ e ∈ (ordinaryForbiddenRequired Target Sample Reference Bad Inner).edgeFinset, ∃ u, e ∈ New u)
    (hAvoid : ∀ u x, ¬Href (f u x) u)
    (hSpokeCover : ∀ u v, v ∈ ordinaryInnerSpokeTargets Inner Hubs Href u → ∃ x, f u x = v) :
    let R := Target \ ordinaryEmbeddedComplements Fs C f
    let S := fun v u => v ∉ Set.range (f u);
    A ⊆ ordinaryHostResources R S ∧
    (∀ v ∈ Inner, ∀ w ∈ Inner, (R.Adj v w ↔ Reference.Adj v w)) ∧
    (∀ v ∈ Inner, ∀ u ∈ Hubs, (S v u ↔ Href v u)) ∧ Disjoint R Bad := by
  intro R S
  have hcover' : ∀ e ∈ (ordinaryProtectedRequired Target Sample Reference Inner).edgeFinset, ∃ u, e ∈ New u := by
    intro e he
    apply hcover e
    exact SimpleGraph.edgeFinset_mono (show ordinaryProtectedRequired Target Sample Reference Inner ≤
      ordinaryForbiddenRequired Target Sample Reference Bad Inner from le_sup_left) he
  have hp := ordinary_complement_protected_pair_and_reservoir_of_sample_agreement Target Sample Reference Protect Inner Hubs
    Href Fs C f Old New A hRef hAgreement hProtect hInnerProtect hA hReserveProtect hReserveTarget
    hRim hpartition hcover' hAvoid hSpokeCover
  have hf := ordinary_forbidden_placement_completion_inputs Target Sample Reference Bad Inner Fs C f Old New hpartition hcover
  exact ⟨hp.1, hp.2.1, hp.2.2, hf.2.1⟩
end Oberwolfach
