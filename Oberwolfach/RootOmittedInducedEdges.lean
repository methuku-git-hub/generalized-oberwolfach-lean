module

public import Oberwolfach.InducedFractionalCycles
public import Oberwolfach.EdgeRetention
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! The physical edges tested by a bounded induced set, with its prescribed
root edge omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def rootOmittedInducedEdges (P : SimpleGraph V) (S : Finset V) (root : Sym2 V) : Finset (Sym2 V) :=
  (spanningRestriction P S).edgeFinset.erase root

theorem mem_rootOmittedInducedEdges (P : SimpleGraph V) (S : Finset V) (root : Sym2 V) (z t : V) :
    s(z,t)∈rootOmittedInducedEdges P S root ↔
      s(z,t)≠root ∧ P.Adj z t ∧ z∈S ∧ t∈S := by
  simp only [rootOmittedInducedEdges,Finset.mem_erase,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,spanningRestriction_adj]

theorem rootOmittedInducedEdges_card (P : SimpleGraph V) (S : Finset V) (root : Sym2 V) :
    (rootOmittedInducedEdges P S root).card≤S.card^2 := by
  calc
    _ ≤ ((S×ˢS).image (fun a=>s(a.1,a.2))).card := by
      apply Finset.card_le_card
      intro e he
      induction e using Sym2.ind with
      | _ z t=>
        obtain ⟨hne,hzt,hz,ht⟩ := (mem_rootOmittedInducedEdges P S root z t).mp he
        exact Finset.mem_image.mpr ⟨(z,t),Finset.mem_product.mpr ⟨hz,ht⟩,rfl⟩
    _ ≤ (S×ˢS).card := Finset.card_image_le
    _ = S.card^2 := by simp only [Finset.card_product,pow_two]

/-- This equivalence does not require the root trial to succeed. -/
theorem rootOmittedInducedEdges_survive (P : SimpleGraph V) (S : Finset V) (x y : V)
    (σ : Sym2 V → Bool) :
    (∀ e∈rootOmittedInducedEdges P S s(x,y),σ e=true) ↔
      ∀ z∈S,∀ t∈S,P.Adj z t → s(z,t)≠s(x,y) → (retainedGraph P σ).Adj z t := by
  constructor
  · intro h z hz t ht hzt hne
    exact ⟨hzt,h _ ((mem_rootOmittedInducedEdges P S s(x,y) z t).mpr ⟨hne,hzt,hz,ht⟩)⟩
  · intro h e he
    induction e using Sym2.ind with
    | _ z t=>
      obtain ⟨hne,hzt,hz,ht⟩ := (mem_rootOmittedInducedEdges P S s(x,y) z t).mp he
      exact (h z hz t ht hzt hne).2

end Oberwolfach
