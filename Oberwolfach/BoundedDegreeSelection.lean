module

public import Oberwolfach.BoundedDegreeSelectionFinite
public import Oberwolfach.SelectionPotentialOrder

@[expose] public section

/-! The manuscript's selection lemma, with the order threshold chosen
before the graph, number of support sets, and candidate families. The
proof uses conditional averaging of a common potential and therefore
requires no independence between successive choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mul_sqrt_eq_rpow_three_halves (p : ℝ) (hp : 0 < p) :
    p * Real.sqrt p = p ^ (3/2 : ℝ) := by
  have hh := Real.rpow_add hp 1 (1/2)
  norm_num at hh
  simpa only [Real.sqrt_eq_rpow] using hh.symm

theorem bounded_degree_selection (p : ℝ) (hp : 0 < p) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V],
    n₀ ≤ Fintype.card V → ∀ (N D : ℕ) (G : SimpleGraph V)
    (S : Fin N → Finset V) (family : Fin N → Set (SimpleGraph V)),
    (∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ p^2 * Fintype.card V) →
    (∀ v, ((Finset.univ.filter (fun i => v ∈ S i)).card : ℝ) ≤ p * Fintype.card V) →
    (∀ i, ∀ J : SimpleGraph V, J ≤ spanningRestriction G (S i) →
      (∀ v, (J.degree v : ℝ) ≤ D * (p * Real.sqrt p * Fintype.card V)) →
      ∃ C : Fin (Nat.ceil (4 * (p * Real.sqrt p * Fintype.card V))) → SimpleGraph V,
        (∀ a, C a ∈ family i ∧ C a ≤ spanningRestriction G (S i) ∧
          (∀ v, (C a).degree v ≤ D) ∧ Disjoint (C a) J) ∧
        (∀ a b, a ≠ b → Disjoint (C a) (C b))) →
    ∃ F : Fin N → SimpleGraph V,
      (∀ i, F i ∈ family i ∧ F i ≤ spanningRestriction G (S i) ∧ ∀ v, (F i).degree v ≤ D) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
      ∀ v, ((⨆ i, F i).degree v : ℝ) ≤ D * (p * Fintype.card V) := by
  obtain ⟨n₀, hn₀, horder⟩ := bounded_degree_selection_order p hp
  refine ⟨n₀, hn₀, ?_⟩
  intro V _ _ hn N D G S family hinter hmem hcandidates
  let n := Fintype.card V
  let s := p * Real.sqrt p * n
  let t := Nat.ceil (4 * s)
  let B := Nat.floor s + 1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from lt_of_lt_of_le (by omega) hn)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hscale := selection_candidate_scale p n hp hnpos
  change 0 < t ∧ p^2 * n ≤ (Real.sqrt p / 4) * t ∧ (Nat.floor s : ℝ) ≤ s at hscale
  have hcount : (Fintype.card (SelectionVertexTest S) : ℝ) ≤ p * (n : ℝ)^2 := by
    have hh := selectionVertexTest_card_le S (p*n) hmem
    convert hh using 1 <;> dsimp [n] <;> ring
  have hremaining (x : SelectionVertexTest S) :
      (selectionRemaining (graphSelectionActive S) 0 x : ℝ) ≤ p*n := by
    have hh : (selectionRemaining (graphSelectionActive S) 0 x : ℝ) ≤
      ((Finset.univ.filter (fun i => x.val.2 ∈ S i)).card : ℝ) := by
      exact_mod_cast graphSelection_remaining_le S 0 x
    exact hh.trans (hmem x.val.2)
  have hsmall := horder n hn (SelectionVertexTest S) N (graphSelectionActive S) hcount hremaining
  exact bounded_degree_selection_finite N D t B hscale.1 (Real.sqrt p/4) s (p*n)
    (by positivity) hs (by simpa [B] using hscale.2.2) G S family
    (fun i j hij => (hinter i j hij).trans hscale.2.1) hmem hsmall hcandidates

end Oberwolfach
