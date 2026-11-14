module

public import Oberwolfach.BoundedDegreeSelection
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! The repeated-candidate and numerical substitutions in the ordinary
and marked cover-down callers. No factor-existence premise is discharged
by these lemmas; each caller must supply it for every allowed deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cover_down_candidate_budget (p nS a loss : ℝ)
    (hp : 0 ≤ p) (hn : 0 ≤ nS) (hna : nS ≤ 2*a) :
    4*(p*Real.sqrt p*nS) + 4*(Nat.ceil (4*(p*Real.sqrt p*nS)):ℝ) + loss
      ≤ 40*(p*Real.sqrt p)*a + 4 + loss := by
  have hs : 0 ≤ 4*(p*Real.sqrt p*nS) := by positivity
  have hc := (Nat.ceil_lt_add_one hs).le
  have hn' := mul_le_mul_of_nonneg_left hna (by positivity : 0 ≤ p*Real.sqrt p)
  nlinarith

theorem bounded_degree_selection_from_single_copy (p : ℝ) (hp : 0 < p) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V],
    n₀ ≤ Fintype.card V → ∀ (N D : ℕ) (G : SimpleGraph V)
    (S : Fin N → Finset V) (family : Fin N → Set (SimpleGraph V)),
    (∀ i j, i ≠ j → ((S i ∩ S j).card : ℝ) ≤ p^2 * Fintype.card V) →
    (∀ v, ((Finset.univ.filter (fun i => v ∈ S i)).card : ℝ) ≤ p * Fintype.card V) →
    (∀ i, ∀ K : SimpleGraph V, K ≤ spanningRestriction G (S i) →
      (∀ v, (K.degree v : ℝ) ≤ D * (p * Real.sqrt p * Fintype.card V) +
        D * (Nat.ceil (4 * (p * Real.sqrt p * Fintype.card V)) : ℝ)) →
      ∃ C : SimpleGraph V, C ∈ family i ∧ C ≤ spanningRestriction G (S i) ∧
          (∀ v, C.degree v ≤ D) ∧ Disjoint C K) →
    ∃ F : Fin N → SimpleGraph V,
      (∀ i, F i ∈ family i ∧ F i ≤ spanningRestriction G (S i) ∧ ∀ v, (F i).degree v ≤ D) ∧
      (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
      ∀ v, ((⨆ i, F i).degree v : ℝ) ≤ D * (p * Fintype.card V) := by
  obtain ⟨n₀, hn₀, hselect⟩ := bounded_degree_selection p hp
  refine ⟨n₀, hn₀, ?_⟩
  intro V _ _ hn N D G S family hinter hmem hsingle
  apply hselect V hn N D G S family hinter hmem
  intro i J hJG hJD
  exact greedy_graph_candidates (spanningRestriction G (S i)) J (family i)
    (Nat.ceil (4*(p*Real.sqrt p*Fintype.card V))) D
    (D*(p*Real.sqrt p*Fintype.card V)) hJG hJD (hsingle i)

end Oberwolfach
