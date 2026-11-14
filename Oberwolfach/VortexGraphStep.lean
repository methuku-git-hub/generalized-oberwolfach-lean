module

public import Oberwolfach.VortexSubsetStep
public import Oberwolfach.AmbientSubset

@[expose] public section

/-! A vortex step with ambient graph roots, including roots outside the current set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe w

theorem vortex_ambient_subset_step {ε : ℝ} (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type w) (B R : Finset V) (A : V → Finset V),
      N ≤ B.card → (R.card : ℝ) ≤ 2 * B.card / ε →
      ∃ C : Finset V, C ⊆ B ∧ C.card = Nat.floor (ε * B.card) ∧
        ∀ x ∈ R, |((A x ∩ C).card : ℝ) / C.card -
          ((A x ∩ B).card : ℝ) / B.card| < (B.card : ℝ) ^ (-1 / 3 : ℝ) := by
  obtain ⟨N, hN⟩ := vortex_uniform_subset_step.{w, w} he he1
  refine ⟨N, ?_⟩
  intro V B R A hn hR
  let : DecidableEq {x // x ∈ B} := Classical.decEq _
  let A' (x : V) := (A x).subtype (fun y => y ∈ B)
  obtain ⟨S, hS⟩ := hN {y // y ∈ B} (by simpa using hn) V R A' (by simpa using hR)
  let C := S.1.map (Function.Embedding.subtype (fun y => y ∈ B))
  have hc : C.card = Nat.floor (ε * B.card) := by
    simpa only [C, Finset.card_map, Fintype.card_coe] using S.2
  refine ⟨C, subtype_sample_subset B S.1, hc, ?_⟩
  intro x hx
  have hh := hS x hx
  dsimp only [A'] at hh
  rw [subtype_sample_intersection_card (A x) B S.1, subtype_restriction_card (A x) B] at hh
  simpa only [Fintype.card_coe, ← hc] using hh

theorem vortex_graph_step {ε : ℝ} (he : 0 < ε) (he1 : ε ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type w) [Fintype V] (G : SimpleGraph V) (B R : Finset V),
      N ≤ B.card → (R.card : ℝ) ≤ 2 * B.card / ε →
      ∃ C : Finset V, C ⊆ B ∧ C.card = Nat.floor (ε * B.card) ∧
        ∀ x ∈ R, |((G.neighborFinset x ∩ C).card : ℝ) / C.card -
          ((G.neighborFinset x ∩ B).card : ℝ) / B.card| < (B.card : ℝ) ^ (-1 / 3 : ℝ) := by
  obtain ⟨N, hN⟩ := vortex_ambient_subset_step.{w} he he1
  exact ⟨N, fun V _ G B R hn hR => hN V B R (fun x => G.neighborFinset x) hn hR⟩

end Oberwolfach
