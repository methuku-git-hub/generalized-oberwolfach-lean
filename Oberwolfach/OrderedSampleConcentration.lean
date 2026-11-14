module

public import Oberwolfach.OrderedSampleCoupling
public import Oberwolfach.UniformExposure

@[expose] public section

/-! The exposure martingale for a uniformly random ordered sample.
Changing one exposed label is coupled by a transposition of the remaining labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem orderedSample_cons_law {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty V] [Nonempty (Fin (r + 1) ↪ V)]
    [∀ x : V, Nonempty (Fin r ↪ {y : V // y ≠ x})] :
    ((FiniteLaw.uniform V).sigma (fun x => FiniteLaw.uniform (Fin r ↪ {y : V // y ≠ x}))).map
      (fun p => embeddingCons p.1 p.2) = FiniteLaw.uniform (Fin (r + 1) ↪ V) := by
  rw [finiteLaw_uniform_sigma_equal_fibres
    ((Fintype.card V - 1).descFactorial r) (orderedSample_fibre_card r)]
  exact finiteLaw_uniform_map_equiv (orderedSampleFirstEquiv V r).symm

theorem orderedSample_mgf
    {r : ℕ} {V : Type*} [Fintype V]
    [Nonempty (Fin r ↪ V)] (hr : r ≤ Fintype.card V)
    (f : (Fin r ↪ V) → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexchange : ∀ σ u v, |f σ - f (σ.trans (Equiv.swap u v).toEmbedding)| ≤ b)
    (t : ℝ) :
    (FiniteLaw.uniform (Fin r ↪ V)).expectation
      (fun σ => Real.exp (t * (f σ - (FiniteLaw.uniform (Fin r ↪ V)).expectation f))) ≤
      Real.exp (t ^ 2 * (r : ℝ) * b ^ 2 / 8) := by
  induction r generalizing V t with
  | zero =>
    let σ₀ : Fin 0 ↪ V := Function.Embedding.ofIsEmpty
    have hf : f = fun _ => f σ₀ := by
      funext σ
      have hσ : σ = σ₀ := by ext i; exact Fin.elim0 i
      rw [hσ]
    rw [hf, finiteLaw_expectation_const]
    simp [finiteLaw_expectation_const]
  | succ r ih =>
    let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let (x : V) : Nonempty (Fin r ↪ {y : V // y ≠ x}) := orderedSample_fibre_nonempty hr x
    let ν (x : V) := FiniteLaw.uniform (Fin r ↪ {y : V // y ≠ x})
    let X (p : Σ x : V, Fin r ↪ {y : V // y ≠ x}) := f (embeddingCons p.1 p.2)
    have hdiam (x y : V) : |(ν x).expectation (fun z => X ⟨x,z⟩) -
        (ν y).expectation (fun z => X ⟨y,z⟩)| ≤ b := by
      apply finiteLaw_uniform_expectation_difference_of_equiv
        (Equiv.embeddingCongr (Equiv.refl (Fin r)) (remainingSwap x y))
      intro σ
      change |f (embeddingCons x σ) -
        f (embeddingCons y (σ.trans (remainingSwap x y).toEmbedding))| ≤ b
      rw [embeddingCons_remainingSwap]
      exact hexchange (embeddingCons x σ) x y
    have htail (x : V) (u : ℝ) : (ν x).expectation (fun z =>
        Real.exp (u * (X ⟨x,z⟩ - (ν x).expectation (fun w => X ⟨x,w⟩)))) ≤
          Real.exp (u ^ 2 * ((r : ℝ) * b ^ 2) / 8) := by
      let : DecidableEq {y : V // y ≠ x} := Classical.decEq _
      have he : ∀ σ u v, |f (embeddingCons x σ) -
          f (embeddingCons x (σ.trans (Equiv.swap u v).toEmbedding))| ≤ b := by
        intro σ u v
        rw [embeddingCons_swap_tail]
        exact hexchange (embeddingCons x σ) u.1 v.1
      have hh := ih (V := {y : V // y ≠ x})
        (by rw [remainingLabels_card]; omega) (fun σ => f (embeddingCons x σ)) he u
      simpa only [ν, X, mul_assoc] using hh
    have hstep := finiteLaw_sigma_mgf_bound (FiniteLaw.uniform V) ν X hb hdiam htail t
    have hlaw := orderedSample_cons_law (V := V) (r := r)
    have he (Y : (Fin (r + 1) ↪ V) → ℝ) :
        ((FiniteLaw.uniform V).sigma ν).expectation (fun p => Y (embeddingCons p.1 p.2)) =
        (FiniteLaw.uniform (Fin (r + 1) ↪ V)).expectation Y := by
      have hm := finiteLaw_map_expectation ((FiniteLaw.uniform V).sigma ν)
        (fun p => embeddingCons p.1 p.2) Y
      rw [hlaw] at hm
      exact hm.symm
    have hmean : ((FiniteLaw.uniform V).sigma ν).expectation X =
        (FiniteLaw.uniform (Fin (r + 1) ↪ V)).expectation f := he f
    have hcenter : ((FiniteLaw.uniform V).sigma ν).expectation
        (fun z => Real.exp (t * (X z - ((FiniteLaw.uniform V).sigma ν).expectation X))) =
        (FiniteLaw.uniform (Fin (r + 1) ↪ V)).expectation
          (fun σ => Real.exp (t * (f σ - (FiniteLaw.uniform (Fin (r + 1) ↪ V)).expectation f))) := by
      rw [hmean]
      exact he (fun σ => Real.exp (t * (f σ -
        (FiniteLaw.uniform (Fin (r + 1) ↪ V)).expectation f)))
    rw [hcenter] at hstep
    convert hstep using 1
    congr 1
    push_cast
    ring

theorem orderedSample_absolute_tail
    {r : ℕ} {V : Type*} [Fintype V]
    [Nonempty (Fin r ↪ V)] (hr : r ≤ Fintype.card V)
    (f : (Fin r ↪ V) → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hexchange : ∀ σ u v, |f σ - f (σ.trans (Equiv.swap u v).toEmbedding)| ≤ b)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.uniform (Fin r ↪ V)).probability
      (fun σ => t ≤ |f σ - (FiniteLaw.uniform (Fin r ↪ V)).expectation f|) ≤
      2 * Real.exp (-2 * t ^ 2 / ((r : ℝ) * b ^ 2)) := by
  apply finiteLaw_mgf_absolute_tail _ _ (by positivity) _ ht
  intro u
  simpa only [mul_assoc] using orderedSample_mgf hr f hb hexchange u

end Oberwolfach
