module

public import Oberwolfach.VortexAmbientStepArbitraryRootRatio
public import Oberwolfach.FloorOrbitLookbackRatio
public import Oberwolfach.VortexGraphStep
public import Oberwolfach.FloorOrbit

@[expose] public section

/-! Successive subset choices with tests at the previous larger domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe z

theorem vortex_set_sequence_lookback {ε : ℝ} (he : 0 < ε) (he1 : ε < 1) (t:ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (V : Type z) (B₀ : Finset V) (A : V → Finset V) (ℓ : ℕ),
      (∀ i < ℓ, N ≤ floorOrbit ε B₀.card i) →
      ∃ B : ℕ → Finset V, B 0 = B₀ ∧
        (∀ i ≤ ℓ, (B i).card = floorOrbit ε B₀.card i) ∧
        ∀ i < ℓ, B (i + 1) ⊆ B i ∧
          ∀ x ∈ B (i - t),
            |((A x ∩ B (i + 1)).card : ℝ) / (B (i + 1)).card -
              ((A x ∩ B i).card : ℝ) / (B i).card| <
              ((B i).card : ℝ) ^ (-1 / 3 : ℝ) := by
  obtain ⟨N, hN⟩ := vortex_ambient_subset_step_root_ratio.{z} he he1.le (C:=(2/ε)^t) (by positivity)
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro V B₀ A ℓ
  induction ℓ with
  | zero =>
    intro _
    refine ⟨fun _ => B₀, rfl, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst i
      rfl
    · intro i hi
      omega
  | succ ℓ ih =>
    intro hsize
    obtain ⟨B, hB₀, hcard, hstep⟩ := ih (fun i hi => hsize i (by omega))
    have hcurrent : max N 2 ≤ (B ℓ).card := by rw [hcard ℓ (by omega)]; exact hsize ℓ (by omega)
    have hcurrentPos:0<floorOrbit ε B₀.card ℓ:=by
      have hh:=hcurrent
      rw [hcard ℓ (by omega)] at hh
      omega
    have hroot:((B (ℓ-t)).card:ℝ)≤(2/ε)^t*(B ℓ).card:=by
      rw [hcard (ℓ-t) (by omega),hcard ℓ (by omega)]
      exact floorOrbit_lookback_le_ratio he he1 B₀.card ℓ t hcurrentPos
    obtain ⟨C, hCB, hc, hC⟩ := hN V (B ℓ) (B (ℓ - t)) A (by omega) hroot
    let B' := Function.update B (ℓ + 1) C
    refine ⟨B', ?_, ?_, ?_⟩
    · simpa only [B', Function.update_of_ne (by omega : 0 ≠ ℓ + 1)] using hB₀
    · intro i hi
      by_cases hi' : i = ℓ + 1
      · subst i
        simp only [B', Function.update_self]
        rw [hc, hcard ℓ (by omega), floorOrbit_succ]
      · rw [show B' i = B i by simp [B', hi']]
        exact hcard i (by omega)
    · intro i hi
      by_cases hi' : i = ℓ
      · subst i
        have hcur : B' ℓ = B ℓ := by simp [B']
        have hnext : B' (ℓ + 1) = C := by simp [B']
        have hprev : B' (ℓ - t) = B (ℓ - t) := by
          apply Function.update_of_ne
          omega
        rw [hcur, hnext, hprev]
        exact ⟨hCB, hC⟩
      · have hcur : B' i = B i := by apply Function.update_of_ne; omega
        have hnext : B' (i + 1) = B (i + 1) := by apply Function.update_of_ne; omega
        have hprev : B' (i - t) = B (i - t) := by apply Function.update_of_ne; omega
        rw [hcur, hnext, hprev]
        exact hstep i (by omega)

end Oberwolfach
