module

public import Oberwolfach.SuccessorCyclicMargin

@[expose] public section
/-! The marked successor-cycle threshold is below any fixed margin above
one half, uniformly once its internal length is sufficiently large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_successor_margin_cutoff (α:ℝ) (hα:0<α):
    ∃ K:ℕ, 2≤K ∧ ∀ k:ℕ,K≤k→successorCycleRatio k+α/4≤1/2+α/2 := by
  obtain ⟨K,hK⟩:=exists_nat_gt (1/α)
  refine ⟨max K 2,le_max_right _ _,?_⟩
  intro k hk
  have hKk:K≤k := (le_max_left K 2).trans hk
  have hKkR:(K:ℝ)≤k := by exact_mod_cast hKk
  have hkreal:(1/α:ℝ)<k := lt_of_lt_of_le hK hKkR
  have hkα:1<α*(k:ℝ) := by
    have hh:=mul_lt_mul_of_pos_left hkreal hα
    simpa [ne_of_gt hα] using hh
  have hk0:(0:ℝ)≤k := Nat.cast_nonneg _
  have hden:(0:ℝ)<2*((k:ℝ)+2)-1 := by linarith
  have hrat:successorCycleRatio k≤1/2+α/4 := by
    unfold successorCycleRatio
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

theorem marked_odd_length_successor_margin (α:ℝ) (hα:0<α):
    ∃ R:ℕ, ∀ r:ℕ,R≤r→Odd r→
      ∃ k:ℕ,2≤r ∧ r+4+1=(k+2)*2 ∧
        successorCycleRatio k+α/4≤1/2+α/2 := by
  obtain ⟨K,hK,hmargin⟩:=marked_successor_margin_cutoff α hα
  refine ⟨2*K-1,?_⟩
  intro r hr hodd
  obtain ⟨j,hj⟩:=hodd
  refine ⟨j+1,?_,?_,?_⟩
  · omega
  · omega
  · apply hmargin
    omega
end Oberwolfach
