module

public import Oberwolfach.OrdinaryAboveThresholdAlmostRegularCyclePacking

@[expose] public section
/-! Arbitrarily small uncovered fraction, with the allowed regularity error
and graph order chosen before the graph. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_above_threshold_almost_regular_near_spanning_cycles
    (r:ℕ) (hr:3≤r) (α ε:ℝ) (hα:0<α) (hε:0<ε):
    ∃ η:ℝ,0<η ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V),
      N≤Fintype.card V→∀ d:ℝ,(Fintype.card V:ℝ)/2≤d→d≤Fintype.card V→
      (∀ v,(cycleThreshold r+α)*Fintype.card V≤(G.degree v:ℝ))→
      (∀ v,|(G.degree v:ℝ)-d|≤η*(Fintype.card V:ℝ))→
      ∃ M:Finset (OrdinaryCycle G r),
        (∀ C∈M,∀ C'∈M,C≠C'→Disjoint C.val.val.support.toFinset C'.val.val.support.toFinset) ∧
        (1-ε)*Fintype.card V≤(r:ℝ)*M.card := by
  let ε₀:=min ε 1
  have he0:0<ε₀:=by dsimp [ε₀];positivity
  have he1:ε₀≤1:=min_le_right _ _
  have heε:ε₀≤ε:=min_le_left _ _
  let θ:=ε₀/40
  let γ:=ε₀/2
  let η:=ε₀/160
  have hθ:0<θ:=by dsimp [θ];positivity
  have hθsmall:θ≤1/20:=by dsimp [θ];linarith
  have hγ:0<γ:=by dsimp [γ];positivity
  have hγ1:γ≤1:=by dsimp [γ];linarith
  have hη:0<η:=by dsimp [η];positivity
  have heq:η=θ/4:=by dsimp [η,θ];ring
  obtain ⟨N,hpack⟩:=ordinary_above_threshold_almost_regular_cycle_packing r hr α θ γ hα hθ hθsmall hγ hγ1
  refine ⟨η,hη,N,?_⟩
  intro V _ _ G hn d hdlo hdhi hdeg hreg
  obtain ⟨M,hdisj,hcover⟩:=hpack V G hn d hdlo hdhi hdeg (fun v=>by have hh:=hreg v; rw [heq] at hh; nlinarith only [hh])
  refine ⟨M,hdisj,?_⟩
  have hcoeff:1-ε≤(1-γ)*(1-10*θ):=by
    dsimp [γ,θ]
    nlinarith [sq_nonneg ε₀]
  exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)).trans hcover
end Oberwolfach
