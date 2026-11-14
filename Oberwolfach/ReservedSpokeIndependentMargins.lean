module

public import Oberwolfach.ReservedSpokeFlexibleTheta
public import Oberwolfach.PartitionMargins

@[expose] public section
/-! Reserved ordinary labels yield a positive list parameter independent of θ and m. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reserved_spoke_independent_margins
    (γ p η:ℝ) (hγ:0<γ) (hp:0<p) (hη:0<η):
    ∃βraw β θ δ:ℝ,0<βraw ∧ 0<β ∧ β≤1 ∧ βraw=4*β ∧
      0<θ ∧ θ≤η ∧ θ≤1/100 ∧ 0<δ ∧ 10*θ≤δ ∧ δ≤(β/100)^2 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→βraw*n+(n:ℝ)^(3/4:ℝ)≤γ*p^2*n/100:=by
  let q:ℝ:=γ*p^2/100
  have hq:0<q:=by dsimp [q]; positivity
  let βraw:ℝ:=min 1 (q/2)
  let β:ℝ:=βraw/4
  have hr:0<βraw:=lt_min (by norm_num) (by positivity)
  have hr1:βraw≤1:=min_le_left _ _
  have hrq:βraw≤q/2:=min_le_right _ _
  have hβ:0<β:=by dsimp [β]; positivity
  have hβ1:β≤1:=by dsimp [β];linarith
  obtain ⟨θ,δ,hθ,hθη,hθ1,hδ,hθδ,hδbound⟩:=reserved_spoke_residual_parameter_choice_below β η hβ hβ1 hη
  obtain ⟨N,hN⟩:=eventually_sublinear_le_linear (p:=3/4) (ε:=q/2) (by norm_num) (by positivity)
  refine ⟨βraw,β,θ,δ,hr,hβ,hβ1,?_,hθ,hθη,hθ1,hδ,hθδ,hδbound,N,?_⟩
  · dsimp [β]; ring
  · intro n hn
    have hs:=hN n hn
    have hh:=mul_le_mul_of_nonneg_right hrq (Nat.cast_nonneg n)
    dsimp [q] at *
    nlinarith
end Oberwolfach
