module

public import Oberwolfach.SuccessorPreweightExistence
public import Oberwolfach.SuccessorSequenceWeights

@[expose] public section
/-! Weights built for a stronger density margin remain valid for a weaker
margin, with the same weights and tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem successor_weight_lower_mono (k:ℕ) (a b:ℝ) (ha:0≤a) (hab:a≤b):
    successorWeightLower k a≤successorWeightLower k b:=by
  unfold successorWeightLower cyclicSectorLower
  have hk:(0:ℝ)<(k+2:ℕ):=by positivity
  have hk':(0:ℝ)<(k+1:ℕ):=by positivity
  have hf:(0:ℝ)<2*(k+2:ℝ)-1:=by have hkn:0≤(k:ℝ):=Nat.cast_nonneg _; linarith
  have h0:0≤(2*(k+2:ℝ)-1)*(a/2)/(k+2):=by positivity
  have h1:(2*(k+2:ℝ)-1)*(a/2)/(k+2)≤(2*(k+2:ℝ)-1)*(b/2)/(k+2):=by gcongr
  gcongr

theorem successor_weight_upper_antitone (k:ℕ) (a b:ℝ) (ha:0<a) (hab:a≤b):
    successorWeightUpper k b≤successorWeightUpper k a:=by
  unfold successorWeightUpper cyclicSectorUpper
  have hk:(0:ℝ)<(k+2:ℕ):=by positivity
  have hk':(0:ℝ)<(k+1:ℕ):=by positivity
  have hf:(0:ℝ)<2*(k+2:ℝ)-1:=by have hkn:0≤(k:ℝ):=Nat.cast_nonneg _; linarith
  have hb:0<b:=lt_of_lt_of_le ha hab
  have h0:0<(k+1:ℝ)*((2*(k+2:ℝ)-1)*(a/2)/(k+2))*((k+2:ℝ)/(2*(k+2:ℝ)-1)):=by positivity
  have h1:(k+1:ℝ)*((2*(k+2:ℝ)-1)*(a/2)/(k+2))*((k+2:ℝ)/(2*(k+2:ℝ)-1))≤
      (k+1:ℝ)*((2*(k+2:ℝ)-1)*(b/2)/(k+2))*((k+2:ℝ)/(2*(k+2:ℝ)-1)):=by gcongr
  gcongr

theorem successor_sequence_weight_bounds_mono
    {V:Type} [Fintype V] {c:ℕ} (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (D τ A B A' B':ℝ) (w:(Fin c→V)→ℝ) (hA:A'≤A) (hB:B≤B')
    (h:SuccessorSequenceWeightConditions G π d D τ A B w):
    SuccessorSequenceWeightConditions G π d D τ A' B' w:=by
  refine ⟨h.nonneg,h.support,?_,?_,h.edges,h.positions⟩
  · intro f
    exact (h.upper f).trans (div_le_div_of_nonneg_right hB (by positivity))
  · intro f hf hs
    exact (div_le_div_of_nonneg_right hA (by positivity)).trans (h.lower f hf hs)
theorem successor_sequence_weights_weaken_margin
    {V:Type} [Fintype V] {c:ℕ} (G:SimpleGraph V) (π:Equiv.Perm V) (d k:ℕ)
    (D τ a b:ℝ) (w:(Fin c→V)→ℝ) (ha:0<a) (hab:a≤b)
    (h:SuccessorSequenceWeightConditions G π d D τ (successorWeightLower k b) (successorWeightUpper k b) w):
    SuccessorSequenceWeightConditions G π d D τ (successorWeightLower k a) (successorWeightUpper k a) w:=
  successor_sequence_weight_bounds_mono G π d D τ _ _ _ _ w
    (successor_weight_lower_mono k a b ha.le hab) (successor_weight_upper_antitone k a b ha hab) h
end Oberwolfach
