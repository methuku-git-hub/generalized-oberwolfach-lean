module

public import Oberwolfach.OrdinaryCycleVertexWeight
public import Oberwolfach.OrdinaryCyclePairWeight
public import Oberwolfach.CycleIndependentSampling

@[expose] public section
/-! The original, independently sampled actual cycles have the stated vertex
and pair means. Cycle weights and probabilities are fixed before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_sample_vertex_mean {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) [DecidableEq (OrdinaryCycle G r)]
    (w:OrdinaryCycle G r→ℝ)
    (hw:∀ e:G.edgeSet,∑ C,w C*ordinaryCycleIncidence G r C e=1)
    (scale:ℝ) (hp:∀ C,0≤scale*w C) (hp1:∀ C,scale*w C≤1) (v:V):
    (FiniteLaw.pi (fun C=>FiniteLaw.retentionCoin (scale*w C) (hp C) (hp1 C))).expectation
      (independentCycleCount (fun C=>v∈C.val.val.support))=scale*(G.degree v:ℝ)/2 := by
  rw [independent_cycle_count_expectation]
  have h:=ordinary_cycle_fractional_vertex_weight G r w hw v
  have he:(∑ C:OrdinaryCycle G r,@ite ℝ (v∈C.val.val.support) (Classical.propDecidable _) (scale*w C) 0)=
      scale*(∑ C:OrdinaryCycle G r,if v∈C.val.val.support then w C else 0):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    by_cases hmem:v∈C.val.val.support <;> simp [hmem]
  rw [he,←h]
  ring

theorem ordinary_cycle_sample_pair_mean_bound {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) [DecidableEq (OrdinaryCycle G r)]
    (u v:V) (huv:u≠v) (hn:0<Fintype.card V)
    (B scale:ℝ) (hB:0≤B) (hscale:0≤scale) (w:OrdinaryCycle G r→ℝ)
    (hw:∀ C,w C≤B/(Fintype.card V:ℝ)^(r-2))
    (hp:∀ C,0≤scale*w C) (hp1:∀ C,scale*w C≤1):
    (FiniteLaw.pi (fun C=>FiniteLaw.retentionCoin (scale*w C) (hp C) (hp1 C))).expectation
      (independentCycleCount (fun C=>u∈C.val.val.support ∧ v∈C.val.val.support))≤scale*((r:ℝ)^2*B) := by
  rw [independent_cycle_count_expectation]
  have h:=ordinary_cycle_pair_weight_bound G r u v huv hn B hB w hw
  have he:(∑ C:OrdinaryCycle G r,
      @ite ℝ (u∈C.val.val.support ∧ v∈C.val.val.support) (Classical.propDecidable _) (scale*w C) 0)=
      scale*(∑ C:OrdinaryCycle G r,
        if u∈C.val.val.support ∧ v∈C.val.val.support then w C else 0):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C _
    by_cases hmem:u∈C.val.val.support ∧ v∈C.val.val.support <;> simp [hmem]
  rw [he]
  exact mul_le_mul_of_nonneg_left h hscale
end Oberwolfach
