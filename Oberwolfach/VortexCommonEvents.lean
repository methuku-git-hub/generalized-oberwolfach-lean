module

public import Oberwolfach.VortexSummation
public import Oberwolfach.GoodPlacementEvents
public import Oberwolfach.CommonEvents

@[expose] public section

/-! One event at all fixed vortex levels. The probability space is common
to every level, and no independence between the level events is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_inverse_sum_bound (ε M : ℝ) (hε : 0<ε) (hε1 : ε<1) (hM : 0<M)
    (n : ℕ→ℝ) (k : ℕ) (hn : ∀ i≤k,0<n i)
    (hstep : ∀ i<k,n (i+1)≤ε*n i) (hlast : M≤n k) :
    ∑ i∈Finset.range (k+1),1/n i≤1/((1-ε)*M) := by
  have hh := geometric_chain_sum_bound hε.le hε1 (fun i=>1/n i) k
    (fun i hi=>by have := hn i hi;positivity) (by
      intro i hi
      have hi0 := hn i (by omega)
      have hi1 := hn (i+1) (by omega)
      apply (div_le_iff₀ hi0).mpr
      have hs : 1≤ε*n i/n (i+1) := (le_div_iff₀ hi1).mpr (by simpa using hstep i hi)
      nlinarith only [hs,show ε*n i/n (i+1)=(ε*(1/n (i+1)))*n i by ring])
  calc
    _ ≤ (1/n k)/(1-ε) := hh
    _ ≤ (1/M)/(1-ε) := div_le_div_of_nonneg_right
      (one_div_le_one_div_of_le hM hlast) (by linarith)
    _ = _ := by rw [div_div];congr 1;ring

theorem vortex_fixed_domain_common_event {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (ε M : ℝ) (hε : 0<ε) (hε1 : ε<1) (hM : 0<M)
    (n : ℕ→ℝ) (k : ℕ) (hn : ∀ i≤k,0<n i)
    (hstep : ∀ i<k,n (i+1)≤ε*n i) (hlast : M≤n k)
    (Good : ℕ→Ω→Prop) (hGood : ∀ i≤k,1-1/n i≤μ.probability (Good i)) :
    1-1/((1-ε)*M)≤μ.probability (fun ω=>∀ i≤k,Good i ω) := by
  have hh := finiteLaw_common_event_lower μ (Finset.range (k+1)) (fun i ω=>¬Good i ω)
    (fun i=>1/n i) (by
      intro i hi
      have h := hGood i (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi)
      have hc := finiteLaw_probability_compl μ (Good i)
      linarith)
  have he : (fun ω=>∀ i∈Finset.range (k+1),¬¬Good i ω)=(fun ω=>∀ i≤k,Good i ω) := by
    funext ω
    apply propext
    simp only [Finset.mem_range,not_not,Nat.lt_succ_iff]
  rw [he] at hh
  have hs := vortex_inverse_sum_bound ε M hε hε1 hM n k hn hstep hlast
  linarith only [hh,hs]

end Oberwolfach
