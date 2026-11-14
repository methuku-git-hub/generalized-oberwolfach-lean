module

public import Oberwolfach.ClassFrequencyDomainError

@[expose] public section
/-! Bounds for the remainder after selecting retained short-cycle classes. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem retained_complement_target_bounds {K:ℕ} (long rare θ:ℝ) (f:Fin K→ℝ)
    (hθ:0≤θ) (hlong:0≤long) (hrare:0≤rare ∧ rare≤θ/100)
    (hf:∀i,0≤f i) (hsum:long+(∑i,f i)+rare=1):
    long≤1-(1-θ)*(∑i,f i) ∧
    1-(1-θ)*(∑i,f i)≤long+(101/100:ℝ)*θ :=by
  have hnon:0≤∑i,f i:=Finset.sum_nonneg (fun i _=>hf i)
  have hle:(∑i,f i)≤1:=by linarith [hrare.1]
  have hm0:0≤θ*(∑i,f i):=mul_nonneg hθ hnon
  have hmle:θ*(∑i,f i)≤θ*1:=mul_le_mul_of_nonneg_left hle hθ
  constructor <;> nlinarith [hrare.1,hrare.2]
end Oberwolfach
