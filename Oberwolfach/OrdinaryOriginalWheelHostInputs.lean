module

public import Oberwolfach.OriginalRegularHostFactorCount
public import Oberwolfach.Vortex

@[expose] public section
/-! The original regular-host assumptions supply the size and density
bounds used by both initial and later wheel certificates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_wheel_host_inputs {n D q:ℕ}
    (hn:0<n) (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D)
    (θ α:ℝ) (hθ:1/2≤θ) (hα:0<α) (hdegree:(θ+α)*(n:ℝ)≤D)
    (hρhi:initialIndexDensity (Fin q) D≤1):
    0<D ∧ q≤n ∧ (n:ℝ)/2≤D ∧ (θ+α/2)*(n:ℝ)≤D :=by
  have hρhi':2*(q:ℝ)/(D:ℝ)≤1:=by simpa [initialIndexDensity] using hρhi
  obtain ⟨hD,_,hq⟩:=original_regular_host_factor_count hn P hP θ α hθ hα hdegree hρhi'
  have hn0:0≤(n:ℝ):=by positivity
  have hhalf:((1/2:ℝ)*(n:ℝ))≤(θ+α)*n:=
    mul_le_mul_of_nonneg_right (by linarith : (1/2:ℝ)≤θ+α) hn0
  have hsmall:(θ+α/2)*(n:ℝ)≤(θ+α)*n:=
    mul_le_mul_of_nonneg_right (by linarith : θ+α/2≤θ+α) hn0
  exact ⟨hD,hq,by linarith,hsmall.trans hdegree⟩
end Oberwolfach
