module

public import Oberwolfach.CycleSamplingDegreeMargins

@[expose] public section
/-! One integer upper degree is fixed before the random sample. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem cycle_sampling_integer_degree
    (θ T:ℝ) (hθ:0≤θ) (hθhi:θ≤1/10) (hT:0≤T) (hlarge:1≤θ*T):
    ∃ D:ℕ,(1+2*θ)*T≤D ∧ D≤(1+3*θ)*T ∧
      ∀ m:ℝ,(1-θ/2)*T≤m→m≤(1+θ/2)*T→
        (1-10*θ)*D≤(1-θ)*m ∧ (1+θ)*m≤D := by
  let D:=Nat.ceil ((1+2*θ)*T)
  have hnon:0≤(1+2*θ)*T:=by positivity
  have hlo:(1+2*θ)*T≤D:=Nat.le_ceil _
  have hhi:(D:ℝ)≤(1+3*θ)*T:=by
    have hceil:(D:ℝ)≤(1+2*θ)*T+1:=(Nat.ceil_lt_add_one hnon).le
    nlinarith only [hceil,hlarge]
  refine ⟨D,hlo,hhi,?_⟩
  intro m hml hmh
  exact cycle_sampling_degree_margins θ T D m hθ hθhi hT hml hmh hlo hhi
end Oberwolfach
