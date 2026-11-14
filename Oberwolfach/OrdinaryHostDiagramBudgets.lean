module

public import Oberwolfach.OrdinaryActualDiagramOrders

@[expose] public section

/-! The diagram's finite exclusions are chosen before the host-order
threshold; only the order threshold depends on the bounded forbidden sets. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem ordinary_host_diagram_budgets (β ε d:ℝ) (hβ:0<β) (hd:0≤d) (hε:ε≤β/4)
    (r m M f:ℕ) : ∃ n₀:ℕ,1≤n₀∧∀ n:ℕ,n₀≤n→∀ W R B:ℕ,
      W≤f→R≤m→(B:ℝ)≤ε*n+f→
      (W:ℝ)+((R:ℝ)+6*M+r+6)*(d+1)<(β/2)*n∧
      (B:ℝ)+6*M<(β/2)*n := by
  let P:ℝ:=f+(m+6*M+r+6)*(d+1)+f+6*M+1
  have hP:0<P:=by dsimp [P];positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (4*P/β)
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro n hn W R B hW hR hB
  have hnR:(N:ℝ)≤n:=by exact_mod_cast (le_max_right 1 N).trans hn
  have hlarge:4*P<β*n:=by simpa only [mul_comm] using (div_lt_iff₀ hβ).mp (hN.trans_le hnR)
  have hn0:0≤(n:ℝ):=by positivity
  have hW':(W:ℝ)≤f:=by exact_mod_cast hW
  have hR':(R:ℝ)≤m:=by exact_mod_cast hR
  have hterm:=mul_le_mul_of_nonneg_right (show (R:ℝ)+6*M+r+6≤m+6*M+r+6 by linarith only [hR']) (by linarith:(0:ℝ)≤d+1)
  have hP₁:(f:ℝ)+(m+6*M+r+6)*(d+1)≤P:=by
    dsimp [P]
    have h0:0≤(f:ℝ)+6*M+1:=by positivity
    linarith only [h0]
  have hP₂:(f:ℝ)+6*M≤P:=by
    dsimp [P]
    have h0:0≤(f:ℝ)+(m+6*M+r+6)*(d+1)+1:=by positivity
    linarith only [h0]
  have hεn:=mul_le_mul_of_nonneg_right hε hn0
  constructor
  · linarith only [hW',hterm,hP₁,hlarge,hP]
  · linarith only [hB,hP₂,hεn,hlarge,hP]

end Oberwolfach
