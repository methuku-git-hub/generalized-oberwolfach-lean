module

public import Oberwolfach.OrdinaryProfileDeletionMargins

@[expose] public section

/-! Numerical substitution for the relative transformer. A linear
forbidden hub set costs its realised size; the row/edge allowance remains
bounded and is chosen only after the transformer's order bound. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem ordinary_relative_transformer_budgets (β ε d:ℝ) (hβ:0<β) (hd:0≤d)
    (hε:ε≤β/4) (r m f:ℕ) :
    ∃ n₀:ℕ,∀ n:ℕ,n₀≤n→∀ W R B e s v:ℕ,
      W≤f→R≤m→e≤m*m→s≤m*m→v≤2*(m*m)→
      (B:ℝ)≤ε*n+f→
      (W:ℝ)+((R:ℝ)+(e+s)*(r-1:ℕ)+r+7)*(d+1)<(β/2)*n ∧
      (W:ℝ)+(e+s)*(r-1:ℕ)+v*r+((r:ℝ)+4)*(d+1)<(β/2)*n ∧
      (W:ℝ)+(e+s)*(r-1:ℕ)+2*(r:ℝ)*v≤f+2*(m*m)*(r-1:ℕ)+4*(r:ℝ)*(m*m) ∧
      (B:ℝ)+e<(β/2)*n := by
  let P:ℝ:=f+(m+2*(m*m)*(r-1:ℕ)+r+7)*(d+1)+2*(m*m)*(r-1:ℕ)+2*(m*m)*r+((r:ℝ)+4)*(d+1)+f+m*m+1
  have hP:0<P:=by dsimp [P];positivity
  obtain ⟨n₀,hn₀⟩:=exists_nat_gt (4*P/β)
  refine ⟨n₀,?_⟩
  intro n hn W R B e s v hW hR he hs hv hB
  have hnR:(n₀:ℝ)≤n:=by exact_mod_cast hn
  have hlarge:4*P<β*n:=by simpa only [mul_comm] using (div_lt_iff₀ hβ).mp (hn₀.trans_le hnR)
  have hn0:0≤(n:ℝ):=by positivity
  have hW':(W:ℝ)≤f:=by exact_mod_cast hW
  have hR':(R:ℝ)≤m:=by exact_mod_cast hR
  have he':(e:ℝ)≤m*m:=by exact_mod_cast he
  have hs':(s:ℝ)≤m*m:=by exact_mod_cast hs
  have hv':(v:ℝ)≤2*(m*m):=by exact_mod_cast hv
  have hsum:(e:ℝ)+s≤2*(m*m):=by linarith only [he',hs']
  have hsumr:=mul_le_mul_of_nonneg_right hsum (by positivity:(0:ℝ)≤(r-1:ℕ))
  have hvR:=mul_le_mul_of_nonneg_right hv' (by positivity:(0:ℝ)≤r)
  have hv2R:=mul_le_mul_of_nonneg_left hv' (by positivity:(0:ℝ)≤2*r)
  have hpar:=mul_le_mul_of_nonneg_right
    (show (R:ℝ)+((e:ℝ)+s)*(r-1:ℕ)+r+7≤m+2*(m*m)*(r-1:ℕ)+r+7 by linarith only [hR',hsumr])
    (by linarith:(0:ℝ)≤d+1)
  have hP₁:(f:ℝ)+(m+2*(m*m)*(r-1:ℕ)+r+7)*(d+1)≤P:=by
    dsimp [P]
    have h1:0≤2*(m*m:ℝ)*(r-1:ℕ)+2*(m*m)*r+((r:ℝ)+4)*(d+1)+f+m*m+1:=by positivity
    linarith only [h1]
  have hP₂:(f:ℝ)+2*(m*m)*(r-1:ℕ)+2*(m*m)*r+((r:ℝ)+4)*(d+1)≤P:=by
    dsimp [P]
    have h1:0≤((m:ℝ)+2*(m*m)*(r-1:ℕ)+r+7)*(d+1)+f+m*m+1:=by positivity
    linarith only [h1]
  have hP₃:(f:ℝ)+m*m≤P:=by
    dsimp [P]
    have h1:0≤(f:ℝ)+(m+2*(m*m)*(r-1:ℕ)+r+7)*(d+1)+2*(m*m)*(r-1:ℕ)+2*(m*m)*r+((r:ℝ)+4)*(d+1)+1:=by positivity
    linarith only [h1]
  have hεn:=mul_le_mul_of_nonneg_right hε hn0
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [hW',hpar,hP₁,hlarge,hP]
  · linarith only [hW',hsumr,hvR,hP₂,hlarge,hP]
  · linarith only [hW',hsumr,hv2R]
  · linarith only [hB,hεn,he',hP₃,hlarge,hP]

end Oberwolfach
