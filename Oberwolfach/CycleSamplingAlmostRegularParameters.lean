module

public import Oberwolfach.CycleSamplingIntegerDegree

@[expose] public section
/-! Uniform integer sampled-degree and linear codegree margins for an
almost-regular graph. The parameters are fixed before the graph order. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem cycle_sampling_almost_regular_parameters
    (B θ c:ℝ) (hB:1≤B) (hθ:0<θ) (hθsmall:θ≤1/20) (hc:0≤c):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ d:ℝ,(n:ℝ)/2≤d→d≤n→
      let scale:ℝ:=n/(2*B);
      ∃ D:ℕ,n≤D ∧ D≤n^2 ∧ c*n≤(8*B*c)*D/n ∧
        ∀ deg:ℝ,|deg-d|≤θ*(n:ℝ)/4→
          (1-10*θ)*D≤(1-θ)*(scale*deg/2) ∧
          (1+θ)*(scale*deg/2)≤D := by
  have hBpos:0<B := by linarith
  let N:=Nat.ceil (8*B*(1+1/θ)+1)
  refine ⟨N,?_⟩
  intro n hn d hdlo hdhi scale
  let T:ℝ:=scale*d/2
  have hN : 8*B*(1+1/θ)+1≤(n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hid : 8*B*(1+1/θ) = 8*B+8*B/θ := by ring
  rw [hid] at hN
  have hn1:1≤(n:ℝ) := by
    have hh:0≤8*B+8*B/θ := by positivity
    linarith
  have hnpos:0<(n:ℝ) := by linarith
  have hnB:8*B≤(n:ℝ) := by
    have hh:0≤8*B/θ := by positivity
    nlinarith
  have hnTheta:8*B/θ≤(n:ℝ) := by
    have hh:0≤8*B := by positivity
    nlinarith
  have hscale:0≤scale := by dsimp [scale];positivity
  have hdpos:0<d := by linarith
  have hT:0≤T := by dsimp [T]; positivity
  have hlo:n^2/(8*B)≤T := by
    have hh:=mul_le_mul_of_nonneg_left hdlo hscale
    have hid:scale*((n:ℝ)/2)/2=(n:ℝ)^2/(8*B) := by
      dsimp [scale];field_simp;ring
    rw [←hid]
    dsimp [T]
    linarith only [hh]
  have hhi:T≤(n:ℝ)^2/(4*B) := by
    have hh:=mul_le_mul_of_nonneg_left hdhi hscale
    have hid:scale*(n:ℝ)/2=(n:ℝ)^2/(4*B) := by
      dsimp [scale];field_simp;ring
    rw [←hid]
    dsimp [T]
    linarith only [hh]
  have hlarge:1≤θ*T := by
    have hdiv: (n:ℝ)/(8*B)≥1/θ := (le_div_iff₀ (by positivity)).2 (by
      have heq:(1/θ)*(8*B)=8*B/θ := by ring
      rw [heq]
      exact hnTheta)
    have hquad:(n:ℝ)/(8*B)≤(n:ℝ)^2/(8*B) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have hbase:1/θ≤T := hdiv.trans (hquad.trans hlo)
    have hh':=mul_le_mul_of_nonneg_left hbase hθ.le
    have : θ*(1/θ)=1 := by field_simp
    linarith
  obtain ⟨D,hDlo,hDhi,hrows⟩:=cycle_sampling_integer_degree θ T hθ.le (by linarith) hT hlarge
  have hDreal:(n:ℝ)≤D := by
    have hdiv:(1:ℝ)≤(n:ℝ)/(8*B):=(le_div_iff₀ (by positivity)).2 (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hdiv hnpos.le
    have hid:(n:ℝ)*((n:ℝ)/(8*B))=(n:ℝ)^2/(8*B) := by ring
    have hh' : (n:ℝ)≤(n:ℝ)^2/(8*B) := by rw [←hid];linarith
    have hTlo:T≤(1+2*θ)*T := by nlinarith
    exact hh'.trans (hlo.trans (hTlo.trans hDlo))
  have hDn:n≤D := by exact_mod_cast hDreal
  have hDsq:(D:ℝ)≤(n:ℝ)^2 := by
    have ht:T≤(n:ℝ)^2/4 := by
      have hBden:4≤4*B:=by linarith
      exact hhi.trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hBden)
    have hm:=mul_le_mul_of_nonneg_left ht (show 0≤1+3*θ by positivity)
    nlinarith [sq_nonneg (n:ℝ)]
  have hDnat:D≤n^2 := by exact_mod_cast hDsq
  have hcode:c*n≤(8*B*c)*D/n := by
    have hDquad:(n:ℝ)^2/(8*B)≤D := hlo.trans (by
      have hh:T≤(1+2*θ)*T:=by nlinarith
      exact hh.trans hDlo)
    have hh:=mul_le_mul_of_nonneg_left hDquad (show 0≤8*B*c by positivity)
    have hd: (8*B*c)*((n:ℝ)^2/(8*B))/(n:ℝ)=c*n := by
      field_simp
    rw [←hd]
    exact div_le_div_of_nonneg_right hh hnpos.le
  refine ⟨D,hDn,hDnat,hcode,?_⟩
  intro deg hdeg
  obtain ⟨hdeglo,hdeghi⟩:=abs_le.mp hdeg
  have hdtheta:θ*(n:ℝ)/4≤θ*d/2 := by
    have hh:=mul_le_mul_of_nonneg_left hdlo hθ.le
    nlinarith
  have hdeglo':(1-θ/2)*d≤deg := by nlinarith
  have hdeghi':deg≤(1+θ/2)*d := by nlinarith
  apply hrows (scale*deg/2)
  · have hh:=mul_le_mul_of_nonneg_left hdeglo' hscale
    dsimp [T];nlinarith only [hh]
  · have hh:=mul_le_mul_of_nonneg_left hdeghi' hscale
    dsimp [T];nlinarith only [hh]
end Oberwolfach
