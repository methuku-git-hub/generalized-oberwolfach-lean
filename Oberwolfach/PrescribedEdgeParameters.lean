module

public import Oberwolfach.SuccessiveRootParameters

@[expose] public section

/-! Explicit cap choices for a quadratic number of prescribed edges.
The permitted edge density is chosen before the forbidden degree; the
order threshold is chosen afterwards. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach

theorem prescribed_edge_cap_parameters (r:ℕ) (β:ℝ) (hβ:0<β) :
    ∃ α₀:ℝ,0<α₀ ∧ α₀≤1 ∧ ∀ α L:ℝ,0<α → α≤α₀ → 0≤L →
      ∃ m₀:ℕ,∀ m N D:ℕ,m₀≤m → (N:ℝ)≤α^2*m^2 → (D:ℝ)≤α*m →
      let K:=⌈α*m⌉₊
      0<K ∧ (K:ℝ)≤2*α*m ∧
      (N*r:ℕ)/(K:ℝ)+(K*r:ℕ)+((r:ℝ)+2)*(L+1)+4*(K+D:ℕ)<β*m ∧
      (N:ℝ)/K+2*(K+D:ℕ)<β*m ∧
      (N*r:ℕ)/(K:ℝ)+(D*r:ℕ)+((r:ℝ)+2)*(L+1)+8*(K+D:ℕ)<β*m :=by
  let c:ℝ:=3*r+24
  have hc:0<c:=by dsimp [c];positivity
  let α₀:=min 1 (β/(4*c))
  have hα₀:0<α₀:=by dsimp [α₀];positivity
  refine ⟨α₀,hα₀,min_le_left _ _,?_⟩
  intro α L hα hαsmall hL
  obtain ⟨M₁,hM₁⟩:=exists_nat_gt (1/α)
  obtain ⟨M₂,hM₂⟩:=exists_nat_gt (4*((r:ℝ)+2)*(L+1)/β)
  refine ⟨max M₁ M₂,?_⟩
  intro m N D hm hN hD
  dsimp only
  let K:=⌈α*m⌉₊
  have hαm:1<α*m:=by
    have h:1/α<(m:ℝ):=hM₁.trans_le (Nat.cast_le.mpr (show M₁≤m by omega))
    have hh:=(div_lt_iff₀ hα).mp h
    nlinarith only [hh]
  have hmpos:(0:ℝ)<m:=by nlinarith only [hαm,hα.le]
  have hKlo:α*m≤(K:ℝ):=Nat.le_ceil _
  have hKpos:(0:ℝ)<K:=lt_of_lt_of_le (by linarith only [hαm]) hKlo
  have hKhi:(K:ℝ)≤2*α*m:=by
    have h:=Nat.ceil_lt_add_one (show 0≤α*m by linarith only [hαm])
    change (K:ℝ)<α*m+1 at h
    linarith only [h,hαm]
  have hNs:(N:ℝ)/K≤α*m:=by
    apply (div_le_iff₀ hKpos).mpr
    have hh:=mul_le_mul_of_nonneg_left hKlo (show 0≤α*m by positivity)
    nlinarith only [hN,hh]
  have hNr:(N*r:ℕ)/(K:ℝ)≤r*(α*m):=by
    have hh:=mul_le_mul_of_nonneg_right hNs (Nat.cast_nonneg r)
    simpa only [Nat.cast_mul,mul_div_assoc,mul_comm,mul_left_comm,mul_assoc] using hh
  have hαbound:α*c≤β/4:=by
    have ha:α≤β/(4*c):=hαsmall.trans (min_le_right _ _)
    have hh:=(le_div_iff₀ (by positivity:0<4*c)).mp ha
    linarith only [hh]
  have hsmall:c*(α*m)≤β*m/4:=by
    have hh:=mul_le_mul_of_nonneg_right hαbound hmpos.le
    nlinarith only [hh]
  have hconstant:((r:ℝ)+2)*(L+1)<β*m/4:=by
    have hh:=(div_lt_iff₀ hβ).mp (hM₂.trans_le (Nat.cast_le.mpr (show M₂≤m by omega)))
    nlinarith only [hh]
  have hKd:((K+D:ℕ):ℝ)≤3*(α*m):=by simp only [Nat.cast_add];linarith only [hKhi,hD]
  have hKr:((K*r:ℕ):ℝ)≤2*r*(α*m):=by
    rw [Nat.cast_mul]
    have hh:=mul_le_mul_of_nonneg_right hKhi (Nat.cast_nonneg r)
    nlinarith only [hh]
  have hDr:((D*r:ℕ):ℝ)≤r*(α*m):=by
    rw [Nat.cast_mul]
    have hh:=mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg r)
    nlinarith only [hh]
  have hβm:0<β*m:=mul_pos hβ hmpos
  have hnon:0≤(r:ℝ)*(α*m):=by positivity
  refine ⟨Nat.cast_pos.mp hKpos,hKhi,?_,?_,?_⟩
  · dsimp [c] at hsmall
    nlinarith only [hNr,hKr,hKd,hsmall,hconstant,hβm,hαm]
  · have hseven:7*(α*m)≤c*(α*m):=by
      dsimp [c]
      nlinarith only [hnon,hαm]
    nlinarith only [hNs,hKd,hseven,hsmall,hβm]
  · dsimp [c] at hsmall
    nlinarith only [hNr,hDr,hKd,hsmall,hconstant,hβm,hnon,hαm]

end Oberwolfach
