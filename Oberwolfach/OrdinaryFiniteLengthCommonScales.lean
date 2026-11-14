module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the absorber-input lower bounds once for triangles and all
ordinary lengths in a fixed finite range. The positive density floor is fixed
before the length and before the host or factor family are chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_common_scales_for_bounded_lengths
    (K:ℕ) (hK:3≤K) (α p ω:ℝ) (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃ β row:ℝ,0<β ∧ 0<row ∧
      β≤2*(min (α/2) (1/4))*p^4*p^4 ∧ β≤ω*p^9/4 ∧
      ∀m:ℕ,3≤m→m≤K→
        β≤(α/2)*p^2*p^2 ∧ β≤ω*p^(m+7)/4 ∧ row≤p^(m+7)/2 := by
  let A:ℝ:=(min (α/2) (1/4))*p^8
  let B:ℝ:=ω*p^(K+7)/4
  let β:ℝ:=min A B/2
  let row:ℝ:=p^(K+7)/4
  have hA:0<A:=by dsimp [A];positivity
  have hB:0<B:=by dsimp [B];positivity
  have hβ:0<β:=by dsimp [β];positivity
  have hβA:β≤A:=by dsimp [β];have hh:=min_le_left A B;linarith
  have hβB:β≤B:=by dsimp [β];have hh:=min_le_right A B;linarith
  have hrow:0<row:=by dsimp [row];positivity
  have h8:p^8≤p^4:=pow_le_pow_of_le_one hp.le hp1 (by omega:4≤8)
  have h9:p^(K+7)≤p^9:=pow_le_pow_of_le_one hp.le hp1 (by omega:9≤K+7)
  have hmin:0<min (α/2) (1/4):=by positivity
  have hminα:min (α/2) (1/4)≤α/2:=min_le_left _ _
  refine ⟨β,row,hβ,hrow,?_,?_,?_⟩
  · dsimp [A] at hβA
    nlinarith [pow_nonneg hp.le 4]
  · dsimp [B] at hβB
    nlinarith
  · intro m hm hmK
    have hpow:p^(K+7)≤p^(m+7):=pow_le_pow_of_le_one hp.le hp1 (by omega)
    refine ⟨?_,?_,?_⟩
    · dsimp [A] at hβA
      have hstep:=mul_le_mul_of_nonneg_left h8 hmin.le
      have halpha:=mul_le_mul_of_nonneg_right hminα (pow_nonneg hp.le 4)
      nlinarith [pow_nonneg hp.le 4]
    · dsimp [B] at hβB
      nlinarith
    · dsimp [row]
      nlinarith [pow_nonneg hp.le (m+7)]
end Oberwolfach
