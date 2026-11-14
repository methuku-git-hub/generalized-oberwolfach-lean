module

public import Oberwolfach.BoundaryPathMargins

@[expose] public section

/-! Choose the reservation density before the conflict-degree bound. The
later order threshold makes the integer cap and all finite extension losses
fit the prescribed common-neighbourhood and inner-degree margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach

theorem boundary_finish_parameters (r:ℕ) (C β ν:ℝ) (hC:0≤C) (hβ:0<β) (hν:0<ν):
    ∃ τ:ℝ,0<τ ∧ τ≤1 ∧ ∀ L:ℝ,0≤L→∃ n₀:ℕ,
      ∀ (n N D:ℕ),n₀≤n→∀ d₀ e₀:ℝ,
        (N:ℝ)≤C*τ*(n:ℝ)^2→(D:ℝ)≤C*τ*n→d₀≤C*τ*n→e₀≤C*τ*n→
        0<Nat.ceil (Real.sqrt τ*n) ∧
        (N*r:ℕ)/(Nat.ceil (Real.sqrt τ*n):ℝ)+((r:ℝ)+3)*(L+1)+
          2*(d₀+2*(Nat.ceil (Real.sqrt τ*n)+D:ℕ))+e₀+(D*r:ℕ)+3*D<β*n ∧
        d₀+(3*(Nat.ceil (Real.sqrt τ*n)+D):ℕ)≤ν*n ∧ (D*r:ℕ)≤ν*n:=by
  let A:ℝ:=(2*(r:ℝ)+10)*C+4
  let B:ℝ:=4*C+C*r+7
  have hA:0<A:=by dsimp [A];positivity
  have hB:0<B:=by dsimp [B];positivity
  let κ:=min 1 (min (β/(4*A)) (ν/B))
  have hκ:0<κ:=lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hκ1:κ≤1:=min_le_left _ _
  have hκβ:κ≤β/(4*A):=(min_le_right _ _).trans (min_le_left _ _)
  have hκν:κ≤ν/B:=(min_le_right _ _).trans (min_le_right _ _)
  have hsmall:A*κ≤β/4:=by
    have hh:κ*(4*A)≤β:=(le_div_iff₀ (by positivity : (0:ℝ)<4*A)).mp hκβ
    nlinarith only [hh]
  have hνbound:B*κ≤ν:=by
    have hh:κ*B≤ν:=(le_div_iff₀ hB).mp hκν
    nlinarith only [hh]
  have hrow:(4*C+6)*κ≤ν:=by
    apply le_trans _ hνbound
    exact mul_le_mul_of_nonneg_right (by dsimp [B];nlinarith only [hC,mul_nonneg hC (Nat.cast_nonneg r)]) hκ.le
  have hcol:C*r*κ≤ν:=by
    apply le_trans _ hνbound
    exact mul_le_mul_of_nonneg_right (by dsimp [B];nlinarith only [hC,mul_nonneg hC (Nat.cast_nonneg r)]) hκ.le
  refine ⟨κ^2,pow_pos hκ _,by nlinarith only [hκ.le,hκ1],?_⟩
  intro L hL
  obtain ⟨n₀,hn₀⟩:=exists_nat_gt (max (1/κ) (4*(((r:ℝ)+3)*(L+1)+4)/β))
  refine ⟨max 1 n₀,?_⟩
  intro n N D hn d₀ e₀ hN hD hd he
  have hnR:(0:ℝ)<n:=Nat.cast_pos.mpr (by omega)
  have hnn:(n₀:ℝ)≤n:=by exact_mod_cast (show n₀≤n by omega)
  have hscale:1≤κ*n:=by
    have hh:1/κ≤(n:ℝ):=(le_max_left _ _).trans (hn₀.le.trans hnn)
    nlinarith only [(div_le_iff₀ hκ).mp hh]
  have horder:4*(((r:ℝ)+3)*(L+1)+4)≤β*n:=by
    have hh:4*(((r:ℝ)+3)*(L+1)+4)/β≤(n:ℝ):=(le_max_right _ _).trans (hn₀.le.trans hnn)
    nlinarith only [(div_le_iff₀ hβ).mp hh]
  have hsqrt:Real.sqrt (κ^2)=κ:=Real.sqrt_sq hκ.le
  rw [hsqrt]
  obtain ⟨hK,hbudget⟩:=boundary_path_square_root_margin n N D r (by omega) κ C β L d₀ e₀
    hκ hκ1 hC hβ hN hD hd he hsmall horder
  have hκsq:κ^2≤κ:=by nlinarith only [hκ.le,hκ1]
  have hD':(D:ℝ)≤C*κ*n:=hD.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκsq hC) hnR.le)
  have hd':d₀≤C*κ*n:=hd.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκsq hC) hnR.le)
  have hKhi:(Nat.ceil (κ*n):ℝ)≤κ*n+1:=(Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤κ*n)).le
  refine ⟨hK,hbudget,?_,?_⟩
  · push_cast
    nlinarith only [hKhi,hscale,hD',hd',mul_le_mul_of_nonneg_right hrow hnR.le]
  · push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hD' (Nat.cast_nonneg r),
      mul_le_mul_of_nonneg_right hcol hnR.le]

end Oberwolfach
