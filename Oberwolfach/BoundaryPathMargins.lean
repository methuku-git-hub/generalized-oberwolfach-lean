module

public import Oberwolfach.EndpointBoundaryCompletion

@[expose] public section

/-! Explicit numerical margins for the square-root cap in boundary-path
completion. The fixed conflict degree enters only the order requirement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem boundary_path_square_root_margin (n N D r:ℕ) (hn:0<n)
    (κ C β L d₀ e₀:ℝ) (hκ:0<κ) (hκ1:κ≤1) (hC:0≤C) (hβ:0<β)
    (hN:(N:ℝ)≤C*κ^2*(n:ℝ)^2) (hD:(D:ℝ)≤C*κ^2*n)
    (hd:d₀≤C*κ^2*n) (he:e₀≤C*κ^2*n)
    (hsmall:((2*(r:ℝ)+10)*C+4)*κ≤β/4)
    (horder:4*(((r:ℝ)+3)*(L+1)+4)≤β*n):
    0<Nat.ceil (κ*n) ∧
      (N*r:ℕ)/(Nat.ceil (κ*n):ℝ)+((r:ℝ)+3)*(L+1)+
        2*(d₀+2*(Nat.ceil (κ*n)+D:ℕ))+e₀+(D*r:ℕ)+3*D<β*n:=by
  have hnR:(0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hK:0<Nat.ceil (κ*n):=Nat.ceil_pos.mpr (mul_pos hκ hnR)
  have hKlo:κ*n≤(Nat.ceil (κ*n):ℝ):=Nat.le_ceil _
  have hKhi:(Nat.ceil (κ*n):ℝ)≤κ*n+1:=(Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤κ*n)).le
  have hNr:(N*r:ℕ)/(Nat.ceil (κ*n):ℝ)≤C*r*κ*n:=by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hK)).mpr
    calc
      (N*r:ℕ)≤C*κ^2*(n:ℝ)^2*r:=by exact_mod_cast mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg r)
      _=(C*r*κ*n)*(κ*n):=by ring
      _≤(C*r*κ*n)*(Nat.ceil (κ*n):ℝ):=
        mul_le_mul_of_nonneg_left hKlo (by positivity)
  have hκsq:κ^2≤κ:=by nlinarith only [hκ.le,hκ1]
  have hscale:C*κ^2*n≤C*κ*n:=by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκsq hC) hnR.le
  have hD':(D:ℝ)≤C*κ*n:=hD.trans hscale
  have hdr:d₀≤C*κ*n:=hd.trans hscale
  have her:e₀≤C*κ*n:=he.trans hscale
  have hDr:(D:ℝ)*r≤C*κ*n*r:=mul_le_mul_of_nonneg_right hD' (Nat.cast_nonneg r)
  have hmain:((2*(r:ℝ)+10)*C+4)*κ*n≤β*n/4:=by
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hnR.le]
  refine ⟨hK,?_⟩
  push_cast
  have hNr':(N:ℝ)*r/(Nat.ceil (κ*n):ℝ)≤C*r*κ*n:=by exact_mod_cast hNr
  nlinarith only [hNr',hKhi,hD',hdr,her,hDr,hmain,horder,mul_pos hβ hnR]

theorem boundary_path_square_root_degrees (n D r:ℕ) (κ C ν:ℝ)
    (hκ:0<κ) (hκ1:κ≤1) (hC:0≤C) (hscale:1≤κ*n)
    (hD:(D:ℝ)≤C*κ^2*n)
    (hrow:3*(C+2)*κ≤ν) (hcol:C*r*κ≤ν):
    (3*(Nat.ceil (κ*n)+D):ℕ)≤ν*n ∧ (D*r:ℕ)≤ν*n:=by
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hKhi:(Nat.ceil (κ*n):ℝ)≤κ*n+1:=(Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤κ*n)).le
  have hκsq:κ^2≤κ:=by nlinarith only [hκ.le,hκ1]
  have hD':(D:ℝ)≤C*κ*n:=hD.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκsq hC) hn)
  constructor
  · push_cast
    nlinarith only [hKhi,hscale,hD',mul_le_mul_of_nonneg_right hrow hn]
  · push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hD' (Nat.cast_nonneg r),
      mul_le_mul_of_nonneg_right hcol hn]

end Oberwolfach
