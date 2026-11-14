module

public import Oberwolfach.MarkedBoundaryFinishParameters

@[expose] public section

/-! The reservation density is chosen before the separation radius. The
later order threshold absorbs that radius and the integer rounding of the
free-row cap. All losses are charged on the inner row set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem marked_boundary_finish_parameters_upto (l:ℕ) (C β ν:ℝ) (hC:0≤C) (hβ:0<β) (hν:0<ν):
    ∃ τ₀:ℝ,0<τ₀∧τ₀≤1∧∀ τ:ℝ,0<τ→τ≤τ₀→∀ b:ℕ,∃ n₀:ℕ,∀ (n N D:ℕ),n₀≤n→∀ δ:ℝ,
      (N:ℝ)≤C*τ*(n:ℝ)^2→(D:ℝ)≤C*τ*n→δ≤C*τ*n→
      0<Nat.ceil (Real.sqrt τ*n)∧
      (N*(l+4):ℕ)/(Nat.ceil (Real.sqrt τ*n):ℝ)+D+(D*(l+4):ℕ)+
        (l+5)*(2*b+1)+2*(δ+4*(Nat.ceil (Real.sqrt τ*n)+D:ℕ))<β*n∧
      δ+(5*(Nat.ceil (Real.sqrt τ*n)+D):ℕ)≤ν*n∧(D*(l+4):ℕ)≤ν*n:=by
  let A:ℝ:=(2*(l:ℝ)+19)*C+8
  let B:ℝ:=6*C+C*(l+4)+10
  have hA:0<A:=by dsimp [A];positivity
  have hB:0<B:=by dsimp [B];positivity
  let κ:=min 1 (min (β/(4*A)) (ν/B))
  have hκ:0<κ:=lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hκ1:κ≤1:=min_le_left _ _
  have hκβ:κ≤β/(4*A):=(min_le_right _ _).trans (min_le_left _ _)
  have hκν:κ≤ν/B:=(min_le_right _ _).trans (min_le_right _ _)
  have hsmall:A*κ≤β/4:=by
    have hh:κ*(4*A)≤β:=(le_div_iff₀ (by positivity:(0:ℝ)<4*A)).mp hκβ
    nlinarith only [hh]
  have hνB:B*κ≤ν:=by
    have hh:κ*B≤ν:=(le_div_iff₀ hB).mp hκν
    nlinarith only [hh]
  have hrow:(6*C+10)*κ≤ν:=by
    apply le_trans _ hνB
    exact mul_le_mul_of_nonneg_right (by dsimp [B];nlinarith only [mul_nonneg hC (by positivity:(0:ℝ)≤l+4)]) hκ.le
  have hcol:C*(l+4)*κ≤ν:=by
    apply le_trans _ hνB
    exact mul_le_mul_of_nonneg_right (by dsimp [B];linarith only [hC]) hκ.le
  have hκsq:κ^2≤κ:=by nlinarith only [hκ.le,hκ1]
  refine ⟨κ^2,pow_pos hκ _,hκsq.trans hκ1,?_⟩
  intro τ hτ hτmax
  have hsmall' := hsmall
  have hrow' := hrow
  have hcol' := hcol
  have hsqrt:Real.sqrt τ≤κ:=(Real.sqrt_le_left hκ.le).mpr hτmax
  have hsmall:A*Real.sqrt τ≤β/4:=
    (mul_le_mul_of_nonneg_left hsqrt hA.le).trans hsmall'
  have hrow:(6*C+10)*Real.sqrt τ≤ν:=
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)).trans hrow'
  have hcol:C*(l+4)*Real.sqrt τ≤ν:=
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)).trans hcol'
  have hκ1:Real.sqrt τ≤1:=hsqrt.trans hκ1
  have hκ:0<Real.sqrt τ:=Real.sqrt_pos.mpr hτ
  have hκsq:(Real.sqrt τ)^2≤Real.sqrt τ:=by nlinarith only [hκ.le,hκ1]
  intro b
  obtain ⟨n₀,hn₀⟩:=exists_nat_gt (max (1/(Real.sqrt τ)) (4*(((l:ℝ)+5)*(2*b+1)+8)/β))
  refine ⟨max 1 n₀,?_⟩
  intro n N D hn δ hN hD hδ
  have hnR:(0:ℝ)<n:=Nat.cast_pos.mpr (by omega)
  have hnn:(n₀:ℝ)≤n:=by exact_mod_cast (show n₀≤n by omega)
  have hscale:1≤(Real.sqrt τ)*n:=by
    have hh:1/(Real.sqrt τ)≤(n:ℝ):=(le_max_left _ _).trans (hn₀.le.trans hnn)
    nlinarith only [(div_le_iff₀ hκ).mp hh]
  have horder:4*(((l:ℝ)+5)*(2*b+1)+8)≤β*n:=by
    have hh:4*(((l:ℝ)+5)*(2*b+1)+8)/β≤(n:ℝ):=(le_max_right _ _).trans (hn₀.le.trans hnn)
    nlinarith only [(div_le_iff₀ hβ).mp hh]
  have hK:0<Nat.ceil ((Real.sqrt τ)*n):=Nat.ceil_pos.mpr (mul_pos hκ hnR)
  have hKlo:(Real.sqrt τ)*n≤(Nat.ceil ((Real.sqrt τ)*n):ℝ):=Nat.le_ceil _
  have hKhi:(Nat.ceil ((Real.sqrt τ)*n):ℝ)≤(Real.sqrt τ)*n+1:=(Nat.ceil_lt_add_one (by positivity:(0:ℝ)≤(Real.sqrt τ)*n)).le
  rw [←Real.sq_sqrt hτ.le] at hN hD hδ
  have hNr:(N*(l+4):ℕ)/(Nat.ceil ((Real.sqrt τ)*n):ℝ)≤C*(l+4)*(Real.sqrt τ)*n:=by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hK)).mpr
    calc
      (N*(l+4):ℕ)≤C*(Real.sqrt τ)^2*(n:ℝ)^2*(l+4):=by exact_mod_cast mul_le_mul_of_nonneg_right hN (by positivity:(0:ℝ)≤l+4)
      _=(C*(l+4)*(Real.sqrt τ)*n)*((Real.sqrt τ)*n):=by ring
      _≤(C*(l+4)*(Real.sqrt τ)*n)*(Nat.ceil ((Real.sqrt τ)*n):ℝ):=mul_le_mul_of_nonneg_left hKlo (by positivity)
  have hD':(D:ℝ)≤C*(Real.sqrt τ)*n:=hD.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκsq hC) hnR.le)
  have hδ':δ≤C*(Real.sqrt τ)*n:=hδ.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκsq hC) hnR.le)
  have hDr:(D:ℝ)*(l+4)≤C*(Real.sqrt τ)*n*(l+4):=mul_le_mul_of_nonneg_right hD' (by positivity)
  have hmain:((2*(l:ℝ)+19)*C+8)*(Real.sqrt τ)*n≤β*n/4:=by
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hnR.le]
  refine ⟨hK,?_,?_,?_⟩
  · push_cast at hNr ⊢
    nlinarith only [hNr,hD',hδ',hDr,hKhi,hmain,horder,mul_pos hβ hnR]
  · push_cast
    nlinarith only [hKhi,hscale,hD',hδ',mul_le_mul_of_nonneg_right hrow hnR.le]
  · push_cast
    nlinarith only [hDr,mul_le_mul_of_nonneg_right hcol hnR.le]

end Oberwolfach
