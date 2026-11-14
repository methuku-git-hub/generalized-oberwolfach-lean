module

public import Oberwolfach.ColourRoundProgress

@[expose] public section

/-! Floors and ceilings for the next colouring round. The integer choices
retain a uniform lower list-size bound and strict ratio progress. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace Oberwolfach

theorem colouring_round_integer_parameters
    {k l s : ℕ} (hk : 0<k) (hl : 0<l) (hs : 0<s)
    {ρ a b ε η M r : ℝ}
    (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hε : 0<ε) (hε1 : ε≤1)
    (hη : 0<η) (hρ : a≤ρ ∧ ρ≤1) (hr : 1+ε≤r) (hrM : r≤M)
    (hratio : r*s≤l) (hlarge : (l : ℝ)≤M*s)
    (hκ : b≤1-(s : ℝ)*ρ/(l : ℝ)) (hκ1 : 1-(s : ℝ)*ρ/(l : ℝ)≤1)
    (herror : η*M*(M+2)≤(a*ε/4)*b^(k-1))
    (hηsmall : η≤b^k/2) (hηl : 4≤η*l) :
    let κ := 1-(s : ℝ)*ρ/(l : ℝ)
    let X := (l : ℝ)*κ^k-η*l/2
    let Y := (s : ℝ)*(1-ρ)*κ^(k-1)+η*l/2
    ∃ l' s' : ℕ, 0<l' ∧ 0<s' ∧ l'≤l ∧ s'≤l' ∧
      (l' : ℝ)≤X ∧ Y≤(s' : ℝ) ∧
      (b^k/2)*(l : ℝ)≤l' ∧ (r+a*ε/4)*(s' : ℝ)≤l' := by
  dsimp only
  let κ := 1-(s : ℝ)*ρ/(l : ℝ)
  let X := (l : ℝ)*κ^k-η*l/2
  let Y := (s : ℝ)*(1-ρ)*κ^(k-1)+η*l/2
  have hlR : (0 : ℝ)<l := Nat.cast_pos.mpr hl
  have hsR : (0 : ℝ)<s := Nat.cast_pos.mpr hs
  have hκ0 : 0≤κ := hb.le.trans hκ
  have hpow := pow_le_pow_left₀ hb.le hκ k
  have hpow1 : κ^k≤1 := pow_le_one₀ hκ0 hκ1
  have hX : 0≤X := by
    have hh := mul_le_mul_of_nonneg_right hηsmall hlR.le
    have hh' := mul_le_mul_of_nonneg_left hpow hlR.le
    have hp : 0≤(b^k)*(l : ℝ) := by positivity
    dsimp [X];nlinarith
  have hXl : X≤(l : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hpow1 hlR.le
    dsimp [X];nlinarith [mul_pos hη hlR]
  have hY : 0≤Y := by
    dsimp [Y]
    exact add_nonneg (mul_nonneg (mul_nonneg hsR.le (by linarith [hρ.2])) (pow_nonneg hκ0 _))
      (by positivity)
  have hYpos : 0<Y := by
    have hh : 0≤(s : ℝ)*(1-ρ)*κ^(k-1) :=
      mul_nonneg (mul_nonneg hsR.le (by linarith [hρ.2])) (pow_nonneg hκ0 _)
    dsimp [Y];nlinarith
  let l' := ⌊X⌋₊
  let s' := ⌈Y⌉₊
  have hfloor : (l' : ℝ)≤X := Nat.floor_le hX
  have hceil : Y≤(s' : ℝ) := Nat.le_ceil _
  have hlow : (l : ℝ)*κ^k-η*l≤(l' : ℝ) := by
    have hh := Nat.lt_floor_add_one X
    change X<(l' : ℝ)+1 at hh
    dsimp [X] at hh
    linarith
  have hupp : (s' : ℝ)≤(s : ℝ)*(1-ρ)*κ^(k-1)+η*l := by
    have hh := Nat.ceil_lt_add_one hY
    change (s' : ℝ)<Y+1 at hh
    dsimp [Y] at hh
    linarith
  have hratio' := colouring_round_ratio_progress hk hsR ha ha1 hb hε hε1 hη.le
    hρ hr hrM hratio hlarge hκ herror hlow hupp
  have hlow' := colouring_round_list_lower hlR.le hb.le hκ hηsmall hlow
  have hlpos : 0<l' := by
    have hh : (0 : ℝ)<l' := (by positivity : 0<(b^k/2)*(l : ℝ)).trans_le hlow'
    exact_mod_cast hh
  have hspos : 0<s' := Nat.cast_pos.mp (hYpos.trans_le hceil)
  have hll : l'≤l := by exact_mod_cast hfloor.trans hXl
  have hsl : s'≤l' := by
    have hc : 0<a*ε/4 := by positivity
    have h₁ : 1≤r+a*ε/4 := by linarith
    have hh := mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg s')
    have hh' : (s' : ℝ)≤l' := by linarith
    exact_mod_cast hh'
  exact ⟨l',s',hlpos,hspos,hll,hsl,hfloor,hceil,hlow',hratio'⟩

end Oberwolfach
