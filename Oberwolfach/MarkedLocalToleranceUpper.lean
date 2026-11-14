module

public import Oberwolfach.MarkedLocalPhysicalEvent

@[expose] public section
/-! Any nonnegative configuration tolerance allowed by the local-cycle
slack is at most the original density margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_local_configuration_tolerance_le_margin
    (r:ℕ) (α tstar kstar ζ βrec:ℝ)
    (hα:0≤α) (hα1:α≤1) (ht:0≤tstar) (ht1:tstar≤1)
    (hk:0≤kstar) (hk1:kstar≤1) (hζ:0≤ζ) (hβ:0≤βrec)
    (hslack:3*βrec≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζ):
    ζ≤α :=by
  let q:=α*(tstar/2)/4
  have hq:0≤q:=by dsimp [q];positivity
  have hqα:q≤α:=by dsimp [q];nlinarith [mul_nonneg hα (sub_nonneg.mpr ht1)]
  have hq1:q≤1:=hqα.trans hα1
  have hpow: q^(r+5)≤q:=by
    have hh: q^(r+4)≤1:=pow_le_one₀ hq hq1
    calc
      q^(r+5)=q^(r+4)*q:=by rw [pow_succ]
      _≤1*q:=mul_le_mul_of_nonneg_right hh hq
      _=q:=by ring
  have hkpow:kstar^(r+5)≤1:=pow_le_one₀ hk hk1
  have hpnon:0≤q^(r+5):=pow_nonneg hq _
  have hcoef:markedLocalCycleCoefficient r α (tstar/2) kstar≤α:=by
    unfold markedLocalCycleCoefficient
    change kstar^(r+5)*q^(r+5)/2≤α
    have hh:=mul_le_mul_of_nonneg_right hkpow hpnon
    nlinarith only [hh,hpow,hqα,hα]
  have hr:(1:ℝ)≤(r+5:ℕ):=by exact_mod_cast (show 1≤r+5 by omega)
  have hmul:ζ≤((r+5:ℕ):ℝ)*ζ:=by nlinarith [mul_nonneg (sub_nonneg.mpr hr) hζ]
  nlinarith only [hslack,hcoef,hmul,hβ]
end Oberwolfach
