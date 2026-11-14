module

public import Mathlib.Tactic

@[expose] public section

/-! The inner factor tolerance is fixed before the earlier packing's
permitted deletion. Each smaller deletion tolerance remains valid. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_inner_factor_deletion_tolerance
    (r h:ℕ) (t beta eta C:ℝ) (ht:0<t) (hb:0<beta) (he:0<eta) (hC:0≤C):
    ∃ zeta:ℝ,0<zeta∧∀ zR zS:ℝ,0≤zR→0≤zS→zR≤zeta→zS≤zeta→
    h*(zR+zS)≤t/4∧(r+5:ℝ)*(zR+zS)≤beta∧
    (r+7:ℝ)*zR+(r+4:ℝ)*zS≤beta∧
    5*(r+5:ℝ)^4*C*(2*zR+zS)≤eta/2:=by
  obtain ⟨a,ha,haB⟩:=exists_pos_mul_lt (show 0<t/4 by positivity) (2*(h:ℝ))
  obtain ⟨b,hb',hbB⟩:=exists_pos_mul_lt hb (2*(r:ℝ)+12)
  obtain ⟨c,hc,hcB⟩:=exists_pos_mul_lt (show 0<eta/2 by positivity) (15*(r+5:ℝ)^4*C)
  refine ⟨min a (min b c),lt_min ha (lt_min hb' hc),?_⟩
  intro zR zS hzR hzS hR hS
  have hRa:=hR.trans (min_le_left _ _)
  have hSa:=hS.trans (min_le_left _ _)
  have hRb:=hR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSb:=hS.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRc:=hR.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSc:=hS.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh:0≤(h:ℝ):=Nat.cast_nonneg _
  have hr:0≤(r:ℝ):=Nat.cast_nonneg _
  have hRa':=mul_le_mul_of_nonneg_left hRa hh
  have hSa':=mul_le_mul_of_nonneg_left hSa hh
  have hRb5:=mul_le_mul_of_nonneg_left hRb (show 0≤(r+5:ℝ) by positivity)
  have hSb5:=mul_le_mul_of_nonneg_left hSb (show 0≤(r+5:ℝ) by positivity)
  have hRb7:=mul_le_mul_of_nonneg_left hRb (show 0≤(r+7:ℝ) by positivity)
  have hSb4:=mul_le_mul_of_nonneg_left hSb (show 0≤(r+4:ℝ) by positivity)
  have hRc':=mul_le_mul_of_nonneg_left hRc (show 0≤10*(r+5:ℝ)^4*C by positivity)
  have hSc':=mul_le_mul_of_nonneg_left hSc (show 0≤5*(r+5:ℝ)^4*C by positivity)
  exact ⟨by nlinarith only [hRa',hSa',haB],by nlinarith only [hRb5,hSb5,hbB,hb'],
    by nlinarith only [hRb7,hSb4,hbB,hb'],by nlinarith only [hRc',hSc',hcB]⟩

end Oberwolfach
