module

public import Oberwolfach.MarkedParentConfigurationRecordInputs
public import Oberwolfach.MarkedCommonConfigurationParameterMono

@[expose] public section
/-! Choose the local error before the common coefficient, and the record
coefficient before the smaller retention and geometry errors. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem marked_parent_configuration_hierarchy_choice
    (r:ℕ) (α tstar kstar βcap ζCfgCap:ℝ)
    (hα:0<α) (ht:0<tstar) (hk:0<kstar) (hβcap:0<βcap) (hζCfgCap:0<ζCfgCap):
    ∃ ζCfg:ℝ,0<ζCfg ∧ ζCfg≤ζCfgCap ∧ ∀ βCommon:ℝ,0<βCommon→
    ∃ βA:ℝ,0<βA ∧ βA≤βcap ∧ βA≤βCommon ∧
      3*βA≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg ∧
      3*βA≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg ∧
    ∀ κcap ζCommonCap:ℝ,0<κcap→0<ζCommonCap→
    ∃ κ ζCommon:ℝ,0<κ ∧ κ≤κcap ∧ κ≤βA/(16*(r+5:ℕ)) ∧
      0<ζCommon ∧ ζCommon≤ζCommonCap ∧ ζCommon≤κ/4:=by
  let bC:=markedLocalCycleCoefficient r α (tstar/2) kstar
  let bP:=markedLocalPathCoefficient r α (tstar/2) kstar
  have hC:0<bC:=by dsimp [bC,markedLocalCycleCoefficient];positivity
  have hP:0<bP:=by dsimp [bP,markedLocalPathCoefficient];positivity
  let b:=min bC bP
  have hb:0<b:=by dsimp [b];positivity
  have hbC:b≤bC:=min_le_left _ _
  have hbP:b≤bP:=min_le_right _ _
  let ζCfg:=min ζCfgCap (b/(4*(r+5:ℕ)))
  have hζ:0<ζCfg:=by dsimp [ζCfg];positivity
  have hζcap:ζCfg≤ζCfgCap:=min_le_left _ _
  have hζb:ζCfg≤b/(4*(r+5:ℕ)):=min_le_right _ _
  have hmul:ζCfg*(4*(r+5:ℕ))≤b:=(le_div_iff₀ (by positivity)).mp hζb
  have hlossC:((r+5:ℕ):ℝ)*ζCfg≤b/4:=by nlinarith
  have hless:((r+4:ℕ):ℝ)≤(r+5:ℕ):=by exact_mod_cast (show r+4≤r+5 by omega)
  have hlossP:((r+4:ℕ):ℝ)*ζCfg≤b/4:=by nlinarith [mul_nonneg hζ.le (sub_nonneg.mpr hless)]
  refine ⟨ζCfg,hζ,hζcap,?_⟩
  intro βCommon hβCommon
  let βA:=min βcap (min βCommon (b/12))
  have hβA:0<βA:=by dsimp [βA];positivity
  have hβcap':βA≤βcap:=min_le_left _ _
  have hβcommon:βA≤βCommon:=(min_le_right _ _).trans (min_le_left _ _)
  have hβb:βA≤b/12:=(min_le_right _ _).trans (min_le_right _ _)
  have hβC:3*βA≤bC-(r+5:ℕ)*ζCfg:=by linarith
  have hβP:3*βA≤bP-(r+4:ℕ)*ζCfg:=by linarith
  refine ⟨βA,hβA,hβcap',hβcommon,hβC,hβP,?_⟩
  intro κcap ζCommonCap hκcap hζCommonCap
  let κ:=min κcap (βA/(16*(r+5:ℕ)))
  have hκ:0<κ:=by dsimp [κ];positivity
  have hκcap':κ≤κcap:=min_le_left _ _
  have hκβ:κ≤βA/(16*(r+5:ℕ)):=min_le_right _ _
  let ζCommon:=min ζCommonCap (κ/8)
  have hζCommon:0<ζCommon:=by dsimp [ζCommon];positivity
  have hζCommonCap':ζCommon≤ζCommonCap:=min_le_left _ _
  have hζκ:ζCommon≤κ/8:=min_le_right _ _
  refine ⟨κ,ζCommon,hκ,hκcap',hκβ,hζCommon,hζCommonCap',?_⟩
  linarith
end Oberwolfach
