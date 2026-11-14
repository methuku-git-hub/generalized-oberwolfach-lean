module

public import Oberwolfach.MarkedParentConfigurationHierarchy

@[expose] public section
/-! The parent coefficient is fixed before the cover-down theorem supplies
its active coefficient cap. The later cap does not change the parent choice. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_shared_configuration_delayed_active_choice
    (r:ℕ) (α tstar kstar βconfig βCommon ζCfgCap:ℝ)
    (hα:0<α) (ht:0<tstar) (hk:0<kstar) (hc:0<βconfig)
    (hcommon:0<βCommon) (hζcap:0<ζCfgCap):
    ∃ ζCfg βA:ℝ,
      0<ζCfg ∧ ζCfg≤ζCfgCap ∧ 0<βA ∧ βA≤βconfig ∧ βA≤βCommon ∧
      3*βA≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg ∧
      3*βA≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg ∧
      (∀ κcap ζCommonCap:ℝ,0<κcap→0<ζCommonCap→
        ∃ κ ζCommon:ℝ,0<κ ∧ κ≤κcap ∧ κ≤βA/(16*(r+5:ℕ)) ∧
          0<ζCommon ∧ ζCommon≤ζCommonCap ∧ ζCommon≤κ/4) ∧
      (∀ βrecCap:ℝ,0<βrecCap→∃ βrec:ℝ,0<βrec ∧ βrec≤βA ∧
        βrec≤tstar/4 ∧ βrec≤βrecCap ∧
        3*βrec≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg ∧
        3*βrec≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg):=by
  obtain ⟨ζCfg,hζ,hζcap,hchoice⟩:=marked_parent_configuration_hierarchy_choice r α tstar kstar βconfig ζCfgCap
    hα ht hk hc hζcap
  obtain ⟨βA,hβA,hβconfig,hβcommon,hC,hP,hrest⟩:=hchoice βCommon hcommon
  refine ⟨ζCfg,βA,hζ,hζcap,hβA,hβconfig,hβcommon,hC,hP,hrest,?_⟩
  intro βrecCap hrec
  let βrec:=min βA (min (tstar/4) βrecCap)
  have hb:0<βrec:=by dsimp [βrec];positivity
  have hba:βrec≤βA:=min_le_left _ _
  have hbt:βrec≤tstar/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hbc:βrec≤βrecCap:=(min_le_right _ _).trans (min_le_right _ _)
  exact ⟨βrec,hb,hba,hbt,hbc,by linarith,by linarith⟩
end Oberwolfach
