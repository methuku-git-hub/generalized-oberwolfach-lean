module

public import Oberwolfach.MarkedParentConfigurationHierarchy

@[expose] public section
/-! A parent coefficient and a smaller active coefficient can be chosen before
the retention and geometry errors, while both use the same fixed estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem marked_shared_configuration_hierarchy_choice
    (r:ℕ) (α tstar kstar βconfig βCommon βcap βrecCap ζCfgCap:ℝ)
    (hα:0<α) (ht:0<tstar) (hk:0<kstar) (hc:0<βconfig) (hcommon:0<βCommon)
    (hcap:0<βcap) (hrec:0<βrecCap) (hζcap:0<ζCfgCap):
    ∃ ζCfg βA βrec:ℝ,0<ζCfg ∧ ζCfg≤ζCfgCap ∧ 0<βA ∧ βA≤βconfig ∧ βA≤βCommon ∧ βA≤βcap ∧
      0<βrec ∧ βrec≤βA ∧ βrec≤tstar/4 ∧ βrec≤βrecCap ∧
      3*βA≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg ∧
      3*βA≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg ∧
      3*βrec≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg ∧
      3*βrec≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg ∧
      ∀ κcap ζCommonCap:ℝ,0<κcap→0<ζCommonCap→
        ∃ κ ζCommon:ℝ,0<κ ∧ κ≤κcap ∧ κ≤βA/(16*(r+5:ℕ)) ∧
          0<ζCommon ∧ ζCommon≤ζCommonCap ∧ ζCommon≤κ/4:=by
  have hmin:0<min βconfig βcap:=lt_min hc hcap
  obtain ⟨ζCfg,hζ,hζcap',hchoose⟩:=marked_parent_configuration_hierarchy_choice r α tstar kstar (min βconfig βcap) ζCfgCap
    hα ht hk hmin hζcap
  obtain ⟨βA,hβA,hβmin,hβcommon,hC,hP,hrest⟩:=hchoose βCommon hcommon
  have hβconfig:βA≤βconfig:=hβmin.trans (min_le_left _ _)
  have hβcap:βA≤βcap:=hβmin.trans (min_le_right _ _)
  let βrec:=min βA (min (tstar/4) βrecCap)
  have hβrec:0<βrec:=by dsimp [βrec];positivity
  have hrecA:βrec≤βA:=min_le_left _ _
  have hrect:βrec≤tstar/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hreccap:βrec≤βrecCap:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ζCfg,βA,βrec,hζ,hζcap',hβA,hβconfig,hβcommon,hβcap,hβrec,hrecA,hrect,hreccap,hC,hP,?_,?_,hrest⟩ <;> linarith
end Oberwolfach
