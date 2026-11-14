module

public import Oberwolfach.MarkedActualParentConfigurationEvent
public import Oberwolfach.MarkedLocalEstimateMonotonicity

@[expose] public section
/-! Explicit coefficient choices for the parent configuration field. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_parent_configuration_record_input
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (bC bP βA t:ℝ)
    (hC:3*βA≤bC) (hP:3*βA≤bP)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (h:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ bC bP σ H):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (3*(min βA (t/4))) (3*(min βA (t/4))) σ H:=by
  have hmin:3*(min βA (t/4))≤3*βA:=by linarith [min_le_left βA (t/4)]
  exact markedLocalConfigurations_mono r P π d Finset.univ bC bP _ _ (hmin.trans hC) (hmin.trans hP) σ H h

theorem marked_parent_configuration_parameter_choice
    (r:ℕ) (α tstar kstar βcap ζcap:ℝ)
    (hα:0<α) (ht:0<tstar) (hk:0<kstar) (hβcap:0<βcap) (hζcap:0<ζcap):
    ∃ βA ζ:ℝ,0<βA ∧ βA≤βcap ∧ 0<ζ ∧ ζ≤ζcap ∧
      3*βA≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζ ∧
      3*βA≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζ:=by
  let bC:=markedLocalCycleCoefficient r α (tstar/2) kstar
  let bP:=markedLocalPathCoefficient r α (tstar/2) kstar
  have hC:0<bC:=by dsimp [bC,markedLocalCycleCoefficient];positivity
  have hP:0<bP:=by dsimp [bP,markedLocalPathCoefficient];positivity
  let b:=min bC bP
  have hb:0<b:=by dsimp [b];positivity
  have hbC:b≤bC:=min_le_left _ _
  have hbP:b≤bP:=min_le_right _ _
  let βA:=min βcap (b/12)
  have hβ:0<βA:=by dsimp [βA];positivity
  have hβcap':βA≤βcap:=min_le_left _ _
  have hβb:βA≤b/12:=min_le_right _ _
  let ζ:=min ζcap (b/(4*(r+5:ℕ)))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζcap':ζ≤ζcap:=min_le_left _ _
  have hζb:ζ≤b/(4*(r+5:ℕ)):=min_le_right _ _
  have hr:(0:ℝ)<(r+5:ℕ):=by exact_mod_cast (show 0<r+5 by omega)
  have hmul:ζ*(4*(r+5:ℕ))≤b:=(le_div_iff₀ (by positivity)).mp hζb
  have hlossC:((r+5:ℕ):ℝ)*ζ≤b/4:=by nlinarith
  have hless:((r+4:ℕ):ℝ)≤(r+5:ℕ):=by exact_mod_cast (show r+4≤r+5 by omega)
  have hlossP:((r+4:ℕ):ℝ)*ζ≤b/4:=by nlinarith [mul_nonneg hζ.le (sub_nonneg.mpr hless)]
  refine ⟨βA,ζ,hβ,hβcap',hζ,hζcap',?_,?_⟩ <;> dsimp [bC,bP] at * <;> linarith
end Oberwolfach
