module

public import Oberwolfach.MarkedReferenceDeepFieldsAfterChanges

@[expose] public section
/-! Leave half the configuration error and half the parent load allowance
unused for later bounded physical changes. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem marked_deep_perturbation_slack
    (r:ℕ) (α tstar kstar ζCfg theta B pstar:ℝ)
    (hζCfg:0<ζCfg) (hθ:0<theta) (hB:0≤B) (hpstar:0<pstar):
    let C:=15*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1));
    ∃ ζ:ℝ,0<ζ ∧
      ∀ βA t eps:ℝ,
      3*βA≤markedLocalCycleCoefficient r α (tstar/2) kstar-(r+5:ℕ)*ζCfg→
      3*βA≤markedLocalPathCoefficient r α (tstar/2) kstar-(r+4:ℕ)*ζCfg→
      eps≤theta/8→
      3*min βA (t/4)≤markedLocalCycleCoefficient r α (tstar/2) kstar-
        (r+5:ℕ)*(ζCfg/2)-(r+5:ℕ)*(ζ+ζ) ∧
      3*min βA (t/4)≤markedLocalPathCoefficient r α (tstar/2) kstar-
        (r+4:ℕ)*(ζCfg/2)-(r+7:ℕ)*ζ-(r+4:ℕ)*ζ ∧
      eps+C*ζ≤theta/4 := by
  intro C
  have hC:0≤C:=by dsimp [C];positivity
  let ζ:=min (ζCfg/16) (theta/(8*(C+1)))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζc:ζ≤ζCfg/16:=min_le_left _ _
  have hζt:ζ≤theta/(8*(C+1)):=min_le_right _ _
  have hζC:ζ*(8*(C+1))≤theta:=(le_div_iff₀ (by positivity)).mp hζt
  refine ⟨ζ,hζ,?_⟩
  intro βA t eps hcycle hpath heps
  have hmin:min βA (t/4)≤βA:=min_le_left _ _
  have hr:(0:ℝ)≤r:=Nat.cast_nonneg _
  have hCyc:((r+5:ℕ):ℝ)*(ζ+ζ)≤((r+5:ℕ):ℝ)*(ζCfg/2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hPath:((r+7:ℕ):ℝ)*ζ+((r+4:ℕ):ℝ)*ζ≤((r+4:ℕ):ℝ)*(ζCfg/2) := by
    push_cast
    nlinarith [mul_nonneg hr (show 0≤ζCfg-16*ζ by linarith)]
  refine ⟨?_,?_,?_⟩
  · nlinarith [hCyc]
  · nlinarith [hPath]
  · nlinarith [mul_nonneg hC hζ.le]
end Oberwolfach
