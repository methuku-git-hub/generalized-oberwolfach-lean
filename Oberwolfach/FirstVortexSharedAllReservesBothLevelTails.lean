module

public import Oberwolfach.FirstVortexUniformLevelActualParentTail
public import Oberwolfach.FirstVortexInitialVortexReserveData
public import Oberwolfach.SuccessorWeightParameterMono
public import Oberwolfach.FirstVortexUniformLevelActualParentTailExactMargin
public import Oberwolfach.FirstVortexUniformLevelActualParentTailExactMargin
public import Oberwolfach.FirstVortexNamedAllReservesProbabilityTail
public import Oberwolfach.FirstVortexUniformLevelActualParentTailExactMargin
public import Oberwolfach.FirstVortexSeedDensityHierarchy

@[expose] public section
/-! Fix one family of parent and active constants for the positive matching
selector and the uniform level theorem, before choosing the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem first_vortex_shared_all_reserves_both_level_tails
    (α ρ₀:ℝ) (hα:0<α) (hαCap:2*α≤1) (hρ₀:0<ρ₀) (hρ₀one:ρ₀≤1):
    ∃c₀:ℕ,∀r:ℕ,2≤r→c₀≤r+5→∀k₀:ℕ,
      r+4+1=(k₀+2)*2→successorCycleRatio k₀+α/2≤1/2+α→
    let sstar:ℝ:=1/100
    let tstar:ℝ:=1/(200*((r+4:ℕ):ℝ))
    let kstar:ℝ:=ρ₀/(800*((r+4:ℕ):ℝ))
    let ω:ℝ:=ρ₀/4
    let γRich:ℝ:=min α (1/2:ℝ)/2
    let aLoA:=successorWeightLower k₀ (α/4)
    let BA:=successorWeightUpper k₀ (α/4);
    ∃β βCommon εAbs εRob ζRob δAbs:ℝ,0<β ∧ 0<βCommon ∧ 0<εAbs ∧ 0<εRob ∧ 0<ζRob ∧ 0<δAbs ∧
    ∃εAbsP ζAbsP δAbsP βconfigP βCommonP:ℝ,
      0<εAbsP ∧ 0<ζAbsP ∧ 0<δAbsP ∧ 0<βconfigP ∧ 0<βCommonP ∧
    ∃εStable ζStable capStable:ℝ,0<εStable ∧ 0<ζStable ∧ 0<capStable ∧
      aLoA≤successorWeightLower k₀ ((2*α)/4) ∧ successorWeightUpper k₀ ((2*α)/4)≤BA ∧
      FirstVortexNamedAllReservesProbabilityTail r (r+12) k₀ 1 α sstar ω γRich tstar kstar ρ₀ hρ₀
        β βCommon εAbs εRob ζRob δAbs εAbsP ζAbsP δAbsP βconfigP βCommonP εStable ζStable capStable ∧
      FirstVortexUniformLevelActualParentTailExactMargin r α ρ₀ hα hρ₀ βconfigP βCommonP aLoA BA ∧
      FirstVortexUniformLevelActualParentTail r α ρ₀ hα hρ₀ βconfigP βCommonP
        (successorWeightLower k₀ ((2*α)/4)) (successorWeightUpper k₀ ((2*α)/4)) ∧
      FirstVortexInitialVortexReserveData α ρ₀ :=by
  obtain ⟨c₀,hLevel⟩:=first_vortex_uniform_level_global_actual_parent_choice_exact_margin α ρ₀ hα hαCap hρ₀ hρ₀one
  obtain ⟨c₁,hLevelTwo⟩:=first_vortex_uniform_level_global_actual_parent_choice α ρ₀ hα hαCap hρ₀ hρ₀one
  refine ⟨max c₀ c₁,?_⟩
  intro r hr hrc k₀ hlen hmargin sstar tstar kstar ω γRich aLoA BA
  have hrc₀:c₀≤r+5:=(le_max_left _ _).trans hrc
  have hrc₁:c₁≤r+5:=(le_max_right _ _).trans hrc
  obtain ⟨s₀,t₀,k₀',hsEq,htEq,hkEq,hs,hs1,ht,ht1,hts,htcap,hk,hkhalf,hpBound,hDensity⟩:=
    first_vortex_seed_density_hierarchy r ρ₀ hρ₀ hρ₀one
  have hsstar:0<sstar:=by dsimp [sstar];norm_num
  have hsstar1:sstar≤1/100:=by dsimp [sstar];norm_num
  have htstar:0<tstar:=by simpa only [tstar,htEq] using ht
  have htstar1:tstar≤1:=by simpa only [tstar,htEq] using ht1
  have htstarS:tstar≤sstar:=by simpa only [tstar,sstar,htEq,hsEq] using hts
  have hkstar:0<kstar:=by simpa only [kstar,hkEq] using hk
  have hω:0<ω:=by dsimp [ω];positivity
  have hωBound:4*ω≤ρ₀:=by dsimp [ω];linarith
  have hγ:0<γRich:=by dsimp [γRich];positivity
  have hγ1:γRich≤1/2:=by dsimp [γRich];have hh:=min_le_right α (1/2:ℝ);linarith
  have hγα:γRich≤α:=by dsimp [γRich];have hh:=min_le_left α (1/2:ℝ);linarith
  have hweights:=successorWeightConstants_pos k₀ (α/4) (by positivity)
  have ha:0<aLoA:=by simpa only [aLoA] using hweights.1
  have hBA:0<BA:=by simpa only [BA] using hweights.2
  have hLower:aLoA≤successorWeightLower k₀ ((2*α)/4):=by
    dsimp [aLoA]
    exact successor_weight_lower_mono k₀ (α/4) ((2*α)/4) (by positivity) (by linarith)
  have hUpper:successorWeightUpper k₀ ((2*α)/4)≤BA:=by
    dsimp [BA]
    exact successor_weight_upper_antitone k₀ (α/4) ((2*α)/4) (by positivity) (by linarith)
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hSelector⟩:=
    long_all_structural_core_all_reserves_high_probability r (r+12) k₀ 1 hr (by omega) hlen
      α sstar ω γRich tstar kstar hα hsstar hsstar1 hω hmargin hαCap hγ hγ1 hγα htstar htstar1 htstarS hkstar ρ₀ hρ₀ hωBound
  have hLevelTail:FirstVortexUniformLevelActualParentTailExactMargin r α ρ₀ hα hρ₀ βconfigP βCommonP aLoA BA:=
    hLevel r hr hrc₀ βconfigP βCommonP aLoA BA hβconfigP hβCommonP ha hBA
  have hstrong:=successorWeightConstants_pos k₀ ((2*α)/4) (by positivity)
  have hLevelTailTwo:FirstVortexUniformLevelActualParentTail r α ρ₀ hα hρ₀ βconfigP βCommonP
      (successorWeightLower k₀ ((2*α)/4)) (successorWeightUpper k₀ ((2*α)/4)):=
    hLevelTwo r hr hrc₁ βconfigP βCommonP _ _ hβconfigP hβCommonP hstrong.1 hstrong.2
  exact ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,
    εAbsP,ζAbsP,δAbsP,βconfigP,βCommonP,hεAbsP,hζAbsP,hδAbsP,hβconfigP,hβCommonP,
    εStable,ζStable,capStable,hεStable,hζStable,hcapStable,hLower,hUpper,hSelector,hLevelTail,hLevelTailTwo,first_vortex_initial_vortex_reserve_hierarchy α ρ₀ hα hρ₀⟩
end Oberwolfach
