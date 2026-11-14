module

public import Oberwolfach.MarkedVortexCorrectionErrorChoice
public import Oberwolfach.LongEarlyExtraFailureBudget
public import Oberwolfach.LongHostMatchingBetaAlignment

@[expose] public section
/-! Choose the vortex error, then the event-failure budgets, then the
vortex ratio after its matching threshold is available. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_host_matching_ordered_probability_geometry_choices
    (εAbs εRob εGeom γRich kstar tstar:ℝ)
    (hAbs:0<εAbs) (hRob:0<εRob) (hGeom:0<εGeom) (hγ:0<γRich) (hk:0<kstar) (ht:0<tstar):
    ∃ εQ:ℝ,0<εQ ∧ εQ<1/4 ∧ εQ≤εAbs ∧ εQ≤εRob ∧ εQ≤εGeom ∧
      εQ≤min ((γRich/2)*kstar) tstar/128 ∧
    ∀ ε₀ εExtra cap:ℝ,0<ε₀→0<εExtra→4*εExtra≤ε₀→0<cap→
    ∃ χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ χ≤cap ∧ 0<χCommon ∧ χCommon≤cap ∧
      0<χBal ∧ χBal≤cap ∧ 0<χNbr ∧ χNbr≤cap ∧
      0<χLoad ∧ χLoad≤cap ∧ 0<χLocal ∧ χLocal≤cap ∧
      0<χConfig ∧ χConfig≤cap ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ ∧
    ∀ αHost αRef βmax εBal εRef κ x:ℝ,0<αRef→αRef=αHost/2→
      0<βmax→0<εBal→0<εRef→0<κ→0<x→
    ∃ βQ:ℝ,0<βQ ∧ βQ≤βmax ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 ∧
      βQ≤1/4 ∧ βQ≤αRef/4 ∧ βQ≤αHost/8 ∧ βQ≤3*αHost/40 ∧
      βQ≤3/20 ∧ βQ≤κ ∧ βQ≤x := by
  obtain ⟨εQ,hεQ,hεQ1,hεAbs,hεRob,hεGeom,hεsmall⟩:=
    marked_vortex_correction_error_choice εAbs εRob εGeom γRich kstar tstar hAbs hRob hGeom hγ hk ht
  refine ⟨εQ,hεQ,hεQ1,hεAbs,hεRob,hεGeom,hεsmall,?_⟩
  intro ε₀ εExtra cap hε₀ hεExtra hExtraCap hcap
  obtain ⟨χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχc,hχCommon,hχCommonc,
    hχBal,hχBalc,hχNbr,hχNbrc,hχLoad,hχLoadc,hχLocal,hχLocalc,hχConfig,hχConfigc,hgap⟩:=
    long_early_extra_failure_budget_choice ε₀ εExtra cap hε₀ hεExtra hExtraCap hcap
  refine ⟨χ,χCommon,χBal,χNbr,χLoad,χLocal,χConfig,hχ,hχc,hχCommon,hχCommonc,
    hχBal,hχBalc,hχNbr,hχNbrc,hχLoad,hχLoadc,hχLocal,hχLocalc,hχConfig,hχConfigc,hgap,?_⟩
  intro αHost αRef βmax εBal εRef κ x hα hαeq hβ hBal hRef hκ hx
  exact long_host_matching_beta_alignment αHost αRef βmax εBal εRef κ x hα hαeq hβ hBal hRef hκ hx
end Oberwolfach
