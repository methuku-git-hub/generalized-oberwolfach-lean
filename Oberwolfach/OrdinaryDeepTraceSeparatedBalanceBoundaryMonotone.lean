module

public import Oberwolfach.OrdinaryDeepTraceCoverAndSeparatedBalanceOrdered

@[expose] public section
/-! The boundary rate selected for deep balance may be decreased, allowing
it to be shared with other pre-sampling constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_trace_separated_balance_boundary_monotone
    (ε ρ₀ α pmin hmin η ζ cSmall cLarge δ rate:ℝ) (d buffer:ℕ) (β C:ℝ) (mSmall mLarge:ℕ)
    (hε:0≤ε) (hc:cSmall≤cLarge) (hm:mSmall≤mLarge)
    (hbig:OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin η ζ cLarge δ rate d buffer β C mSmall):
    OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin η ζ cSmall δ rate d buffer β C mLarge :=by
  intro V U Γ Color _ _ _ _ _ _ P JQ JH D m hreg hn hD hρlo hρhi hmm Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hdegree hpEq hs hεR hεRδ hεH hεHδ hβe hβes hβh hβhs
    K hJQ hJH havoid hgood cost deepCost i hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ Jwin htrace hhost hcost
  have hbe:βe≤cLarge*ε:=hβes.trans (mul_le_mul_of_nonneg_right hc hε)
  have hbh:βh≤cLarge*ε:=hβhs.trans (mul_le_mul_of_nonneg_right hc hε)
  have hh:=hbig V U Γ Color P JQ JH D m hreg hn hD hρlo hρhi (by omega) Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hdegree hpEq hs hεR hεRδ hεH hεHδ hβe hbe hβh hbh
    K hJQ hJH havoid hgood cost deepCost i hi A G Hs htrace hhost hcost
  exact hh
end Oberwolfach
