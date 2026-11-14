module

public import Oberwolfach.OrdinaryActualTraceBalanceAndFineCoverAt

@[expose] public section
/-! A smaller selected level cost preserves the existing uniform profile
and balance callback, without changing its sample or boundary parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_trace_balance_rate_monotone
    (ε ρ₀ α pmin hmin η ζ cBoundary δ rateSmall rateBig:ℝ) (d buffer:ℕ) (β C:ℝ) (m₀:ℕ)
    (hrate:rateSmall≤rateBig)
    (hbig:OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin η ζ cBoundary δ rateBig d buffer β C m₀):
    OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin η ζ cBoundary δ rateSmall d buffer β C m₀:=by
  intro V U Γ Color _ _ _ _ _ _ P Gbase Hbase D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    K hPairRim hPairSpoke havoid hgood cost deepCost i hi A G Hs F R J S H S₀ H₀ X T Z W I B f g ρ Jwin htrace hstate hcost
  have hcost':∀j∈Jwin,0≤cost j ∧ cost j≤4*rateBig*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C:=by
    intro j hj
    refine ⟨(hcost j hj).1,(hcost j hj).2.trans ?_⟩
    have hh:=mul_le_mul_of_nonneg_right hrate
      (show (0:ℝ)≤Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j) by positivity)
    nlinarith only [hh]
  exact hbig V U Γ Color P Gbase Hbase D m hreg hn hD hρlo hρhi hm Q π hπ s j σ
    pR pH θ εR εH βe βh hpR hpR1 hpH hθ hdegree hpEq hs hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh
    K hPairRim hPairSpoke havoid hgood cost deepCost i hi A G Hs htrace hstate hcost'
end Oberwolfach
