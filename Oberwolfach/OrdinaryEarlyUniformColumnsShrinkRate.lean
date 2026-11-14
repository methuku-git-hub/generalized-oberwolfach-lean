module

public import Oberwolfach.OrdinaryEarlyUniformColumnsAtRate

@[expose] public section
/-! A uniform edited-target construction remains valid when the allowed
edit rate is reduced, preserving the one reservoir chosen for all targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_early_uniform_columns_shrink_rate
    (d mMatch:ℕ) (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α ξnew ξold:ℝ)
    (hξ:ξnew≤ξold)
    (hbase:OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α ξold):
    OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch α ξnew :=by
  intro r m t a bAbs
  obtain ⟨N,hbase⟩:=hbase r m t a bAbs
  refine ⟨N,?_⟩
  intro n hn hn2 qCount hqCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests ε Sample Bad Reference Href
    hInnerEarly hRes J Kdim F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling pActual p₂ LF
    hK hD hrs0 hrs1 hρ₀ hρlo hρhi S hS hClass hzero hlocalHub hlocalCol hfamily hcolour
  obtain ⟨K,JQ,JH,hreservoir,hTarget⟩:=hbase n hn hn2 qCount hqCount P Host hHost π σ A Z Wterm Inner Bterm B Hubs ξabs γ pstar p smin rsv β ζ s
    hγ hpstar hp hsmin hs hseq hβ hζ hbζ hP herror hmargin hlistBudget hTests hInnerEarly hRes
    F₀ hF₀ Cres i₀ lamMatch D ρ₀ sampling hK hD hrs0 hrs1 hρ₀ hρlo hρhi S hS hClass hzero hlocalHub hlocalCol hfamily hcolour
  refine ⟨K,JQ,JH,hreservoir,?_⟩
  intro Target hTargetNew
  apply hTarget Target
  intro v
  exact (hTargetNew v).trans (mul_le_mul_of_nonneg_right hξ (by positivity))
end Oberwolfach
