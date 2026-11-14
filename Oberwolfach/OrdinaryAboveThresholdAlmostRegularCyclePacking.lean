module

public import Oberwolfach.OrdinaryAlmostRegularFractionalCyclePacking
public import Oberwolfach.PositiveOrdinaryCycleWeights
public import Oberwolfach.ThresholdComparisons

@[expose] public section
/-! The bounded fractional weights needed for the almost-spanning packing
follow from the ordinary cycle-decomposition threshold. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_above_threshold_almost_regular_cycle_packing
    (r:ℕ) (hr:3≤r) (α θ γ:ℝ) (hα:0<α) (hθ:0<θ) (hθsmall:θ≤1/20)
    (hγ:0<γ) (hγ1:γ≤1):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V),
      N≤Fintype.card V→∀ d:ℝ,(Fintype.card V:ℝ)/2≤d→d≤Fintype.card V→
      (∀ v,(cycleThreshold r+α)*Fintype.card V≤(G.degree v:ℝ))→
      (∀ v,|(G.degree v:ℝ)-d|≤θ*(Fintype.card V:ℝ)/4)→
      ∃ M:Finset (OrdinaryCycle G r),
        (∀ C∈M,∀ C'∈M,C≠C'→Disjoint C.val.val.support.toFinset C'.val.val.support.toFinset) ∧
        (1-γ)*(1-10*θ)*Fintype.card V≤(r:ℝ)*M.card := by
  obtain ⟨c,C,hc,hC,Nweight,hNweight,hweights⟩:=positive_ordinary_fractional_cycle_weights r hr α hα
  let B:=max 1 C
  have hB:1≤B:=le_max_left _ _
  have hCB:C≤B:=le_max_right _ _
  obtain ⟨Npack,hpack⟩:=ordinary_almost_regular_fractional_cycle_packing r hr B θ γ hB hθ hθsmall hγ hγ1
  refine ⟨max Nweight Npack,?_⟩
  intro V _ _ G hn d hdlo hdhi hdeg hregular
  letI:DecidableEq (OrdinaryCycle G r):=Classical.decEq _
  have hn0:0<Fintype.card V:=by omega
  have hnreal:0<(Fintype.card V:ℝ):=by exact_mod_cast hn0
  have hhalf:(1/2:ℝ)≤cycleThreshold r:=cycleThreshold_half_le hr
  have hmin:∀ v,(Fintype.card V:ℝ)/2≤(G.degree v:ℝ) := by
    intro v
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤cycleThreshold r+α by linarith) hnreal.le
    linarith [hdeg v]
  obtain ⟨w,hwBound,hw⟩:=hweights V ((le_max_left Nweight Npack).trans hn) G hdeg
  have hwB:∀ C',0≤w C' ∧ w C'≤B/(Fintype.card V:ℝ)^(r-2) := by
    intro C'
    have hden:0<(Fintype.card V:ℝ)^(r-2):=pow_pos hnreal _
    constructor
    · exact (div_nonneg hc.le hden.le).trans (hwBound C').1
    · exact (hwBound C').2.trans (div_le_div_of_nonneg_right hCB hden.le)
  exact hpack V G ((le_max_right Nweight Npack).trans hn) d hdlo hdhi hmin hregular w hw hwB
end Oberwolfach
