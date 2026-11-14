module

public import Oberwolfach.OrdinaryAllBoundedLengthsUniformEvents
public import Oberwolfach.OrdinaryFiniteLengthUniformEvents
public import Oberwolfach.OrdinaryAssignedTriangleWithoutUpperMargin

@[expose] public section
/-! Choose the input scales and order threshold before choosing a triangle
or any longer ordinary cycle length in the fixed bounded range. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_events_fixed_cycle_thresholds
    (K d:ℕ) (hK:3≤K) (hd:2≤d)
    (α ρ₀ s₀ ω ηP ηH L:ℝ) (hα:0<α) (hα1:α≤1)
    (hρ₀:0<ρ₀) (hρ₁:ρ₀≤1) (hs₀:0<s₀) (hs₁:s₀≤1/100)
    (hω:0<ω) (hηP:0<ηP) (hηH:0<ηH) (hL:0≤L)
:
    ∃ (β row:ℝ),0<β ∧ 0<row ∧
    ∃ (ktri:ℕ) (βHtri ctri Btri:ℝ)
      (k:OrdinaryBoundedLongLengths K→ℕ)
      (βH c B:OrdinaryBoundedLongLengths K→ℝ) (N:ℕ),
      5≤ktri ∧ 0<βHtri ∧ 0<ctri ∧ 0<Btri ∧
      ordinaryAssignedTriangleAtBound d K hd (cycleThreshold 3) α ρ₀ s₀ ω β ηP ηH L
        hρ₀ hs₀ ktri βHtri ctri Btri N ∧
      ∀ m:OrdinaryBoundedLongLengths K,
        m.1.1+3≤k m ∧ 0<βH m ∧ 0<c m ∧ 0<B m ∧
        ordinaryAssignedClassAtBound m.1.1 d K m.2 hd (cycleThreshold (m.1.1+1)) α ρ₀ s₀ ω β ηP row ηH L
          hρ₀ hs₀ (k m) (βH m) (c m) (B m) N := by
  exact ordinary_uniform_events_all_bounded_lengths K d hK hd α ρ₀ s₀ ω ηP ηH L
    hα hα1 hρ₀ hρ₁ hs₀ hs₁ hω hηP hηH hL (cycleThreshold 3) le_rfl
    (fun m=>cycleThreshold (m.1.1+1)) (fun _=>le_rfl)
end Oberwolfach
