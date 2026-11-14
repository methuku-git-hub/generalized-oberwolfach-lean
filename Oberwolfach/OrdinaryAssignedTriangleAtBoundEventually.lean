module

public import Oberwolfach.OrdinaryAssignedTriangleAtBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) triangleFiniteEquality5 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)
theorem ordinary_assigned_triangle_at_bound_eventually
    (d K:ℕ) (hd:2≤d) (hK:0<K)
    (θhost α ρ₀ s₀ ω βP ηP ηH L:ℝ)
    (hθhost:cycleThreshold 3≤θhost) (hα:0<α) (hα1:α≤1) (hθhost1:θhost+α/2≤1)
    (hρ₀:0<ρ₀) (hρ₁:ρ₀≤1) (hs₀:0<s₀) (hs₁:s₀≤1/100) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤2*(min (α/2) (1/4))*(ρ₀*s₀/2)^4*(ρ₀*s₀/2)^4)
    (hβhub:βP≤ω*(ρ₀*s₀/2)^9/4) (hηP:0<ηP) (hηH:0<ηH) (hL:0≤L):
    ∃ (k:ℕ) (βH c B:ℝ),5≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ ∃ N:ℕ,
    ordinaryAssignedTriangleAtBound d K hd θhost α ρ₀ s₀ ω βP ηP ηH L hρ₀ hs₀ k βH c B N := by
  exact ordinary_assigned_triangle_class_combined_event_uniform_late_class d K hd hK
    θhost α ρ₀ s₀ ω βP ηP ηH L hθhost hα hα1 hθhost1
    hρ₀ hρ₁ hs₀ hs₁ hω hβP hβmax hβhub hηP hηH hL
end Oberwolfach
