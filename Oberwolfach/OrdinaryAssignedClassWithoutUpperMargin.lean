module

public import Oberwolfach.OrdinaryAssignedClassAtBoundEventually
public import Oberwolfach.OrdinaryAssignedClassAtBoundVacuous

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_assigned_class_at_bound_without_upper_margin
    (m d K:ℕ) (hm:3≤m) (hd:2≤d) (hK:0<K)
    (θhost α ρ₀ s₀ ω βP ηP row ηH L:ℝ)
    (hθhost:cycleThreshold (m+1)≤θhost) (hα:0<α) (hα1:α≤1)
    (hρ₀:0<ρ₀) (hρ₁:ρ₀≤1) (hs₀:0<s₀) (hs₁:s₀≤1/100) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤(α/2)*(ρ₀*s₀/2)^2*(ρ₀*s₀/2)^2)
    (hβhub:βP≤ω*(ρ₀*s₀/2)^(m+7)/4) (hηP:0<ηP) (hrow:0<row)
    (hrowmax:row≤(ρ₀*s₀/2)^(m+7)/2) (hηH:0<ηH) (hL:0≤L):
    ∃ (k:ℕ) (βH c B:ℝ),m+3≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧ ∃ N:ℕ,
    ordinaryAssignedClassAtBound m d K hm hd θhost α ρ₀ s₀ ω βP ηP row ηH L hρ₀ hs₀ k βH c B N := by
  by_cases hθhost1:θhost+α/2≤1
  · exact ordinary_assigned_class_at_bound_eventually m d K hm hd hK
      θhost α ρ₀ s₀ ω βP ηP row ηH L hθhost hα hα1 hθhost1
      hρ₀ hρ₁ hs₀ hs₁ hω hβP hβmax hβhub hηP hrow hrowmax hηH hL
  · refine ⟨m+3,1,1,1,by omega,by norm_num,by norm_num,by norm_num,0,?_⟩
    apply ordinary_assigned_class_at_bound_vacuous m d K hm hd θhost α ρ₀ s₀ ω βP ηP row ηH L hρ₀ hs₀
    linarith
end Oberwolfach
