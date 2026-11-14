module

public import Oberwolfach.LongActualRawLawParameters
public import Oberwolfach.RawMarkedRetention

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- The seed-density and assigned-recipe presentations use the same retained
law: their second physical parameter differs only in the order of division. -/
theorem long_assigned_reference_retention_law_alignment
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [Nonempty V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (a:Γ) (ρ s₀ M:ℝ)
    (hp:0≤ρ*s₀/2) (hk:0≤(ρ*s₀/2)/M) (hphys:2*(ρ*s₀/2)+2*((ρ*s₀/2)/M)≤1)
    (hk':0≤ρ*(s₀/M)/2) (hphys':2*(ρ*s₀/2)+2*(ρ*(s₀/M)/2)≤1)
    (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑a,q u a)):
    rawMarkedRetentionLaw π d hd a (ρ*s₀/2) ((ρ*s₀/2)/M) hp hk hphys q hq hQ s hs hS =
    rawMarkedRetentionLaw π d hd a (ρ*s₀/2) (ρ*(s₀/M)/2) hp hk' hphys' q hq hQ s hs hS := by
  have heq : (ρ*s₀/2)/M = ρ*(s₀/M)/2 := by ring
  simp only [heq]

/-- At the marked colour the assigned recipe has the constant marginals
required by the reference event. -/
theorem long_assigned_reference_colour_marginals
    {U:Type} [Fintype U] {n:ℕ} (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K m:ℕ) (θ:ℝ):
    (∀u,longAssignedIntervalProbability F hF K m θ u false=(1/100:ℝ)/(m:ℝ)) ∧
    (∀u,longAssignedSpokeProbability F hF K m θ u false=(1/100:ℝ)) := by
  constructor <;> intro u <;> rfl
end Oberwolfach
