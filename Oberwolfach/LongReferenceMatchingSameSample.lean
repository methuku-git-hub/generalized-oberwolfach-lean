module

public import Oberwolfach.LongAssignedReferenceLawAlignment

@[expose] public section
/-! A reference-event probability bound in the seed-density convention may be
fed directly to a matching selector in the assigned-recipe convention. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reference_event_matching_same_sample
    {V U Γ Color Ω:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
    [LinearOrder V] [Nonempty V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (a:Γ) (ρ s₀ M:ℝ)
    (hp:0≤ρ*s₀/2) (hk:0≤(ρ*s₀/2)/M) (hphys:2*(ρ*s₀/2)+2*((ρ*s₀/2)/M)≤1)
    (hk':0≤ρ*(s₀/M)/2) (hphys':2*(ρ*s₀/2)+2*(ρ*(s₀/M)/2)≤1)
    (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑a,q u a))
    (μ:FiniteLaw Ω) (project:Ω→RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (Good:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (Prepared:Ω→Prop)
    (εExtra:ℝ)
    (hGood:1-εExtra≤(rawMarkedRetentionLaw π d hd a (ρ*s₀/2) ((ρ*s₀/2)/M)
      hp hk hphys q hq hQ s hs hS).probability Good)
    (hSelect:∀ Extra:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop,
      1-εExtra≤(rawMarkedRetentionLaw π d hd a (ρ*s₀/2) (ρ*(s₀/M)/2)
        hp hk' hphys' q hq hQ s hs hS).probability Extra →
      ∃z:Ω,0<μ.mass z ∧ Extra (project z) ∧ Prepared z):
    ∃z:Ω,0<μ.mass z ∧ Good (project z) ∧ Prepared z := by
  apply hSelect Good
  rw [←long_assigned_reference_retention_law_alignment π d hd a ρ s₀ M hp hk hphys hk' hphys' q hq hQ s hs hS]
  exact hGood
end Oberwolfach
