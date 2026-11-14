module

public import Oberwolfach.RetainedHubStartLower

@[expose] public section
/-! The retained final starts and raw approximate starts retain their joint
hub-wise mass on the full-row retention event. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_raw_hub_start_count_lower
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U] [DecidableEq Γ]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (ζ q₀ q₁ e:ℝ)
    (hgood:RetainedRestrictionGood π d σ g₀ t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J)
    (w:U)
    (h₀:|rawIntervalHubStartCount π d g₀ σ w-(Fintype.card V:ℝ)*q₀/(d:ℝ)|<e)
    (h₁:|rawIntervalHubStartCount π d g₁ σ w-(Fintype.card V:ℝ)*q₁/(d:ℝ)|<e):
    (Fintype.card V:ℝ)*(q₀+q₁)/(d:ℝ)-2*e-ζ*Fintype.card V≤
      (Fintype.card (retainedAndRawIntervalIndex π d σ g₀ g₁ t J w):ℝ):=by
  have hret:=retained_hub_start_count_lower_from_row_test π d hd σ g₀ t J ζ hgood w
  have hraw:=raw_interval_hub_count_eq_card π d σ g₁ w
  have hleft:-(e)<rawIntervalHubStartCount π d g₀ σ w-(Fintype.card V:ℝ)*q₀/(d:ℝ):=(abs_lt.mp h₀).1
  have hright:-(e)<rawIntervalHubStartCount π d g₁ σ w-(Fintype.card V:ℝ)*q₁/(d:ℝ):=(abs_lt.mp h₁).1
  simp only [retainedAndRawIntervalIndex,Fintype.card_sum,Nat.cast_add]
  rw [hraw] at hright
  have hsplit:(Fintype.card V:ℝ)*(q₀+q₁)/(d:ℝ)=
      (Fintype.card V:ℝ)*q₀/(d:ℝ)+(Fintype.card V:ℝ)*q₁/(d:ℝ):=by ring
  rw [hsplit]
  linarith
end Oberwolfach
