module

public import Oberwolfach.RetainedAndRawIntervalGeometry
public import Oberwolfach.RawIntervalHubStartsExpectation

@[expose] public section
/-! Count the actual retained and raw interval indices by the two raw start
counts in the same sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] [DecidableEq Γ]

theorem raw_interval_hub_count_eq_card (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (w:U):
    rawIntervalHubStartCount π d g σ w =
      (Fintype.card {a:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) a g}:ℝ):=by
  classical
  unfold rawIntervalHubStartCount rawIntervalFamilyStartState
  rw [Fintype.card_subtype]
  simp

theorem retained_raw_interval_count_le_raw_counts (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U):
    (Fintype.card (retainedAndRawIntervalIndex π d σ g₀ g₁ t J w):ℝ)≤
      rawIntervalHubStartCount π d g₀ σ w+rawIntervalHubStartCount π d g₁ σ w:=by
  classical
  let e:retainedMarkedIndex π d σ g₀ t J w ↪ {a:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) a g₀}:=
    ⟨fun a=>⟨a.val,a.property.1⟩,by intro a b h;exact Subtype.ext (congrArg (fun x:{a:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) a g₀}=>x.val) h)⟩
  have hcard:=Fintype.card_le_of_injective e e.injective
  rw [raw_interval_hub_count_eq_card,raw_interval_hub_count_eq_card]
  simp only [retainedAndRawIntervalIndex,Fintype.card_sum,Nat.cast_add]
  have hcR:(Fintype.card (retainedMarkedIndex π d σ g₀ t J w):ℝ)≤
      (Fintype.card {a:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) a g₀}:ℝ):=by exact_mod_cast hcard
  linarith
end Oberwolfach
