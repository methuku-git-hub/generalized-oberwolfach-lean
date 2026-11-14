module

public import Oberwolfach.RetainedRawIntervalCardinality
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
/-! The common start-count event bounds the actual interval demand at a hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_raw_interval_demand_from_start_counts
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U] [DecidableEq Γ]
    (π:Equiv.Perm V) (d c:ℕ) (hd:0<d) (hc:0<c)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (w:U)
    (q:U→Γ→ℝ) (θ ell:ℝ)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-(Fintype.card V:ℝ)*q w g/d|<
      (Fintype.card V:ℝ)^(3/4:ℝ)/d)
    (hclass:q w g₀+q w g₁≤(1-θ)*ell/c):
    (Fintype.card (retainedAndRawIntervalIndex π d σ g₀ g₁ t J w):ℝ)≤
      (1-θ)*ell*(Fintype.card V:ℝ)/(c*d)+2*(Fintype.card V:ℝ)^(3/4:ℝ)/d:=by
  have h0:= (abs_lt.mp (hcounts g₀)).2
  have h1:= (abs_lt.mp (hcounts g₁)).2
  have hn:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hmul:=mul_le_mul_of_nonneg_left hclass hn
  have hc':(0:ℝ)<c:=by exact_mod_cast hc
  have hd':(0:ℝ)<d:=by exact_mod_cast hd
  have hcbd:(Fintype.card V:ℝ)*(q w g₀+q w g₁)/(d:ℝ)≤
      (1-θ)*ell*(Fintype.card V:ℝ)/((c:ℝ)*d):=by
    apply (div_le_div_iff₀ hd' (mul_pos hc' hd')).2
    field_simp at hmul ⊢
    nlinarith
  have hraw:=retained_raw_interval_count_le_raw_counts π d σ g₀ g₁ t J w
  have hsum:rawIntervalHubStartCount π d g₀ σ w+rawIntervalHubStartCount π d g₁ σ w≤
      (Fintype.card V:ℝ)*(q w g₀+q w g₁)/d+2*(Fintype.card V:ℝ)^(3/4:ℝ)/d:=by
    calc
      _ ≤ ((Fintype.card V:ℝ)*q w g₀/d+(Fintype.card V:ℝ)^(3/4:ℝ)/d)+
          ((Fintype.card V:ℝ)*q w g₁/d+(Fintype.card V:ℝ)^(3/4:ℝ)/d):=by linarith
      _ = _ :=by ring
  exact hraw.trans (hsum.trans (by linarith [hcbd]))
end Oberwolfach
