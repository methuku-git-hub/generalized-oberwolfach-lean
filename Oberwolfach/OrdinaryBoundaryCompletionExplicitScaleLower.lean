module

public import Oberwolfach.OrdinaryBoundaryCompletionTraceUniformExplicit

@[expose] public section
/-! Quantify the explicit endpoint capacity selected by the uniform finishing lemma. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_boundary_completion_explicit_scale_lower
    (m:ℕ) (β rate:ℝ) (hβ:0<β) (hrate:0<rate):
    let A:ℝ:=100*((m:ℝ)+20);let B:ℝ:=2*((m:ℝ)+10);
    let q:ℝ:=min 1 (min β rate);let k:ℝ:=min (rate/B) (min 1 (β/A));
    0<q/(A+B) ∧ q/(A+B)≤k :=by
  intro A B q k
  have hA:0<A:=by dsimp [A];positivity
  have hB:0<B:=by dsimp [B];positivity
  have hD:0<A+B:=add_pos hA hB
  have hD1:1≤A+B:=by
    dsimp [A,B]
    have hm:(0:ℝ)≤m:=by positivity
    nlinarith only [hm]
  have hq:0<q:=by dsimp [q];positivity
  have hq1:q≤1:=min_le_left _ _
  have hqβ:q≤β:=(min_le_right _ _).trans (min_le_left _ _)
  have hqr:q≤rate:=(min_le_right _ _).trans (min_le_right _ _)
  have hAlev:A≤A+B:=by linarith
  have hBlev:B≤A+B:=by linarith
  have hqA:q*A≤β*(A+B):=by
    have h1:=mul_le_mul_of_nonneg_left hAlev hq.le
    have h2:=mul_le_mul_of_nonneg_right hqβ hD.le
    linarith only [h1,h2]
  have hqB:q*B≤rate*(A+B):=by
    have h1:=mul_le_mul_of_nonneg_left hBlev hq.le
    have h2:=mul_le_mul_of_nonneg_right hqr hD.le
    linarith only [h1,h2]
  have hβbound:q/(A+B)≤β/A:=(div_le_div_iff₀ hD hA).mpr hqA
  have hrbound:q/(A+B)≤rate/B:=(div_le_div_iff₀ hD hB).mpr hqB
  have hone:q/(A+B)≤1:=(div_le_iff₀ hD).mpr (by linarith)
  exact ⟨div_pos hq hD,le_min hrbound (le_min hone hβbound)⟩
end Oberwolfach
