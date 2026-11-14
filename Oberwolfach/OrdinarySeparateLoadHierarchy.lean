module

public import Oberwolfach.OrdinaryGeneralFinishOrderedHierarchy

@[expose] public section
/-! The prescribed-packing load, deeper-set fraction and correction scale can
be chosen independently below any positive selection and extension budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_separate_load_hierarchy (m K:ℕ) (a s β:ℝ)
    (ha:0<a) (hs:0<s) (hβ:0<β):
    ∃b θ ξ:ℝ,0<b ∧ 0<θ ∧ 0<ξ ∧ b≤a ∧ b≤1 ∧
      18*b+3*((K:ℝ)+2)*θ≤s ∧
      3*b*((m:ℝ)+1)+θ*((m:ℝ)+1)≤s ∧
      80*ξ≤b^2 ∧ 30*ξ+θ≤β/4:=by
  let c:ℝ:=(m:ℝ)+(K:ℝ)+100
  let δ:ℝ:=min s β
  have hc:0<c:=by dsimp [c];positivity
  have hm0:(0:ℝ)≤m:=Nat.cast_nonneg _
  have hK0:(0:ℝ)≤K:=Nat.cast_nonneg _
  have hc1:1≤c:=by dsimp [c];linarith only [hm0,hK0]
  have hδ:0<δ:=lt_min hs hβ
  let b:ℝ:=min (min a 1) (δ/(100*c))
  let θ:ℝ:=b
  let ξ:ℝ:=min (b^2/160) (β/240)
  have hb:0<b:=by dsimp [b];positivity
  have hθ:0<θ:=hb
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hba:b≤a:=(min_le_left _ _).trans (min_le_left _ _)
  have hb1:b≤1:=(min_le_left _ _).trans (min_le_right _ _)
  have hbδ:b≤δ/(100*c):=min_le_right _ _
  have hbcap:100*c*b≤δ:=by
    have hh: b*(100*c)≤δ:=(le_div_iff₀ (by positivity:0<100*c)).mp hbδ
    nlinarith only [hh]
  have hbsmall:b≤δ/100:=by nlinarith only [hbcap,hc1,hb]
  have hcoeff1:18+3*((K:ℝ)+2)≤100*c:=by dsimp [c];linarith only [hm0,hK0]
  have hcoeff2:4*((m:ℝ)+1)≤100*c:=by dsimp [c];linarith only [hm0,hK0]
  have hbound1:(18+3*((K:ℝ)+2))*b≤δ:=by
    have hh:=mul_le_mul_of_nonneg_right hcoeff1 hb.le
    nlinarith only [hh,hbcap]
  have hbound2:(4*((m:ℝ)+1))*b≤δ:=by
    have hh:=mul_le_mul_of_nonneg_right hcoeff2 hb.le
    nlinarith only [hh,hbcap]
  have hξb:ξ≤b^2/160:=min_le_left _ _
  have hξβ:ξ≤β/240:=min_le_right _ _
  refine ⟨b,θ,ξ,hb,hθ,hξ,hba,hb1,?_,?_,?_,?_⟩
  · dsimp [θ];nlinarith only [hbound1,min_le_left s β]
  · dsimp [θ];nlinarith only [hbound2,min_le_left s β]
  · nlinarith only [hξb,sq_nonneg b]
  · dsimp [θ]
    have hδβ:δ≤β:=min_le_right _ _
    nlinarith only [hξβ,hbsmall,hδβ,hβ]
end Oberwolfach
