module

public import Mathlib.Tactic

@[expose] public section
/-! Choose one parent sampling error before the host and sample, with enough
room for the later common, configuration, potential, active and boundary
transfers. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_precise_parent_shared_error_budget
    (r h:ℕ) (κ theta eta t x gapC gapP C B:ℝ)
    (hκ:0<κ) (hθ:0<theta) (hη:0<eta) (ht:0<t) (hx:0<x)
    (hgapC:0<gapC) (hgapP:0<gapP) (hC:0≤C) (hB:0≤B):
    ∃δ:ℝ,0<δ ∧
      ((r:ℝ)+13)*δ≤κ/8 ∧
      (2+11*C)*δ≤κ/8 ∧ (2+11*C)*δ≤theta/8 ∧
      (2+20*B)*δ≤eta/8 ∧ 2*δ≤t/16 ∧
      (1+(h:ℝ))*δ≤x/4 ∧
      2*((r:ℝ)+5)*δ≤gapC ∧ 2*((r:ℝ)+4)*δ≤gapP :=by
  let v:=min κ (min theta (min eta (min t (min x (min gapC gapP)))))
  let A:ℝ:=1+(r:ℝ)+(h:ℝ)+C+B
  have hv:0<v:=by dsimp [v];positivity
  have hA:0<A:=by dsimp [A];positivity
  let δ:=v/(1000*A)
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδeq:δ*(1000*A)=v:=by dsimp [δ];field_simp
  have hvκ:v≤κ:=by dsimp [v];exact min_le_left _ _
  have hvθ:v≤theta:=by dsimp [v]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hvη:v≤eta:=by dsimp [v];exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hvt:v≤t:=by dsimp [v];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hvx:v≤x:=by dsimp [v];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hvgC:v≤gapC:=by dsimp [v];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hvgP:v≤gapP:=by dsimp [v];exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hr:0≤(r:ℝ):=Nat.cast_nonneg _
  have hh:0≤(h:ℝ):=Nat.cast_nonneg _
  have hcoeff1:8*((r:ℝ)+13)≤1000*A:=by dsimp [A];nlinarith
  have hcoeff2:8*(2+11*C)≤1000*A:=by dsimp [A];nlinarith
  have hcoeff3:8*(2+20*B)≤1000*A:=by dsimp [A];nlinarith
  have hcoeff4:(32:ℝ)≤1000*A:=by dsimp [A];nlinarith
  have hcoeff5:4*(1+(h:ℝ))≤1000*A:=by dsimp [A];nlinarith
  have hcoeff6:2*((r:ℝ)+5)≤1000*A:=by dsimp [A];nlinarith
  have hcoeff7:2*((r:ℝ)+4)≤1000*A:=by dsimp [A];nlinarith
  have hc1:=mul_le_mul_of_nonneg_left hcoeff1 hδ.le
  have hc2:=mul_le_mul_of_nonneg_left hcoeff2 hδ.le
  have hc3:=mul_le_mul_of_nonneg_left hcoeff3 hδ.le
  have hc4:=mul_le_mul_of_nonneg_left hcoeff4 hδ.le
  have hc5:=mul_le_mul_of_nonneg_left hcoeff5 hδ.le
  have hc6:=mul_le_mul_of_nonneg_left hcoeff6 hδ.le
  have hc7:=mul_le_mul_of_nonneg_left hcoeff7 hδ.le
  rw [hδeq] at hc1 hc2 hc3 hc4 hc5 hc6 hc7
  refine ⟨δ,hδ,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [hc1,hvκ]
  · nlinarith only [hc2,hvκ]
  · nlinarith only [hc2,hvθ]
  · nlinarith only [hc3,hvη]
  · nlinarith only [hc4,hvt]
  · nlinarith only [hc5,hvx]
  · nlinarith only [hc6,hvgC]
  · nlinarith only [hc7,hvgP]
end Oberwolfach
