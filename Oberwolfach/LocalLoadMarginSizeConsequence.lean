module

public import Oberwolfach.ActualPrescribedLoadLocalOccurrence

@[expose] public section

noncomputable section
namespace Oberwolfach

theorem local_load_margin_forces_large_path_parameter
    (β δ m:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ)
    (hδbound:δ≤(β/100)^2) (hm:0<m) (hmargin:4/m≤δ/4) :
    160000≤m:=by
  have hb:β^2≤1:=by nlinarith [sq_nonneg (1-β)]
  have hd:δ≤1/10000:=by nlinarith only [hδbound,hb]
  have hmult:=mul_le_mul_of_nonneg_right hd (le_of_lt hm)
  have hfour:(4:ℝ)≤(δ/4)*m:=(div_le_iff₀ hm).1 hmargin
  nlinarith only [hmult,hfour]
end Oberwolfach
