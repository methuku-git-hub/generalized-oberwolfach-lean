module

public import Oberwolfach.SignedDemandNormalization

@[expose] public section

/-! The large-cut condition in graph cardinalities implies the normalized
condition used by the fractional-demand theorem. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem equal_part_cut_normalization {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (δ h : ℝ) (hn : 0<Fintype.card V)
    (hlarge : ∀ (S T : Finset V),
      (1-2*δ)*Fintype.card V < (S.card : ℝ)+T.card →
      h*Fintype.card V*min (S.card : ℝ) T.card ≤
        ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card : ℝ)) :
    ∀ (S T : Finset V),
      1-2*δ < (S.card : ℝ)/Fintype.card V+(T.card : ℝ)/Fintype.card V →
      h*Fintype.card V*Fintype.card V*
        min ((S.card : ℝ)/Fintype.card V) ((T.card : ℝ)/Fintype.card V) ≤
        ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card : ℝ) := by
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  intro S T hST
  rw [← add_div] at hST
  have hh := hlarge S T ((lt_div_iff₀ hnr).mp hST)
  rw [min_div_div_right hnr.le]
  convert hh using 1 <;> field_simp [hnr.ne'] <;> ring

end Oberwolfach
