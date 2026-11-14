module

public import Oberwolfach.MarkedPreparationReferenceMargin

@[expose] public section
/-! Choosing the marked length above one threshold, before the later cutoffs,
supplies the exact density margin and indices used by the reference theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_preparation_reference_length_threshold (α:ℝ) (hα:0<α):
    ∃ L:ℕ,6≤L ∧ ∀ m:ℕ,L≤m→Even (m+1)→
      ∃ r k₀:ℕ,2≤r ∧ r+4=m ∧ r+4+1=(k₀+2)*2 ∧
        successorCycleRatio k₀+α/4≤1/2+α/2:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (4/α)
  refine ⟨max N 6,le_max_right _ _,?_⟩
  intro m hm heven
  have hm6:6≤m:=(le_max_right N 6).trans hm
  have hmR:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have hNm:(N:ℝ)≤m:=by exact_mod_cast ((le_max_left N 6).trans hm)
  have hratio:4/α<(m:ℝ):=hN.trans_le hNm
  have hmul:4<α*(m:ℝ):=by
    have hh:4<(m:ℝ)*α:=(div_lt_iff₀ hα).mp hratio
    nlinarith
  have hhalf:1/(2*(m:ℝ))≤α/4:=by
    apply (div_le_iff₀ (by positivity:0<2*(m:ℝ))).2
    nlinarith [hmul]
  have hid:((m+1:ℕ):ℝ)/(2*((m+1:ℕ):ℝ)-2)=1/2+1/(2*(m:ℝ)):=by
    push_cast
    field_simp [ne_of_gt hmR]
    <;> ring
  have hmargin:((m+1:ℕ):ℝ)/(2*((m+1:ℕ):ℝ)-2)+α/4≤1/2+α/2:=by
    rw [hid]
    linarith
  exact marked_preparation_reference_margin m hm6 heven α hmargin
end Oberwolfach
