module

public import Oberwolfach.MarkedPreparationLengthChoice
public import Oberwolfach.SuccessorCyclicMargin

@[expose] public section
/-! Every sufficiently large permitted marked length satisfies the reference
successor-density margin, uniformly after the length cutoff is fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_preparation_reference_length (α:ℝ) (hα:0<α) (L₀:ℕ):
    ∃ L:ℕ,7≤L ∧ L₀≤L ∧ ∀ m:ℕ,L≤m→Even (m+1)→
      ∃ r k₀:ℕ,2≤r ∧ r+4=m ∧ r+4+1=(k₀+2)*2 ∧
        successorCycleRatio k₀+α/4≤1/2+α/2:=by
  obtain ⟨M,hM,hLM,heven,hmargin⟩:=marked_preparation_length_choice (α/2) (by positivity) (max 7 L₀)
  refine ⟨M,(le_max_left 7 L₀).trans hLM,(le_max_right 7 L₀).trans hLM,?_⟩
  intro m hm hmEven
  have hM7:7≤M:=(le_max_left 7 L₀).trans hLM
  have hm7:7≤m:=hM7.trans hm
  obtain ⟨t,ht⟩:=hmEven
  let k₀:=t-2
  let r:=m-4
  have hlen:r+4+1=(k₀+2)*2:=by dsimp [r,k₀];omega
  have hreq:r+4=m:=by dsimp [r];omega
  have hr:2≤r:=by dsimp [r];omega
  have hmR:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have hMR:(0:ℝ)<M:=by exact_mod_cast (show 0<M by omega)
  have hMM:(M:ℝ)≤m:=by exact_mod_cast hm
  have hratioM:((M+1:ℕ):ℝ)/(2*((M+1:ℕ):ℝ)-2)=1/2+1/(2*(M:ℝ)):=by
    push_cast;field_simp [ne_of_gt hMR];ring
  have hratio:successorCycleRatio k₀=1/2+1/(2*(m:ℝ)):=by
    unfold successorCycleRatio
    have hnat:m+1=(k₀+2)*2:=by omega
    have hcast0:((m+1:ℕ):ℝ)=(((k₀+2)*2:ℕ):ℝ):=by exact_mod_cast hnat
    push_cast at hcast0
    have hcast:(k₀:ℝ)+2=((m:ℝ)+1)/2:=by linarith
    rw [hcast]
    field_simp [ne_of_gt hmR];ring
  have hmono:(1:ℝ)/(2*m)≤1/(2*(M:ℝ)):=by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  rw [hratioM] at hmargin
  refine ⟨r,k₀,hr,hreq,hlen,?_⟩
  rw [hratio]
  linarith
end Oberwolfach
