module

public import Oberwolfach.MarkedPreparationWeightChoice

@[expose] public section
/-! A fixed sufficiently large even marked cycle length meets the successor
weight theorem's density requirement at any prescribed positive margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_preparation_length_choice (γ:ℝ) (hγ:0<γ) (L:ℕ):
    ∃ m:ℕ,3≤m ∧ L≤m ∧ Even (m+1) ∧
      ((m+1:ℕ):ℝ)/(2*((m+1:ℕ):ℝ)-2)+γ/2≤1/2+γ:=by
  obtain ⟨k,hk⟩:=exists_nat_gt (max (1/γ) ((L:ℝ)+1))
  let m:=2*k+1
  have hk1:(1:ℝ)<k:=by
    have hh:=(le_max_right (1/γ) ((L:ℝ)+1)).trans_lt hk
    have hL:(0:ℝ)≤L:=by positivity
    linarith
  have hkpos:1≤k:=by exact_mod_cast (show (1:ℝ)≤k by linarith)
  have hm:3≤m:=by dsimp [m];omega
  have hmR:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have hkg:(1/γ:ℝ)<m:=by
    have hh:1/γ<(k:ℝ):=(le_max_left (1/γ) ((L:ℝ)+1)).trans_lt hk
    have hkM:(k:ℝ)≤m:=by dsimp [m];push_cast;linarith
    exact hh.trans_le hkM
  have hgm:1≤γ*(m:ℝ):=by
    have hh:1/γ<(m:ℝ):=hkg
    have hh':1<γ*(m:ℝ):=by
      have h:= (div_lt_iff₀ hγ).mp hh
      nlinarith
    linarith
  have hLm:L≤m:=by
    have hh:= (le_max_right (1/γ) ((L:ℝ)+1)).trans_lt hk
    have hh':L≤k:=by exact_mod_cast (show (L:ℝ)≤k by linarith)
    dsimp [m]
    omega
  refine ⟨m,hm,hLm,?_,?_⟩
  · dsimp [m]
    exact ⟨k+1,by omega⟩
  · have hratio:((m+1:ℕ):ℝ)/(2*((m+1:ℕ):ℝ)-2)=1/2+1/(2*(m:ℝ)):=by
      push_cast
      field_simp [ne_of_gt hmR]
      <;> ring
    rw [hratio]
    have hbound:1/(2*(m:ℝ))≤γ/2:=by
      apply (div_le_iff₀ (by positivity:0<2*(m:ℝ))).2
      nlinarith [hgm]
    linarith
end Oberwolfach
