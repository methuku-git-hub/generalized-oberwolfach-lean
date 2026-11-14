module

public import Mathlib.Tactic

@[expose] public section
/-! One fixed constant bounds all marked and ordinary deletion coefficients;
it is independent of the sampled outcome and later deleted graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_mixed_deletion_uniform_constant {K:ℕ}
    (m:ℕ) (ni:Fin K→ℕ) (BM:ℝ) (BO:Fin K→ℝ)
    (hBM:0≤BM) (hBO:∀i,0≤BO i):
    let C:=10*(((m:ℝ)+1)^4*BM+∑i:Fin K,((ni i:ℝ)+2)^4*BO i)
    0≤C ∧ ∀i:Option (Fin K),
      (match i with
      | none=>10*((m:ℝ)+1)^4*BM
      | some i=>10*((ni i:ℝ)+2)^4*BO i)≤C :=by
  intro C
  have hmark:0≤((m:ℝ)+1)^4*BM:=by positivity
  have hord:∀i,0≤((ni i:ℝ)+2)^4*BO i:=fun i=>mul_nonneg (by positivity) (hBO i)
  have hsum:0≤∑i:Fin K,((ni i:ℝ)+2)^4*BO i:=Finset.sum_nonneg (fun i _=>hord i)
  constructor
  · dsimp only [C]; exact mul_nonneg (show (0:ℝ)≤10 by norm_num) (add_nonneg hmark hsum)
  · intro i
    cases i with
    | none =>
      dsimp [C]
      have hd:((m:ℝ)+1)^4*BM≤((m:ℝ)+1)^4*BM+∑i:Fin K,((ni i:ℝ)+2)^4*BO i:=le_add_of_nonneg_right hsum
      have hh:=mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤10 by norm_num)
      convert hh using 1 <;> ring
    | some i =>
      have hi:((ni i:ℝ)+2)^4*BO i≤∑j:Fin K,((ni j:ℝ)+2)^4*BO j:=
        Finset.single_le_sum (fun j _=>hord j) (Finset.mem_univ i)
      dsimp [C]
      have hh:=mul_le_mul_of_nonneg_left (hi.trans (le_add_of_nonneg_left hmark)) (show (0:ℝ)≤10 by norm_num)
      convert hh using 1 <;> ring
end Oberwolfach
