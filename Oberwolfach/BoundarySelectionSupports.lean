module

public import Oberwolfach.BoundarySupportEvent

@[expose] public section

/-! Convert the three sampled boundary estimates to the intersection and
membership bounds used for simultaneous selection. All subsequent changes
are measured in the realised graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem boundary_selection_supports (P G:SimpleGraph V) (A Z:Finset V)
    (τ κ ε:ℝ) (hτ:0≤τ) (hτ1:τ≤1) (hκ:0<κ) (hκ1:κ≤1)
    (hsize:κ*Fintype.card V≤(A.card:ℝ)) (herr:ε≤τ^2*A.card)
    (hrow:∀ x,|((A∩G.neighborFinset x).card:ℝ)-τ*(A∩P.neighborFinset x).card|≤ε)
    (hpair:∀ x y,x≠y→
      |(((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card:ℝ)-
        τ^2*((A∩P.neighborFinset x)∩(A∩P.neighborFinset y)).card|≤ε)
    (hcol:∀ v∈A,|((Z.filter (fun x=>v∈A∩G.neighborFinset x)).card:ℝ)-
      τ*(Z∩P.neighborFinset v).card|≤ε):
    (∀ x,((A∩G.neighborFinset x).card:ℝ)≤2*τ*A.card) ∧
    (∀ x y,x≠y→(((A∩G.neighborFinset x)∩(A∩G.neighborFinset y)).card:ℝ)≤
      (3*τ/κ)^2*A.card) ∧
    (∀ v,((Z.filter (fun x=>v∈A∩G.neighborFinset x)).card:ℝ)≤(3*τ/κ)*A.card):=by
  have ha:0≤(A.card:ℝ):=Nat.cast_nonneg _
  have hτsq:τ^2≤τ:=by nlinarith
  have hετ:ε≤τ*A.card:=herr.trans (mul_le_mul_of_nonneg_right hτsq ha)
  have hdiv:τ≤3*τ/κ:=by apply (le_div_iff₀ hκ).mpr;nlinarith
  have hsq:2*τ^2≤(3*τ/κ)^2:=by
    have hh:3*τ≤3*τ/κ:=by apply (le_div_iff₀ hκ).mpr;nlinarith
    have hp:0≤3*τ/κ:=by positivity
    nlinarith [sq_nonneg τ]
  refine ⟨?_,?_,?_⟩
  · intro x
    have hcount:((A∩P.neighborFinset x).card:ℝ)≤A.card:=
      Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
    have hh:=(abs_le.mp (hrow x)).2
    have hm:=mul_le_mul_of_nonneg_left hcount hτ
    linarith
  · intro x y hxy
    have hcount:(((A∩P.neighborFinset x)∩(A∩P.neighborFinset y)).card:ℝ)≤A.card:=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_left.trans Finset.inter_subset_left))
    have hh:=(abs_le.mp (hpair x y hxy)).2
    have hm:=mul_le_mul_of_nonneg_left hcount (sq_nonneg τ)
    have hn:=mul_le_mul_of_nonneg_right hsq ha
    linarith
  · intro v
    by_cases hv:v∈A
    · have hcount:((Z∩P.neighborFinset v).card:ℝ)≤Fintype.card V:=
        Nat.cast_le.mpr (Finset.card_le_univ _)
      have hh:=(abs_le.mp (hcol v hv)).2
      have hm:=mul_le_mul_of_nonneg_left hcount hτ
      have hsize':(Fintype.card V:ℝ)≤(A.card:ℝ)/κ:=by
        apply (le_div_iff₀ hκ).mpr;simpa only [mul_comm] using hsize
      have hs:=mul_le_mul_of_nonneg_left hsize' hτ
      have hthree:τ*((A.card:ℝ)/κ)+τ*A.card≤(3*τ/κ)*A.card:=by
        apply (mul_le_mul_iff_of_pos_right hκ).mp
        field_simp
        nlinarith [mul_nonneg hτ ha,mul_le_mul_of_nonneg_left hκ1 (mul_nonneg hτ ha)]
      linarith
    · have he:Z.filter (fun x=>v∈A∩G.neighborFinset x)=∅:=by
        ext x;simp [hv]
      rw [he];simp only [Finset.card_empty,Nat.cast_zero];positivity

end Oberwolfach
