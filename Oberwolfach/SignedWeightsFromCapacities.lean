module

public import Oberwolfach.MarkedCapacityTheorem

@[expose] public section

/-! Subtracting two proved bounded positive capacity decompositions gives a
bounded signed response on the same balance subspace and same cycle family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem signed_weights_from_capacities {I E : Type*} [Fintype I] [Fintype E]
    (A : I → E → ℝ) (S : Submodule ℝ (E → ℝ)) (w₀ : E → ℝ) (hw₀ : w₀∈S)
    (κ B : ℝ) (hκ : 0<κ) (hB : 0≤B)
    (hcap : ∀ w : E → ℝ,w∈S → ‖w-w₀‖≤κ →
      ∃ q : I → ℝ,(∀ i,0≤q i ∧ q i≤B) ∧ (∑ i,q i • A i)=w)
    (z : E → ℝ) (hz : z∈S) (η : ℝ) (hη : 0≤η) (hnorm : ‖z‖≤η) :
    ∃ q : I → ℝ,(∀ i,|q i|≤(2*B/κ)*η) ∧ (∑ i,q i • A i)=z := by
  by_cases hη0 : η=0
  · have hz0 : z=0 := norm_eq_zero.mp (le_antisymm (hη0 ▸ hnorm) (norm_nonneg _))
    refine ⟨fun _ => 0,?_,?_⟩
    · intro i;simp only [abs_zero,hη0,mul_zero,le_refl]
    · simp only [zero_smul,Finset.sum_const_zero,hz0]
  · have hηpos : 0<η := lt_of_le_of_ne hη (Ne.symm hη0)
    obtain ⟨q₀,hq₀,he₀⟩ := hcap w₀ hw₀ (by simpa using hκ.le)
    let w := w₀+(κ/η) • z
    have hw : w∈S := S.add_mem hw₀ (S.smul_mem _ hz)
    have hwclose : ‖w-w₀‖≤κ := by
      have he : w-w₀=(κ/η) • z := by dsimp [w];module
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hκ hηpos)]
      calc
        _ ≤ (κ/η)*η := mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = κ := by field_simp
    obtain ⟨q₁,hq₁,he₁⟩ := hcap w hw hwclose
    let q (i : I) : ℝ := (η/κ)*(q₁ i-q₀ i)
    refine ⟨q,?_,?_⟩
    · intro i
      have hd : |q₁ i-q₀ i|≤2*B := by
        calc
          _ ≤ |q₁ i|+|q₀ i| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (q₁ i) (-q₀ i)
          _ ≤ B+B := by rw [abs_of_nonneg (hq₁ i).1,abs_of_nonneg (hq₀ i).1];exact add_le_add (hq₁ i).2 (hq₀ i).2
          _ = _ := by ring
      dsimp [q]
      rw [abs_mul,abs_of_pos (div_pos hηpos hκ)]
      calc
        _ ≤ (η/κ)*(2*B) := mul_le_mul_of_nonneg_left hd (by positivity)
        _ = _ := by ring
    · calc
        _ = (η/κ) • ((∑ i,q₁ i • A i)-(∑ i,q₀ i • A i)) := by
          simp only [q,mul_sub,smul_sub,Finset.smul_sum,Finset.sum_sub_distrib,smul_smul,sub_smul]
        _ = (η/κ) • (w-w₀) := by rw [he₁,he₀]
        _ = z := by
          have he : w-w₀=(κ/η) • z := by dsimp [w];module
          rw [he,smul_smul,show (η/κ)*(κ/η)=(1:ℝ) by field_simp,one_smul]

end Oberwolfach
