module

public import Oberwolfach.WeightedEdgeColoring
public import Oberwolfach.FiniteChernoff

@[expose] public section

/-! Concentration for independently coloured weighted edges, with the
sampling probability retained in the exponential bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E C : Type*} [Fintype E] [Fintype C] [DecidableEq E] [Nonempty C]

theorem weightedColor_normalized_mean (w : E → ℝ) (c : C) (b : ℝ) :
    (FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)).expectation
      (fun σ=>∑ e,if σ e=c then w e/b else 0)=((∑ e,w e)/Fintype.card C)/b := by
  rw [finiteLaw_pi_expectation_sum (fun _ : E=>FiniteLaw.uniform C)
    (fun e x=>if x=c then w e/b else 0)]
  simp_rw [finiteLaw_uniform_expectation]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.sum_div,← Finset.sum_div]
  ring

theorem weightedColor_normalized_value (w : E → ℝ) (c : C) (b : ℝ) (σ : E → C) :
    (∑ e,if σ e=c then w e/b else 0)=(∑ e,if σ e=c then w e else 0)/b := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

theorem weightedColor_chernoff (w : E → ℝ) (b : ℝ) (hb : 0<b)
    (hw : ∀ e,0≤w e ∧ w e≤b) (c : C)
    (ε : ℝ) (he : 0≤ε) (he1 : ε≤1) :
    (FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)).probability
      (fun σ=>ε*((∑ e,w e)/Fintype.card C)≤
        |(∑ e,if σ e=c then w e else 0)-(∑ e,w e)/Fintype.card C|)≤
      2*Real.exp (-ε^2*((∑ e,w e)/Fintype.card C)/(3*b)) := by
  have hX (e : E) (x : C) : (if x=c then w e/b else 0)∈Set.Icc (0:ℝ) 1 := by
    split_ifs
    · exact ⟨div_nonneg (hw e).1 hb.le,(div_le_one hb).mpr (hw e).2⟩
    · exact ⟨le_rfl,zero_le_one⟩
  have hh := finiteLaw_independent_chernoff (fun _ : E=>FiniteLaw.uniform C)
    (fun e x=>if x=c then w e/b else 0) hX he he1
  dsimp only at hh
  rw [weightedColor_normalized_mean] at hh
  simp_rw [weightedColor_normalized_value] at hh
  have hv (σ : E → C) :
      ε*(((∑ e,w e)/Fintype.card C)/b)≤
        |(∑ e,if σ e=c then w e else 0)/b-((∑ e,w e)/Fintype.card C)/b| ↔
      ε*((∑ e,w e)/Fintype.card C)≤
        |(∑ e,if σ e=c then w e else 0)-(∑ e,w e)/Fintype.card C| := by
    rw [← sub_div,abs_div,abs_of_pos hb,← mul_div_assoc,div_le_div_iff_of_pos_right hb]
  simp_rw [hv] at hh
  convert hh using 1 <;> congr 2 <;> ring

theorem weightedColor_exponential_tail (w : E → ℝ) (b : ℝ) (hb : 0<b)
    (hw : ∀ e,0≤w e ∧ w e≤b) (c : C)
    (s t : ℝ) (hs : 0≤s) :
    (FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)).probability
      (fun σ=>t≤∑ e,if σ e=c then w e else 0)≤
      Real.exp ((((∑ e,w e)/Fintype.card C)*(Real.exp s-1)-s*t)/b) := by
  let μ := FiniteLaw.pi (fun _ : E=>FiniteLaw.uniform C)
  let X (σ : E → C) := ∑ e,if σ e=c then w e/b else 0
  have hX (e : E) (x : C) : (if x=c then w e/b else 0)∈Set.Icc (0:ℝ) 1 := by
    split_ifs
    · exact ⟨div_nonneg (hw e).1 hb.le,(div_le_one hb).mpr (hw e).2⟩
    · exact ⟨le_rfl,zero_le_one⟩
  have hm := finiteLaw_independent_unit_interval_mgf
    (fun _ : E=>FiniteLaw.uniform C) (fun e x=>if x=c then w e/b else 0) hX s
  have hmean := weightedColor_normalized_mean w c b
  rw [finiteLaw_pi_expectation_sum (fun _ : E=>FiniteLaw.uniform C)
    (fun e x=>if x=c then w e/b else 0)] at hmean
  rw [hmean] at hm
  have ht := finiteLaw_exponential_markov μ X (t/b) hs
  have hev : (fun σ=>t/b≤X σ)=(fun σ=>t≤∑ e,if σ e=c then w e else 0) := by
    funext σ
    unfold X
    rw [weightedColor_normalized_value]
    exact propext (div_le_div_iff_of_pos_right hb)
  rw [hev] at ht
  calc
    _ ≤ Real.exp (-s*(t/b))*μ.expectation (fun σ=>Real.exp (s*X σ)) := ht
    _ ≤ Real.exp (-s*(t/b))*Real.exp ((((∑ e,w e)/Fintype.card C)/b)*(Real.exp s-1)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add];congr 1;ring

end Oberwolfach
