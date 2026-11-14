module

public import Oberwolfach.FractionalDegrees
public import Oberwolfach.DenseBipartiteCuts
public import Oberwolfach.RegularizationComplement

@[expose] public section

/-! A two-sided bounded fractional perfect matching in a dense bipartite
zero-one matrix. The proof uses the already proved real-flow cut criterion;
no matching existence statement is taken as an assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_bipartite_fractional_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1)
    (β : ℝ) (hβ : 0 < β) (hβhalf : β < 1/2)
    (hn : 0 < Fintype.card V)
    (hrow : ∀ x, (1/2+β)*Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ))
    (hcol : ∀ y, (1/2+β)*Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ)) :
    ∃ w : BipartiteEdges M → ℝ,
      (∀ e, β/(5*Fintype.card V) ≤ w e ∧ w e ≤ 5/(β*Fintype.card V)) ∧
      (∀ x, (∑ e, if e.1=x then w e else 0)=1) ∧
      (∀ y, (∑ e, if e.2.1=y then w e else 0)=1) := by
  let n : ℝ := Fintype.card V
  have hnR : 0<n := Nat.cast_pos.mpr hn
  let a : ℝ := β/(5*n)
  let p : ℝ := 4/(β*n)
  have ha : 0<a := div_pos hβ (by positivity)
  have hp : 0<p := div_pos (by norm_num) (mul_pos hβ hnR)
  have han : a*n=β/5 := by dsimp [a];field_simp <;> ring
  have hpn : p*(β*n)=4 := by dsimp [p];field_simp
  let f (x : V) : ℝ := 1-a*((∑ y, M x y : ℕ) : ℝ)
  let g (y : V) : ℝ := 1-a*((∑ x, M x y : ℕ) : ℝ)
  have hdegree (N : V → V → ℕ) (hN : ∀ x y, N x y ≤ 1) (x : V) :
      ((∑ y, N x y : ℕ) : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast (show (∑ y, N x y) ≤ Fintype.card V from
      (Finset.sum_le_sum (fun y _ => hN x y)).trans_eq (by simp))
  have hf (x : V) : 1-β/5 ≤ f x ∧ f x ≤ 1 := by
    have hd := mul_le_mul_of_nonneg_left (hdegree M hM x) ha.le
    have hd0 : 0≤a*((∑ y, M x y : ℕ) : ℝ) := by positivity
    dsimp [f]; constructor <;> linarith
  have hg (y : V) : 1-β/5 ≤ g y ∧ g y ≤ 1 := by
    have hd := mul_le_mul_of_nonneg_left
      (hdegree (fun y x => M x y) (fun y x => hM x y) y) ha.le
    have hd0 : 0≤a*((∑ x, M x y : ℕ) : ℝ) := by positivity
    dsimp [g]; constructor <;> linarith
  have htotal : ∑ x, f x = ∑ y, g y := by
    simp only [f,g,Finset.sum_sub_distrib,← Finset.mul_sum,← Nat.cast_sum]
    rw [Finset.sum_comm (f := M)]
  let T : ℝ := ∑ x, f x
  have hTlo : n*(1-β/5)≤T := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => (hf x).1)
  have hThi : T≤n := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => (hf x).2)
  have hT : 0≤T := le_trans (mul_nonneg hnR.le (by linarith : 0≤1-β/5)) hTlo
  have hrel : n ≤ (1+β/4)*T := by
    have he : 1≤(1+β/4)*(1-β/5) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hTlo (by linarith : 0≤1+β/4)
    nlinarith [mul_le_mul_of_nonneg_left he hnR.le]
  have hcap : T/p ≤ (3*β/4)*n*n/2 := by
    apply (div_le_iff₀ hp).mpr
    have hh : ((3*β/4)*n*n/2)*p=3*n/2 := by dsimp [p];field_simp <;> ring
    rw [hh]
    linarith
  have hupper (z : ℝ) (hz : z≤1) : z/p ≤ (1+β/4)*(T/p)/n := by
    have hz' : z*n≤n := mul_le_of_le_one_left hnR.le hz
    apply (le_div_iff₀ hnR).mpr
    rw [div_mul_eq_mul_div, mul_div_assoc]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right (hz'.trans hrel) hp.le
  obtain ⟨q,hq,hl,hr⟩ := bipartite_nearUniformFractionalDegrees
    (fun e : BipartiteEdges M => e.1) (fun e => e.2.1)
    (fun x => f x/p) (fun y => g y/p)
    (δ := β/4) (δ₀ := β/4) (M := T/p) (h := 3*β/4)
    hn hn (by positivity) le_rfl (by linarith) (div_nonneg hT hp.le)
    hcap (by rw [← Finset.sum_div]) (by rw [← Finset.sum_div,← htotal])
    (fun x => div_nonneg (by linarith [(hf x).1]) hp.le)
    (fun y => div_nonneg (by linarith [(hg y).1]) hp.le)
    (fun x => hupper _ (hf x).2) (fun y => hupper _ (hg y).2)
    (fun S U hSU => matrixEdges_normalized_large_cuts M hM β (β/4) (3*β/4)
      hn (by linarith) hrow hcol S U hSU)
  refine ⟨fun e => a+p*q e, ?_, ?_, ?_⟩
  · intro e
    have hqe := hq e
    constructor
    · change a≤a+p*q e
      exact le_add_of_nonneg_right (mul_nonneg hp.le hqe.1)
    · have hb : a+p ≤ 5/(β*n) := by
        dsimp [a,p]
        apply (le_div_iff₀ (mul_pos hβ hnR)).mpr
        have he : (β/(5*n)+4/(β*n))*(β*n)=β^2/5+4 := by field_simp <;> ring
        rw [he]
        nlinarith
      have hh := mul_le_of_le_one_right hp.le hqe.2
      change a+p*q e ≤ 5/(β*n)
      linarith
  · intro x
    have hsum : (∑ e : BipartiteEdges M, if e.1=x then a+p*q e else 0)=
        a*((∑ y, M x y : ℕ) : ℝ)+p*(f x/p) := by
      rw [← hl x,Finset.mul_sum]
      simp only [mul_ite,mul_zero]
      have hc : (∑ e : BipartiteEdges M, if e.1=x then a else 0)=
          a*((∑ y, M x y : ℕ) : ℝ) := by
        have hh := congrArg (fun z : ℕ => a*(z : ℝ)) (bipartiteEdges_row_degree M x)
        simpa only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
          Finset.mul_sum,mul_ite,mul_one,mul_zero] using hh
      rw [← hc,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    rw [hsum,mul_div_cancel₀ _ hp.ne']
    dsimp [f];ring
  · intro y
    have hsum : (∑ e : BipartiteEdges M, if e.2.1=y then a+p*q e else 0)=
        a*((∑ x, M x y : ℕ) : ℝ)+p*(g y/p) := by
      rw [← hr y,Finset.mul_sum]
      simp only [mul_ite,mul_zero]
      have hc : (∑ e : BipartiteEdges M, if e.2.1=y then a else 0)=
          a*((∑ x, M x y : ℕ) : ℝ) := by
        have hh := congrArg (fun z : ℕ => a*(z : ℝ)) (bipartiteEdges_column_degree M y)
        simpa only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
          Finset.mul_sum,mul_ite,mul_one,mul_zero] using hh
      rw [← hc,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    rw [hsum,mul_div_cancel₀ _ hp.ne']
    dsimp [g];ring

end Oberwolfach
