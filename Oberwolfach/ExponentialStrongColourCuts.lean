module

public import Oberwolfach.ExponentialColourCuts
public import Oberwolfach.StrongSampledColourCuts

@[expose] public section

/-! Uniform exponential probability for the deterministic strong physical
cut criterion, before choosing any permutation of the columns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourOrientation_large_cuts_exponential
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar) (k : ℕ) :
    ∃ N : ℕ,1≤N ∧ ∀ (V : Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V),(∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (ρ : Fin k→ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1),
    1-8*k*Fintype.card V*Real.exp
      (-min (2*(pstar/32)^2) ((α*pstar^2/1024)^2/4)*Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
      (fun σ=>∀ a : Fin k,pstar≤ρ a → ∀ δ : ℝ,δ≤α/32 → δ≤ρ a/64 → ∀ S T : Finset V,
        (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
        (α*ρ a/4)*Fintype.card V*min (S.card:ℝ) T.card≤
          (matrixCut (sampledColourOrientation P σ a) S T:ℝ)) := by
  let ε : ℝ := pstar/32
  let q : ℝ := α*pstar^2/1024
  let c := min (2*ε^2) (q^2/4)
  have hε : 0<ε := by dsimp [ε];positivity
  have hq : 0<q := by dsimp [q];positivity
  obtain ⟨N,hN1,hN⟩ := sampledColourCut_quadratic_exponential_event k hq
  refine ⟨N,hN1,?_⟩
  intro V _ _ hnN P hP ρ hρ hsum
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by dsimp [n];omega)
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)
  have hd := sampledColourDegrees_common_event P P ρ hρ hsum (t:=ε*n) (by positivity)
  have hcuts := hN V hnN P ρ hρ hsum
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ a v,
      |((∑ y,sampledColourOrientation P σ a v y:ℕ):ℝ)-ρ a/2*P.degree v|<ε*n ∧
      |((∑ y,sampledColourOrientation P σ a y v:ℕ):ℝ)-ρ a/2*P.degree v|<ε*n ∧
      |(sampledColourDegree P (fun e=>(σ e).1) a v:ℝ)-ρ a*P.degree v|<ε*n)
    _ (2*k*Real.exp (-(q^2/4)*n)) hcuts
  have hbase := (sub_le_sub_right hd (2*k*Real.exp (-(q^2/4)*n))).trans hjoint
  have he : -2*(ε*n)^2/n=-(2*ε^2)*n := by field_simp [ne_of_gt hn0] <;> ring
  have heD : Real.exp (-(2*ε^2)*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_left (2*ε^2) (q^2/4)) hn0.le
    change c*n≤(2*ε^2)*n at h
    linarith only [h]
  have heC : Real.exp (-(q^2/4)*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right (2*ε^2) (q^2/4)) hn0.le
    change c*n≤(q^2/4)*n at h
    linarith only [h]
  have hbD : 6*k*n*Real.exp (-2*(ε*n)^2/n)≤6*k*n*Real.exp (-c*n) := by
    rw [he]
    exact mul_le_mul_of_nonneg_left heD (by positivity)
  have hbC : 2*k*Real.exp (-(q^2/4)*n)≤2*k*n*Real.exp (-c*n) := by
    apply mul_le_mul _ heC (by positivity) (by positivity)
    have h := mul_le_mul_of_nonneg_left hn1 (show (0:ℝ)≤2*k by positivity)
    simpa only [mul_one] using h
  have hbound : 1-8*k*n*Real.exp (-c*n)≤
      (1-6*k*n*Real.exp (-2*(ε*n)^2/n))-2*k*Real.exp (-(q^2/4)*n) := by
    linarith only [hbD,hbC]
  apply (hbound.trans hbase).trans
  apply finiteLaw_probability_mono
  intro σ hσ a ha δ hδα hδρ S T hlarge
  have hrow (v : V) : ρ a*n/4-ε*n≤((∑ y,sampledColourOrientation P σ a v y:ℕ):ℝ) := by
    have hh := (abs_lt.mp (hσ.1 a v).1).1
    have hdeg := mul_le_mul_of_nonneg_left (hP v) (div_nonneg (hρ a) (by norm_num : (0:ℝ)≤2))
    have hpos := mul_nonneg (hρ a) (mul_nonneg hα.le hn0.le)
    nlinarith only [hh,hdeg,hpos]
  have hcol (v : V) : ρ a*n/4-ε*n≤((∑ y,sampledColourOrientation P σ a y v:ℕ):ℝ) := by
    have hh := (abs_lt.mp (hσ.1 a v).2.1).1
    have hdeg := mul_le_mul_of_nonneg_left (hP v) (div_nonneg (hρ a) (by norm_num : (0:ℝ)≤2))
    have hpos := mul_nonneg (hρ a) (mul_nonneg hα.le hn0.le)
    nlinarith only [hh,hdeg,hpos]
  have hh := matrixCut_large_of_degree_and_quadratic_strong P (sampledColourOrientation P σ a)
    hα.le hα1 (hρ a) hδα hδρ
    (by dsimp [ε,n];nlinarith only [mul_le_mul_of_nonneg_right ha hn0.le])
    (by
      have hs : pstar^2≤(ρ a)^2 := by nlinarith only [ha,hpstar,hρ a]
      dsimp [q]
      nlinarith only [mul_le_mul_of_nonneg_left hs hα.le])
    (by intro x y;unfold sampledColourOrientation;split_ifs <;> omega)
    hP hrow hcol (fun X Y=>hσ.2 a X Y) S T hlarge
  exact hh

end Oberwolfach
