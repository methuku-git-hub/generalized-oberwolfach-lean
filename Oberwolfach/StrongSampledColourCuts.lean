module

public import Oberwolfach.ColourDegreeEvent
public import Oberwolfach.ColourCutEvent
public import Oberwolfach.StrongRawColourCutBounds
public import Oberwolfach.ConfigurationFailureMargins
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! A common large-cut event for independently coloured and oriented
physical edges. The cut constants precede the actual colour probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourOrientation_large_cuts_strong
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar)
    (k q₀ : ℕ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V), (∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (ρ : Fin k→ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1),
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
        (fun σ=>∀ a : Fin k,pstar≤ρ a → ∀ δ : ℝ,δ≤α/32 → δ≤ρ a/64 → ∀ S T : Finset V,
          (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
          (α*ρ a/4)*Fintype.card V*min (S.card:ℝ) T.card≤
            (matrixCut (sampledColourOrientation P σ a) S T:ℝ)) := by
  let ε : ℝ := pstar/32
  let q : ℝ := α*pstar^2/1024
  have hε : 0<ε := by dsimp [ε];positivity
  have hq : 0<q := by dsimp [q];positivity
  obtain ⟨N₁,hN₁⟩ := linear_deviation_failure_eventually_small (3*k) 1 ε
    (by norm_num) hε 1 (q₀+1)
  obtain ⟨N₂,hN₂⟩ := sampledColourCut_quadratic_event_pow k hq (q₀+1)
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V _ _ hnN P hP ρ hρ hsum
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)
  have hd := sampledColourDegrees_common_event P P ρ hρ hsum (t:=ε*n) (by positivity)
  have ht := hN₁ n (by dsimp [n] at *;omega) (3*k*n) n
    (by positivity) (by simp) hn0 (by simp)
  have htail : 6*k*n*Real.exp (-2*(ε*n)^2/n)≤1/(n:ℝ)^(q₀+1) := by
    convert ht using 1 <;> ring
  have hdegrees : 1-1/(n:ℝ)^(q₀+1)≤μ.probability
      (fun σ=>∀ a v,
        |((∑ y,sampledColourOrientation P σ a v y:ℕ):ℝ)-ρ a/2*P.degree v|<ε*n ∧
        |((∑ y,sampledColourOrientation P σ a y v:ℕ):ℝ)-ρ a/2*P.degree v|<ε*n ∧
        |(sampledColourDegree P (fun e=>(σ e).1) a v:ℝ)-ρ a*P.degree v|<ε*n) :=
    (sub_le_sub_left htail 1).trans hd
  have hcuts := hN₂ V (by dsimp [n] at *;omega) P ρ hρ hsum
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ a v,
        |((∑ y,sampledColourOrientation P σ a v y:ℕ):ℝ)-ρ a/2*P.degree v|<ε*n ∧
        |((∑ y,sampledColourOrientation P σ a y v:ℕ):ℝ)-ρ a/2*P.degree v|<ε*n ∧
        |(sampledColourDegree P (fun e=>(σ e).1) a v:ℝ)-ρ a*P.degree v|<ε*n)
    _ (1/(n:ℝ)^(q₀+1)) hcuts
  have hbase := (sub_le_sub_right hdegrees (1/(n:ℝ)^(q₀+1))).trans hjoint
  have hsumerr := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤(1-1/(n:ℝ)^(q₀+1))-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsumerr 1 using 1 <;> ring
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
