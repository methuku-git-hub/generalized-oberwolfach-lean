module

public import Oberwolfach.ExponentialSelectedCuts
public import Oberwolfach.RawSelectedDegreeTails
public import Oberwolfach.RawSelectedSpokeCuts

@[expose] public section

/-! Uniform exponential large-cut bounds for either selected spoke type.
The actual interval sampling law, all fixed marginals and both part sizes
are retained throughout the degree and quadratic-cut deductions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawSelectedSpokeMatrix_large_cuts_exponential
    (pstar ω : ℝ) (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) (d : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Γ⊕Color),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pH : ℝ,pstar≤pH → (∀ u,Sum.elim (q u) (s u) j=pH) →
    1-6*Fintype.card V*Real.exp
      (-min (2*(min (pstar/4) (pstar*ω/4))^2/(4*(d:ℝ)+3)^2)
        ((pstar^2*ω/128)^2/(4*(d:ℝ)+3)^2)*Fintype.card V)≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (X : Finset V) (Y : Finset U),
        1-pstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
        pstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
          (bipartiteMatrixCut (rawSelectedSpokeMatrix π d σ j) X Y:ℝ)) := by
  let ε := min (pstar/4) (pstar*ω/4)
  let ζ : ℝ := pstar^2*ω/128
  let A : ℝ := 4*d+3
  let c := min (2*ε^2/A^2) (ζ^2/A^2)
  have hε : 0<ε := by dsimp [ε];positivity
  have hζ : 0<ζ := by dsimp [ζ];positivity
  have hA : 0<A := by dsimp [A];positivity
  obtain ⟨N,hN1,hN⟩ := rawSelectedCutCount_quadratic_exponential_event d hd ζ hζ
  refine ⟨N,hN1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi π q hq hQ s hs hS j hnoshort pH hpH hj
  let n := Fintype.card V
  let m := Fintype.card U
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by dsimp [n];omega)
  have hm0 : (0:ℝ)<m := (mul_pos hω hn0).trans_le hmlo
  have hm : 0<m := by exact_mod_cast hm0
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hdegree := rawSelectedSpokeMatrix_degree_tail π d hd q hq hQ s hs hS hnoshort hn hm hmhi
    j pH hj (ε*n) (by positivity)
  have hmin : 1-4*n*Real.exp (-2*(ε*n)^2/(A^2*n))≤μ.probability
      (fun σ=>(∀ v : V,pstar*(m:ℝ)/2≤((∑ u,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)) ∧
        (∀ u : U,pstar*(n:ℝ)/2≤((∑ v,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ))) := by
    apply hdegree.trans
    apply finiteLaw_probability_mono
    intro σ hσ
    constructor
    · intro v
      have hh := (abs_lt.mp (hσ.1 v)).1
      have hmul := mul_le_mul_of_nonneg_right hpH hm0.le
      have hεω := mul_le_mul_of_nonneg_right (min_le_right (pstar/4) (pstar*ω/4)) hn0.le
      have hscale := mul_le_mul_of_nonneg_left hmlo hpstar.le
      dsimp only [ε,n,m] at hh ⊢
      nlinarith only [hh,hmul,hεω,hscale,mul_pos hpstar hm0]
    · intro u
      have hh := (abs_lt.mp (hσ.2 u)).1
      have hmul := mul_le_mul_of_nonneg_right hpH hn0.le
      have hεn := mul_le_mul_of_nonneg_right (min_le_left (pstar/4) (pstar*ω/4)) hn0.le
      dsimp only [ε,n] at hh ⊢
      nlinarith only [hh,hmul,hεn,mul_pos hpstar hn0]
  have hcuts := hN V U Γ Color hnN hm hmhi π q hq hQ s hs hS j hnoshort pH hj
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>(∀ v : V,pstar*(m:ℝ)/2≤((∑ u,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)) ∧
        (∀ u : U,pstar*(n:ℝ)/2≤((∑ v,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)))
    _ (2*Real.exp (-(ζ^2/A^2)*n)) hcuts
  have hbase := (sub_le_sub_right hmin (2*Real.exp (-(ζ^2/A^2)*n))).trans hjoint
  have heD : -2*(ε*n)^2/(A^2*n)=-(2*ε^2/A^2)*n := by field_simp [ne_of_gt hn0,ne_of_gt hA] <;> ring
  have heR : Real.exp (-(2*ε^2/A^2)*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_left (2*ε^2/A^2) (ζ^2/A^2)) hn0.le
    change c*n≤(2*ε^2/A^2)*n at h
    linarith only [h]
  have heC : Real.exp (-(ζ^2/A^2)*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (min_le_right (2*ε^2/A^2) (ζ^2/A^2)) hn0.le
    change c*n≤(ζ^2/A^2)*n at h
    linarith only [h]
  have hbD : 4*n*Real.exp (-2*(ε*n)^2/(A^2*n))≤4*n*Real.exp (-c*n) := by
    rw [heD]
    exact mul_le_mul_of_nonneg_left heR (by positivity)
  have hbC : 2*Real.exp (-(ζ^2/A^2)*n)≤2*n*Real.exp (-c*n) :=
    mul_le_mul (by linarith only [hn1]) heC (by positivity) (by positivity)
  have hbound : 1-6*n*Real.exp (-c*n)≤1-4*n*Real.exp (-2*(ε*n)^2/(A^2*n))-2*Real.exp (-(ζ^2/A^2)*n) := by
    linarith only [hbD,hbC]
  apply (hbound.trans hbase).trans
  apply finiteLaw_probability_mono
  intro σ hσ X Y hlarge
  have hquad (S : Finset V) (T : Finset U) :
      |(bipartiteMatrixCut (rawSelectedSpokeMatrix π d σ j) S T:ℝ)-pH*S.card*T.card|≤
        (pstar^2/128)*(n:ℝ)*m := by
    unfold bipartiteMatrixCut
    rw [rawSelectedSpokeMatrix_cut]
    have hh := (hσ.2 S T).le
    have hscale := mul_le_mul_of_nonneg_left hmlo (by positivity : (0:ℝ)≤pstar^2/128*n)
    dsimp only [ζ,n,m] at hh ⊢
    nlinarith only [hh,hscale]
  have hcross := mul_lt_mul_of_pos_right hlarge (mul_pos hn0 hm0)
  have heq : ((X.card:ℝ)/n+(Y.card:ℝ)/m)*((n:ℝ)*m)=(m:ℝ)*X.card+(n:ℝ)*Y.card := by field_simp <;> ring
  change (1-pstar/8)*((n:ℝ)*m)<((X.card:ℝ)/n+(Y.card:ℝ)/m)*((n:ℝ)*m) at hcross
  rw [heq] at hcross
  exact bipartiteMatrixCut_large_of_degree_and_quadratic (rawSelectedSpokeMatrix π d σ j)
    (rawSelectedSpokeMatrix_le_one π d σ j) hn hm pstar pH (pstar/16) (pstar^2/128)
    hpstar hpstar1 hpH le_rfl le_rfl hσ.1.1 hσ.1.2 hquad X Y
    (by convert hcross using 1 <;> ring)

end Oberwolfach
