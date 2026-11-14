module

public import Oberwolfach.RawIntervalSpokeMatrix
public import Oberwolfach.ConfigurationFailureMargins
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Minimum degrees on both sides of the actual ordinary spoke sample,
with a common event and a threshold uniform over all marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawIntervalSpokeMatrix_degree_event
    (pstar ω : ℝ) (hpstar : 0<pstar) (hω : 0<ω) (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V)
      (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x k,0<k → k<2*d+1 → (π^k) x≠x) →
    ∀ pH : ℝ,pstar≤pH → (∀ u,s u j=pH) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability (fun σ=>
        (∀ v : V,pstar*(Fintype.card U:ℝ)/2≤((∑ u,rawIntervalSpokeMatrix π d σ j v u:ℕ):ℝ)) ∧
        (∀ u : U,pstar*(Fintype.card V:ℝ)/2≤((∑ v,rawIntervalSpokeMatrix π d σ j v u:ℕ):ℝ))) := by
  let ε := min (pstar/4) (pstar*ω/4)
  have hε : 0<ε := lt_min (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := linear_deviation_failure_eventually_small 1 ((4*(d:ℝ)+3)^2) ε
    (by positivity) hε 1 (q₀+1)
  refine ⟨max N 2,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi π q hq hQ s hs hS j hnoshort pH hpH hj
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := (mul_pos hω hn0).trans_le hmlo
  have hm : 0<Fintype.card U := by exact_mod_cast hm0
  have hmhiR : (Fintype.card U:ℝ)≤n := by exact_mod_cast hmhi
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hrows := rawIntervalLabelCount_common_event π d hd q hq hQ s hs hS hnoshort hm j
    (fun v : V=>({v}:Finset V))
    (by intro v x hx y hy hxy;simp only [Finset.mem_singleton] at hx hy;exact (hxy (hx.trans hy.symm)).elim)
    (fun v=>Finset.singleton_nonempty v) 1 (by omega) (by intro v;simp) (ε*n) (by positivity)
  simp only [Finset.card_singleton,pow_one,hj,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Nat.cast_one,one_mul] at hrows
  have hcols := rawIntervalNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn j
    (fun _ : U=>(Finset.univ : Finset V)) (fun u : U=>({u}:Finset U))
    (fun u=>Finset.singleton_nonempty u) 1 (by omega) (by intro u;simp) (ε*n) (by positivity)
  simp only [Finset.card_univ,Finset.prod_singleton,hj,Nat.cast_one,one_mul] at hcols
  have htrow := hN n (by dsimp [n] at *;omega) n ((4*(d:ℝ)+3)^2*Fintype.card U)
    hn0.le (by simp) (by positivity) (mul_le_mul_of_nonneg_left hmhiR (by positivity))
  have htcol := hN n (by dsimp [n] at *;omega) (Fintype.card U) ((4*(d:ℝ)+3)^2*n)
    (by positivity) (by simpa using hmhiR) (by positivity) le_rfl
  have hrprob : 1-1/(n:ℝ)^(q₀+1)≤μ.probability
      (fun σ=>∀ v : V,|rawIntervalLabelCount π d σ j {v}-(Fintype.card U:ℝ)*pH|<ε*n) :=
    (sub_le_sub_left htrow 1).trans hrows
  have hcprob : 1-1/(n:ℝ)^(q₀+1)≤μ.probability
      (fun σ=>∀ u : U,|rawIntervalNeighbourCount π d σ j Finset.univ {u}-(n:ℝ)*pH|<ε*n) :=
    (sub_le_sub_left htcol 1).trans hcols
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ v : V,|rawIntervalLabelCount π d σ j {v}-(Fintype.card U:ℝ)*pH|<ε*n)
    _ (1/(n:ℝ)^(q₀+1)) hcprob
  have hjoint' : 1-2/(n:ℝ)^(q₀+1)≤μ.probability
      (fun σ=>(∀ v : V,|rawIntervalLabelCount π d σ j {v}-(Fintype.card U:ℝ)*pH|<ε*n) ∧
        (∀ u : U,|rawIntervalNeighbourCount π d σ j Finset.univ {u}-(n:ℝ)*pH|<ε*n)) := by
    have hh := (sub_le_sub_right hrprob (1/(n:ℝ)^(q₀+1))).trans hjoint
    convert hh using 1 <;> ring
  have hsum := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  apply ((sub_le_sub_left hsum 1).trans hjoint').trans
  apply finiteLaw_probability_mono
  intro σ hσ
  constructor
  · intro v
    rw [rawIntervalSpokeMatrix_row]
    have hh := (abs_lt.mp (hσ.1 v)).1
    have hmul := mul_le_mul_of_nonneg_right hpH hm0.le
    have hεω := mul_le_mul_of_nonneg_right (min_le_right (pstar/4) (pstar*ω/4)) hn0.le
    have hscale := mul_le_mul_of_nonneg_left hmlo hpstar.le
    dsimp only [ε] at hh
    nlinarith only [hh,hmul,hεω,hscale,mul_pos hpstar hm0]
  · intro u
    rw [rawIntervalSpokeMatrix_col]
    have hh := (abs_lt.mp (hσ.2 u)).1
    have hmul := mul_le_mul_of_nonneg_right hpH hn0.le
    have hεn := mul_le_mul_of_nonneg_right (min_le_left (pstar/4) (pstar*ω/4)) hn0.le
    dsimp only [ε] at hh
    nlinarith only [hh,hmul,hεn,mul_pos hpstar hn0]

end Oberwolfach
