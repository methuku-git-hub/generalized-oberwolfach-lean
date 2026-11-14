module

public import Oberwolfach.RawSelectedSpokeDegrees

@[expose] public section

/-! Two-sided selected-spoke degree estimates with explicit exponential
error, before any lower-degree or cut deduction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawSelectedSpokeMatrix_degree_tail
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hn : 0<Fintype.card V) (hm : 0<Fintype.card U) (hmhi : Fintype.card U≤Fintype.card V)
    (j : Γ⊕Color) (pH : ℝ) (hj : ∀ u,Sum.elim (q u) (s u) j=pH) (t : ℝ) (ht : 0<t) :
    1-4*Fintype.card V*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>(∀ v : V,|((∑ u,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)-pH*Fintype.card U|<t) ∧
        (∀ u : U,|((∑ v,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)-pH*Fintype.card V|<t)) := by
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hmR : (0:ℝ)<Fintype.card U := by exact_mod_cast hm
  have hmhiR : (Fintype.card U:ℝ)≤Fintype.card V := by exact_mod_cast hmhi
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hrows := rawIntervalSelectedLabelCount_common_event π d hd q hq hQ s hs hS hnoshort hm (fun _ _=>j)
    (fun v : V=>({v}:Finset V))
    (by intro v x hx y hy hxy;simp only [Finset.mem_singleton] at hx hy;exact (hxy (hx.trans hy.symm)).elim)
    (fun v=>Finset.singleton_nonempty v) 1 (by omega) (by intro v;simp) t ht
  simp only [Finset.prod_singleton,hj,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_one,one_mul] at hrows
  have hcols := rawIntervalSelectedNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn (fun _ _=>j)
    (fun _ : U=>(Finset.univ : Finset V)) (fun u : U=>({u}:Finset U))
    (fun u=>Finset.singleton_nonempty u) 1 (by omega) (by intro u;simp) t ht
  simp only [Finset.card_univ,Finset.prod_singleton,hj,Nat.cast_one,one_mul] at hcols
  let f := 2*Fintype.card V*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V))
  have hrowBound : (Fintype.card V:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U)))≤f := by
    have he : Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U))≤
        Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V)) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      apply mul_le_mul_of_nonpos_left _ (by nlinarith only [sq_nonneg t])
      gcongr
    dsimp [f]
    nlinarith only [mul_le_mul_of_nonneg_left he (show (0:ℝ)≤2*Fintype.card V by positivity)]
  have hcolBound : (Fintype.card U:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V)))≤f := by
    dsimp [f]
    nlinarith only [mul_le_mul_of_nonneg_right hmhiR
      (show 0≤2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V)) by positivity)]
  have hR := (sub_le_sub_left hrowBound 1).trans hrows
  have hC := (sub_le_sub_left hcolBound 1).trans hcols
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ v : V,|rawIntervalSelectedLabelCount π d σ (fun _=>j) {v}-(Fintype.card U:ℝ)*pH|<t)
    _ f hC
  have hbase := (sub_le_sub_right hR f).trans hjoint
  have he : 1-f-f=1-4*Fintype.card V*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V)) := by dsimp [f];ring
  rw [he] at hbase
  apply hbase.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  constructor
  · intro v
    rw [rawSelectedSpokeMatrix_row]
    simpa only [mul_comm] using hσ.1 v
  · intro u
    rw [rawSelectedSpokeMatrix_col]
    simpa only [mul_comm] using hσ.2 u

end Oberwolfach
