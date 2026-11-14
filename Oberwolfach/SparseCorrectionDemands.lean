module

public import Oberwolfach.IntegralDegreeSplitting

@[expose] public section

/-! Integer demands for simultaneous rim and spoke deletions. The signed
imbalance is retained exactly, and the two oriented demands have equal totals. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem balanced_half_degrees_real {V : Type*} [Fintype V] (g : V → ℕ)
    (htotal : Even (∑ v,g v)) :
    ∃ gp gm : V → ℕ,(∀ v,gp v+gm v=g v) ∧ (∑ v,gp v=∑ v,gm v) ∧
      (∀ v,|(gp v : ℝ)-(g v : ℝ)/2|≤1/2) ∧
      (∀ v,|(gm v : ℝ)-(g v : ℝ)/2|≤1/2) := by
  obtain ⟨gp,gm,hs,ht,hd⟩ := balanced_integer_half_degrees g htotal
  refine ⟨gp,gm,hs,ht,?_,?_⟩
  all_goals
    intro v
    have hv : |(gp v : ℝ)-(gm v : ℝ)|≤1 := by exact_mod_cast hd v
    have hsum : (gp v : ℝ)+gm v=g v := by exact_mod_cast hs v
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1,hv.2]

/-- Near-uniform demands, signed balance, and parity suffice to choose
both oriented rim demands. No graph existence assertion is assumed here. -/
theorem signed_balanced_degree_demands {V : Type*} [Fintype V]
    (hn : 0<Fintype.card V) (hv : V → ℕ) (b : V → ℤ)
    (hb : Even (∑ v,b v)) {T e : ℝ}
    (_he : 0≤e) (hmean : (∑ v,(hv v : ℝ))/Fintype.card V=T)
    (hh : ∀ v,|(hv v : ℝ)-T|≤1)
    (hbnd : ∀ v,|(b v : ℝ)|≤e)
    (hpos : e+2≤2*T) :
    ∃ gp gm : V → ℕ,
      (∀ v,(gp v : ℤ)+gm v=2*(hv v : ℤ)+b v) ∧
      (∑ v,gp v=∑ v,gm v) ∧
      (|(∑ v,(gp v : ℝ))/Fintype.card V-T|≤e/2) ∧
      (∀ v,|(gp v : ℝ)-(∑ x,(gp x : ℝ))/Fintype.card V|≤3/2+e) ∧
      (∀ v,|(gm v : ℝ)-(∑ x,(gp x : ℝ))/Fintype.card V|≤3/2+e) := by
  classical
  have hnR : (0 : ℝ)<Fintype.card V := by exact_mod_cast hn
  have hz (v : V) : 0≤2*(hv v : ℤ)+b v := by
    have hh' := (abs_le.mp (hh v)).1
    have hb' := (abs_le.mp (hbnd v)).1
    have hr : (0 : ℝ)≤2*(hv v : ℝ)+b v := by linarith
    exact_mod_cast hr
  let g (v : V) := (2*(hv v : ℤ)+b v).toNat
  have hg (v : V) : (g v : ℤ)=2*(hv v : ℤ)+b v := Int.toNat_of_nonneg (hz v)
  have hgr (v : V) : (g v : ℝ)=2*(hv v : ℝ)+b v := by exact_mod_cast hg v
  have hgeven : Even (∑ v,g v) := by
    have hs : ((∑ v,g v : ℕ) : ℤ)=2*(∑ v,(hv v : ℤ))+(∑ v,b v) := by
      push_cast
      simp_rw [hg]
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hev : Even (((∑ v,g v : ℕ) : ℤ)) := by
      rw [hs]
      exact (even_two_mul _).add hb
    exact_mod_cast hev
  obtain ⟨gp,gm,hs,ht,hp,hm⟩ := balanced_half_degrees_real g hgeven
  have hsum : (∑ v,(gp v : ℝ))=(∑ v,(gm v : ℝ)) := by exact_mod_cast ht
  have hsplit (v : V) : (gp v : ℝ)+gm v=2*(hv v : ℝ)+b v := by
    rw [← hgr v]
    exact_mod_cast hs v
  have htot : 2*(∑ v,(gp v : ℝ))=2*(∑ v,(hv v : ℝ))+(∑ v,(b v : ℝ)) := by
    calc
      _ = (∑ v,(gp v : ℝ))+(∑ v,(gm v : ℝ)) := by rw [← hsum];ring
      _ = ∑ v,((gp v : ℝ)+gm v) := (Finset.sum_add_distrib).symm
      _ = _ := by simp_rw [hsplit];rw [Finset.sum_add_distrib,← Finset.mul_sum]
  have hbtotal : |∑ v,(b v : ℝ)|≤Fintype.card V*e := by
    calc
      _ ≤ ∑ v,|(b v : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : V,e := Finset.sum_le_sum (fun v _=>hbnd v)
      _ = _ := by simp
  have havg : |(∑ v,(gp v : ℝ))/Fintype.card V-T|≤e/2 := by
    rw [abs_le] at hbtotal ⊢
    have hmean' := (div_eq_iff (ne_of_gt hnR)).mp hmean
    constructor
    · have h' : (T-e/2)*Fintype.card V≤(∑ v,(gp v : ℝ)) := by nlinarith [hbtotal.1]
      have := (le_div_iff₀ hnR).mpr h'
      linarith
    · have h' : (∑ v,(gp v : ℝ))≤(T+e/2)*Fintype.card V := by nlinarith [hbtotal.2]
      have := (div_le_iff₀ hnR).mpr h'
      linarith
  refine ⟨gp,gm,?_,ht,havg,?_,?_⟩
  · intro v
    have hv' : (gp v : ℤ)+gm v=g v := by exact_mod_cast hs v
    exact hv'.trans (hg v)
  all_goals
    intro v
    have hh' := abs_le.mp (hh v)
    have hb' := abs_le.mp (hbnd v)
    have ha' := abs_le.mp havg
    have hp' := abs_le.mp (hp v)
    have hm' := abs_le.mp (hm v)
    rw [hgr v] at hp' hm'
    rw [abs_le]
    constructor <;> linarith [hh'.1,hh'.2,hb'.1,hb'.2,ha'.1,ha'.2,hp'.1,hp'.2,hm'.1,hm'.2]

end Oberwolfach
