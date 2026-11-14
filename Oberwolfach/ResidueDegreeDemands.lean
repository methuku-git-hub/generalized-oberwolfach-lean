module

public import Oberwolfach.IntegralDegreeSplitting

@[expose] public section

/-! Spoke deletion demands with prescribed hub residues and almost equal
rim degrees. The sizes of the two vertex classes may differ. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_average_interval {I : Type*} [Fintype I]
    (hI : 0<Fintype.card I) (f : I → ℝ) {a b : ℝ}
    (hf : ∀ i,a≤f i ∧ f i≤b) :
    a≤(∑ i,f i)/Fintype.card I ∧ (∑ i,f i)/Fintype.card I≤b := by
  have hn : (0 : ℝ)<Fintype.card I := by exact_mod_cast hI
  constructor
  · apply (le_div_iff₀ hn).mpr
    calc
      _ = ∑ _ : I,a := by simp;ring
      _ ≤ _ := Finset.sum_le_sum (fun i _=>(hf i).1)
  · apply (div_le_iff₀ hn).mpr
    calc
      _ ≤ ∑ _ : I,b := Finset.sum_le_sum (fun i _=>(hf i).2)
      _ = _ := by simp;ring

theorem residue_degree_demands {V U : Type*} [Fintype V] [Fintype U]
    (hn : 0<Fintype.card V) (hs : 0<Fintype.card U)
    (hsn : Fintype.card U≤Fintype.card V)
    (d : U → ℕ) (base r : ℕ) (hr : 0<r)
    {ω δ : ℝ} (hω : 0<ω) (hωn : ω*Fintype.card V≤Fintype.card U)
    (hδ : 0≤δ) (hrδ : (r : ℝ)≤δ*base) (hunit : 1≤δ*ω*base) :
    ∃ (k : U → ℕ) (f : V → ℕ) (T : ℕ),
      (∀ u,base≤k u ∧ k u<base+r ∧ k u%r=d u%r) ∧
      (∑ u,k u=T) ∧ (∑ v,f v=T) ∧
      (ω*base≤(T : ℝ)/Fintype.card V) ∧
      ((T : ℝ)/Fintype.card V≤base+r) ∧
      (∀ v,|(f v : ℝ)-(T : ℝ)/Fintype.card V|≤1) ∧
      (∀ u,(k u : ℝ)≤(1+δ)*(T : ℝ)/Fintype.card U) ∧
      (∀ v,(f v : ℝ)≤(1+δ)*(T : ℝ)/Fintype.card V) := by
  classical
  choose k hk using (fun u=>residue_in_integer_interval base (d u) r hr)
  let T := ∑ u,k u
  obtain ⟨f,hf,he⟩ := near_uniform_integer_demands (V:=V) hn T
  have hnR : (0 : ℝ)<Fintype.card V := by exact_mod_cast hn
  have hsR : (0 : ℝ)<Fintype.card U := by exact_mod_cast hs
  have hsNR : (Fintype.card U : ℝ)≤Fintype.card V := by exact_mod_cast hsn
  have hklo (u : U) : (base : ℝ)≤k u := by exact_mod_cast (hk u).1
  have hkhi (u : U) : (k u : ℝ)≤base+r := by exact_mod_cast (hk u).2.1.le
  have hTlo : (Fintype.card U : ℝ)*base≤T := by
    calc
      _ = ∑ _ : U,(base : ℝ) := by simp
      _ ≤ ∑ u,(k u : ℝ) := Finset.sum_le_sum (fun u _=>hklo u)
      _ = _ := by simp [T]
  have hThi : (T : ℝ)≤Fintype.card U*(base+r) := by
    calc
      _ = ∑ u,(k u : ℝ) := by simp [T]
      _ ≤ ∑ _ : U,((base : ℝ)+r) := Finset.sum_le_sum (fun u _=>hkhi u)
      _ = _ := by simp;ring
  have hmeanlo : ω*base≤(T : ℝ)/Fintype.card V := by
    apply (le_div_iff₀ hnR).mpr
    have := mul_le_mul_of_nonneg_right hωn (Nat.cast_nonneg base : (0 : ℝ)≤base)
    nlinarith
  have hmeanhi : (T : ℝ)/Fintype.card V≤base+r := by
    apply (div_le_iff₀ hnR).mpr
    have := mul_le_mul_of_nonneg_right hsNR (show (0 : ℝ)≤base+r by positivity)
    nlinarith
  have hublo : (base : ℝ)≤(T : ℝ)/Fintype.card U := by
    apply (le_div_iff₀ hsR).mpr
    nlinarith
  refine ⟨k,f,T,hk,rfl,hf,hmeanlo,hmeanhi,he,?_,?_⟩
  · intro u
    have hm := mul_le_mul_of_nonneg_left hublo hδ
    calc
      (k u : ℝ) ≤ base+r := hkhi u
      _ ≤ (1+δ)*((T : ℝ)/Fintype.card U) := by nlinarith
      _ = _ := by ring
  · intro v
    have hm := mul_le_mul_of_nonneg_left hmeanlo hδ
    have hh := (abs_le.mp (he v)).2
    calc
      (f v : ℝ) ≤ (1+δ)*((T : ℝ)/Fintype.card V) := by nlinarith
      _ = _ := by ring

end Oberwolfach
