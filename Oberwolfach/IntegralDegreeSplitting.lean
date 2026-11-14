module

public import Mathlib.Tactic

@[expose] public section

/-! Finite integer degree choices for sparse degree corrections. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem balanced_integer_half_degrees {V : Type*} [Fintype V] (g : V → ℕ)
    (htotal : Even (∑ v,g v)) :
    ∃ gp gm : V → ℕ,(∀ v,gp v+gm v=g v) ∧ (∑ v,gp v=∑ v,gm v) ∧
      ∀ v,|(gp v : ℤ)-(gm v : ℤ)|≤1 := by
  classical
  let O := Finset.univ.filter (fun v=>g v%2=1)
  have hdecomp : (∑ v,g v)=2*(∑ v,g v/2)+O.card := by
    have hv (v : V) : g v=2*(g v/2)+(if v∈O then 1 else 0) := by
      have hm := Nat.mod_lt (g v) (by omega : 0<2)
      simp only [O,Finset.mem_filter,Finset.mem_univ,true_and]
      split_ifs <;> omega
    calc
      _ = ∑ v,(2*(g v/2)+(if v∈O then 1 else 0)) := Finset.sum_congr rfl (fun v _=>hv v)
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.card_filter]
        have heq : Finset.univ.filter (fun v=>v∈O)=O := by ext v;simp
        rw [heq]
  obtain ⟨j,hj⟩ := htotal
  have hOeven : O.card%2=0 := by omega
  obtain ⟨S,hSO,hScard⟩ := Finset.exists_subset_card_eq (s:=O) (n:=O.card/2) (Nat.div_le_self _ _)
  let gp (v : V) := g v/2+if v∈S then 1 else 0
  have hgp (v : V) : gp v≤g v := by
    by_cases hv : v∈S
    · have hodd : g v%2=1 := (Finset.mem_filter.mp (hSO hv)).2
      dsimp [gp]
      rw [if_pos hv]
      omega
    · simp only [gp,hv,ite_false,add_zero]
      exact Nat.div_le_self _ _
  let gm (v : V) := g v-gp v
  have hsum : 2*(∑ v,gp v)=∑ v,g v := by
    have hs : (∑ v,gp v)=(∑ v,g v/2)+S.card := by
      simp only [gp,Finset.sum_add_distrib,← Finset.card_filter]
      have heq : Finset.univ.filter (fun v=>v∈S)=S := by ext v;simp
      rw [heq]
    rw [hs,hScard]
    omega
  refine ⟨gp,gm,fun v=>by dsimp [gm];exact Nat.add_sub_of_le (hgp v),?_,?_⟩
  · have hs := Finset.sum_tsub_distrib Finset.univ (fun v _=>hgp v)
    change (∑ v,gm v)=(∑ v,g v)-(∑ v,gp v) at hs
    omega
  · intro v
    have hm := Nat.mod_lt (g v) (by omega : 0<2)
    have h := hgp v
    rw [abs_le]
    dsimp [gm,gp]
    by_cases hv : v∈S
    · have hodd : g v%2=1 := (Finset.mem_filter.mp (hSO hv)).2
      simp only [hv,ite_true]
      constructor <;> omega
    · simp only [hv,ite_false,add_zero]
      constructor <;> omega

theorem near_uniform_integer_demands {V : Type*} [Fintype V]
    (hn : 0<Fintype.card V) (T : ℕ) :
    ∃ f : V → ℕ,(∑ v,f v)=T ∧ ∀ v,|(f v : ℝ)-(T : ℝ)/Fintype.card V|≤1 := by
  classical
  let n := Fintype.card V
  have hm : T%n<n := Nat.mod_lt T hn
  obtain ⟨S,hS,hScard⟩ := Finset.exists_subset_card_eq (s:=Finset.univ (α:=V))
    (n:=T%n) (by simpa only [Finset.card_univ] using hm.le)
  let q := T/n
  let f (v : V) := q+if v∈S then 1 else 0
  have hsum : (∑ v,f v)=n*q+T%n := by
    simp only [f,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,← Finset.card_filter]
    change n*q+_=n*q+T%n
    congr 1
    rw [← hScard]
    congr 1
    ext v
    simp
  refine ⟨f,?_,?_⟩
  · rw [hsum]
    exact Nat.div_add_mod T n
  · intro v
    have hnR : (0 : ℝ)<n := by exact_mod_cast hn
    have hlo : (q : ℝ)≤(T : ℝ)/n := by
      apply (le_div_iff₀ hnR).mpr
      exact_mod_cast (Nat.div_mul_le_self T n)
    have hhi : (T : ℝ)/n≤q+1 := by
      apply (div_le_iff₀ hnR).mpr
      have hh : T≤(q+1)*n := by
        have hdiv := Nat.div_add_mod T n
        change n*q+T%n=T at hdiv
        nlinarith
      exact_mod_cast hh
    have hv : (q : ℝ)≤f v ∧ (f v : ℝ)≤q+1 := by
      dsimp [f]
      split_ifs <;> push_cast <;> constructor <;> linarith
    change |(f v : ℝ)-(T : ℝ)/n|≤1
    rw [abs_le]
    constructor <;> linarith [hv.1,hv.2]


/-- A prescribed residue has a representative in every interval of r
consecutive natural numbers. This chooses the hub deletion demands. -/
theorem residue_in_integer_interval (base d r : ℕ) (hr : 0<r) :
    ∃ k : ℕ,base≤k ∧ k<base+r ∧ k%r=d%r := by
  let q := base/r
  have hbase : r*q+base%r=base := Nat.div_add_mod base r
  have hb : base%r<r := Nat.mod_lt base hr
  have hd : d%r<r := Nat.mod_lt d hr
  by_cases h : base%r≤d%r
  · refine ⟨r*q+d%r,by omega,by omega,?_⟩
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,zero_add,Nat.mod_mod]
  · refine ⟨r*q+r+d%r,by omega,by omega,?_⟩
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,zero_add,Nat.mod_mod]

end Oberwolfach
