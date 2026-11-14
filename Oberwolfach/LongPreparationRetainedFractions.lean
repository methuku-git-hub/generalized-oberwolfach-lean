module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Discarding short lengths below the fixed threshold loses at most θ/100
of the factor, uniformly in the factor. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_retained_fractions (K:ℕ) (hK:0<K) (θ ℓ:ℝ) (hθ:0≤θ)
    (f:Fin K→ℝ) (hf:∀ i,0≤f i) (hsum:ℓ+∑ i,f i=1):
    let threshold:=θ/(100*(K:ℝ))
    let S:Finset (Fin K):=Finset.univ.filter (fun i=>threshold≤f i)
    let rare:=∑ i∈Finset.univ\S,f i;
    (∀ i∈S,threshold≤f i) ∧ 0≤rare ∧ rare≤θ/100 ∧
    ℓ+(∑ i∈S,f i)+rare=1:=by
  intro threshold S rare
  have hK':(0:ℝ)<K:=by exact_mod_cast hK
  have hden:(0:ℝ)<100*K:=by positivity
  have hthreshold:0≤threshold:=by dsimp [threshold];positivity
  have hsubset:S⊆Finset.univ:=Finset.subset_univ _
  have hrare0:0≤rare:=Finset.sum_nonneg (fun i _=>hf i)
  have hsbound:rare≤((Finset.univ\S).card:ℝ)*threshold:=by
    dsimp [rare]
    calc
      _ ≤ ∑ _i∈Finset.univ\S,threshold:=by
        apply Finset.sum_le_sum
        intro i hi
        have hn:i∉S:=(Finset.mem_sdiff.mp hi).2
        have hnot:¬threshold≤f i:=by
          intro h
          apply hn
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩
        exact (lt_of_not_ge hnot).le
      _ = _:=by simp
  have hcard:((Finset.univ\S).card:ℝ)≤K:=by
    exact_mod_cast (by simpa using (Finset.card_le_univ (Finset.univ\S)))
  have htop:((Finset.univ\S).card:ℝ)*threshold≤(K:ℝ)*threshold:=mul_le_mul_of_nonneg_right hcard hthreshold
  have hscale:(K:ℝ)*threshold=θ/100:=by
    dsimp [threshold]
    field_simp
  have hpartition:(∑ i∈S,f i)+(∑ i∈Finset.univ\S,f i)=∑ i,f i:=by
    exact Finset.sum_add_sum_compl S (fun i=>f i)
  refine ⟨?_,hrare0,?_,?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · exact (hsbound.trans htop).trans_eq hscale
  · dsimp [rare]
    linarith [hpartition,hsum]
end Oberwolfach
