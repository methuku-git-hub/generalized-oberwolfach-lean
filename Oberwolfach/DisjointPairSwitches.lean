module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Simultaneous switches on disjoint pairs are a single permutation of the
original coordinates. Weighted sums change by the explicitly computed
contribution of each pair. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pairSwitchPermutation {I E : Type*} [Fintype I] [DecidableEq E]
    (ι : (I×Bool)↪E) : Equiv.Perm E :=
  Equiv.Perm.viaFintypeEmbedding (Equiv.prodCongr (Equiv.refl I) Bool.involutive_not.toPerm) ι

theorem pairSwitchPermutation_apply {I E : Type*} [Fintype I] [DecidableEq E]
    (ι : (I×Bool)↪E) (i : I) (b : Bool) :
    pairSwitchPermutation ι (ι (i,b))=ι (i,!b) := by
  simp only [pairSwitchPermutation,Equiv.Perm.viaFintypeEmbedding_apply_image]
  rfl

theorem pairSwitchPermutation_fixed {I E : Type*} [Fintype I] [DecidableEq E]
    (ι : (I×Bool)↪E) (e : E) (he : e∉Set.range ι) : pairSwitchPermutation ι e=e :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ he

theorem sum_supported_embedding {I E R : Type*} [Fintype I] [Fintype E]
    [AddCommMonoid R] (ι : I↪E) (f : E → R)
    (hf : ∀ e,e∉Set.range ι → f e=0) : (∑ e,f e)=∑ i,f (ι i) := by
  classical
  calc
    (∑ e,f e)=∑ e∈Finset.univ.image ι,f e := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e _ he
      apply hf e
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using he
    _ = ∑ i,f (ι i) := Finset.sum_image (fun _ _ _ _ h => ι.injective h)

theorem pair_switch_weighted_difference {I E C R : Type*}
    [Fintype I] [Fintype E] [DecidableEq E] [CommRing R]
    (ι : (I×Bool)↪E) (σ : E → C) (t : E → R) (g : C → R) :
    (∑ e,t e*g (σ (pairSwitchPermutation ι e)))-(∑ e,t e*g (σ e))=
      ∑ i,(t (ι (i,false))-t (ι (i,true)))*
        (g (σ (ι (i,true)))-g (σ (ι (i,false)))) := by
  rw [← Finset.sum_sub_distrib]
  rw [sum_supported_embedding ι _ (by
    intro e he
    rw [pairSwitchPermutation_fixed ι e he,sub_self])]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool,pairSwitchPermutation_apply,Bool.not_true,Bool.not_false]
  ring

theorem pair_switch_preserves_weighted_sum {I E C R : Type*}
    [Fintype I] [Fintype E] [DecidableEq E] [CommRing R]
    (ι : (I×Bool)↪E) (σ : E → C) (t : E → R) (g : C → R)
    (ht : ∀ i,t (ι (i,false))=t (ι (i,true))) :
    (∑ e,t e*g (σ (pairSwitchPermutation ι e)))=(∑ e,t e*g (σ e)) := by
  apply sub_eq_zero.mp
  rw [pair_switch_weighted_difference]
  simp only [ht,sub_self,zero_mul,Finset.sum_const_zero]

end Oberwolfach
