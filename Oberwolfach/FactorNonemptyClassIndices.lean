module

public import Oberwolfach.FactorClassDensitySum

@[expose] public section
/-! Reindex the nonempty classes by the finite index set used by the
protected regular partition theorem. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_nonempty_class_indices {W B:Type} [Fintype W] [Fintype B] [DecidableEq B]
    (classify:W→B) (D:ℕ) (hD:0<D) (hsize:2*Fintype.card W=D):
    let fibres:=fun j:B=>Finset.univ.filter (fun w=>classify w=j)
    let C:=Finset.univ.filter (fun j=>(fibres j).Nonempty)
    let k:=C.card
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
    let m:=fun a:Fin k=>(fibres (e a).val).card
    let ρ:=fun a:Fin k=>2*(m a:ℝ)/(D:ℝ);
    0<k ∧ (∀ a,0<m a) ∧ (∑ a,m a)=D/2 ∧
    (∀ a,0<ρ a) ∧ (∑ a,ρ a)=1 ∧ (∀ a,ρ a/2*D=m a):=by
  intro fibres C k e m ρ
  have hW:0<Fintype.card W:=by omega
  obtain ⟨w⟩:=Fintype.card_pos_iff.mp hW
  have hC:C.Nonempty:=by
    refine ⟨classify w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have hk:0<k:=Finset.card_pos.mpr hC
  have hm:∀ a,0<m a:=by
    intro a
    exact Finset.card_pos.mpr (Finset.mem_filter.mp (e a).property).2
  have hsumall:(∑ j:B,(fibres j).card)=Fintype.card W:=by
    simpa [fibres] using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ:Finset W) (Finset.univ:Finset B) classify
  have hsumC:(∑ j:↥C,(fibres j.val).card)=Fintype.card W:=by
    rw [Finset.sum_coe_sort C (fun j=>(fibres j).card)]
    calc
      _ = ∑ j:B,(fibres j).card:=by
        apply Finset.sum_subset (Finset.subset_univ C)
        intro j _ hj
        have hempty:¬(fibres j).Nonempty:=by
          intro h
          apply hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hempty)
      _ = _:=hsumall
  have hsumm:(∑ a,m a)=Fintype.card W:=by
    calc
      _ = ∑ j:↥C,(fibres j.val).card:=e.sum_comp (fun j=>(fibres j.val).card)
      _ = _:=hsumC
  have hD':(0:ℝ)<D:=by exact_mod_cast hD
  have hmR:(∑ a:Fin k,(m a:ℝ))=Fintype.card W:=by exact_mod_cast hsumm
  have hsize':(2:ℝ)*Fintype.card W=D:=by exact_mod_cast hsize
  refine ⟨hk,hm,?_,?_,?_,?_⟩
  · rw [hsumm]
    omega
  · intro a
    dsimp [ρ]
    have hh:(0:ℝ)<m a:=by exact_mod_cast hm a
    positivity
  · dsimp [ρ]
    rw [←Finset.sum_div,←Finset.mul_sum,hmR,hsize']
    exact div_self (ne_of_gt hD')
  · intro a
    dsimp [ρ]
    field_simp
end Oberwolfach
