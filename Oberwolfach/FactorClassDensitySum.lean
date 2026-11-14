module

public import Oberwolfach.FactorRemainingFamilySize

@[expose] public section
/-! The densities of the retained factor classes sum to one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_class_density_sum {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)) (D:ℕ) (hD:0<D)
    (hsize:2*Fintype.card W=D):
    (∑ j:Option (Fin K),2*((Finset.univ.filter (fun w=>classify w=j)).card:ℝ)/D)=1:=by
  have hD':(0:ℝ)<D:=by exact_mod_cast hD
  have hcard:(∑ j:Option (Fin K),(Finset.univ.filter (fun w=>classify w=j)).card)=Fintype.card W:=by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ:Finset W)
      (Finset.univ:Finset (Option (Fin K))) classify)
  have hcard':(∑ j:Option (Fin K),((Finset.univ.filter (fun w=>classify w=j)).card:ℝ))=Fintype.card W:=by
    exact_mod_cast hcard
  have hsize':(2:ℝ)*Fintype.card W=D:=by exact_mod_cast hsize
  rw [← Finset.sum_div,← Finset.mul_sum,hcard',hsize']
  exact div_self (ne_of_gt hD')

/-- The normalized densities of the classes left after deleting factors sum
to one for the actual residual degree. -/
theorem factor_remaining_class_density_sum {W:Type} [Fintype W] (D:ℕ) (hEven:Even D)
    (hsize:Fintype.card W=D/2) (removed:Finset W) (hbound:2*removed.card<D)
    (K:ℕ) (classify:{w:W // w∉removed}→Option (Fin K)):
    (∑ j:Option (Fin K),
      2*((Finset.univ.filter (fun w=>classify w=j)).card:ℝ)/(D-2*removed.card:ℕ))=1:=by
  have hpos:0<D-2*removed.card:=by omega
  have hh:=factor_remaining_family_size D hEven hsize removed hbound.le
  have hsize':2*Fintype.card {w:W // w∉removed}=D-2*removed.card:=by
    rw [hh.1]
    obtain ⟨k,hk⟩:=hh.2
    omega
  exact factor_class_density_sum K classify (D-2*removed.card) hpos hsize'
end Oberwolfach
