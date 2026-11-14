module

public import Oberwolfach.FactorClassFibreEquiv

@[expose] public section
/-! Glue the actual nonempty fibre classes back to the retained family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_decomposition_from_actual_nonempty_classes
    {n:ℕ} {W J:Type} [Fintype W] [Fintype J] [DecidableEq J]
    (G:SimpleGraph (Fin n)) (F:W→SimpleGraph (Fin n)) (classify:W→J):
    let fibres:=fun j:J=>Finset.univ.filter (fun w=>classify w=j)
    let C:=Finset.univ.filter (fun j=>(fibres j).Nonempty)
    let k:=C.card
    let eC:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
    let m:=fun a:Fin k=>(fibres (eC a).val).card
    let eF:=fun a:Fin k=>factorClassFibreEquiv classify (eC a).val;
    ∀H:Fin k→SimpleGraph (Fin n),EdgePartition G H→
      (∀a,HasFactorDecomposition (H a) (fun i:Fin (m a)=>F ((eF a i).val)))→
    HasFactorDecomposition G (fun i:Fin (Fintype.card W)=>F ((Fintype.equivFin W).symm i)) :=by
  intro fibres C k eC m eF H hpart hdec
  have hcover:∀w,classify w∈C:=by
    intro w
    simp only [C,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨w,by simp [fibres]⟩
  exact factor_decomposition_from_nonempty_class_reindex G F classify C eC hcover m eF H hpart hdec
end Oberwolfach
