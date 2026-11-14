module

public import Oberwolfach.FactorRetainedClassCard

@[expose] public section
/-! Every nonempty class of the remaining family is one of the retained
classes, so it meets the appropriate original size cutoff. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_remaining_class_not_small {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)) (n κL κS:ℝ):
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w));
    ∀ j,(∃ w:{w:W // w∉removed},classify w.val=j)→¬small j:=by
  intro fibres cutoff small removed j ⟨w,hw⟩ hj
  apply w.property
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [hw] using hj⟩
end Oberwolfach
