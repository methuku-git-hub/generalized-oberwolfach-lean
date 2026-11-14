module

public import Oberwolfach.FactorPrunedClassIndices

@[expose] public section
/-! The two existing pruning interfaces use pointwise and factored forms of
the same class-size cutoff. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_cutoff_removed_sets_equal {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)) (κL κS t:ℝ):
    (Finset.univ.filter (fun w=>
      (((Finset.univ.filter (fun v=>classify v=classify w)).card):ℝ)<
        (if classify w=none then κL*t else κS*t)))=
    (Finset.univ.filter (fun w=>
      (((Finset.univ.filter (fun v=>classify v=classify w)).card):ℝ)<
        (if classify w=none then κL else κS)*t)) :=by
  ext w
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> rfl
end Oberwolfach
