module

public import Oberwolfach.FactorNonemptyClassIndices

@[expose] public section
/-! There are at most K short classes and one long class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_nonempty_class_count_bound {W:Type} [Fintype W] (K:ℕ)
    (classify:W→Option (Fin K)):
    (Finset.univ.filter (fun j:Option (Fin K)=>
      (Finset.univ.filter (fun w=>classify w=j)).Nonempty)).card≤K+1:=by
  simpa using (Finset.card_le_univ (Finset.univ.filter (fun j:Option (Fin K)=>
    (Finset.univ.filter (fun w=>classify w=j)).Nonempty)))
end Oberwolfach
