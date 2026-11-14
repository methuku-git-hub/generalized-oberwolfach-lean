module

public import Oberwolfach.FactorDecompositionNonemptyClassReindex

@[expose] public section
/-! The finite class count is exactly the number of indices in that class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

noncomputable def factorClassFibreEquiv {W J:Type} [Fintype W] [DecidableEq J]
    (classify:W→J) (j:J):Fin ((Finset.univ.filter (fun w=>classify w=j)).card)≃{w:W // classify w=j} :=by
  let S:Finset W:=Finset.univ.filter (fun w=>classify w=j)
  let e:Fin S.card≃↥S:=(Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let f:↥S≃{w:W // classify w=j}:={
    toFun:=fun w=>⟨w.val,(Finset.mem_filter.mp w.property).2⟩
    invFun:=fun w=>⟨w.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,w.property⟩⟩
    left_inv:=by intro w;apply Subtype.ext;rfl
    right_inv:=by intro w;apply Subtype.ext;rfl }
  exact e.trans f
end Oberwolfach
