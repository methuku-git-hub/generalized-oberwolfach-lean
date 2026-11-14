module

public import Oberwolfach.OrdinaryInducedRimEvent

@[expose] public section
/-! A rim-cut event on an embedded set transfers to its original subtype,
with no loss in the cut constants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_rim_cut_embedding
    {V W:Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
    (f:W↪V) (D:Finset W) (A:V→V→ℕ) (α pstar:ℝ)
    (h:OrdinaryInducedRimCutEvent (D.image f) A α pstar):
    OrdinaryInducedRimCutEvent D (fun x y=>A (f x) (f y)) α pstar:=by
  let e:D↪↥(D.image f):={
    toFun:=fun x=>⟨f x.val,Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩⟩
    inj':=by
      intro x y hxy
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val hxy) }
  intro S T hST
  let S':=S.image e
  let T':=T.image e
  have hD:(D.image f).card=D.card:=Finset.card_image_of_injective _ f.injective
  have hS:S'.card=S.card:=Finset.card_image_of_injective _ e.injective
  have hT:T'.card=T.card:=Finset.card_image_of_injective _ e.injective
  have hcut:matrixCut (fun x y:↥(D.image f)=>A x.val y.val) S' T'=
      matrixCut (fun x y:D=>A (f x.val) (f y.val)) S T:=by
    simp [S',T',matrixCut,Finset.sum_image,e.injective,e]
  have hh:=h S' T' (by simpa only [hD,hS,hT] using hST)
  rw [hD,hS,hT,hcut] at hh
  exact hh
end Oberwolfach
