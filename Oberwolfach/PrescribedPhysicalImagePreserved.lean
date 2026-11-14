module

public import Oberwolfach.Definitions

@[expose] public section
/-! Updating a vertex map outside an assigned set leaves every physical edge
whose endpoints lie in that set unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_physical_image_preserved (A:Finset X) (f g:X→V)
    (hpres:∀ x∈A,g x=f x) (T:Finset (Sym2 X))
    (hends:∀ e∈T,∀ x∈e.toFinset,x∈A):
    T.image (Sym2.map g)=T.image (Sym2.map f) := by
  apply Finset.image_congr
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hx:x∈A:=hends _ he x (by simp)
    have hy:y∈A:=hends _ he y (by simp)
    simp [hpres x hx,hpres y hy]
end Oberwolfach
