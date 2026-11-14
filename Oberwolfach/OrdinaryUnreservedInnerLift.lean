module

public import Oberwolfach.OrdinaryUnreservedWalkFamiliesDisjoint

@[expose] public section
/-! Lift the buffered inner paths along with the extended paths, preserving
both their offsets and their original source vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_inner_lift
    {V A B:Type} (S:Set V) (L:ℕ)
    (ext:∀i:A⊕B,Fin (L+5)↪V) (inner:∀a:A,Fin (L+1)↪V)
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (ext':∀i:A⊕B,Fin (L+5)↪S) (hext:∀i k,(ext' i k).val=ext i k):
    ∃inner':∀a:A,Fin (L+1)↪S,
      (∀a k,inner' a k=ext' (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀a k,(inner' a k).val=inner a k):=by
  let inner':∀a:A,Fin (L+1)↪S:=fun a=>⟨fun k=>ext' (.inl a) ⟨k.val+2,by omega⟩,by
    intro i j hij
    apply Fin.ext
    have hh: (⟨i.val+2,by omega⟩:Fin (L+5))=⟨j.val+2,by omega⟩:=(ext' (.inl a)).injective hij
    have hh':i.val+2=j.val+2:=congrArg Fin.val hh
    omega⟩
  refine ⟨inner',fun _ _=>rfl,?_⟩
  intro a k
  change (ext' (.inl a) ⟨k.val+2,by omega⟩).val=inner a k
  rw [hext,hinner]
end Oberwolfach
