module

public import Oberwolfach.LongReservedPrescribedWalks
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

@[expose] public section
/-! The interior path is a subwalk of its two-edge extension. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_interior_list_infix {V:Type*} (ℓ:ℕ) (f:Fin (ℓ+5)↪V):
    List.ofFn (longReservedInteriorEmbedding ℓ f) <:+: List.ofFn f := by
  have heq:List.ofFn (longReservedInteriorEmbedding ℓ f)=
      ((List.ofFn f).drop 2).take (ℓ+1):=by
    apply List.ext_getElem
    · simp; omega
    · intro i hi hj
      have hi':i<ℓ+1:=by simpa using hi
      simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
      change f ⟨i+2,by omega⟩=f ⟨2+i,by omega⟩
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  rw [heq]
  exact (List.take_prefix (ℓ+1) ((List.ofFn f).drop 2)).isInfix.trans
    (List.drop_suffix 2 (List.ofFn f)).isInfix

theorem long_reserved_interior_is_subwalk
    {V:Type*} (G:SimpleGraph V) (ℓ:ℕ) (f:Fin (ℓ+5)↪V)
    {a b x y:V} (p:G.Walk a b) (q:G.Walk x y)
    (hp:p.support=List.ofFn (longReservedInteriorEmbedding ℓ f))
    (hq:q.support=List.ofFn f):p.IsSubwalk q := by
  apply SimpleGraph.Walk.isSubwalk_iff_support_isInfix.mpr
  rw [hp,hq]
  exact long_reserved_interior_list_infix ℓ f
end Oberwolfach
