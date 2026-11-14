module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

@[expose] public section
/-! Read adjacent vertices from a walk whose support is a finite sequence. -/
set_option autoImplicit false
namespace Oberwolfach

theorem walk_ofFn_support_adjacent
    {V:Type*} (G:SimpleGraph V) (N:ℕ) (f:Fin (N+1)→V)
    {a b:V} (p:G.Walk a b) (hlen:p.length=N) (hsupport:p.support=List.ofFn f):
    ∀k:Fin N,G.Adj (f ⟨k.val,by omega⟩) (f ⟨k.val+1,by omega⟩) := by
  have hv (k:Fin (N+1)):p.getVert k.val=f k:=by
    rw [p.getVert_eq_support_getElem (by omega)]
    simp only [hsupport, List.getElem_ofFn]
  intro k
  have hadj:=p.adj_getVert_succ (i:=k.val) (by omega)
  rw [hv ⟨k.val,by omega⟩,hv ⟨k.val+1,by omega⟩] at hadj
  exact hadj
end Oberwolfach
