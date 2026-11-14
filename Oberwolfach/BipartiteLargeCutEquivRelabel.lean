module

public import Oberwolfach.BipartiteLargeCutEmbedding

@[expose] public section
/-! A large-cut condition is preserved by full relabelling of both sides. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bipartite_large_cut_equiv_relabel
    {A B X Y:Type} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq B] [DecidableEq X] [DecidableEq Y]
    (f:A≃X) (g:B≃Y) (L:X→Y→ℕ)
    (hA:0<Fintype.card A) (hB:0<Fintype.card B) (δ h:ℝ) (hh:0≤h)
    (hcut:BipartiteLargeCut L δ h):
    BipartiteLargeCut (fun x y=>L (f x) (g y)) δ h:=by
  have hAsize:(1:ℝ)*Fintype.card X≤Fintype.card A:=by
    rw [Fintype.card_congr f];simp
  have hBsize:(1:ℝ)*Fintype.card Y≤Fintype.card B:=by
    rw [Fintype.card_congr g];simp
  exact bipartiteLargeCut_embedding f.toEmbedding g.toEmbedding L hA hB 1 δ δ h
    (by norm_num) hh hAsize hBsize (by linarith) hcut
end Oberwolfach
