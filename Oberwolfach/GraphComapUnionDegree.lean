module

public import Oberwolfach.MarkedActiveDeletionDegrees

@[expose] public section

/-! Sum actual physical degrees after restriction to the active domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_comap_union_degree_bound {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G H:SimpleGraph V) (f:W↪V) (a b:ℝ)
    (hG:∀ x,(G.degree x:ℝ)≤a) (hH:∀ x,((H.comap f).degree x:ℝ)≤b):
    ∀ x,(((G⊔H).comap f).degree x:ℝ)≤a+b:=by
  have he:(G⊔H).comap f=G.comap f⊔H.comap f:=by ext x y;rfl
  intro x
  have hle:((G.comap f).degree x:ℝ)≤a:=
    (Nat.cast_le.mpr (graph_comap_injective_degree_le G f x)).trans (hG (f x))
  have hb:(((G.comap f)⊔(H.comap f)).degree x:ℝ)≤(G.comap f).degree x+(H.comap f).degree x:=by
    exact_mod_cast graph_degree_sup_le (G.comap f) (H.comap f) x
  have hh:=hb.trans (add_le_add hle (hH x))
  simpa only [←SimpleGraph.ncard_neighborSet,he] using hh

end Oberwolfach
