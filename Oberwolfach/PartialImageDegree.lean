module

public import Oberwolfach.Definitions

@[expose] public section
/-! Partial physical images of degree-two source graphs have degree at most
two at an image vertex, and degree zero outside the image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem partial_injective_image_degree {X V:Type} [Fintype X] [Fintype V]
    [DecidableEq V] (Q:SimpleGraph X) (f:X↪V) (H:SimpleGraph V)
    (hsub:H≤Q.map f) (hQ:∀ x,Q.degree x≤2) (v:V):
    H.degree v≤(if ∃ x,f x=v then 2 else 0) := by
  by_cases hv:∃ x,f x=v
  · rcases hv with ⟨x,rfl⟩
    have hx:∃ z,f z=f x:=⟨x,rfl⟩
    simp only [if_pos hx]
    have hN:H.neighborFinset (f x)⊆(Q.map f).neighborFinset (f x):=by
      intro y hy
      simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact hsub hy
    have hh:H.degree (f x)≤(Q.map f).degree (f x):=by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card hN
    exact hh.trans ((SimpleGraph.degree_map_apply Q f x).le.trans (hQ x))
  · simp only [if_neg hv]
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    apply Nat.le_zero.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    simp only [SimpleGraph.mem_neighborFinset] at hy
    have hh:(Q.map f).Adj v y:=hsub hy
    obtain ⟨x,z,hxz,hx,hz⟩:=(SimpleGraph.map_adj f Q v y).mp hh
    exact hv ⟨x,hx⟩
end Oberwolfach
