module

public import Oberwolfach.OrderedCycleAnyPosition

@[expose] public section
/-! Exact position-wise counts for a fixed physical cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem orderedCycle_position_adj (H:SimpleGraph V) (n:ℕ) (f:OrderedCycleRepresentations H (n+2)) (i:Fin (n+2)):
    H.Adj (f.val i) (f.val (cycleNext i)):=by
  apply (congrArg (fun G:SimpleGraph V=>G.Adj (f.val i) (f.val (cycleNext i))) f.property).mpr
  apply SimpleGraph.map_adj_apply.mpr
  rw [cycleGraph_modular_adj (by omega)]
  left
  rfl

theorem orderedCycle_position_edge_sum (H:SimpleGraph V) (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2))
    (i:Fin (n+2)) (x y:V) (c:ℝ):
    (∑ f:OrderedCycleRepresentations H (n+2),if f.val i=x ∧ f.val (cycleNext i)=y then c else 0)=
      if H.Adj x y then c else 0:=by
  by_cases hxy:H.Adj x y
  · obtain ⟨f,hf,huniq⟩:=orderedCycle_position_fibre_unique H n hn hH i x y hxy
    rw [if_pos hxy,Finset.sum_eq_single f]
    · simp [hf]
    · intro g _ hgf
      have hn':¬(g.val i=x ∧ g.val (cycleNext i)=y):=fun hg=>hgf (huniq g hg)
      simp [hn']
    · simp
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro f _
    have hn':¬(f.val i=x ∧ f.val (cycleNext i)=y):=by
      rintro ⟨hx,hy⟩
      have h:=orderedCycle_position_adj H n f i
      rw [hx,hy] at h
      exact hxy h
    simp [hn']

theorem orderedCycle_position_vertex_sum (H:SimpleGraph V) (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2))
    (i:Fin (n+2)) (x:V) (c:ℝ):
    (∑ f:OrderedCycleRepresentations H (n+2),if f.val i=x then c else 0)=(H.degree x:ℝ)*c:=by
  have hc:(Finset.univ.filter (fun f:OrderedCycleRepresentations H (n+2)=>f.val i=x)).card=H.degree x:=by
    simpa only [Fintype.card_subtype] using orderedCycle_position_vertex_card H n hn hH i x
  rw [←Finset.sum_filter,Finset.sum_const,hc,nsmul_eq_mul]
end Oberwolfach
