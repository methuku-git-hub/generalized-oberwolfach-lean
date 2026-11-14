module

public import Oberwolfach.OrdinaryNearBalancePackingData

@[expose] public section
/-! The packing cut parameter may be fixed before the later deletion scale
is chosen; stronger normalized cut bounds can be weakened. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_large_cut_weaken {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (L:X→Y→ℕ) (δ h h':ℝ) (hh:h'≤h) (hc:BipartiteLargeCut L δ h):
    BipartiteLargeCut L δ h':=by
  intro S T hST
  have hn:(0:ℝ)≤Fintype.card X:=Nat.cast_nonneg _
  have hm:(0:ℝ)≤Fintype.card Y:=Nat.cast_nonneg _
  have hs:0≤min ((S.card:ℝ)/Fintype.card X) ((T.card:ℝ)/Fintype.card Y):=by positivity
  have hprod:0≤(Fintype.card X:ℝ)*(Fintype.card Y:ℝ)*
      min ((S.card:ℝ)/Fintype.card X) ((T.card:ℝ)/Fintype.card Y):=by positivity
  have hmul:=mul_le_mul_of_nonneg_right hh hprod
  have hcut:=hc S T hST
  nlinarith only [hmul,hcut]

theorem ordinary_near_balance_data_weaken_cut {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] (r:ℕ) (hr:3≤r) (k:ℕ) (α ω β bminus bplus h h' δ εstar η:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (hh:h'≤h)
    (d:OrdinaryNearBalancePackingData r hr k α ω β bminus bplus h δ εstar η P Q F H):
    Nonempty (OrdinaryNearBalancePackingData r hr k α ω β bminus bplus h' δ εstar η P Q F H):=by
  refine ⟨⟨d.hub_lower,d.hub_upper,d.graph_sub,d.orientation,d.orientation_graph,?_,?_,d.spoke_degree,
    d.balance,d.isolators,d.transfers,d.weight,d.weight_bounds,d.rim_load,d.spoke_load⟩⟩
  · exact ordinary_large_cut_weaken d.orientation δ h h' hh d.rim_cuts
  · exact ordinary_large_cut_weaken (fun v u=>if H v u then 1 else 0) δ h h' hh d.spoke_cuts
end Oberwolfach
