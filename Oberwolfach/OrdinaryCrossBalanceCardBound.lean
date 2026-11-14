module

public import Oberwolfach.OrdinaryVortexBufferedDomains

@[expose] public section
/-! A deterministic balance bound for a small reserve, needing no additional
sample event or lookback degree estimate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_cross_balance_card_bound (G:SimpleGraph V) (H:V→U→Prop)
    (T:Finset V) (W:Finset U) (v:V):
    |((G.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤(T.card:ℝ)+2*W.card:=by
  have ha:((G.neighborFinset v∩T).card:ℝ)≤T.card:=by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)
  have hb:((W.filter (H v)).card:ℝ)≤W.card:=by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have ha0:0≤((G.neighborFinset v∩T).card:ℝ):=by positivity
  have hb0:0≤((W.filter (H v)).card:ℝ):=by positivity
  rw [abs_le]
  constructor <;> nlinarith
end Oberwolfach
