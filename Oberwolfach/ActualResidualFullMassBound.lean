module

public import Oberwolfach.ResidualActualFullSelection
public import Oberwolfach.ResidualActualData
public import Oberwolfach.ResidualSizeMassBudget

@[expose] public section
/-! The exact full-selection comparison applied to the actual residual data. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_size_from_mass_and_missing
    {V K J:Type} [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph V} (a:ActualResidualData (K:=K) (J:=J) F) (ε κ:ℝ)
    (hmass:(1-ε)*Fintype.card V≤
      ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)+
        (a.c*a.d-1:ℕ)*(a.s₁.card+a.s₂.card))
    (hmissing:(((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤κ*Fintype.card V):
    (a.remaining.card:ℝ)≤(ε+(a.c+1)*κ)*Fintype.card V:=by
  have hh:=residual_actual_full_selection_comparison F a.s₁ a.s₂ a.hs a.u a.v a.P a.hp a.hP a.c a.d
    (by have h:=a.hc;omega) a.hd a.hlen a.T a.hT a.t a.root a.C a.hcross
  dsimp only at hh
  have hbase:=hh.1
  have hupper:=hh.2.2
  change a.remaining.card≤_ at hupper
  exact residual_size_from_mass_and_missing (Fintype.card V) a.c a.d (a.s₁.card+a.s₂.card)
    (a.t.biUnion (fun j=>(a.C j).support.toFinset)).card _ a.remaining.card
    (∑i∈a.s₂,(a.d-(a.T i).card)) ε κ hbase hupper (by simpa only [Nat.cast_add] using hmass) hmissing
end Oberwolfach
