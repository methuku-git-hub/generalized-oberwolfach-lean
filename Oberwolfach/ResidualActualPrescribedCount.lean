module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.ResidualRunFamilyCounts
public import Oberwolfach.ResidualSubtypePositionBudget

@[expose] public section
/-! Count actual prescribed residual positions using missing marked segments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_prescribed_le_starts_and_missing
    {V K J:Type} [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph V} (hF:F.IsRegularOfDegree 2) (a:ActualResidualData (K:=K) (J:=J) F):
    (residualSubtypeSet a.remaining a.prescribed).card≤
      2*(a.s₁.card+a.s₂.card)+2*(∑i∈a.s₂,(a.d-(a.T i).card)):=by
  have hg:=residual_actual_graph_and_prescriptions F hF a.s₁ a.s₂ a.hs a.u a.v a.P a.hp a.hP a.c a.d a.hc a.hd a.hlen a.T a.hT a.t a.root a.C a.hcycle a.hC a.hcross
  have hsub:a.prescribed⊆a.remaining:=hg.1
  have hcount:a.prescribed.card=2*a.s₁.card+a.s₂.card+
      (∑i∈a.s₂,(a.d-(a.T i).card))+
      (∑i∈a.s₂,(selectedSegmentRuns a.d (a.T i)).card):=hg.2.2.1
  have hruns:=maximal_run_family_counts a.s₂ a.d a.hd a.T (fun i _=>a.hT i)
  rw [residual_subtype_set_card a.remaining a.prescribed hsub]
  dsimp at hruns
  omega
end Oberwolfach
