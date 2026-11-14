module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.ResidualDeletedPathsDisjoint
public import Oberwolfach.ResidualDeletedPathProperties

@[expose] public section
/-! The actual selected run walks are simple and mutually vertex-disjoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_runs_are_disjoint_simple_paths
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G):
    (∀r:SelectedRunIndex data.s₂ data.d data.T,(data.path (.inr r)).IsPath) ∧
    (∀r s:SelectedRunIndex data.s₂ data.d data.T,r≠s→
      Disjoint (data.path (.inr r)).support.toFinset (data.path (.inr s)).support.toFinset):=by
  constructor
  · intro r
    exact (deleted_path_family_properties G data.s₁ data.s₂ data.u data.v data.P data.hp data.c data.d
      (lt_of_lt_of_le (by decide : 0<3) data.hc) data.hd data.hlen data.T (fun i _=>data.hT i) (.inr r)).1
  · intro r s hrs
    exact deleted_path_family_vertex_disjoint G data.s₁ data.s₂ data.hs data.u data.v data.P data.hp data.hP data.c data.d
      (lt_of_lt_of_le (by decide : 0<3) data.hc) data.hlen data.T (fun i _=>data.hT i) (.inr r) (.inr s) (fun hh=>hrs (Sum.inr.inj hh))
end Oberwolfach
