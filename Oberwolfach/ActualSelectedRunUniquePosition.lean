module

public import Oberwolfach.ResidualActualData
public import Oberwolfach.ResidualRunsSeparated

@[expose] public section
/-! A selected segment belongs to a unique actual maximal run of its parent
path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_run_unique_at_position
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (r s:SelectedRunIndex data.s₂ data.d data.T) (j:ℕ)
    (hparent:r.1.val=s.1.val)
    (hrlo:r.2.val.1≤j) (hrhi:j≤r.2.val.2)
    (hslo:s.2.val.1≤j) (hshi:j≤s.2.val.2):r=s:=by
  rcases r with ⟨i,r⟩
  rcases s with ⟨i',s⟩
  have hi:i=i':=Subtype.ext hparent
  subst i'
  have hr:=(selected_run_mem data.d (data.T i.val) (data.hT i.val) r.val.1 r.val.2).mp r.property
  have hs:=(selected_run_mem data.d (data.T i.val) (data.hT i.val) s.val.1 s.val.2).mp s.property
  have he:=selected_runs_with_common_segment_equal (data.T i.val) r.val.1 r.val.2 s.val.1 s.val.2 j hr hs hrlo hrhi hslo hshi
  have hrs:r=s:=Subtype.ext (Prod.ext he.1 he.2)
  subst s
  rfl
end Oberwolfach
