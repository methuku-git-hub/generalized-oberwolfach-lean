module

public import Oberwolfach.ActualSelectedRunUniquePosition

@[expose] public section
/-! Even with both endpoints included, distinct maximal selected runs of the
same parent have disjoint marker-index intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_run_unique_at_marker
    {X K J:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (r s:SelectedRunIndex data.s₂ data.d data.T) (j:ℕ)
    (hparent:r.1.val=s.1.val)
    (hrlo:r.2.val.1≤j) (hrhi:j≤r.2.val.2+1)
    (hslo:s.2.val.1≤j) (hshi:j≤s.2.val.2+1):r=s:=by
  rcases r with ⟨i,r⟩
  rcases s with ⟨i',s⟩
  have hi:i=i':=Subtype.ext hparent
  subst i'
  by_cases he:r=s
  · subst s;rfl
  · have hne:r.val≠s.val:=fun h=>he (Subtype.ext h)
    have hsep:=distinct_selected_runs_separated data.d (data.T i.val) (data.hT i.val)
      r.val.1 r.val.2 s.val.1 s.val.2 r.property s.property hne
    change r.val.1≤j at hrlo
    change j≤r.val.2+1 at hrhi
    change s.val.1≤j at hslo
    change j≤s.val.2+1 at hshi
    omega
end Oberwolfach
