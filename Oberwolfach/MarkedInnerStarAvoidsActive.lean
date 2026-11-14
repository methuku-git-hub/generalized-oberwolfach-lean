module

public import Oberwolfach.MarkedResourceDomainMonotonicity

@[expose] public section
/-! Inner resources confined to the removed star do not meet the active
inner pair. This is the form supplied by the deep-cover construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [DecidableEq V] [DecidableEq U]

theorem marked_inner_star_avoids_active
    (R:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hstar:∀ e∈R,markedInnerResource I J e→markedStarResource T W e):
    R.filter (markedInnerResource (I\T) (J\W))=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hh:=Finset.mem_filter.mp he
  have hi:markedInnerResource I J e:=markedInnerResource_mono Finset.sdiff_subset Finset.sdiff_subset e hh.2
  exact (marked_active_inner_avoids_star I T J W e hh.2) (hstar e hh.1 hi)
end Oberwolfach
