module

public import Oberwolfach.RetainedAndRawIntervalGeometry
public import Oberwolfach.RetainedMarkedSpokeGeometry

@[expose] public section
/-! Every retained final interval and every raw approximate interval,
including its final endpoint, avoids retained selected ordinary spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem retained_and_raw_intervals_avoid_retained_outer
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (u:U)
    (i:retainedAndRawIntervalIndex π d σ false true t J u) (j:Fin (d+1)):
    ¬retainedRawMarkedSpokes π d σ false t J false false false
      ((π^j.val) (retainedAndRawIntervalRoot π d σ false true t J u i)) u:=by
  intro hout
  have hnot:=retainedIntervalState_ordinary_not_blocked π d (fun e=>σ (u,e))
    (retainedRawStart π d σ false t J u)
    ((π^j.val) (retainedAndRawIntervalRoot π d σ false true t J u i)) false hout
  have hstart:∃g,retainedRawStart π d σ false t J u
      (retainedAndRawIntervalRoot π d σ false true t J u i) g:=by
    cases i with
    | inl a=>
      refine ⟨false,?_,?_⟩
      · exact a.property.1
      · intro _;exact a.property.2 rfl
    | inr a=>
      refine ⟨true,a.property,?_⟩
      intro h
      cases h
  obtain ⟨g,hg⟩:=hstart
  apply hnot
  refine ⟨g,retainedAndRawIntervalRoot π d σ false true t J u i,hg,?_⟩
  apply (permutationWindow_mem_iff π 0 d _ _).mpr
  refine ⟨⟨j.val,by have hh:=j.isLt;omega⟩,?_⟩
  simp only [pow_zero,Equiv.Perm.one_apply]
end Oberwolfach
