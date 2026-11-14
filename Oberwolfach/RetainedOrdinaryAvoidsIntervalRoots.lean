module

public import Oberwolfach.RetainedAndRawIntervalsAvoidRetainedOuter
public import Oberwolfach.MarkedIntervalRootCardinality

@[expose] public section
/-! Retained ordinary spokes avoid both the retained marked interval and its
final endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem retained_ordinary_avoids_interval_roots
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (u:U):
    let Outer:=Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t J false false false v u)
    let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J u=>d) Subtype.val
    let End:=Finset.univ.image (fun j:retainedMarkedIndex π d σ false t J u=>(π^d) j.val);
    Disjoint Outer Y ∧ Disjoint Outer End:=by
  intro Outer Y End
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hv hy
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hy
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hi
    have hjlt:j.val<d:=j.isLt
    have hh:=retained_and_raw_intervals_avoid_retained_outer π d σ t J u (.inl i) ⟨j.val,Nat.lt_succ_of_lt hjlt⟩
    have ho:retainedRawMarkedSpokes π d σ false t J false false false v u:=(Finset.mem_filter.mp hv).2
    apply hh
    simpa only [retainedAndRawIntervalRoot] using hj ▸ ho
  · apply Finset.disjoint_left.mpr
    intro v hv he
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
    have hh:=retained_and_raw_intervals_avoid_retained_outer π d σ t J u (.inl i) ⟨d,by omega⟩
    have ho:retainedRawMarkedSpokes π d σ false t J false false false v u:=(Finset.mem_filter.mp hv).2
    apply hh
    simpa only [retainedAndRawIntervalRoot] using hi ▸ ho
end Oberwolfach
