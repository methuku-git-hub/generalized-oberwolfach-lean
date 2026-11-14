module

public import Oberwolfach.InnerRequiredTargetsProtectedMonotone
public import Oberwolfach.RawReservedSpokeList
public import Oberwolfach.RawApproximateRetainedSelectedSpokes

@[expose] public section
/-! Protect all retained ordinary spokes, including newly exposed ones.
The required inner targets only shrink and remain disjoint from the
approximate spoke layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_retained_protected_inner_targets
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (inner:Finset U) (vertices:Finset V) (selected absorber occupied:U→Finset V):
    let Outer:=fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t J false false false v u)
    let Old:=rawReservedSpokeList π d σ;
    (∀u,Old u⊆Outer u) ∧
    (∀u,innerRequiredTargets inner vertices Outer selected absorber occupied u⊆
      innerRequiredTargets inner vertices Old selected absorber occupied u) ∧
    (∀v,(inner.filter (fun u=>v∈innerRequiredTargets inner vertices Outer selected absorber occupied u)).card≤
      (inner.filter (fun u=>v∈innerRequiredTargets inner vertices Old selected absorber occupied u)).card) ∧
    (∀u v b,rawMarkedSpokes π d σ true true b v u→v∉Outer u):=by
  intro Outer Old
  have hsub:∀u,Old u⊆Outer u:=by
    intro u
    exact raw_ordinary_outer_subset_retained π d σ false t J false false u
  obtain ⟨htarget,hload⟩:=inner_required_targets_protected_mono inner vertices Old Outer selected absorber occupied hsub
  refine ⟨hsub,htarget,hload,?_⟩
  intro u v b ha hv
  have hs:retainedRawMarkedSpokes π d σ false t J false false false v u:=by
    simpa only [Outer,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  exact raw_approximate_spoke_avoids_retained_selected π d σ false true (by decide) t J false true (by decide) v u b false ⟨ha,hs⟩
end Oberwolfach
