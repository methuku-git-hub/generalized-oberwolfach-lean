module

public import Oberwolfach.OrdinarySampleForcedSpokes

@[expose] public section
/-! The manuscript's trimmed reserved free lists and actual forced inner
spoke targets both avoid the absorber's reserved labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_actual_target_avoidance
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset V) (Hubs:Finset U) (Abs:U→Finset V)
    (hAbsSub:∀u,Abs u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u):
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let T:=ordinaryInnerSpokeTargets Inner Hubs Href
    let L:=fun u=>rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\(Inner∪Abs u);
    ∀u,L u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u ∧
      Disjoint (L u) (Abs u) ∧ Disjoint (T u) (Abs u) ∧
      T u⊆Inner ∧ (T u≠∅→u∈Hubs) :=by
  intro Href T L u
  have ht:=ordinary_sample_inner_targets_avoid_reserved π d σ Inner Hubs u
  refine ⟨Finset.sdiff_subset,?_,ht.1.mono_right (hAbsSub u),ht.2.1,ht.2.2⟩
  apply Finset.disjoint_left.mpr
  intro v hv ha
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ ha)
end Oberwolfach
