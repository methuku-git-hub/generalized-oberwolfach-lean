module

public import Oberwolfach.OrdinaryOuterHostBalance
public import Oberwolfach.OrdinaryPackingTransport

@[expose] public section
/-! An approximate packing made after reserving boundary resources can be
viewed in the original host without touching either the protected pair or
the reserved graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reserved_packing_transport
    (Q F D:SimpleGraph V) (H S:V→U→Prop) (I:Finset V) (J:Finset U) (r:ℕ)
    (M:Finset (OrdinaryWheel ((Q\spanningRestriction Q I)\D) F
      (fun v u=>(H v u∧¬(v∈I∧u∈J))∧¬S v u) r))
    (hM:∀W∈M,∀Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)):
    ∃M':Finset (OrdinaryWheel Q F H r),
      (∀W∈M',∀Z∈M',W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      Disjoint (M'.biUnion ordinaryWheelResources)
        (ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J)) ∧
      Disjoint (M'.biUnion ordinaryWheelResources) (ordinaryHostResources D S) ∧
      (∀x:V⊕U,(ordinaryPhysicalIncidentEdges ((Q\spanningRestriction Q I)\D)
          (fun v u=>(H v u∧¬(v∈I∧u∈J))∧¬S v u) x\M'.biUnion ordinaryWheelResources).card=
        (ordinaryIncidentEdges ((Q\spanningRestriction Q I)\D)
          (fun v u=>(H v u∧¬(v∈I∧u∈J))∧¬S v u) x\M.biUnion ordinaryActiveResources).card):=by
  let R:=(Q\spanningRestriction Q I)\D
  let K:=fun v u=>(H v u∧¬(v∈I∧u∈J))∧¬S v u
  have hRQ:R≤Q:=sdiff_le.trans sdiff_le
  have hKH:∀v u,K v u→H v u:=by intro v u h;exact h.1.1
  let M':=M.image (ordinaryWheelToLarger (F:=F) (r:=r) hRQ hKH)
  have htransport:=ordinary_packing_transport hRQ hKH M hM
  have hsub:M.biUnion ordinaryWheelResources⊆ordinaryHostResources R K:=by
    intro e he
    obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ordinaryWheelResources_present W e heW⟩
  have hres:ordinaryHostResources R K=
      (ordinaryHostResources Q H\ordinaryHostResources (spanningRestriction Q I)
        (fun v u=>H v u∧v∈I∧u∈J))\ordinaryHostResources D S:=by
    rw [ordinaryHostResources_sdiff,ordinary_outer_host_resources]
  have hdis1:Disjoint (M.biUnion ordinaryWheelResources)
      (ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J)):=by
    apply Finset.disjoint_left.mpr
    intro e he hi
    have hh:=hsub he
    rw [hres] at hh
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hh).1).2 hi
  have hdis2:Disjoint (M.biUnion ordinaryWheelResources) (ordinaryHostResources D S):=by
    apply Finset.disjoint_left.mpr
    intro e he hi
    have hh:=hsub he
    rw [hres] at hh
    exact (Finset.mem_sdiff.mp hh).2 hi
  refine ⟨M',htransport.1,?_,?_,?_⟩
  · rw [htransport.2];exact hdis1
  · rw [htransport.2];exact hdis2
  · intro x;rw [htransport.2];exact (ordinary_leftover_card_physical M x).symm
end Oberwolfach
