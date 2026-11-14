module

public import Oberwolfach.MarkedFactorPhysical
public import Oberwolfach.MappedFactorGraph
public import Oberwolfach.MarkedRowSupportComparison

@[expose] public section

/-! A marked factor uses physical rows in Y union pi(Y), even though its
auxiliary cycle labels cover exactly Y. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_factor_physical_supported (u:U)
    (D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u))
    (Y:Finset V) (hY:D.biUnion (hubMarkedCycleVertices u)=Y) :
    GraphSupportedOn (Y∪Y.image π) (physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges u))) := by
  intro x y hxy
  obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp hxy.2
  have hs:=markedWheelRimGraph_supported (hubCycleWheel u C) x y ⟨hxy.1,he⟩
  have hsub:markedWheelRows (hubCycleWheel u C)⊆Y:=by
    intro v hv
    rw [←hY]
    exact Finset.mem_biUnion.mpr ⟨C,hC,hv⟩
  have htotal:markedWheelRows (hubCycleWheel u C)∪(markedWheelRows (hubCycleWheel u C)).image π⊆Y∪Y.image π:=
    Finset.union_subset_union hsub (Finset.image_subset_image hsub)
  exact ⟨htotal hs.1,htotal hs.2⟩

theorem marked_factor_physical_restriction (u:U)
    (D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u))
    (Y:Finset V) (hY:D.biUnion (hubMarkedCycleVertices u)=Y) :
    physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges u))≤spanningRestriction ⊤ (Y∪Y.image π) := by
  intro x y hxy
  exact (spanningRestriction_adj _ _ _ _).mpr
    ⟨hxy.1,marked_factor_physical_supported u D Y hY x y hxy⟩

theorem marked_factor_physical_map_restriction {W:Type} [Fintype W] [DecidableEq W]
    (u:U) (e:V↪W) (D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u))
    (Y:Finset V) (hY:D.biUnion (hubMarkedCycleVertices u)=Y) :
    (physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges u))).map e≤
      spanningRestriction ⊤ ((Y∪Y.image π).image e) :=
  graph_map_restriction _ ⊤ ⊤ e _ (marked_factor_physical_restriction u D Y hY) le_top

end Oberwolfach
