module

public import Oberwolfach.MarkedWheelUnionRealization
public import Oberwolfach.IndexedMarkedRealizationPullback
public import Oberwolfach.IndexedMarkedComparison
public import Oberwolfach.MarkedFreeWheelFamilies

@[expose] public section

/-! Construct the comparison graph as an actual disjoint marked-wheel
union, then identify its occurrences with the original graph by type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

def indexedMarkedComparisonRealization (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced (l+4))
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:G.MarkedSpokes→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):
    IndexedMarkedHostRealization (indexedMarkedComparison G (l+4) hG) tail head ktail khead H₀ HK π b:=
  (indexedMarkedWheelUnionRealization (by omega) hp C hpack).pullbackOccurrences
    (typedOccurrenceEquiv G.jr (indexedMarkedWheelUnion G.MarkedSpokes (l+4)).jr (indexedMarkedComparison_type_counts G (l+4) hG).1)
    (typedOccurrenceEquiv G.js (indexedMarkedWheelUnion G.MarkedSpokes (l+4)).js (indexedMarkedComparison_type_counts G (l+4) hG).2)

theorem indexedMarkedComparisonRealization_resources (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced (l+4))
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:G.MarkedSpokes→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):
    (indexedMarkedComparisonRealization G hG hp C hpack).resources=
      Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i)):=by
  unfold indexedMarkedComparisonRealization
  rw [IndexedMarkedHostRealization.resources_pullbackOccurrences,indexedMarkedWheelUnionRealization_resources]

theorem marked_comparison_realization
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced (l+4))
    (v₀:V) (W Z:Finset V) (B:Finset U)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Fintype.card G.MarkedSpokes*(l+5)+Z.card+l+13)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card G.MarkedSpokes<ch):
    ∃ R:IndexedMarkedHostRealization (indexedMarkedComparison G (l+4) hG) tail head ktail khead H₀ HK π b,
      Function.Injective R.rows∧Function.Injective R.hubs∧
      (∀ u,R.hubs u∉B)∧
      (∀ v,R.rows v∉W∧R.rows v∉Z∧∀ z∈Z,¬PermutationClose π b (R.rows v) z)∧
      PermutationSeparated π b R.rows∧
      HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources C) R.resources:=by
  obtain ⟨C,hCv,hCu,hCB,hav,hsep,hpack,hdec⟩:=marked_free_wheel_families (I:=G.MarkedSpokes) Q hl v₀ W Z B hp hbudget hB
  let R:=indexedMarkedComparisonRealization G hG hp C hpack
  refine ⟨R,hCv,hCu,hCB,?_,?_,?_⟩
  · rintro ⟨i,k⟩;exact hav i k
  · rintro ⟨i,k⟩ ⟨j,k'⟩ hne;exact hsep i j k k' hne
  · rw [show R.resources=Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i)) from
      indexedMarkedComparisonRealization_resources G hG hp C hpack]
    exact hdec

end Oberwolfach
