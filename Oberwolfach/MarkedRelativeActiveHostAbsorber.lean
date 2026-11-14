module

public import Oberwolfach.MarkedRelativeHostAbsorber
public import Oberwolfach.IndexedMarkedActiveGraph

@[expose] public section

/-! The bounded absorber input counts only vertices incident with a remainder
edge. The number of occurrences is derived from physical injectivity, rather
than supplied as an additional hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_relative_active_host_absorber (l:ℕ) (hl:2≤l)
    (ρ σ q₀ β blo bhi:ℝ) (hρ:0<ρ) (hσ:0<σ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ a₀ b₀:ℕ,∀ f b:ℕ,∀ dF:ℝ,0≤dF→∃ N:ℕ,
    ∀ (V₀ U₀ V U E K A S:Type) [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),1≤b→
    ∀ (G:IndexedMarkedGraph V₀ U₀ A S),G.IsBalanced (l+4)→
    G.activeRows.card+G.activeHubs.card≤s→
    ∀ (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b) (W:Finset V) (B:Finset U),
    (∀ u,R.active.hubs u∈B)→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l (ρ*Fintype.card V) (σ*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F:SimpleGraph V,permutationConflictGraph π b≤F→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      IsResourceAbsorber (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
        R.active.resources C.edges∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ v∈C.rows,v∈W∪R.active.rowSet→v∈R.active.rowSet)∧(∀ u∈C.hubs,u∈B→u∈R.active.hubSet)∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π (W∪R.active.rowSet) B e)∧
      (∀ v∈C.rows\R.active.rowSet,∀ w∈C.rows\R.active.rowSet,v≠w→¬PermutationClose π b v w)∧
      ∀ v∈C.rows\R.active.rowSet,∀ w∈R.active.rowSet,¬PermutationClose π b v w:=by
  obtain ⟨ε,hε,habs⟩:=marked_relative_host_absorber l hl ρ σ q₀ β blo bhi hρ hσ hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨a₀,b₀,habs⟩:=habs s (3*s*s)
  refine ⟨a₀,b₀,?_⟩
  intro f b dF hdF
  obtain ⟨N,habs⟩:=habs f b dF hdF
  refine ⟨N,?_⟩
  intro V₀ U₀ V U E K A S _ _ _ _ _ _ _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hb G hG hsize R W B hRH Q hp hB hW F hconf htypes hF Profiles
  have hs:Fintype.card G.activeRows+Fintype.card G.activeHubs≤s:=by simpa only [Fintype.card_coe] using hsize
  exact habs G.activeRows G.activeHubs V U E K A S hn hs (R.active_occurrence_bound s hsize)
    tail head ktail khead H₀ HK π hb G.active (G.active_balanced hG) R.active W B hRH Q hp hB hW F hconf htypes hF Profiles

end Oberwolfach
