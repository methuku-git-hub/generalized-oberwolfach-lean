module

public import Oberwolfach.TypedMarkedLoadBounds
public import Oberwolfach.OrderedOrdinaryLocality

@[expose] public section
/-! Every genuine marked or ordinary candidate has at least two resources;
the existing linear upper bounds remain unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem typed_marked_seed_resource_size
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ):
    2≤(typedMarkedOccurrenceResources W).card ∧
      (typedMarkedOccurrenceResources W).card≤2*(m+1) := by
  refine ⟨?_,typedMarkedOccurrenceResources_card W⟩
  let a:(E⊕K)⊕(Bool×V×U):=Sum.inl (markedCycleTypedEdge tail head ktail khead m π b W.1 0)
  let c:(E⊕K)⊕(Bool×V×U):=Sum.inr (true,W.1.val 0,W.2.val)
  have ha:a∈typedMarkedOccurrenceResources W:=by
    apply (typedMarkedOccurrenceResources_rim W _).mpr
    exact ⟨0,rfl⟩
  have hc:c∈typedMarkedOccurrenceResources W:=by
    apply (typedMarkedOccurrenceResources_spoke W _).mpr
    exact ⟨0,by simp [c]⟩
  have hne:a≠c:=by simp [a,c]
  have hsub:({a,c}:Finset ((E⊕K)⊕(Bool×V×U)))⊆typedMarkedOccurrenceResources W:=by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> assumption
  have hcard:=Finset.card_le_card hsub
  simpa [hne] using hcard

theorem ordered_ordinary_seed_resource_size
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {r b:ℕ} {π:Equiv.Perm V} (hr:1≤r) (W:OrderedOrdinaryWheel (U:=U) π b r):
    2≤(orderedOrdinaryResources W).card ∧ (orderedOrdinaryResources W).card≤2*r := by
  refine ⟨?_,orderedOrdinaryResources_card W⟩
  let i:Fin r:=⟨0,hr⟩
  let a:(V×V)⊕(V×U):=Sum.inl (W.1.val i,W.1.val (cycleNext i))
  let c:(V×V)⊕(V×U):=Sum.inr (W.1.val i,W.2)
  have ha:a∈orderedOrdinaryResources W:=by apply (orderedOrdinaryResources_rim W _).mpr;exact ⟨i,rfl⟩
  have hc:c∈orderedOrdinaryResources W:=by apply (orderedOrdinaryResources_spoke W _).mpr;exact ⟨i,rfl⟩
  have hne:a≠c:=by simp [a,c]
  have hsub:({a,c}:Finset ((V×V)⊕(V×U)))⊆orderedOrdinaryResources W:=by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> assumption
  have hcard:=Finset.card_le_card hsub
  simpa [hne] using hcard
end Oberwolfach
