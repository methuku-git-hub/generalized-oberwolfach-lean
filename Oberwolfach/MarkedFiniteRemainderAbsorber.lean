module

public import Oberwolfach.MarkedRemainderActiveSets
public import Oberwolfach.MarkedRelativeActiveForbiddenAbsorber
public import Oberwolfach.PermutationConflictDegree

@[expose] public section

/-! Apply the constructed marked absorber to an actual finite divisible
remainder. The number of incident vertices is its only size parameter;
no abstract realization, transformer or absorber is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_finite_remainder_absorber (l:ℕ) (hl:2≤l)
    (ρ σ q₀ β blo bhi:ℝ) (hρ:0<ρ) (hσ:0<σ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ a₀ b₀:ℕ,∀ f b:ℕ,∃ N:ℕ,
    ∀ (V U E K:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K],
    N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),1≤b→
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),MarkedRemainderDivisible tail head ktail khead HK A S (l+4)→
    (markedRemainderRows tail head ktail khead A S).card+(markedRemainderHubs S).card≤s→
    (∀ z∈S,H₀ z.1 z.2∨HK z.1 z.2)→
    (∀ a∈A,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))→
    ∀ (W:Finset V) (B:Finset U) (F₀:Finset (Finset V⊕(V×U))),
    F₀.card≤f→(∀ e:Finset V,Sum.inl e∈F₀→e.card≤2)→markedRemainderHubs S⊆B→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l (ρ*Fintype.card V) (σ*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    (∀ v z,HK v z→¬H₀ v z)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      IsResourceAbsorber (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) C.edges∧
      Disjoint C.edges F₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ v∈C.rows,v∈W∪markedRemainderRows tail head ktail khead A S→v∈markedRemainderRows tail head ktail khead A S)∧
      (∀ u∈C.hubs,u∈B→u∈markedRemainderHubs S)∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π (W∪markedRemainderRows tail head ktail khead A S) B e)∧
      (∀ v∈C.rows\markedRemainderRows tail head ktail khead A S,∀ w∈C.rows\markedRemainderRows tail head ktail khead A S,
        v≠w→¬PermutationClose π b v w)∧
      ∀ v∈C.rows\markedRemainderRows tail head ktail khead A S,∀ w∈markedRemainderRows tail head ktail khead A S,
        ¬PermutationClose π b v w:=by
  obtain ⟨ε,hε,habs⟩:=marked_relative_active_host_absorber_avoiding l hl ρ σ q₀ β blo bhi hρ hσ hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨a₀,b₀,habs⟩:=habs s
  refine ⟨a₀,b₀,?_⟩
  intro f b
  obtain ⟨N,habs⟩:=habs f b (2*b) (by positivity)
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hb A S hdiv hsize hS hsep W B F₀ hf hpairs hHB Q hp hB hW htypes Profiles
  let G:=markedRemainderGraph tail head ktail khead HK A S
  let R:=markedRemainderRealization tail head ktail khead H₀ HK π b A S hS hsep hp
  have hG:G.IsBalanced (l+4):=markedRemainderGraph_balanced _ _ _ _ _ _ _ _ hdiv
  have hsz:G.activeRows.card+G.activeHubs.card≤s:=by
    simpa only [G,markedRemainderGraph_active_rows,markedRemainderGraph_active_hubs] using hsize
  have hRH:∀ u,R.active.hubs u∈B:=by
    intro u
    apply hHB
    change u.val∈markedRemainderHubs S
    have hu:=u.property
    simpa only [G,markedRemainderGraph_active_hubs] using hu
  obtain ⟨C,hC⟩:=habs V U V U E K A S hn tail head ktail khead H₀ HK π hb G hG hsz R W B F₀ hf hpairs hRH Q hp hB hW
    (permutationConflictGraph π b) le_rfl htypes
    (fun v=>by exact_mod_cast permutationConflictGraph_degree_le π b v) Profiles
  have hsets:=markedRemainderRealization_active_sets tail head ktail khead H₀ HK π b A S hS hsep hp
  change R.active.rowSet=markedRemainderRows tail head ktail khead A S∧R.active.hubSet=markedRemainderHubs S at hsets
  have hres:R.active.resources=A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr:=
    R.active_resources.trans (markedRemainderRealization_resources _ _ _ _ _ _ _ _ _ _ _ _ _)
  refine ⟨C,?_⟩
  simpa only [hres,hsets.1,hsets.2] using hC

end Oberwolfach
