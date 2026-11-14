module

public import Oberwolfach.EndpointTriangleFactor
public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! The graph of the endpoint-triangle problem: row edges come from R and
row--index edges come from H. The external root x is used to define the two
neighbour sets, and need not belong to the row domain A. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def endpointHostGraph (R H : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj v w := (v∈A ∧ w∈A ∧ R.Adj v w) ∨
    ((v∈A ∧ w∈B ∨ v∈B ∧ w∈A) ∧ H.Adj v w)
  symm := ⟨by
    intro v w h
    rcases h with ⟨hv,hw,he⟩|⟨h,he⟩
    · exact Or.inl ⟨hw,hv,he.symm⟩
    · exact Or.inr ⟨h.elim (fun h=>Or.inr ⟨h.2,h.1⟩) (fun h=>Or.inl ⟨h.2,h.1⟩),he.symm⟩⟩
  loopless := ⟨by intro v h;rcases h with h|h;exact R.loopless.irrefl v h.2.2;exact H.loopless.irrefl v h.2⟩

theorem endpointHostGraph_row (R H : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B)
    {v w : V} (hv : v∈A) (hw : w∈A) :
    (endpointHostGraph R H A B).Adj v w ↔ R.Adj v w := by
  have hvB : v∉B := fun h=>Finset.disjoint_left.mp hAB hv h
  have hwB : w∉B := fun h=>Finset.disjoint_left.mp hAB hw h
  simp [endpointHostGraph,hv,hw,hvB,hwB]

theorem endpointHostGraph_spoke (R H : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B)
    {v w : V} (hv : v∈A) (hw : w∈B) :
    (endpointHostGraph R H A B).Adj v w ↔ H.Adj v w := by
  have hwA : w∉A := fun h=>Finset.disjoint_left.mp hAB h hw
  simp [endpointHostGraph,hv,hw,hwA]

theorem endpointHostGraph_row_common (R H : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B)
    (x : V) (Y J : Finset V)
    (hY : Y⊆common A {x} (fun v=>R.neighborFinset v)) (hJ : J⊆B) :
    common (common A {x} (fun v=>R.neighborFinset v)) (Y∪J)
      (fun v=>(endpointHostGraph R H A B).neighborFinset v)=
    common (common A (insert x Y) (fun v=>R.neighborFinset v)) J (fun v=>H.neighborFinset v) := by
  ext z
  simp only [common,Finset.mem_filter,Finset.mem_singleton,forall_eq,Finset.mem_insert,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hzA,hxz⟩,hh⟩
    refine ⟨⟨hzA,?_⟩,?_⟩
    · intro v hv
      rcases hv with rfl|hv
      · exact hxz
      · have hvA := ((mem_common_iff _ _ _ _).mp (hY hv)).1
        exact (endpointHostGraph_row R H A B hAB hvA hzA).mp (hh v (Finset.mem_union_left _ hv))
    · intro v hv
      exact ((endpointHostGraph_spoke R H A B hAB hzA (hJ hv)).mp
        (hh v (Finset.mem_union_right _ hv)).symm).symm
  · rintro ⟨⟨hzA,hh⟩,hJz⟩
    refine ⟨⟨hzA,hh x (Or.inl rfl)⟩,?_⟩
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · have hvA := ((mem_common_iff _ _ _ _).mp (hY hv)).1
      exact (endpointHostGraph_row R H A B hAB hvA hzA).mpr (hh v (Or.inr hv))
    · exact ((endpointHostGraph_spoke R H A B hAB hzA (hJ hv)).mpr (hJz v hv).symm).symm

theorem endpointHostGraph_index_common (R H : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B)
    (x : V) (Y : Finset V) (hY : Y⊆A) :
    common (common B {x} (fun v=>H.neighborFinset v)) Y
      (fun v=>(endpointHostGraph R H A B).neighborFinset v)=
    common B (insert x Y) (fun v=>H.neighborFinset v) := by
  ext z
  simp only [common,Finset.mem_filter,Finset.mem_singleton,forall_eq,Finset.mem_insert,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hzB,hxz⟩,hh⟩
    refine ⟨hzB,?_⟩
    intro v hv
    rcases hv with rfl|hv
    · exact hxz
    · exact (endpointHostGraph_spoke R H A B hAB (hY hv) hzB).mp (hh v hv)
  · rintro ⟨hzB,hh⟩
    exact ⟨⟨hzB,hh x (Or.inl rfl)⟩,fun v hv=>
      (endpointHostGraph_spoke R H A B hAB (hY hv) hzB).mpr (hh v (Or.inr hv))⟩

end Oberwolfach
