module

public import Oberwolfach.OrdinaryTransferCycles
public import Oberwolfach.OrdinaryCycleIncidence
public import Oberwolfach.FinitePatternSequences
public import Oberwolfach.TupleResourceMultiplicity

@[expose] public section

/-! The actual ordinary cycle family in a specified vertex set, excluding
all cycles whose support contains a forbidden pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

abbrev LocalOrdinaryCycle (Q F : SimpleGraph V) (T : Finset V) (r : ℕ) :=
  {C : OrdinaryCycle Q r // (∀ v∈C.val.val.support,v∈T) ∧
    ∀ v∈C.val.val.support,∀ w∈C.val.val.support,¬F.Adj v w}

def localOrdinaryVertices {Q F : SimpleGraph V} {T : Finset V}
    (C : LocalOrdinaryCycle Q F T r) : Finset V := C.val.val.val.support.toFinset

theorem localOrdinaryVertices_card {Q F : SimpleGraph V} {T : Finset V}
    (C : LocalOrdinaryCycle Q F T r) : (localOrdinaryVertices C).card=r := C.val.val.property.support_card

theorem ordinary_cycle_from_embedding (Q F : SimpleGraph V) (T : Finset V) (hr : 3≤r)
    (f : Fin r ↪ V) (hT : ∀ i,f i∈T) (hF : ∀ i j,¬F.Adj (f i) (f j))
    (hQ : ∀ i j,(SimpleGraph.cycleGraph r).Adj i j → Q.Adj (f i) (f j)) :
    ∃ C : LocalOrdinaryCycle Q F T r,localOrdinaryVertices C=Finset.univ.image f := by
  let G := (SimpleGraph.cycleGraph r).map f
  have hG : G≤Q := by
    intro x y h
    obtain ⟨i,j,hij,rfl,rfl⟩ := (SimpleGraph.map_adj f _ _ _).mp h
    exact hQ i j hij
  have hs : G.support=Set.range f := cycle_map_support hr f
  let C : LocalOrdinaryCycle Q F T r := ⟨⟨⟨G,⟨hr,⟨f,rfl⟩⟩⟩,hG⟩,by
    constructor
    · intro v hv
      obtain ⟨i,rfl⟩ := hs ▸ hv
      exact hT i
    · intro v hv w hw
      obtain ⟨i,rfl⟩ := hs ▸ hv
      obtain ⟨j,rfl⟩ := hs ▸ hw
      exact hF i j⟩
  refine ⟨C,?_⟩
  ext v
  simp only [localOrdinaryVertices,C,Set.mem_toFinset,hs,Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and]

theorem ordinary_base_tuple_cycle (Q F : SimpleGraph V) (T : Finset V) (hr : 3≤r)
    (f : Fin r→V) (hf : SparseGreedyGood Q F T ∅ (finitePatternRequirements (SimpleGraph.cycleGraph r)) f) :
    ∃ C : LocalOrdinaryCycle Q F T r,localOrdinaryVertices C=Finset.univ.image f := by
  exact ordinary_cycle_from_embedding Q F T hr ⟨f,hf.1⟩ (fun i=>(hf.2.1 i).1)
    hf.2.2.1 (finitePatternGood_adj Q F T ∅ (SimpleGraph.cycleGraph r) f hf)

theorem local_ordinary_multiplicity (Q F : SimpleGraph V) (T : Finset V) (Y : Finset V) :
    Fintype.card {C : LocalOrdinaryCycle Q F T r // localOrdinaryVertices C=Y}≤r^r := by
  apply tuple_resource_multiplicity r (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T))
    (fun C=> (embeddedCycleEmbedding C.val.val : Fin r→V))
  · intro C D h
    apply Subtype.ext;apply Subtype.ext
    exact embeddedCycleEmbedding_injective h
  · intro C
    rw [localOrdinaryVertices,embeddedCycleEmbedding_spec C.val.val]
    ext v
    simp only [Set.mem_toFinset,cycle_map_support C.val.val.property.1,
      Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and]
  · exact localOrdinaryVertices_card

end Oberwolfach
