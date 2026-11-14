module

public import Oberwolfach.OrdinaryLocalRestriction
public import Oberwolfach.CanonicalGraphPairs
public import Oberwolfach.ResourceCandidateEmbeddings

@[expose] public section

/-! Cycles avoiding the endpoints of every forbidden rim edge are a
subfamily of the actual surviving cycles. The converse is neither needed
nor asserted: a cycle may contain both endpoints without using that edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

 theorem localOrdinaryRestriction_of_avoidance (Q D F : SimpleGraph V) (T Z : Finset V)
    (C : LocalOrdinaryCycle Q F T r) (hZ : Disjoint (localOrdinaryVertices C) Z)
    (hD : ∀ e∈canonicalGraphPairs D,¬(e.1∈localOrdinaryVertices C ∧ e.2∈localOrdinaryVertices C)) :
    localOrdinaryRestrictionGood (Q\D) (T\Z) C := by
  constructor
  · intro x y hxy
    refine ⟨C.val.property hxy,?_⟩
    intro hDxy
    let e : Sym2 V := s(x,y)
    have heD : e.out∈canonicalGraphPairs D :=
      Finset.mem_image.mpr ⟨e,SimpleGraph.mem_edgeFinset.mpr hDxy,rfl⟩
    have heC : C.val.val.val.Adj e.out.1 e.out.2 := by
      change s(e.out.1,e.out.2)∈C.val.val.val.edgeSet
      apply SimpleGraph.mem_edgeFinset.mp
      have he : s(e.out.1,e.out.2)=e := by rw [Sym2.mk];exact e.out_eq
      rw [he]
      exact SimpleGraph.mem_edgeFinset.mpr hxy
    exact hD e.out heD ⟨Set.mem_toFinset.mpr heC.mem_support_left,Set.mem_toFinset.mpr heC.mem_support_right⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨C.property.1 x (Set.mem_toFinset.mp hx),
      fun hz=>Finset.disjoint_left.mp hZ hx hz⟩

abbrev LocalOrdinaryVertexRetained (Q F : SimpleGraph V) (T Z : Finset V) (r : ℕ) :=
  {C : LocalOrdinaryCycle Q F T r // Disjoint (localOrdinaryVertices C) Z}

abbrev LocalOrdinaryPairRetained (Q D F : SimpleGraph V) (T Z : Finset V) (r : ℕ) :=
  {C : LocalOrdinaryVertexRetained Q F T Z r //
    ∀ e : canonicalGraphPairs D,¬(e.val.1∈localOrdinaryVertices C.val ∧ e.val.2∈localOrdinaryVertices C.val)}

def localOrdinaryRetainedEmbedding (Q D F : SimpleGraph V) (T Z : Finset V) :
    LocalOrdinaryPairRetained Q D F T Z r ↪ LocalOrdinaryCycle (Q\D) F (T\Z) r where
  toFun C := ⟨⟨C.val.val.val.val,(localOrdinaryRestriction_of_avoidance Q D F T Z C.val.val C.val.property
      (fun e he=>C.property ⟨e,he⟩)).1⟩,
    (fun v hv=>(localOrdinaryRestriction_of_avoidance Q D F T Z C.val.val C.val.property
      (fun e he=>C.property ⟨e,he⟩)).2 (Set.mem_toFinset.mpr hv)),C.val.val.property.2⟩
  inj' := by
    intro C D he
    apply Subtype.ext;apply Subtype.ext;apply Subtype.ext;apply Subtype.ext
    exact congrArg (fun C=>C.val.val) he

end Oberwolfach
