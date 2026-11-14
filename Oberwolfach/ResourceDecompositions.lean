module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Exact decompositions of finite physical edge sets. These statements
record edge-disjointness and equality of the covered set, rather than
only an equality of total edge counts. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W : Type*} [DecidableEq E] [DecidableEq W]

def HasResourceDecomposition (R : W → Finset E) (S : Finset E) : Prop :=
  ∃ M : Finset W,
    (∀ a ∈ M, ∀ b ∈ M, a ≠ b → Disjoint (R a) (R b)) ∧ M.biUnion R = S

theorem resource_decomposition_empty (R : W → Finset E) : HasResourceDecomposition R ∅ := by
  exact ⟨∅, by simp, by simp⟩

theorem resource_decomposition_singleton (R : W → Finset E) (w : W) :
    HasResourceDecomposition R (R w) := by
  refine ⟨{w}, ?_, by simp⟩
  intro a ha b hb hab
  have ha' : a=w := Finset.mem_singleton.mp ha
  have hb' : b=w := Finset.mem_singleton.mp hb
  exact (hab (ha'.trans hb'.symm)).elim

theorem resource_subset_union (R : W → Finset E) (M : Finset W) (a : W) (ha : a ∈ M) :
    R a ⊆ M.biUnion R := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨a,ha,he⟩

theorem resource_decomposition_union (R : W → Finset E) (S T : Finset E)
    (hS : HasResourceDecomposition R S) (hT : HasResourceDecomposition R T)
    (hST : Disjoint S T) : HasResourceDecomposition R (S ∪ T) := by
  obtain ⟨M,hM,rfl⟩ := hS
  obtain ⟨N,hN,rfl⟩ := hT
  refine ⟨M∪N, ?_, ?_⟩
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
    · exact hM a ha b hb hab
    · exact hST.mono (resource_subset_union R M a ha) (resource_subset_union R N b hb)
    · exact hST.symm.mono (resource_subset_union R N a ha) (resource_subset_union R M b hb)
    · exact hN a ha b hb hab
  · exact Finset.union_biUnion

theorem resource_decomposition_map {W' : Type*} [DecidableEq W']
    (R : W → Finset E) (R' : W' → Finset E) (f : W → W')
    (hR : ∀ w, R' (f w)=R w) (S : Finset E) (hS : HasResourceDecomposition R S) :
    HasResourceDecomposition R' S := by
  obtain ⟨M,hM,rfl⟩ := hS
  refine ⟨M.image f,?_,?_⟩
  · intro a ha b hb hab
    obtain ⟨a₀,ha₀,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀,hb₀,rfl⟩ := Finset.mem_image.mp hb
    rw [hR,hR]
    exact hM a₀ ha₀ b₀ hb₀ (fun h => hab (congrArg f h))
  · ext e
    simp only [Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,he⟩
      exact ⟨a,ha,by simpa only [hR] using he⟩
    · rintro ⟨a,ha,he⟩
      exact ⟨f a,⟨a,ha,rfl⟩,by simpa only [hR] using he⟩

theorem resource_decomposition_biUnion {I : Type*} [DecidableEq I]
    (R : W → Finset E) (S : I → Finset E) (J : Finset I)
    (hdec : ∀ i ∈ J, HasResourceDecomposition R (S i))
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (S i) (S j)) :
    HasResourceDecomposition R (J.biUnion S) := by
  induction J using Finset.induction_on with
  | empty => simpa using resource_decomposition_empty R
  | @insert i J hi ih =>
    rw [Finset.biUnion_insert]
    apply resource_decomposition_union R (S i) (J.biUnion S) (hdec i (Finset.mem_insert_self _ _))
    · apply ih
      · exact fun j hj => hdec j (Finset.mem_insert_of_mem hj)
      · exact fun j hj k hk hne => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
    · apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨j,hj,hje⟩ := Finset.mem_biUnion.mp hf
      have hn : i≠j := by intro h; subst j;exact hi hj
      exact (Finset.disjoint_left.mp (hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hn)) he hje

theorem disjoint_resource_unions {I : Type*} [DecidableEq I]
    (S : I → Finset E) (A B : Finset I) (hAB : Disjoint A B)
    (hdisj : ∀ i ∈ A, ∀ j ∈ B, i ≠ j → Disjoint (S i) (S j)) :
    Disjoint (A.biUnion S) (B.biUnion S) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,hi,hie⟩ := Finset.mem_biUnion.mp he
  obtain ⟨j,hj,hje⟩ := Finset.mem_biUnion.mp hf
  have hn : i≠j := by intro h; subst j; exact (Finset.disjoint_left.mp hAB) hi hj
  exact (Finset.disjoint_left.mp (hdisj i hi j hj hn)) hie hje

end Oberwolfach
