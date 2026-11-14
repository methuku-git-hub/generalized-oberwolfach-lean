module

public import Oberwolfach.EmbeddedRootedDeletionExpectation

@[expose] public section

/-! Restricting to the sampled vertices and its one retained root
already excludes every other vertex of the deleted population. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rooted_induced_weight_restriction {V C : Type*} [DecidableEq V]
    (R : C → Finset V) (w : C → ℝ) (A Z : Finset V) (hAZ : Disjoint A Z) (v : V) :
    inducedResourceWeight R (vertexRestrictedWeight R w (Z.erase v)) (insert v A)=
      inducedResourceWeight R w (insert v A) := by
  funext C₀
  by_cases hs : R C₀⊆insert v A
  · have hd : Disjoint (R C₀) (Z.erase v) := by
      apply Finset.disjoint_left.mpr
      intro x hx hz
      have hz' := Finset.mem_erase.mp hz
      have hxA := (Finset.mem_insert.mp (hs hx)).resolve_left hz'.1
      exact Finset.disjoint_left.mp hAZ hxA hz'.2
    simp only [inducedResourceWeight,hs,ite_true,vertexRestrictedWeight,hd]
  · simp only [inducedResourceWeight,hs,ite_false]

theorem embedded_rooted_original_weight_expectation
    {I : Type*} [Fintype I] [DecidableEq I]
    {V W : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    [∀ i,Fintype (W i)] [∀ i,DecidableEq (W i)]
    {C : Type*} [Fintype C]
    (e : (Σ i,W i) ↪ (Σ i,V i)) (he : ∀ v,(e v).1=v.1)
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (Z : Finset (Σ i,V i)) (hrange : ∀ v,(∃ u,e u=v) ↔ v∉Z)
    (v : Σ i,V i) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (W i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (W i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (W i) (m i)))).expectation
      (fun σ => hypergraphWeightedDegree R
        (inducedResourceWeight R w (insert v ((profileRootSet σ).map e))) v)=
      (∏ i,((m i).choose (a i-(if v.1=i then 1 else 0)):ℝ)/
        (Fintype.card (W i)).choose (a i-(if v.1=i then 1 else 0)))*
        hypergraphWeightedDegree R (vertexRestrictedWeight R w (Z.erase v)) v := by
  have hd (σ : ∀ i,FixedSubset (W i) (m i)) : Disjoint ((profileRootSet σ).map e) Z := by
    apply Finset.disjoint_left.mpr
    intro x hx hz
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hx
    exact (hrange _).mp ⟨u,rfl⟩ hz
  have hh := embedded_rooted_deletion_expectation e he R w a hR Z hrange v m hm
  dsimp only at hh
  simpa only [rooted_induced_weight_restriction R w _ Z (hd _) v] using hh

end Oberwolfach
