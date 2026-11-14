module

public import Oberwolfach.TriangleTransformerSampleFactors

@[expose] public section
/-! The sampled pair of triangle factors has thresholds uniform over all
bounded sizes of the old set. The bound is fixed before the host graph. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_sample_factors_uniform_old_size
    (L:ℕ) (β ρ:ℝ) (hβ:0<β) (hβ1:β≤1) (hρ:0<ρ) :
    ∃ s₀:ℕ,∀ s:ℕ,s₀≤s → 3∣s → ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],
      N≤Fintype.card V → ∀ (G:SimpleGraph V) (A Z:Finset V),
      Z.card≤L → 3∣Z.card → ρ*Fintype.card V≤(A.card:ℝ) →
      (∀ v∈A∪Z,(3/4+β/2)*(A.card:ℝ)≤((G.neighborFinset v∩A).card:ℝ)) →
      ∃ S:Finset V,S.card=s ∧ S⊆A ∧ Disjoint S Z ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle G 3),
        (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₁.biUnion (ordinaryCycleVertices G 3)=S∪Z ∧
        (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
        (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S) := by
  let T:Type:={z:Fin (L+1) // 3∣z.val}
  have hex:∀ z:T,∃ s₀:ℕ,∀ s:ℕ,s₀≤s → 3∣s → ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],
      N≤Fintype.card V → ∀ (G:SimpleGraph V) (A Z:Finset V),Z.card=z.val.val →
      ρ*Fintype.card V≤(A.card:ℝ) →
      (∀ v∈A∪Z,(3/4+β/2)*(A.card:ℝ)≤((G.neighborFinset v∩A).card:ℝ)) →
      ∃ S:Finset V,S.card=s ∧ S⊆A ∧ Disjoint S Z ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle G 3),
        (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₁.biUnion (ordinaryCycleVertices G 3)=S∪Z ∧
        (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
        (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S) := by
    intro z
    exact triangle_transformer_sample_factors z.val.val z.property β ρ hβ hβ1 hρ
  choose size hsize using hex
  refine ⟨Finset.univ.sup size,?_⟩
  intro s hs hdiv
  have hexN:∀ z:T,∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],
      N≤Fintype.card V → ∀ (G:SimpleGraph V) (A Z:Finset V),Z.card=z.val.val →
      ρ*Fintype.card V≤(A.card:ℝ) →
      (∀ v∈A∪Z,(3/4+β/2)*(A.card:ℝ)≤((G.neighborFinset v∩A).card:ℝ)) →
      ∃ S:Finset V,S.card=s ∧ S⊆A ∧ Disjoint S Z ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle G 3),
        (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₁.biUnion (ordinaryCycleVertices G 3)=S∪Z ∧
        (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
        (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S) := by
    intro z
    exact hsize z s ((Finset.le_sup (s:=Finset.univ) (f:=size) (Finset.mem_univ z)).trans hs) hdiv
  choose bound hbound using hexN
  refine ⟨Finset.univ.sup bound,?_⟩
  intro V _ _ hn G A Z hz hZ hA hdeg
  let z:T:=⟨⟨Z.card,by omega⟩,hZ⟩
  exact hbound z V ((Finset.le_sup (s:=Finset.univ) (f:=bound) (Finset.mem_univ z)).trans hn)
    G A Z rfl hA hdeg
end Oberwolfach
