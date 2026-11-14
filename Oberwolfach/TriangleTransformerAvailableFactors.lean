module

public import Oberwolfach.TriangleTransformerUniformFactors

@[expose] public section
/-! In the triangular transformer the available vertices may be obtained by
excluding a small set from a graph with the stated minimum degree. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_available_neighbours
    {V:Type} [Fintype V] [DecidableEq V] (G:SimpleGraph V) (A:Finset V) (β:ℝ)
    (hβ:0<β) (hβ1:β≤1)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(G.degree v:ℝ))
    (hmiss:(((Finset.univ:Finset V)\A).card:ℝ)≤(β/2)*(Fintype.card V:ℝ)):
    (1/2)*(Fintype.card V:ℝ)≤(A.card:ℝ) ∧
    ∀ v,(3/4+β/2)*(A.card:ℝ)≤((G.neighborFinset v∩A).card:ℝ) := by
  have htotal:(A.card:ℝ)+(((Finset.univ:Finset V)\A).card:ℝ)=Fintype.card V:=by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    have he : A.card + ((Finset.univ:Finset V)\A).card = Fintype.card V := by simpa [add_comm] using hc
    exact_mod_cast he
  have hn:0≤(Fintype.card V:ℝ):=by positivity
  have ha:(A.card:ℝ)≤Fintype.card V:=Nat.cast_le.mpr (Finset.card_le_univ A)
  constructor
  · nlinarith
  · intro v
    have hcard:(G.neighborFinset v∩A).card + (G.neighborFinset v\A).card=G.degree v:=by
      rw [Finset.card_inter_add_card_sdiff,SimpleGraph.card_neighborFinset_eq_degree]
    have hsubset:G.neighborFinset v\A⊆(Finset.univ:Finset V)\A:=by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,(Finset.mem_sdiff.mp hx).2⟩
    have hsmall:((G.neighborFinset v\A).card:ℝ)≤(((Finset.univ:Finset V)\A).card:ℝ):=
      Nat.cast_le.mpr (Finset.card_le_card hsubset)
    have hc:((G.neighborFinset v∩A).card:ℝ)+((G.neighborFinset v\A).card:ℝ)=(G.degree v:ℝ):=by exact_mod_cast hcard
    have hv:=hdeg v
    nlinarith

theorem triangle_transformer_available_sample_factors
    (L:ℕ) (β:ℝ) (hβ:0<β) (hβ1:β≤1) :
    ∃ s₀:ℕ,∀ s:ℕ,s₀≤s → 3∣s → ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],
      N≤Fintype.card V → ∀ (G:SimpleGraph V) (A Z:Finset V),
      Z.card≤L → 3∣Z.card →
      (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(G.degree v:ℝ)) →
      (((Finset.univ:Finset V)\A).card:ℝ)≤(β/2)*(Fintype.card V:ℝ) →
      ∃ S:Finset V,S.card=s ∧ S⊆A ∧ Disjoint S Z ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle G 3),
        (∀ C∈M₁,∀ D∈M₁,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₁.biUnion (ordinaryCycleVertices G 3)=S∪Z ∧
        (∀ C∈M₂,∀ D∈M₂,C≠D → Disjoint (ordinaryCycleVertices G 3 C) (ordinaryCycleVertices G 3 D)) ∧
        M₂.biUnion (ordinaryCycleVertices G 3)=S ∧
        (∀ C∈M₁,∀ D∈M₂,Disjoint C.val.val.edgeFinset D.val.val.edgeFinset) ∧
        (∀ C∈M₁,∀ v w,C.val.val.Adj v w → v∈S ∨ w∈S) := by
  obtain ⟨s₀,hs⟩:=triangle_transformer_sample_factors_uniform_old_size L β (1/2) hβ hβ1 (by norm_num)
  refine ⟨s₀,?_⟩
  intro s hs₀ hdiv
  obtain ⟨N,hN⟩:=hs s hs₀ hdiv
  refine ⟨N,?_⟩
  intro V _ _ hn G A Z hz hZ hdeg hmiss
  obtain ⟨hA,hAdeg⟩:=triangle_transformer_available_neighbours G A β hβ hβ1 hdeg hmiss
  exact hN V hn G A Z hz hZ hA (fun v _=>hAdeg v)
end Oberwolfach
