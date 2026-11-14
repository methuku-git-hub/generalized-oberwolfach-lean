module

public import Oberwolfach.RootedPathCycleEmbedding
public import Oberwolfach.DenseInducedEmbeddings

@[expose] public section

/-! A labelled cycle through a specified vertex in a large induced subgraph.
The root occupies position zero, so later spoke replacements retain it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rooted_cycle_inside_large_subset (β : ℝ) (hβ : 0<β) (r b : ℕ) (hr : 3≤r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V : Type*) [Fintype V] [DecidableEq V],Fintype.card V≤n →
    ∀ (G : SimpleGraph V),(∀ v,(1/2+β)*(n:ℝ)≤G.degree v) →
    ∀ (A S : Finset V),((Finset.univ\A).card:ℝ)≤(β/2)*n → S.card≤b →
    ∀ x : V,x∈A → x∉S →
    ∃ f : Fin r ↪ V,f ⟨0,by omega⟩=x ∧
      (∀ i j,(SimpleGraph.cycleGraph r).Adj i j → G.Adj (f i) (f j)) ∧
      (∀ i,f i∈A) ∧ ∀ i,f i∉S := by
  obtain ⟨n₁,hpath⟩ := fixed_length_path (β/2) (by positivity) (r-1) b (by omega)
  refine ⟨max n₁ (2*b+1),?_⟩
  intro n hn V _ _ hV G hdeg A S hA hS x hxA hxS
  let Q := G.induce (A:Set V)
  let x' : (A:Set V) := ⟨x,hxA⟩
  let S' : Finset (A:Set V) := Finset.univ.filter (fun v => v.val∈S)
  have hS' : S'.card≤b := by
    let f : S' → S := fun v => ⟨v.val.val,(Finset.mem_filter.mp v.property).2⟩
    have hf : Function.Injective f := by
      intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : S => z.val) he
    exact (show S'.card≤S.card by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf).trans hS
  have hQ : ∀ v,(1/2+β/2)*(n:ℝ)≤Q.degree v := induced_dense_degree G A n β hdeg hA
  have hbound : 2*b<n := by have hh := (le_max_right n₁ (2*b+1)).trans hn;omega
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsize : S'.card<(Q.neighborFinset x').card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    have hsR : (S'.card:ℝ)≤b := by exact_mod_cast hS'
    have hbR : 2*(b:ℝ)<n := by exact_mod_cast hbound
    have hh : (S'.card:ℝ)<Q.degree x' := by nlinarith [hQ x']
    exact_mod_cast hh
  obtain ⟨y',hy',hy'S⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  have hxy : Q.Adj x' y' := by simpa only [SimpleGraph.mem_neighborFinset] using hy'
  have hcard : Fintype.card (A:Set V)≤n := by simpa using (Finset.card_le_univ A).trans hV
  obtain ⟨p,hp,hlen,havoid⟩ := hpath n ((le_max_left _ _).trans hn) (A:Set V) hcard Q hQ
    x' y' hxy.ne S' hS' (by simpa [S',x'] using hxS) hy'S
  let f := pathCycleEmbedding p hp hlen
  let g : Fin r ↪ V := f.trans (Function.Embedding.subtype _)
  refine ⟨g,?_,?_,?_,?_⟩
  · change (f ⟨0,by omega⟩).val=x
    rw [show f ⟨0,by omega⟩=x' from pathCycleEmbedding_first _ p hp hlen]
  · intro i j hij
    exact pathCycleEmbedding_hom hr p hp hlen hxy i j hij
  · intro i
    exact (f i).property
  · intro i hmem
    have hh := pathCycleEmbedding_avoids (S':Set (A:Set V)) p hp hlen havoid i
    exact hh (by simp [S',hmem];exact hmem)

end Oberwolfach
