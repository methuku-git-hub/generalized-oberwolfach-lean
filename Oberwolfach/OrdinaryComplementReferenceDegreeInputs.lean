module

public import Oberwolfach.OrdinaryRequiredEdgesCovered
public import Oberwolfach.PrescribedFamilyPhysicalDegree
public import Oberwolfach.OrdinaryProtectedRequiredDegree

@[expose] public section
/-! Translate physical matching coverage and the residual embedding load
into the uncovered and used reference-degree inputs for the actual remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uncovered_minus_conflict_degree
    {V : Type} [Fintype V] [DecidableEq V]
    (Sample State0 Bad Embedded : SimpleGraph V) (v : V) :
    (((Sample \ (State0 \ Bad)) \ Embedded).degree v : ℝ) ≤
      (((Sample \ State0) \ Embedded).degree v : ℝ) + Bad.degree v := by
  have hsub : (Sample \ (State0 \ Bad)) \ Embedded ≤ ((Sample \ State0) \ Embedded) ⊔ Bad := by
    intro x y h
    by_cases hz : State0.Adj x y
    · right
      by_contra hb
      exact h.1.2 ⟨hz,hb⟩
    · left
      exact ⟨⟨h.1.1,hz⟩,h.2⟩
  have hdeg := SimpleGraph.degree_le_of_le hsub (v := v)
  have hsup := graph_degree_sup_le ((Sample \ State0) \ Embedded) Bad v
  have hsup' : (((Sample \ State0) \ Embedded) ⊔ Bad).degree v ≤
      ((Sample \ State0) \ Embedded).degree v + Bad.degree v := by
    convert hsup using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hdeg' : ((Sample \ (State0 \ Bad)) \ Embedded).degree v ≤
      (((Sample \ State0) \ Embedded) ⊔ Bad).degree v := by
    convert hdeg using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hh : (((Sample \ (State0 \ Bad)) \ Embedded).degree v : ℝ) ≤
      (((Sample \ State0) \ Embedded).degree v : ℝ) + Bad.degree v := by
    exact_mod_cast hdeg'.trans hsup' 
  exact hh

theorem ordinary_used_reference_degree_from_new_union {n q : ℕ}
    (Reference : SimpleGraph (Fin n)) (Fs : Fin q → SimpleGraph (Fin n))
    (C : ∀u, Finset (Fs u).ConnectedComponent)
    (f : ∀u, {x : Fin n // (Fs u).connectedComponentMk x ∉ C u} ↪ Fin n)
    (Old New : Fin q → Finset (Sym2 (Fin n)))
    (hpartition : ∀u, (((Fs u).induce {x | (Fs u).connectedComponentMk x ∉ C u}).edgeFinset).image
      (Sym2.map (f u)) = Old u ∪ New u)
    (hold : ∀u, Disjoint (Old u) Reference.edgeFinset) :
    Reference ⊓ ordinaryEmbeddedComplements Fs C f ≤ prescribedPhysicalUnion New := by
  intro v w h
  have hmem : s(v,w) ∈ Reference.edgeFinset := SimpleGraph.mem_edgeFinset.mpr h.1
  obtain ⟨u,hu⟩ := SimpleGraph.iSup_adj.mp h.2
  have hm : s(v,w) ∈ (((Fs u).induce {x | (Fs u).connectedComponentMk x ∉ C u}).edgeFinset).image
      (Sym2.map (f u)) := by
    have hh : s(v,w) ∈ (((Fs u).induce {x | (Fs u).connectedComponentMk x ∉ C u}).map (f u)).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hu
    rw [SimpleGraph.edgeFinset_map] at hh
    obtain ⟨e,he,heq⟩ := Finset.mem_map.mp hh
    exact Finset.mem_image.mpr ⟨e,he,by simpa only [Function.Embedding.sym2Map_apply] using heq⟩
  rw [hpartition u] at hm
  rcases Finset.mem_union.mp hm with ho | hnew
  · exact False.elim (Finset.disjoint_left.mp (hold u) ho hmem)
  · apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨?_,h.1.ne⟩
    exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,hnew⟩
end Oberwolfach
