module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

/-! Greedy colouring of a finite graph with a fresh palette. The bound is
stated using the actual finite neighbour sets. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteGreedyColouring
    {V : Type*} [Fintype V] (G : SimpleGraph V) {q : ℕ} (hq : 0<q)
    (hdegree : ∀ v,(Finset.univ.filter (fun u=>G.Adj v u)).card<q) :
    ∃ f : V → Fin q,∀ u v,G.Adj u v → f u≠f v := by
  classical
  have hpartial (S : Finset V) :
      ∃ f : V → Fin q,∀ u∈S,∀ v∈S,G.Adj u v → f u≠f v := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _=>⟨0,hq⟩,by simp⟩
    | @insert x S hx ih =>
      obtain ⟨f,hf⟩ := ih
      let B := (S.filter (fun u=>G.Adj x u)).image f
      have hB : B.card<q := by
        calc
          _ ≤ (S.filter (fun u=>G.Adj x u)).card := Finset.card_image_le
          _ ≤ (Finset.univ.filter (fun u=>G.Adj x u)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
          _ < _ := hdegree x
      obtain ⟨c,hc⟩ : ∃ c : Fin q,c∉B := by
        by_contra hn
        push Not at hn
        have he : B=Finset.univ := Finset.eq_univ_iff_forall.mpr hn
        simpa [he] using hB
      let g := Function.update f x c
      refine ⟨g,?_⟩
      intro u hu v hv hadj
      by_cases hux : u=x
      · subst u
        have hvx : v≠x := fun he=>G.irrefl (he ▸ hadj)
        have hvS : v∈S := (Finset.mem_insert.mp hv).resolve_left hvx
        have hfv : f v∈B := Finset.mem_image.mpr
          ⟨v,Finset.mem_filter.mpr ⟨hvS,hadj⟩,rfl⟩
        simp only [g,Function.update_self,Function.update_of_ne hvx]
        exact fun he=>hc (he.symm ▸ hfv)
      · have huS : u∈S := (Finset.mem_insert.mp hu).resolve_left hux
        by_cases hvx : v=x
        · subst v
          have hfu : f u∈B := Finset.mem_image.mpr
            ⟨u,Finset.mem_filter.mpr ⟨huS,hadj.symm⟩,rfl⟩
          simp only [g,Function.update_self,Function.update_of_ne hux]
          exact fun he=>hc (he ▸ hfu)
        · have hvS : v∈S := (Finset.mem_insert.mp hv).resolve_left hvx
          simp only [g,Function.update_of_ne hux,Function.update_of_ne hvx]
          exact hf u huS v hvS hadj
  obtain ⟨f,hf⟩ := hpartial Finset.univ
  exact ⟨f,fun u v=>hf u (Finset.mem_univ _) v (Finset.mem_univ _)⟩

end Oberwolfach
