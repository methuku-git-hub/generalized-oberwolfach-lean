module

public import Oberwolfach.DivisibilityResidues
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! Recolouring at most q*h distinct reserve edges fixes every colour-class
size modulo h. The reserve residue follows from h dividing q. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem colour_residue_repair {V : Type*} [Fintype V] [DecidableEq V] {q h : ℕ}
    (hh : 0<h) (hhq : h∣q) (G : SimpleGraph V) (σ : Sym2 V → Fin (q+1))
    (hreserve : q*h≤(edgeColourGraph G σ (Fin.last q)).edgeFinset.card) :
    ∃ τ : Sym2 V → Fin (q+1),
      (∀ a,((edgeColourGraph G τ a).edgeFinset.card:ZMod h)=(G.edgeFinset.card:ZMod h)) ∧
      (∀ a v,|((edgeColourGraph G τ a).degree v:ℝ)-((edgeColourGraph G σ a).degree v:ℝ)|≤q*h) ∧
      (∀ a u v,u≠v → |(colouredTwoPathCount G τ u v a (Fin.last q):ℝ)-
        (colouredTwoPathCount G σ u v a (Fin.last q):ℝ)|≤q*h) := by
  choose a ha using fun j : Fin q => residue_increment h G.edgeFinset.card
    (edgeColourGraph G σ j.castSucc).edgeFinset.card hh
  let I := (j : Fin q)×Fin (a j)
  have hI : Fintype.card I≤q*h := by
    simp only [I,Fintype.card_sigma,Fintype.card_fin]
    calc
      _ ≤ ∑ _ : Fin q,h := Finset.sum_le_sum (fun j _ => (ha j).1.le)
      _ = _ := by simp
  obtain ⟨ι,hι⟩ := Function.Embedding.exists_of_card_le_finset
    (α:=I) (s:=(edgeColourGraph G σ (Fin.last q)).edgeFinset) (hI.trans hreserve)
  have he (i : I) : ι i∈G.edgeFinset ∧ σ (ι i)=Fin.last q := by
    have hh := hι (Set.mem_range_self i)
    rw [edgeColourGraph_edges] at hh
    exact Finset.mem_filter.mp hh
  let c : I → Fin (q+1) := fun i => i.1.castSucc
  let τ := recolourCoordinates ι σ c
  have hcard (j : Fin q) : (Finset.univ.filter (fun i : I => c i=j.castSucc)).card=a j := by
    simp only [Finset.card_filter,I,Fintype.sum_sigma,c,Fin.castSucc_inj]
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hlj
      simp [hlj]
    · simp
  have hres (j : Fin q) : ((edgeColourGraph G τ j.castSucc).edgeFinset.card:ZMod h)=
      (G.edgeFinset.card:ZMod h) := by
    have hc := recolour_nonreserve_card G ι σ c (Fin.last q) j.castSucc
      (fun i => (he i).1) (fun i => (he i).2) (Fin.castSucc_ne_last j)
    rw [hcard] at hc
    change ((edgeColourGraph G (recolourCoordinates ι σ c) j.castSucc).edgeFinset.card:ZMod h)=_
    rw [hc]
    exact (ZMod.natCast_eq_natCast_iff' _ _ h).mpr (ha j).2
  have hIr : (Fintype.card I:ℝ)≤(q:ℝ)*h := by exact_mod_cast hI
  refine ⟨τ,all_colour_residues_of_nonreserve G τ hhq hres,?_,?_⟩
  · intro j v
    exact (recolour_degree_stability G ι σ c j v).trans hIr
  · intro j u v huv
    exact (recolour_path_count_stability G ι σ c u v huv j (Fin.last q)).trans hIr

end Oberwolfach
