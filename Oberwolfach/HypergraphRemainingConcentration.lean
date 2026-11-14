module

public import Oberwolfach.RemainingColourConcentration
public import Oberwolfach.HypergraphColourCliques

@[expose] public section

/-! The remaining-degree concentration estimate with all geometric
inputs derived from rank and codegree of the actual hypergraph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem hypergraph_other_resource_incidence
    {V E : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) {k B : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (z : V) (U : Finset E) (hU : ∀ e∈U,z∈R e) (w : E) :
    (U.filter (fun e=>∃ v∈(R e).erase z,w∈hypergraphVertexClique R v)).card≤k*B := by
  classical
  have he : U.filter (fun e=>∃ v∈(R e).erase z,w∈hypergraphVertexClique R v)=
      U.filter (fun e=>∃ v∈R e,v≠z ∧ v∈R w) := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_erase,hypergraphVertexClique,Finset.mem_univ,true_and]
    tauto
  rw [he]
  exact hypergraph_outside_clique_incidence R hsize hcodeg z U hU w

theorem hypergraph_remaining_colour_concentration
    {V E C : Type*} [Fintype E] [DecidableEq V] [Fintype C]
    (R : E → Finset V) {k B : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (z : V) (U : Finset E) (hU : U.Nonempty) (hUz : ∀ e∈U,z∈R e)
    (c : C) (μ : E → FiniteLaw (C×Bool)) {t : ℝ} (ht : 0≤t)
    (hsmall : (U.card : ℝ)*(4*Real.exp
      (-t^2/(4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))))≤t) :
    (FiniteLaw.pi μ).probability (fun σ=>6*((k : ℝ)+1)*t≤
      |((remainingColourVertices (hypergraphLineGraph R) U (fun e=>(R e).erase z)
        (hypergraphVertexClique R) c σ).card : ℝ)-
        (FiniteLaw.pi μ).expectation (fun σ=>((remainingColourVertices (hypergraphLineGraph R)
          U (fun e=>(R e).erase z) (hypergraphVertexClique R) c σ).card : ℝ))|)≤
      8*((k : ℝ)+1)*Real.exp
        (-t^2/(4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))) := by
  classical
  refine remainingColourVertices_concentration (d:=k*B) (k:=k)
    (hypergraphLineGraph R) U hU ?_ (fun e=>(R e).erase z)
    (hypergraphVertexClique R) ?_ ?_ ?_ ?_ c μ ht hsmall
  · intro e he f hf hne
    exact ⟨hne,fun hd=>Finset.disjoint_left.mp hd (hUz e he) (hUz f hf)⟩
  · intro e _
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans (hsize e)
  · intro e he v hv
    exact hypergraphVertexClique_isClique R v
  · intro w S hN hI
    exact (hypergraphLineGraph_independent_neighbours R w S hN hI).trans (hsize w)
  · exact hypergraph_other_resource_incidence R hsize hcodeg z U hUz

theorem exponential_inverse_scale_mono {t A u s : ℝ} (hA : 0<A) (hu : 0<u) (hus : u≤s) :
    Real.exp (-t^2/(A*u))≤Real.exp (-t^2/(A*s)) := by
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div]
  apply neg_le_neg
  exact div_le_div_of_nonneg_left (sq_nonneg t) (mul_pos hA hu) (mul_le_mul_of_nonneg_left hus hA.le)

end Oberwolfach
