module

public import Oberwolfach.DivisibilityColourSample
public import Oberwolfach.ColourReorientation

@[expose] public section

/-! Dense graphs admit a single uniform edge colouring with small degree
errors and linearly many ordered two-colour paths for every endpoint pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u
attribute [local instance] Classical.propDecidable

theorem dense_graph_common_neighbours {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : ℝ)
    (hdeg : ∀ v,(1/2+ε)*Fintype.card V≤(G.degree v:ℝ)) (u v : V) :
    2*ε*Fintype.card V≤((G.neighborFinset u∩G.neighborFinset v).card:ℝ) := by
  have he := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have hu := Finset.card_le_univ (G.neighborFinset u∪G.neighborFinset v)
  have hr : ((G.neighborFinset u).card:ℝ)+(G.neighborFinset v).card≤
      Fintype.card V+(G.neighborFinset u∩G.neighborFinset v).card := by
    exact_mod_cast (show (G.neighborFinset u).card+(G.neighborFinset v).card≤
      Fintype.card V+(G.neighborFinset u∩G.neighborFinset v).card by omega)
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hr
  linarith [hdeg u,hdeg v]

theorem divisibility_uniform_colour_sample (R : ℕ) (hR : 0<R)
    (ε ξ : ℝ) (hε : 0<ε) (hξ : 0<ξ) :
    ∃ N : ℕ,∀ (V : Type u) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (G : SimpleGraph V),(∀ v,(1/2+ε)*Fintype.card V≤(G.degree v:ℝ)) →
    ∀ b : Fin R,∃ σ : Sym2 V → Fin R,
      (∀ a v,|((edgeColourGraph G σ a).degree v:ℝ)-(G.degree v:ℝ)/R|<ξ*Fintype.card V/4) ∧
      (∀ a u v,u≠v → (ε/(R:ℝ)^2)*Fintype.card V≤(colouredTwoPathCount G σ u v a b:ℝ)) := by
  have hRr : (0:ℝ)<R := Nat.cast_pos.mpr hR
  let η := min (ξ/4) (ε/(R:ℝ)^2)
  have hη : 0<η := lt_min (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := divisibility_colour_sample R η hη
  refine ⟨N,?_⟩
  intro V instV instDec hn G hdeg b
  let ρ : Fin R → ℝ := fun _ => 1/R
  have hρ : ∀ a,0≤ρ a := fun _ => by dsimp [ρ];positivity
  have hsum : ∑ a,ρ a=1 := by simp [ρ,ne_of_gt hRr]
  obtain ⟨σ,hσdeg,hσpath⟩ := hN V hn G ρ hρ hsum b
  refine ⟨σ,?_,?_⟩
  · intro a v
    have hh := hσdeg a v
    have hsmall := mul_le_mul_of_nonneg_right (min_le_left (ξ/4) (ε/(R:ℝ)^2))
      (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
    rw [edgeColourGraph_degree]
    have heq : ρ a*(G.degree v:ℝ)=(G.degree v:ℝ)/R := by dsimp [ρ];ring
    rw [heq] at hh
    exact hh.trans_le (by dsimp only [η] at hh;linarith)
  · intro a u v huv
    have hh := (abs_lt.mp (hσpath a u v huv)).1
    have hc := dense_graph_common_neighbours G ε hdeg u v
    have hmean := div_le_div_of_nonneg_right hc (sq_nonneg (R:ℝ))
    have heq : ((G.neighborFinset u∩G.neighborFinset v).card:ℝ)*ρ a*ρ b=
        ((G.neighborFinset u∩G.neighborFinset v).card:ℝ)/(R:ℝ)^2 := by dsimp [ρ];ring
    rw [heq] at hh
    have hsmall := mul_le_mul_of_nonneg_right (min_le_right (ξ/4) (ε/(R:ℝ)^2))
      (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
    have heq2 : 2*ε*(Fintype.card V:ℝ)/(R:ℝ)^2=2*((ε/(R:ℝ)^2)*Fintype.card V) := by ring
    rw [heq2] at hmean
    dsimp only [η] at hh
    calc
      (ε/(R:ℝ)^2)*Fintype.card V=2*((ε/(R:ℝ)^2)*Fintype.card V)-(ε/(R:ℝ)^2)*Fintype.card V := by ring
      _ ≤ ((G.neighborFinset u∩G.neighborFinset v).card:ℝ)/(R:ℝ)^2-
          min (ξ/4) (ε/(R:ℝ)^2)*Fintype.card V := sub_le_sub hmean hsmall
      _ ≤ (colouredTwoPathCount G σ u v a b:ℝ) := by
        have h := add_lt_add_right hh (((G.neighborFinset u∩G.neighborFinset v).card:ℝ)/(R:ℝ)^2)
        convert h.le using 1 <;> ring

end Oberwolfach
