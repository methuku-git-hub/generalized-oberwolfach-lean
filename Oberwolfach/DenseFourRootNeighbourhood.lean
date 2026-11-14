module

public import Oberwolfach.DenseCommonNeighbourBounds

@[expose] public section
/-! Four or fewer common neighbourhoods in a graph above the three-quarter threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]
theorem dense_four_root_neighbourhood (P:SimpleGraph V) (α:ℝ) (hα:0<α)
    (hP:∀ v,(3/4+α)*Fintype.card V≤(P.degree v:ℝ)):
    ∀ S:Finset V,S.card≤4→
      4*(min α (1/4))*Fintype.card V≤((common Finset.univ S (fun v=>P.neighborFinset v)).card:ℝ) := by
  intro S hS
  let ξ:=min α (1/4)
  let δ:=3/4+ξ
  have hξ1:ξ≤1/4:=min_le_right _ _
  have hξα:ξ≤α:=min_le_left _ _
  have hδ:δ≤1:=by dsimp [δ];linarith
  have hdeg:∀ v,δ*Fintype.card V≤(P.degree v:ℝ):=by
    intro v
    have hh:=mul_le_mul_of_nonneg_right hξα (Nat.cast_nonneg (Fintype.card V))
    dsimp [δ]
    nlinarith only [hh,hP v]
  have hc:=common_neighbour_card_lower (Finset.univ:Finset V) S
    (fun v=>P.neighborFinset v) δ (fun v _=>by
      simpa only [Finset.inter_univ,Finset.univ_inter,Finset.card_univ,
        SimpleGraph.card_neighborFinset_eq_degree] using hdeg v)
  simp only [Finset.card_univ] at hc
  have hSreal:(S.card:ℝ)≤4:=by exact_mod_cast hS
  have hcoef:1-4*(1-δ)≤1-(S.card:ℝ)*(1-δ):=by
    nlinarith only [mul_le_mul_of_nonneg_right hSreal (sub_nonneg.mpr hδ)]
  have hm:=mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (Fintype.card V))
  have heq:1-4*(1-δ)=4*ξ:=by dsimp [δ];ring
  rw [heq] at hm
  exact hm.trans hc
end Oberwolfach
