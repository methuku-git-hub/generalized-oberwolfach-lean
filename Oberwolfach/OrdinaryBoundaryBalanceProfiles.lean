module

public import Oberwolfach.OrdinaryBoundaryDegreeProfiles
public import Oberwolfach.OrdinaryOuterHostBalanceRefined

@[expose] public section
/-! Inside roots inherit boundary balance from the full and inner profiles;
outside roots use the cross-profile bound directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_balance_from_profiles
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (b c d:ℝ)
    (hfull:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤b)
    (hinner:∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤c)
    (hcross:∀v∉I,|((Q.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤d):
    let B:=ordinaryBoundaryGraph Q H I J;
    ∀v,|((B.comap Sum.inl).degree v:ℝ)-2*(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u))).card|≤max (b+c) d:=by
  intro B v
  by_cases hv:v∈I
  · have heR:(B.comap Sum.inl).neighborFinset v=(Q\spanningRestriction Q I).neighborFinset v:=by
      rw [ordinary_boundary_rim_neighbors,if_pos hv]
      ext w
      simp only [Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj,spanningRestriction_adj]
      tauto
    have heS:(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u)))=
        Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J)):=by
      rw [ordinary_boundary_spoke_neighbors,if_pos hv]
      ext u
      simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,hv]
    have hd:(B.comap Sum.inl).degree v=(Q\spanningRestriction Q I).degree v:=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree,heR]
    rw [hd,heS]
    exact (ordinary_outer_host_balance_refined Q H I J b c hfull hinner v).trans (le_max_left _ _)
  · have hd:(B.comap Sum.inl).degree v=(Q.neighborFinset v∩I).card:=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree,ordinary_boundary_rim_neighbors,if_neg hv]
    have hs:(Finset.univ.filter (fun u=>B.Adj (Sum.inl v) (Sum.inr u)))=J.filter (H v):=by
      rw [ordinary_boundary_spoke_neighbors,if_neg hv]
    rw [hd,hs]
    exact (hcross v hv).trans (le_max_right _ _)
end Oberwolfach
