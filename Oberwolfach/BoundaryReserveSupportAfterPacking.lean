module

public import Oberwolfach.BoundaryReserveSupportEvent
public import Oberwolfach.PhysicalBoundaryFullClassAfterPacking
public import Oberwolfach.BoundarySupportFromPhysicalGraph

@[expose] public section
/-! Overlaps and multiplicities of actual surviving boundary classes are
controlled on the fresh sample, charging the unused and cleanup degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W I:Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

theorem boundary_support_after_packing (G C D:SimpleGraph W) (σ:Sym2 W→Bool)
    (τ ε L ρ:ℝ) (hτ:0≤τ) (hgood:BoundaryReserveSupportGood G τ ε σ)
    (hCR:Disjoint C (retainedGraph G σ))
    (hL:∀x,(((G\retainedGraph G σ)\C).degree x:ℝ)+(D.degree x:ℝ)≤L)
    (e:I↪W) (S:I→Finset W) (hS:∀i,S i⊆(((G\C)\D).neighborFinset (e i)))
    (hdeg:(τ+ε)*Fintype.card W+L≤ρ*Fintype.card W)
    (hpair:(τ^2+ε)*Fintype.card W+2*L≤ρ^2*Fintype.card W):
    (∀i j,i≠j→((S i∩S j).card:ℝ)≤ρ^2*Fintype.card W) ∧
    (∀w,((Finset.univ.filter (fun i=>w∈S i)).card:ℝ)≤ρ*Fintype.card W):=by
  let R:=retainedGraph G σ
  let G':=(G\C)\D
  letI : DecidableRel G'.Adj := Classical.decRel _
  have hchange:∀x,((changed (R.neighborFinset x) (G'.neighborFinset x)).card:ℝ)≤L:=by
    intro x
    have hh:=physical_boundary_neighborhood_after_packing x G C D σ hCR
    have hc:((changed (R.neighborFinset x) (G'.neighborFinset x)).card:ℝ)≤
        (((G\R)\C).degree x:ℝ)+(D.degree x:ℝ):=by
      have hh' := (Nat.cast_le (α:=ℝ)).mpr hh
      push_cast at hh'
      convert hh' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact hc.trans (hL x)
  have hest:=boundary_support_estimates_after_changes G R G' Finset.univ Finset.univ τ
    (ε*Fintype.card W) L hchange
    (fun x=>(hgood.1 x).le) (fun x y hxy=>(hgood.2.1 x y hxy).le)
    (fun v hv=>(hgood.2.2 v hv).le)
  have hdegree (x:W):(G'.degree x:ℝ)≤(τ+ε)*Fintype.card W+L:=by
    have hh:|((G'.degree x:ℝ)-τ*(G.degree x:ℝ))|≤ε*Fintype.card W+L:=by
      simpa only [Finset.univ_inter,SimpleGraph.card_neighborFinset_eq_degree] using hest.1 x
    have hc:(G.degree x:ℝ)≤Fintype.card W:=by
      exact_mod_cast (Finset.card_le_univ (G.neighborFinset x))
    have hm:=mul_le_mul_of_nonneg_left hc hτ
    have hu:=(abs_le.mp hh).2
    nlinarith only [hu,hm]
  have hcommon (x y:W) (hxy:x≠y):
      (((G'.neighborFinset x∩G'.neighborFinset y).card):ℝ)≤
        (τ^2+ε)*Fintype.card W+2*L:=by
    have hh:=hest.2.1 x y hxy
    simp only [Finset.univ_inter] at hh
    have hc:(((G.neighborFinset x∩G.neighborFinset y).card):ℝ)≤Fintype.card W:=by
      exact_mod_cast (Finset.card_le_univ (G.neighborFinset x∩G.neighborFinset y))
    have hm:=mul_le_mul_of_nonneg_left hc (sq_nonneg τ)
    have hu:=(abs_le.mp hh).2
    nlinarith only [hu,hm]
  have hS':∀i,S i⊆G'.neighborFinset (e i):=by
    intro i
    convert hS i using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hs:=boundary_support_bounds_of_physical_graph G' e S hS' 
  refine ⟨?_,?_⟩
  · intro i j hij
    exact (hs.1 i j).trans ((hcommon (e i) (e j) (fun h=>hij (e.injective h))).trans hpair)
  · intro w
    exact (hs.2 w).trans ((hdegree w).trans hdeg)
end Oberwolfach
