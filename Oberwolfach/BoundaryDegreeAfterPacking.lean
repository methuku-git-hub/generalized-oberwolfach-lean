module

public import Oberwolfach.BoundaryReserveSupportAfterPacking
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! The surviving boundary has degree at most its sampled degree plus the
uncovered and cleanup errors, independent of the whole-host degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W:Type} [Fintype W] [DecidableEq W]

theorem boundary_degree_after_packing
    (G C D:SimpleGraph W) (σ:Sym2 W→Bool) (p ε L:ℝ)
    (hp:0≤p) (hgood:BoundaryReserveSupportGood G p ε σ)
    (hCR:Disjoint C (retainedGraph G σ))
    (hL:∀w,(((G\retainedGraph G σ)\C).degree w:ℝ)+(D.degree w:ℝ)≤L):
    ∀w,((((G\C)\D).degree w):ℝ)≤(p+ε)*Fintype.card W+L:=by
  let R:=retainedGraph G σ
  let G':=(G\C)\D
  intro w
  have hchange:((changed (R.neighborFinset w) (G'.neighborFinset w)).card:ℝ)≤L:=by
    have hh:=physical_boundary_neighborhood_after_packing w G C D σ hCR
    have hc:((changed (R.neighborFinset w) (G'.neighborFinset w)).card:ℝ)≤
        (((G\R)\C).degree w:ℝ)+(D.degree w:ℝ):=by
      have hh':=(Nat.cast_le (α:=ℝ)).mpr hh
      push_cast at hh'
      convert hh' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact hc.trans (hL w)
  have hraw:|(R.degree w:ℝ)-p*(G.degree w:ℝ)|<ε*Fintype.card W:=by
    simpa only [Finset.univ_inter,SimpleGraph.card_neighborFinset_eq_degree] using hgood.1 w
  have hcard:(G.degree w:ℝ)≤Fintype.card W:=by
    exact_mod_cast (Finset.card_le_univ (G.neighborFinset w))
  have hm:=mul_le_mul_of_nonneg_left hcard hp
  have hd:=card_difference_le_changed (R.neighborFinset w) (G'.neighborFinset w)
  rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at hd
  linarith only [(abs_lt.mp hraw).2,hm,(abs_le.mp hd).1,hchange]
end Oberwolfach
