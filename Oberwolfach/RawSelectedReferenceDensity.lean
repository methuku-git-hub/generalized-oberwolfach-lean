module

public import Oberwolfach.RawSelectedTwoPathsDensity
public import Oberwolfach.RawApproximateTwoPathsDensity
public import Oberwolfach.ColourOrientationTwoPathEvent

@[expose] public section
/-! A positive minimum-degree margin and the two-path estimate yield the
exact test-set density needed by the protected-list extension lemma. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_selected_reference_neighbour_density
    {V:Type} [Fintype V] [LinearOrder V]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool)
    (γ pstar p t:ℝ) (hγ:0≤γ) (hpstar:0≤pstar) (hp: pstar≤p)
    (hV:2≤Fintype.card V) (hP:∀x,(1/2+γ)*Fintype.card V≤(P.degree x:ℝ))
    (herror:t+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*Fintype.card V)
    (hpaths:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-
      2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (ω e)) false x v ∧
        0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (ω e)) false v y)).card:ℝ)):
    ∀i,RawNeighbourTestValid i→γ*pstar^2*Fintype.card V≤(rawSelectedNeighbourTestSet P π d ω i).card:=by
  apply raw_selected_two_paths_imply_neighbour_test_density P π d ω (γ*pstar^2) hV
  intro x y hxy
  have hc:=commonNeighbours_lower_of_minDegree P γ hP x y
  have hp2:pstar^2≤p^2:=by nlinarith
  have hc0:(0:ℝ)≤(P.neighborFinset x∩P.neighborFinset y).card:=by positivity
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have hmul:=mul_le_mul_of_nonneg_right hc (sq_nonneg p)
  have hcmp:=mul_le_mul_of_nonneg_left hp2 (mul_nonneg (by positivity : 0≤2*γ) hn0)
  have hpath:=hpaths x y hxy
  nlinarith
end Oberwolfach
