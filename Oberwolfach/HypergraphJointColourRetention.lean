module

public import Oberwolfach.OverlappingCliqueJointRetention
public import Oberwolfach.HypergraphColourCliques

@[expose] public section

/-! Joint retention in actual resource cliques, with every quantitative
input derived from rank, codegree and the current colour degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem hypergraph_joint_colour_retention
    {V E C J : Type*} [Fintype E] [Fintype C] [Fintype J]
    (R : E → Finset V) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    {l k B s : ℕ} (hl : 1<l) (hcard : ∀ e,(L e).card=l)
    (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (c : C) (hdegree : ∀ v,(hypergraphColourClique R L v c).card≤s) (hsl : s≤l)
    (z : J → V) (hz : Function.Injective z)
    (hsmall : 2*((Fintype.card J)^2*(k^2*B))≤l) :
    let G := hypergraphLineGraph R
    let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (equalizationCoin G L l (k*s) e)
      (equalizationCoin_bounds G L (by omega) (k*s) e))
    let r := ((1-1/(l : ℝ))^(k*s))/(l : ℝ)
    |μ.probability (fun σ=>∀ j,∃ e∈hypergraphColourClique R L (z j) c,
        coinRetainedColour G σ e=some c)-
      (∏ j,((hypergraphColourClique R L (z j) c).card : ℝ)*r)|≤
      (((Fintype.card J)^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ) := by
  classical
  dsimp only
  let T := fun j=>hypergraphColourClique R L (z j) c
  have hinter (i j : J) (hij : i≠j) : (T i∩T j).card≤B :=
    hypergraphColourClique_intersection R L hcodeg (z i) (z j) (fun he=>hij (hz he)) c
  have hc (j : J) (e : E) (he : e∈T j) : c∈L e := (Finset.mem_filter.mp he).2.2
  have hh := overlapping_clique_joint_retention (hypergraphLineGraph R) L hL hl hcard T
    (fun j=>hypergraphColourClique_isClique R L (z j) c) hinter
    (fun j=>hdegree (z j)) hsl
    (fun i j hij e he=>restricted_hypergraph_clique_cross_degree R L z hsize hcodeg c i j hij e he)
    c hc (fun e _=>hypergraph_colour_neighbour_degree R L hsize c hdegree e)
    (hypergraph_colour_common_neighbours R L hsize hcodeg c) hsmall
  dsimp only at hh
  convert hh using 1
  push_cast
  ring

end Oberwolfach
