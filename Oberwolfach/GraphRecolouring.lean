module

public import Oberwolfach.CoordinateRecolouring
public import Oberwolfach.ColouredTwoPaths
public import Oberwolfach.TwoPathSwitchAlgebra
public import Oberwolfach.ColourReorientation

@[expose] public section

/-! The preliminary residue repair uses distinct edges of the reserve colour.
It changes each vertex degree and each candidate-path count by at most the
number of recoloured physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem recolour_colour_card_difference {I V : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (ι : I↪Sym2 V) (σ : Sym2 V → Fin k) (c : I → Fin k)
    (b a : Fin k) (hG : ∀ i,ι i∈G.edgeFinset) (hb : ∀ i,σ (ι i)=b) :
    ((edgeColourGraph G (recolourCoordinates ι σ c) a).edgeFinset.card:ℤ)-
      ((edgeColourGraph G σ a).edgeFinset.card:ℤ)=
      ∑ i,((if c i=a then (1:ℤ) else 0)-(if b=a then 1 else 0)) := by
  rw [edgeColourGraph_card_edge_sum,edgeColourGraph_card_edge_sum]
  have hh := recolour_weighted_difference ι σ c
    (fun e => if e∈G.edgeFinset then (1:ℤ) else 0) (fun d => if d=a then (1:ℤ) else 0)
  simpa only [hG,ite_true,one_mul,hb] using hh

theorem recolour_nonreserve_card {I V : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (ι : I↪Sym2 V) (σ : Sym2 V → Fin k) (c : I → Fin k)
    (b a : Fin k) (hG : ∀ i,ι i∈G.edgeFinset) (hb : ∀ i,σ (ι i)=b) (hab : a≠b) :
    (edgeColourGraph G (recolourCoordinates ι σ c) a).edgeFinset.card=
      (edgeColourGraph G σ a).edgeFinset.card+(Finset.univ.filter (fun i => c i=a)).card := by
  have hh := recolour_colour_card_difference G ι σ c b a hG hb
  simp only [Ne.symm hab,ite_false,sub_zero] at hh
  have hc : (∑ i,if c i=a then (1:ℤ) else 0)=
      ((Finset.univ.filter (fun i => c i=a)).card:ℤ) := by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hc] at hh
  have he : ((edgeColourGraph G (recolourCoordinates ι σ c) a).edgeFinset.card:ℤ)=
      ((edgeColourGraph G σ a).edgeFinset.card:ℤ)+((Finset.univ.filter (fun i => c i=a)).card:ℤ) := by
    omega
  exact_mod_cast he

theorem recolour_path_count_stability {I V : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (ι : I↪Sym2 V) (σ : Sym2 V → Fin k) (c : I → Fin k)
    (u v : V) (huv : u≠v) (a b : Fin k) :
    |(colouredTwoPathCount G (recolourCoordinates ι σ c) u v a b:ℝ)-
      (colouredTwoPathCount G σ u v a b:ℝ)|≤Fintype.card I := by
  have hh := disjoint_pattern_stability (G.neighborFinset u∩G.neighborFinset v)
    (twoPathEdges u v) (fun w e => if e=s(u,w) then a else b)
    (Finset.univ.image ι) σ (recolourCoordinates ι σ c)
    (common_two_path_edges_disjoint G u v huv) (by
      intro e he
      symm
      apply recolourCoordinates_fixed
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using he)
  have hc : (Finset.univ.image ι).card=Fintype.card I := by
    rw [Finset.card_image_of_injective _ ι.injective,Finset.card_univ]
  simpa only [hc,← colouredTwoPathCount_patterns G _ u v huv a b] using hh

theorem recolour_degree_stability {I V : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] {k : ℕ}
    (G : SimpleGraph V) (ι : I↪Sym2 V) (σ : Sym2 V → Fin k) (c : I → Fin k)
    (a : Fin k) (v : V) :
    |((edgeColourGraph G (recolourCoordinates ι σ c) a).degree v:ℝ)-
      ((edgeColourGraph G σ a).degree v:ℝ)|≤Fintype.card I := by
  have hd : ∀ x∈G.neighborFinset v,∀ y∈G.neighborFinset v,x≠y →
      Disjoint ({s(v,x)}:Finset (Sym2 V)) {s(v,y)} := by
    intro x _ y _ hxy
    simp only [Finset.disjoint_singleton_left,Finset.mem_singleton]
    exact fun h => hxy (incidentPair_injective v h)
  have hh := disjoint_pattern_stability (G.neighborFinset v)
    (fun w => {s(v,w)}) (fun _ _ => a) (Finset.univ.image ι) σ (recolourCoordinates ι σ c) hd (by
      intro e he
      symm
      apply recolourCoordinates_fixed
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using he)
  have hc : (Finset.univ.image ι).card=Fintype.card I := by
    rw [Finset.card_image_of_injective _ ι.injective,Finset.card_univ]
  simp only [hc,← sampledColourDegree_patterns G _ a v] at hh
  simpa only [edgeColourGraph_degree] using hh

end Oberwolfach
