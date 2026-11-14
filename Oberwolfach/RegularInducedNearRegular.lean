module

public import Oberwolfach.TriangleTransformerFactors

@[expose] public section
/-! Restricting a regular graph to a large vertex set creates a nearly
regular graph, including at every retained root. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_induced_degree_near_centre {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (D:ℕ) (hreg:G.IsRegularOfDegree D) (B:Finset V)
    (v:(B:Set V)):
    |(((G.induce (B:Set V)).degree v):ℝ)-
       ((D:ℝ)/Fintype.card V)*B.card|≤(Fintype.card V-B.card:ℕ):=by
  have hn:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨v.val⟩
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD:D≤Fintype.card V:=by
    have hh:=G.degree_lt_card_verts v.val
    rw [hreg v.val] at hh
    omega
  have hDR:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hD
  have hB:B.card≤Fintype.card V:=Finset.card_le_univ B
  have hBR:(B.card:ℝ)≤Fintype.card V:=by exact_mod_cast hB
  let θ:ℝ:=D/Fintype.card V
  have hθ0:0≤θ:=by dsimp [θ];positivity
  have hθ1:θ≤1:=by dsimp [θ];exact (div_le_one hnR).mpr hDR
  have hsub:G.neighborFinset v.val⊆(G.neighborFinset v.val∩B)∪(Finset.univ\B):=by
    intro w hw
    by_cases h:w∈B
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hw,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩)
  have hl: D≤(G.neighborFinset v.val∩B).card+(Fintype.card V-B.card):=by
    have hh:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simpa only [SimpleGraph.card_neighborFinset_eq_degree,hreg v.val,Finset.card_sdiff,
      Finset.inter_univ,Finset.card_univ] using hh
  have hu:(G.neighborFinset v.val∩B).card≤D:=by
    have hh:=Finset.card_le_card (Finset.inter_subset_left (s₁:=G.neighborFinset v.val) (s₂:=B))
    simpa only [SimpleGraph.card_neighborFinset_eq_degree,hreg v.val] using hh
  have hlR:(D:ℝ)≤((G.neighborFinset v.val∩B).card:ℝ)+(Fintype.card V-B.card:ℕ):=by exact_mod_cast hl
  have huR:((G.neighborFinset v.val∩B).card:ℝ)≤D:=by exact_mod_cast hu
  have hmiss:((Fintype.card V-B.card:ℕ):ℝ)=(Fintype.card V:ℝ)-B.card:=by rw [Nat.cast_sub hB]
  have hcentre:(D:ℝ)=θ*Fintype.card V:=by dsimp [θ];field_simp
  have hmul0:0≤θ*((Fintype.card V:ℝ)-B.card):=mul_nonneg hθ0 (by linarith)
  have hmul1:θ*((Fintype.card V:ℝ)-B.card)≤(Fintype.card V:ℝ)-B.card:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hBR)]
  rw [graph_induced_degree_as_intersection]
  change |((G.neighborFinset v.val∩B).card:ℝ)-θ*B.card|≤(Fintype.card V-B.card:ℕ)
  rw [hmiss]
  apply abs_le.mpr
  constructor <;> nlinarith
end Oberwolfach
