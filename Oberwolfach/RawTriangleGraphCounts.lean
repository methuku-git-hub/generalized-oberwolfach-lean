module

public import Oberwolfach.TriangleDomainNeighbourhoodEvent
public import Oberwolfach.BipartiteRelationGraph

@[expose] public section

/-! Translate the raw spoke relation into the actual bipartite graph on
the fixed rim and hub domains, with the same cardinalities and targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V Γ Color:Type} [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V]

theorem raw_triangle_counts_on_spoke_domain (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (A B Y:Finset V) (hAY:A⊆Y) (hYB:Disjoint Y B) (pR pH ε:ℝ) (s:V→Color→ℝ) (j:Color)
    (hj:∀ u,s u j=pH) (σ:RawWheelOutcome V V Γ Color)
    (hrow:RawOrdinaryRows P π d 3 A pR s j (ε*A.card) σ)
    (hindex:RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ):
    let R:=rawWheelGraph P σ
    let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
    (∀ S J:Finset V,S⊆Y → J⊆B → S.card≤3 → J.card≤2 → S.card+J.card≤4 →
      |((common (common A S (fun v=>R.neighborFinset v)) J (fun u=>H.neighborFinset u)).card:ℝ)-
        pR^S.card*pH^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card) ∧
    (∀ S:Finset V,S⊆Y → S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common B S (fun v=>H.neighborFinset v)).card:ℝ)-pH^S.card*B.card|≤ε*B.card):=by
  dsimp only
  let R:=rawWheelGraph P σ
  let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
  constructor
  · intro S J _hSY hJB hS hJ _hSJ
    have he:common (common A S (fun v=>R.neighborFinset v)) J (fun u=>H.neighborFinset u)=
        common (common A S (fun v=>R.neighborFinset v)) J (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u)):=by
      ext z
      simp only [mem_common_iff,SimpleGraph.mem_neighborFinset,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨⟨hz,hR⟩,hH⟩
        refine ⟨⟨hz,hR⟩,?_⟩
        intro u hu
        exact ((bipartiteRelationGraph_left Y B hYB _ (hAY hz)).mp (hH u hu).symm).2
      · rintro ⟨⟨hz,hR⟩,hH⟩
        refine ⟨⟨hz,hR⟩,?_⟩
        intro u hu
        exact ((bipartiteRelationGraph_left Y B hYB _ (hAY hz)).mpr ⟨hJB hu,hH u hu⟩).symm
    rw [he]
    simpa only [hj,Finset.prod_const] using (hrow S J hS (by omega)).le
  · intro S hSY hS hI
    have he:common B S (fun v=>H.neighborFinset v)=
        common B S (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v)):=by
      ext u
      simp only [mem_common_iff,SimpleGraph.mem_neighborFinset,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hu,h⟩
        exact ⟨hu,fun v hv=>((bipartiteRelationGraph_left Y B hYB _ (hSY hv)).mp (h v hv)).2⟩
      · rintro ⟨hu,h⟩
        exact ⟨hu,fun v hv=>(bipartiteRelationGraph_left Y B hYB _ (hSY hv)).mpr ⟨hu,h v hv⟩⟩
    rw [he]
    exact (hindex S hS hI).le

end Oberwolfach
