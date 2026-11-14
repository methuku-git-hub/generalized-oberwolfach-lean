module

public import Oberwolfach.LongRequiredInnerCoverageRepair
public import Oberwolfach.RootComparisonHosts

@[expose] public section
/-! A sharper interface for the inner repair: its load is controlled by the
actual per-vertex deficit of matching-allocated edges not yet embedded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_inner_deficit_load_bounds
    (D K:SimpleGraph V) (I:Finset V) (b:ℝ) (hb:0≤b)
    (hdeficit:∀v∈I,(D.degree v:ℝ)≤b):
    let Extra:=spanningRestriction D I
    let Kplus:=K⊔Extra
    (∀v,(Extra.degree v:ℝ)≤b) ∧
    (∀v,(Kplus.degree v:ℝ)≤(K.degree v:ℝ)+b) ∧
    ((Extra.edgeFinset.card:ℝ)≤I.card*b):=by
  intro Extra Kplus
  have hExtra:∀v,(Extra.degree v:ℝ)≤b:=by
    intro v
    dsimp only [Extra]
    rw [spanningRestriction_degree]
    split_ifs with hv
    · have hcard:((D.neighborFinset v∩I).card:ℝ)≤(D.degree v:ℝ):=by
        exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left):
          (D.neighborFinset v∩I).card≤D.degree v)
      exact hcard.trans (hdeficit v hv)
    · simpa using hb
  have he:=internal_graph_edge_count D I b hdeficit
  refine ⟨hExtra,?_,he⟩
  intro v
  have hh:((Kplus.degree v:ℝ)≤(K.degree v:ℝ)+(Extra.degree v:ℝ)):=by
    exact_mod_cast graph_degree_sup_le K Extra v
  linarith [hh,hExtra v]
end Oberwolfach
