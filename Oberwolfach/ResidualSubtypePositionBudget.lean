module

public import Oberwolfach.ResidualSubtypeArcCount
public import Oberwolfach.ResidualInducedCardSet

@[expose] public section
/-! The ambient prescribed set and the residual graph give the numerical
hypothesis of the prescribed-position theorem on the surviving subtype. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def residualSubtypeSet (R A:Finset V):Finset {x // x∈R}:=
  Finset.univ.filter (fun x=>x.1∈A)

theorem residual_subtype_set_image (R A:Finset V) (hAR:A⊆R):
    (residualSubtypeSet R A).image Subtype.val=A := by
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hy).2
  · intro hx
    refine Finset.mem_image.mpr ⟨⟨x,hAR hx⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩

theorem residual_subtype_set_card (R A:Finset V) (hAR:A⊆R):
    (residualSubtypeSet R A).card=A.card := by
  calc
    (residualSubtypeSet R A).card = ((residualSubtypeSet R A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := by rw [residual_subtype_set_image R A hAR]

theorem residual_subtype_position_budget (R A:Finset V) (Q:SimpleGraph V)
    (hAR:A⊆R) (hisol:∀x,x∉R→∀y,¬Q.Adj x y)
    (qs:List (PrescribedSourcePiece {x // x∈R}))
    (hshape:∀p∈qs,p.Shape)
    (hpair:qs.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hgraph:prescribedDependentGraph (fun _ : Unit=>qs) ()=Q.induce (↑R:Set V))
    (hcount:R.card≤Q.edgeFinset.card+A.card):
    Fintype.card {x // x∈R} ≤
      (prescribedArcFinset (prescribedDependentDigraph (fun _ : Unit=>qs) ())).card+
      (residualSubtypeSet R A).card := by
  rw [residual_subtype_arc_count R qs hshape hpair,hgraph,
    residual_subtype_set_card R A hAR]
  have hcard:(Q.induce (↑R:Set V)).edgeFinset.card=Q.edgeFinset.card := by
    convert graph_induce_edge_count_of_isolated_outside_set Q (↑R:Set V) hisol using 1
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  convert hcount using 1
  · simp
  · apply congrArg (fun n=>n+A.card)
    convert hcard using 1
    apply congrArg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rfl
end Oberwolfach
