module

public import Oberwolfach.OrdinaryReferenceCuts
public import Oberwolfach.BipartiteLargeCutEmbedding

@[expose] public section
/-! Convert the original reference-event matrix inequalities to the
normalized cut interface without changing the sample or cut constant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_reference_matrix_cuts_normalized (Q F:SimpleGraph V) (H:V→U→Prop)
    (coins:Sym2 V→Bool) (δ h:ℝ) (hn:0<Fintype.card V) (hu:0<Fintype.card U)
    (hspoke:∀S:Finset V,∀T:Finset U,
      1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card U→
      h*min ((Fintype.card U:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
        (bipartiteMatrixCut (relationMultiplicity H) S T:ℝ))
    (hrim:∀S T:Finset V,
      1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card V→
      h*min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
        (matrixCut (sampledOrientation (Q\F) coins) S T:ℝ)):
    BipartiteLargeCut (sampledOrientation (Q\F) coins) δ h ∧
      BipartiteLargeCut (relationMultiplicity H) δ h:=by
  constructor
  · intro S T hST
    rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hn]
    exact hrim S T hST
  · intro S T hST
    rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hu]
    exact hspoke S T hST
end Oberwolfach
