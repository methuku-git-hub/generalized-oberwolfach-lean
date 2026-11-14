module

public import Oberwolfach.AugmentationDegreeUpper
public import Oberwolfach.ThresholdBounds

@[expose] public section
/-! Deleting a two-regular factor and allowing a bounded old set preserves
both the degree margin and near-regularity at the original centre. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem near_regular_augmentation_bounds {V:Type} [Fintype V] [DecidableEq V]
    (G Dgraph:SimpleGraph V) (S:Finset V) (D δ α η εf:ℝ) (q:ℕ)
    (hδ0:(1/2:ℝ)≤δ) (hδ1:δ≤1) (hα:0<α) (hα1:α≤1) (hη:0≤η)
    (hηα:η≤α/8) (hηε:η≤εf/8) (hε:0<εf)
    (hs:0<S.card) (hq:Fintype.card V-S.card≤q)
    (hlarge:(q:ℝ)+2≤min α εf*(S.card:ℝ)/8)
    (hDlo:(δ+α)*S.card≤D) (hDhi:D≤S.card)
    (hnear:∀ v,|((G.neighborFinset v∩S).card:ℝ)-D|≤η*S.card)
    (hDgraph:∀ v,Dgraph.degree v≤2):
    let Q:=triangleAugmentationGraph G Dgraph S;
    (Fintype.card V:ℝ)/2≤D ∧ D≤2*Fintype.card V ∧
    (∀ v,(δ+α/4)*Fintype.card V≤(Q.degree v:ℝ)) ∧
    (∀ v,|(Q.degree v:ℝ)-D|≤εf*Fintype.card V):=by
  intro Q
  have hsR:(0:ℝ)<S.card:=by exact_mod_cast hs
  have hsV:S.card≤Fintype.card V:=Finset.card_le_univ S
  have hsize:(Fintype.card V:ℝ)≤(S.card:ℝ)+q:=by
    have hh:Fintype.card V≤S.card+q:=by omega
    exact_mod_cast hh
  have hSV:(S.card:ℝ)≤Fintype.card V:=by exact_mod_cast hsV
  have hsmallα:(q:ℝ)+2≤α*S.card/8:=by
    exact hlarge.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hsR.le) (by norm_num))
  have hsmallε:(q:ℝ)+2≤εf*S.card/8:=by
    exact hlarge.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hsR.le) (by norm_num))
  have hηsα:η*S.card≤α*S.card/8:=by nlinarith
  have hηsε:η*S.card≤εf*S.card/8:=by nlinarith
  have hq0:(0:ℝ)≤q:=by positivity
  have hminD:(Fintype.card V:ℝ)/2≤D:=by nlinarith
  have hmaxD:D≤2*Fintype.card V:=by nlinarith
  refine ⟨hminD,hmaxD,?_,?_⟩
  · intro v
    have hl:=triangleAugmentationGraph_degree G Dgraph S hDgraph v
    have hv:=abs_le.mp (hnear v)
    have hfac:0≤δ+α/4:=by linarith
    have hprod: (δ+α/4)*(Fintype.card V:ℝ)≤(δ+α/4)*((S.card:ℝ)+q):=
      mul_le_mul_of_nonneg_left hsize hfac
    have hqterm:(δ+α/4)*(q:ℝ)≤2*q:=by nlinarith
    change (δ+α/4)*Fintype.card V≤(triangleAugmentationGraph G Dgraph S).degree v
    nlinarith
  · intro v
    have hl:=triangleAugmentationGraph_degree G Dgraph S hDgraph v
    have hu:=augmentation_degree_upper G Dgraph S v
    have huR:((triangleAugmentationGraph G Dgraph S).degree v:ℝ)≤
        ((G.neighborFinset v∩S).card:ℝ)+q:=by
      have hq':(Fintype.card V-S.card:ℝ)≤q:=by exact_mod_cast hq
      have huR0:((triangleAugmentationGraph G Dgraph S).degree v:ℝ)≤
          ((G.neighborFinset v∩S).card:ℝ)+(Fintype.card V-S.card:ℝ):=by exact_mod_cast hu
      linarith
    have hv:=abs_le.mp (hnear v)
    apply abs_le.mpr
    constructor
    · nlinarith
    · nlinarith
end Oberwolfach
