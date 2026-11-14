module

public import Oberwolfach.OrdinaryRelationChangeCounts
public import Oberwolfach.BipartiteNormalizedCutDeletion
public import Oberwolfach.RandomOrientation

@[expose] public section
/-! The original sampled orientation and spoke cuts survive the actual
symmetric edits, using the same orientation coins on the edited graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def ordinarySampledOrientedRelation (Q:SimpleGraph V) (σ:Sym2 V→Bool):V→V→Prop:=
  fun x y=>Q.Adj x y∧σ s(x,y)=orientationBit x y

theorem ordinary_sampled_orientation_as_relation (Q:SimpleGraph V) (σ:Sym2 V→Bool):
    sampledOrientation Q σ=relationMultiplicity (ordinarySampledOrientedRelation Q σ):=by
  funext x y
  simp [sampledOrientation,relationMultiplicity,ordinarySampledOrientedRelation]

theorem ordinary_edited_cuts_from_sample
    (Qraw Q F:SimpleGraph V) (H₀ H:V→U→Prop) (coins:Sym2 V→Bool) (δ h ζ d:ℝ)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U) (hζ:0≤ζ) (hQF:Disjoint Q F)
    (hscaleV:d≤ζ*Fintype.card V) (hscaleU:d≤ζ*Fintype.card U)
    (hR:∀v,((changed (Qraw.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤d)
    (hRow:∀v,((changed (Finset.univ.filter (H₀ v)) (Finset.univ.filter (H v))).card:ℝ)≤d)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>H₀ v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤d)
    (hcutR:BipartiteLargeCut (sampledOrientation (Qraw\F) coins) δ h)
    (hcutS:BipartiteLargeCut (relationMultiplicity H₀) δ h):
    (∀x y,sampledOrientation Q coins x y+sampledOrientation Q coins y x=if Q.Adj x y then 1 else 0) ∧
    BipartiteLargeCut (sampledOrientation Q coins) δ (h-ζ) ∧
    BipartiteLargeCut (relationMultiplicity H) δ (h-ζ):=by
  let R:=ordinarySampledOrientedRelation (Qraw\F) coins
  let R':=ordinarySampledOrientedRelation Q coins
  have hpoint (x y:V):¬(R x y↔R' x y)→¬(Qraw.Adj x y↔Q.Adj x y):=by
    intro horient heq
    have hQnot:Q.Adj x y→¬F.Adj x y:=by
      intro hq hf
      exact (disjoint_iff_inf_le.mp hQF) ⟨hq,hf⟩
    have hadj:(Qraw\F).Adj x y↔Q.Adj x y:=by
      simp only [SimpleGraph.sdiff_adj]
      tauto
    apply horient
    dsimp [R,R',ordinarySampledOrientedRelation]
    rw [hadj]
  have hrowR:∀x,(∑y,if ¬(R x y↔R' x y) then (1:ℝ) else 0)≤ζ*Fintype.card V:=by
    intro x
    have hh:(∑y,if ¬(Qraw.Adj x y↔Q.Adj x y) then (1:ℝ) else 0)≤d:=by
      have hRx:((changed (Finset.univ.filter (Qraw.Adj x)) (Finset.univ.filter (Q.Adj x))).card:ℝ)≤d:=by
        simpa only [SimpleGraph.neighborFinset_eq_filter] using hR x
      convert (ordinary_relation_change_sum (Qraw.Adj x) (Q.Adj x)).le.trans hRx using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    apply (Finset.sum_le_sum (fun y _=>?_)).trans (hh.trans hscaleV)
    by_cases he:¬(R x y↔R' x y)
    · have hp:=hpoint x y he
      simp [he,hp]
    · simp only [if_neg he]
      split_ifs <;> norm_num
  have hcolR:∀y,(∑x,if ¬(R x y↔R' x y) then (1:ℝ) else 0)≤ζ*Fintype.card V:=by
    intro y
    have hh:(∑x,if ¬(Qraw.Adj x y↔Q.Adj x y) then (1:ℝ) else 0)≤d:=by
      have hs:(∑x,if ¬(Qraw.Adj x y↔Q.Adj x y) then (1:ℝ) else 0)=
          ∑x,if ¬(Qraw.Adj y x↔Q.Adj y x) then (1:ℝ) else 0:=by
        apply Finset.sum_congr rfl
        intro x _
        rw [Qraw.adj_comm x y,Q.adj_comm x y]
      rw [hs]
      have hRy:((changed (Finset.univ.filter (Qraw.Adj y)) (Finset.univ.filter (Q.Adj y))).card:ℝ)≤d:=by
        simpa only [SimpleGraph.neighborFinset_eq_filter] using hR y
      convert (ordinary_relation_change_sum (Qraw.Adj y) (Q.Adj y)).le.trans hRy using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    apply (Finset.sum_le_sum (fun x _=>?_)).trans (hh.trans hscaleV)
    by_cases he:¬(R x y↔R' x y)
    · have hp:=hpoint x y he
      simp [he,hp]
    · simp only [if_neg he]
      split_ifs <;> norm_num
  have hrowS:∀v,(∑u,if ¬(H₀ v u↔H v u) then (1:ℝ) else 0)≤ζ*Fintype.card U:=by
    intro v
    have hh: (∑u,if ¬(H₀ v u↔H v u) then (1:ℝ) else 0)≤d:=by
      convert (ordinary_relation_change_sum (H₀ v) (H v)).le.trans (hRow v) using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    exact hh.trans hscaleU
  have hcolS:∀u,(∑v,if ¬(H₀ v u↔H v u) then (1:ℝ) else 0)≤ζ*Fintype.card V:=by
    intro u
    have hh: (∑v,if ¬(H₀ v u↔H v u) then (1:ℝ) else 0)≤d:=by
      convert (ordinary_relation_change_sum (fun v=>H₀ v u) (fun v=>H v u)).le.trans (hCol u) using 1 <;>
        congr! 8 <;> exact Subsingleton.elim _ _
    exact hh.trans hscaleV
  have hcutR':BipartiteLargeCut (relationMultiplicity R) δ h:=by
    rw [←ordinary_sampled_orientation_as_relation]
    exact hcutR
  have hnewR:=bipartiteLargeCut_after_relation_changes hn hn R R' δ h ζ hζ hrowR hcolR hcutR'
  have hnewS:=bipartiteLargeCut_after_relation_changes hn hu H₀ H δ h ζ hζ hrowS hcolS hcutS
  refine ⟨sampledOrientation_physical Q coins,?_,hnewS⟩
  rw [ordinary_sampled_orientation_as_relation]
  exact hnewR
end Oberwolfach
