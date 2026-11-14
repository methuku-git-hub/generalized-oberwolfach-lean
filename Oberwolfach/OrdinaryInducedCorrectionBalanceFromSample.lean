module

public import Oberwolfach.OrdinaryInducedPairEmbedding
public import Oberwolfach.OrdinarySameSampleBalanceProfiles
public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! The actual common-sample cleanup profile gives the near-balance input
    for sparse correction on the induced inner subtype. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_correction_balance_from_sample
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (B:Finset U)
    (pR pH density tR tH e L βe βh η:ℝ) (htR:0≤tR) (htH:0≤tH) (he:0≤e) (hL:0≤L)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density tR tH L βe βh s j raw)
    (hparent:∀v,|pR*(P.neighborFinset v∩I).card-2*pH*B.card|≤e)
    (hmargin:e+tR+2*tH+3*L≤η*I.card):
    ∀v:I,|(((Q.induce (I:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card|≤η*I.card:=by
  have hrim:∀v,((changed (Q.neighborFinset v) ((rawWheelGraph P raw).neighborFinset v)).card:ℝ)≤L:=by
    intro v
    simpa [changed,Finset.union_comm] using profile.rim_edit v
  have hspoke:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes π d raw j v))).card:ℝ)≤L:=by
    intro v
    simpa [changed,Finset.union_comm] using profile.spoke_row_edit v
  have hb:=ordinary_same_sample_balance_profiles P F Q H π d I B pR pH tR tH e L htR htH he hL
    s j raw profile.rows profile.columns hparent hrim hspoke
  let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩
  let Hloc:=fun v:I=>fun u:B=>H v.val u.val
  have hG:(Q.induce (I:Set V)).map φ=spanningRestriction Q I:=ordinary_induced_rim_map Q I
  have hH:ordinaryMappedSpokes Hloc φ ψ=(fun v u=>H v u∧v∈I∧u∈B):=ordinary_induced_spokes_map H I B
  intro v
  have hmap:=SimpleGraph.degree_map_apply (Q.induce (I:Set V)) φ v
  have hgn:=congrArg (fun G:SimpleGraph V=>G.neighborFinset v.val) hG
  have hgc:=congrArg Finset.card hgn
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hgc
  have hg:((spanningRestriction Q I).degree v.val)=(Q.induce (I:Set V)).degree v:=by
    have hm:((Q.induce (I:Set V)).map φ).degree v.val=(Q.induce (I:Set V)).degree v:=by
      convert hmap using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
    have hc:((Q.induce (I:Set V)).map φ).degree v.val=(spanningRestriction Q I).degree v.val:=by
      convert hgc using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact hc.symm.trans hm
  have hm:=ordinaryMappedSpokes_row Hloc φ ψ v
  have hcard:=congrArg Finset.card hm
  rw [Finset.card_image_of_injective _ ψ.injective] at hcard
  have heq:=congrFun (congrFun hH v.val)
  have hrow:(Finset.univ.filter (fun u=>H v.val u∧v.val∈I∧u∈B)).card=
      (Finset.univ.filter (fun u:B=>H v.val u.val)).card:=by
    have hf:Finset.univ.filter (ordinaryMappedSpokes Hloc φ ψ v.val)=
        Finset.univ.filter (fun u=>H v.val u∧v.val∈I∧u∈B):=by
      ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and];exact iff_of_eq (heq u)
    have hcard':(Finset.univ.filter (ordinaryMappedSpokes Hloc φ ψ v.val)).card=
        (Finset.univ.filter (fun u:B=>H v.val u.val)).card:=by
      convert hcard using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
    rw [hf] at hcard'
    convert hcard' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hbv:=hb.2 v.val
  have hout:|(((Q.induce (I:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card|≤e+tR+2*tH+3*L:=by
    rw [←hg,←hrow]
    convert hbv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact hout.trans hmargin
end Oberwolfach
