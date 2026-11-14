module

public import Oberwolfach.OrdinaryInducedCorrectionBalanceFromSample
public import Oberwolfach.OrdinaryInnerCrossBalance

@[expose] public section
/-! Near-balance on the inner subtype yields the corresponding spanning
inner profile, including zero outside the inner set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_balance_to_spanning
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (b:ℝ) (hb:0≤b)
    (hnear:∀v:I,|(((Q.induce (I:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:J=>H v.val u.val)).card|≤b):
    ∀v,|((spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b :=by
  let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let ψ:J↪U:=⟨Subtype.val,Subtype.val_injective⟩
  let Hloc:=fun v:I=>fun u:J=>H v.val u.val
  have hG:(Q.induce (I:Set V)).map φ=spanningRestriction Q I:=ordinary_induced_rim_map Q I
  have hH:ordinaryMappedSpokes Hloc φ ψ=(fun v u=>H v u∧v∈I∧u∈J):=ordinary_induced_spokes_map H I J
  intro v
  by_cases hv:v∈I
  · let x:I:=⟨v,hv⟩
    have hmap:=SimpleGraph.degree_map_apply (Q.induce (I:Set V)) φ x
    have hgn:=congrArg (fun G:SimpleGraph V=>G.neighborFinset v) hG
    have hgc:=congrArg Finset.card hgn
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hgc
    have hg:((spanningRestriction Q I).degree v)=(Q.induce (I:Set V)).degree x:=by
      have hm:((Q.induce (I:Set V)).map φ).degree v=(Q.induce (I:Set V)).degree x:=by
        convert hmap using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
      have hc:((Q.induce (I:Set V)).map φ).degree v=(spanningRestriction Q I).degree v:=by
        convert hgc using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
      exact hc.symm.trans hm
    have hm:=ordinaryMappedSpokes_row Hloc φ ψ x
    have hcard:=congrArg Finset.card hm
    rw [Finset.card_image_of_injective _ ψ.injective] at hcard
    have heq:=congrFun (congrFun hH v)
    have hrow:(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card=
        (Finset.univ.filter (fun u:J=>H v u.val)).card:=by
      have hf:Finset.univ.filter (ordinaryMappedSpokes Hloc φ ψ v)=
          Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J):=by
        ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and];exact iff_of_eq (heq u)
      have hc:(Finset.univ.filter (ordinaryMappedSpokes Hloc φ ψ v)).card=
          (Finset.univ.filter (fun u:J=>H v u.val)).card:=by
        convert hcard using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
      rw [hf] at hc
      exact hc
    rw [hg,hrow]
    convert hnear x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · rw [spanningRestriction_degree,if_neg hv]
    simp [hv,hb]
end Oberwolfach
