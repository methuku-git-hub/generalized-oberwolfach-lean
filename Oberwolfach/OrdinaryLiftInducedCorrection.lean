module

public import Oberwolfach.OrdinaryInducedPairEmbedding

@[expose] public section
/-! Lift a sparse balanced correction from the actual induced inner pair
    to ambient rim and spoke resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_lift_induced_correction
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (B:Finset U)
    (D:SimpleGraph I) (J:I→B→Prop) (r:ℕ) (L:ℝ)
    (hD:D≤Q.induce (I:Set V)) (hJ:∀v u,J v u→H v.val u.val)
    (hbal:∀v,((Q.induce (I:Set V))\D).degree v=2*(Finset.univ.filter (fun u:B=>H v.val u.val∧¬J v u)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v:I=>H v.val u.val∧¬J v u)).card)
    (hL:0≤L) (hrow:∀v,(D.degree v:ℝ)+(Finset.univ.filter (J v)).card≤L)
    (hcol:∀u,((Finset.univ.filter (fun v=>J v u)).card:ℝ)≤L):
    ∃(D':SimpleGraph V) (J':V→U→Prop),
      D'=D.map (⟨Subtype.val,Subtype.val_injective⟩:I↪V) ∧
      J'=ordinaryMappedSpokes J (⟨Subtype.val,Subtype.val_injective⟩:I↪V) (⟨Subtype.val,Subtype.val_injective⟩:B↪U) ∧
      D'≤spanningRestriction Q I ∧ (∀v u,J' v u→H v u∧v∈I∧u∈B) ∧
      (∀v,((spanningRestriction Q I)\D').degree v=
        2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J' v u)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J' v u)).card) ∧
      (∀x:V⊕U,((ordinaryPhysicalGraph D' J').degree x:ℝ)≤L):=by
  let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩
  let D':=D.map φ
  let J':=ordinaryMappedSpokes J φ ψ
  have h:=ordinary_mapped_correction (Q.induce (I:Set V)) D (fun v:I=>fun u:B=>H v.val u.val)
    J φ ψ r L hD hJ
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hL hrow hcol
  have hG:(Q.induce (I:Set V)).map φ=spanningRestriction Q I:=ordinary_induced_rim_map Q I
  have hH:ordinaryMappedSpokes (fun v:I=>fun u:B=>H v.val u.val) φ ψ=
      (fun v u=>H v u∧v∈I∧u∈B):=ordinary_induced_spokes_map H I B
  dsimp only at h
  refine ⟨D',J',rfl,rfl,?_,?_,?_,?_,h.2.2.2.2⟩
  · rw [←hG];exact h.1
  · intro v u hvu
    have hh:=h.2.1 v u hvu
    have he:=congrFun (congrFun hH v) u
    exact he ▸ hh
  · intro v
    have hh:=h.2.2.1 v
    simp only [hH] at hh
    have he:=congrArg (fun G:SimpleGraph V=>G.neighborFinset v) hG
    have hc:=congrArg Finset.card he
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    have hdeg:(((Q.induce (I:Set V)).map φ)\D').degree v=((spanningRestriction Q I)\D').degree v:=by
      have hhG:=congrArg (fun G:SimpleGraph V=>(G\D').neighborFinset v) hG
      have hhC:=congrArg Finset.card hhG
      simp only [SimpleGraph.card_neighborFinset_eq_degree] at hhC
      convert hhC using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hh':(((Q.induce (I:Set V)).map φ)\D').degree v=
      2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J' v u)).card:=by
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    convert hdeg.symm.trans hh' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    have hh:=h.2.2.2.1 u
    simp only [hH] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
