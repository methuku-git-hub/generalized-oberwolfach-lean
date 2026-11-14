module

public import Oberwolfach.OrdinaryInducedIntersectionCards
public import Oberwolfach.OrdinaryInnerCrossBalance

@[expose] public section
/-! Transport an ambient inner-pair balance estimate to the nested local
parent and inner types used by the ordinary matching and correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_inner_balance_induced_point_eq
    (G:SimpleGraph V) (H:V→U→Prop) (A I:Finset V) (B J:Finset U) (hI:I⊆A) (hJ:J⊆B):
    let Ilocal:Finset A:=Finset.univ.filter (fun x:A=>x.val∈I);
    let Jlocal:Finset B:=Finset.univ.filter (fun u:B=>u.val∈J);
    ∀v:Ilocal,|(((G.induce (A:Set V)).induce (Ilocal:Set A)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:Jlocal=>H v.val.val u.val.val)).card| =
      |((spanningRestriction G I).degree v.val.val:ℝ)-
      2*(Finset.univ.filter (fun u=>H v.val.val u∧v.val.val∈I∧u∈J)).card| :=by
  intro Ilocal Jlocal v
  have hv:v.val.val∈I:=(Finset.mem_filter.mp v.property).2
  have hII:I∩A=I:=Finset.inter_eq_left.mpr hI
  have hJB:J∩B=J:=Finset.inter_eq_left.mpr hJ
  have hloc1:(((G.induce (A:Set V)).induce (Ilocal:Set A)).degree v)=
      (((G.induce (A:Set V)).neighborFinset v.val)∩Ilocal).card:=by
    have hh:=ordinary_induced_neighbor_intersection_card (G.induce (A:Set V)) Ilocal Ilocal v
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    have hs:((G.induce (A:Set V)).induce (Ilocal:Set A)).neighborFinset v ⊆
        (Finset.univ.filter (fun x:Ilocal=>x.val∈Ilocal)):=by
      intro x hx
      simp [x.property]
    have hinter:=Finset.inter_eq_left.mpr hs
    simp only [Finset.inter_self] at hh
    convert hh using 1 <;> first | exact (congrArg Finset.card hinter).symm | exact Subsingleton.elim _ _
  have hloc2:(((G.induce (A:Set V)).neighborFinset v.val)∩Ilocal).card=
      (G.neighborFinset v.val.val∩I).card:=by
    have hh:=ordinary_induced_neighbor_intersection_card G A I v.val
    rw [hII] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hamb:((spanningRestriction G I).degree v.val.val)=(G.neighborFinset v.val.val∩I).card:=by
    rw [spanningRestriction_degree,if_pos hv]
  have hspoke:(Finset.univ.filter (fun u:Jlocal=>H v.val.val u.val.val)).card=
      (Finset.univ.filter (fun u=>H v.val.val u∧v.val.val∈I∧u∈J)).card:=by
    let T:=Finset.univ.filter (fun u:Jlocal=>H v.val.val u.val.val)
    have himg:T.image (Subtype.val:Jlocal→B)=Jlocal.filter (fun u:B=>H v.val.val u.val):=by
      ext u
      simp only [T,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨w,hw,rfl⟩;exact ⟨w.property,hw⟩
      · rintro ⟨hu,hh⟩;exact ⟨⟨u,hu⟩,hh,rfl⟩
    have hcard:=congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
    have hfilter:Jlocal.filter (fun u:B=>H v.val.val u.val)=
        Finset.univ.filter (fun u:B=>H v.val.val u.val∧u.val∈J):=by
      ext u;simp [Jlocal,and_comm]
    rw [hfilter] at hcard
    have houter:=ordinary_induced_spoke_intersection_card H B J v.val.val
    rw [hJB] at houter
    have he:(Finset.univ.filter (H v.val.val))∩J=
        Finset.univ.filter (fun u=>H v.val.val u∧v.val.val∈I∧u∈J):=by
      ext u;simp [hv,and_comm]
    rw [he] at houter
    exact hcard.trans houter
  rw [hloc1,hloc2,←hamb,hspoke]

 theorem ordinary_inner_balance_induced_reverse
    (G:SimpleGraph V) (H:V→U→Prop) (A I:Finset V) (B J:Finset U) (hI:I⊆A) (hJ:J⊆B) (b:ℝ)
    (hbal:let Ilocal:Finset A:=Finset.univ.filter (fun x:A=>x.val∈I);
      let Jlocal:Finset B:=Finset.univ.filter (fun u:B=>u.val∈J);
      ∀v:Ilocal,|(((G.induce (A:Set V)).induce (Ilocal:Set A)).degree v:ℝ)-
        2*(Finset.univ.filter (fun u:Jlocal=>H v.val.val u.val.val)).card|≤b):
    ∀v∈I,|((spanningRestriction G I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤b :=by
  intro v hv
  let x:A:=⟨v,hI hv⟩
  let Ilocal:Finset A:=Finset.univ.filter (fun x:A=>x.val∈I)
  have hx:x∈Ilocal:=by simp [Ilocal,x,hv]
  let y:Ilocal:=⟨x,hx⟩
  have hh:=hbal y
  have heq:=ordinary_inner_balance_induced_point_eq G H A I B J hI hJ y
  rw [heq] at hh
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
