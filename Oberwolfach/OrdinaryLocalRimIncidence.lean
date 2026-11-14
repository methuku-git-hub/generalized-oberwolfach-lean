module

public import Oberwolfach.PhysicalRimResourceResidual
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Rim resources incident to one vertex and a fixed protected set form
local matching tests of size at most the protected set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryLocalRimIncidence
    {V U W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq U] [DecidableEq W]
    (φ:W↪Sym2 V⊕(V×U)) (x:V) (Inner:Finset V):Finset W:=
  Finset.univ.filter (fun w=>∃y∈Inner,y≠x ∧ φ w=Sum.inl s(x,y))

theorem ordinary_local_rim_incidence_card_le
    {V U W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq U] [DecidableEq W]
    (φ:W↪Sym2 V⊕(V×U)) (x:V) (Inner:Finset V):
    (ordinaryLocalRimIncidence φ x Inner).card≤Inner.card :=by
  let f:{w:W // w∈ordinaryLocalRimIncidence φ x Inner}→{y:V // y∈Inner}:=fun w=>
    ⟨Classical.choose (Finset.mem_filter.mp w.property).2,(Classical.choose_spec (Finset.mem_filter.mp w.property).2).1⟩
  have hf:Function.Injective f:=by
    intro a b hab
    apply Subtype.ext
    apply φ.injective
    have ha:φ a.val=Sum.inl s(x,(f a).val):=(Classical.choose_spec (Finset.mem_filter.mp a.property).2).2.2
    have hb:φ b.val=Sum.inl s(x,(f b).val):=(Classical.choose_spec (Finset.mem_filter.mp b.property).2).2.2
    rw [ha,hb,congrArg Subtype.val hab]
  have hh:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hh

theorem ordinary_local_rim_residual_degree_le_uncovered
    {V U W:Type} [Fintype V] [Fintype U] [Fintype W] [DecidableEq V] [DecidableEq U] [DecidableEq W]
    (φ:W↪Sym2 V⊕(V×U)) (covered:Finset W) (x:V) (Inner:Finset V):
    (spanningRestriction (physicalRimResidualGraph φ covered) Inner).degree x≤
      (ordinaryLocalRimIncidence φ x Inner\covered).card :=by
  let G:=spanningRestriction (physicalRimResidualGraph φ covered) Inner
  let f:{y:V // G.Adj x y}→{w:W // w∈ordinaryLocalRimIncidence φ x Inner\covered}:=fun y=>
    ⟨Classical.choose ((spanningRestriction_adj (physicalRimResidualGraph φ covered) Inner x y.val).mp y.property).1.2,by
      have hy:=(spanningRestriction_adj (physicalRimResidualGraph φ covered) Inner x y.val).mp y.property
      have hw:=Classical.choose_spec hy.1.2
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨y.val,hy.2.2,Ne.symm hy.1.1,hw.2⟩⟩,hw.1⟩⟩
  have hf:Function.Injective f:=by
    intro a b hab
    have ha:=((spanningRestriction_adj (physicalRimResidualGraph φ covered) Inner x a.val).mp a.property).1
    have hb:=((spanningRestriction_adj (physicalRimResidualGraph φ covered) Inner x b.val).mp b.property).1
    have heq:φ (f a).val=φ (f b).val:=congrArg φ (congrArg Subtype.val hab)
    have hea:φ (f a).val=Sum.inl s(x,a.val):=(Classical.choose_spec ha.2).2
    have heb:φ (f b).val=Sum.inl s(x,b.val):=(Classical.choose_spec hb.2).2
    have hp:s(x,a.val)=s(x,b.val):=Sum.inl.inj (hea.symm.trans (heq.trans heb))
    rcases Sym2.eq_iff.mp hp with ⟨_,h⟩|⟨h,_⟩
    · exact Subtype.ext h
    · exact (hb.1 h).elim
  have hh:=Fintype.card_le_of_injective f hf
  have hh':Fintype.card (G.neighborSet x)≤(ordinaryLocalRimIncidence φ x Inner\covered).card:=by
    convert hh using 1 <;> congr! 4
    simp only [Fintype.card_subtype,Finset.sdiff_eq_filter]
    congr 1
    ext w
    simp
  rw [SimpleGraph.card_neighborSet_eq_degree] at hh'
  exact hh'
end Oberwolfach
