module

public import Oberwolfach.OrdinaryMixedIdealNormalization
public import Oberwolfach.OrdinaryPhysicalFiberSums

@[expose] public section
/-! Ideal typed root targets for the ordinary shifted and unshifted seed
families, before imposing the common physical-state event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U:Type} [Fintype I] [Fintype U]

def ordinaryMixedIdealTarget (m D p:ℝ) (a b:U→ℝ) (η:I→U→ℝ):
    Option I→OrdinaryTypedResource V U→ℝ
  | none,Sum.inl (Sum.inl _) => m*(∑u,a u)/(D*p)
  | none,Sum.inl (Sum.inr _) => (∑u,a u)/(D*p)
  | some i,Sum.inl (Sum.inl _) => (∑u,η i u*b u)/(D*p)
  | some _,Sum.inl (Sum.inr _) => 0
  | none,Sum.inr (false,_,u) => m*a u/b u
  | some i,Sum.inr (false,_,u) => η i u
  | none,Sum.inr (true,_,_) => 1
  | some _,Sum.inr (true,_,_) => 0

theorem ordinary_mixed_ideal_ordinary_spoke
    (m D p:ℝ) (a b:U→ℝ) (η:I→U→ℝ) (u:U) (v:V)
    (hb:0<b u) (hbal:m*a u+(∑i,η i u)*b u=b u):
    (∑i:Option I,ordinaryMixedIdealTarget m D p a b η i (Sum.inr (false,v,u)))=1 :=by
  simp only [Fintype.sum_option,ordinaryMixedIdealTarget]
  field_simp [ne_of_gt hb]
  nlinarith

theorem ordinary_mixed_ideal_interval_spoke
    (m D p:ℝ) (a b:U→ℝ) (η:I→U→ℝ) (u:U) (v:V):
    (∑i:Option I,ordinaryMixedIdealTarget m D p a b η i (Sum.inr (true,v,u)))=1 :=by
  simp [Fintype.sum_option,ordinaryMixedIdealTarget]

theorem ordinary_mixed_ideal_rim_two_representations
    (m D p:ℝ) (hD:0<D) (hp:0<p) (a b:U→ℝ) (η:I→U→ℝ)
    (hb:∀u,0<b u) (hbal:∀u,m*a u+(∑i,η i u)*b u=b u)
    (hpdef:(∑u,(a u+b u))=D*p) (x y z:V):
    (∑i:Option I,ordinaryMixedIdealTarget m D p a b η i (Sum.inl (Sum.inl (x,y))))+
    (∑i:Option I,ordinaryMixedIdealTarget m D p a b η i (Sum.inl (Sum.inr (x,z))))=1 :=by
  have hh:=(ordinary_mixed_ideal_normalization m D p hD hp a b η hb hbal hpdef).2
  simp only [Fintype.sum_option,ordinaryMixedIdealTarget,Finset.sum_const_zero,add_zero,←Finset.sum_div]
  have heq:m*(∑u,a u)/(D*p)+(∑i,∑u,η i u*b u)/(D*p)+
      (∑u,a u)/(D*p)=(m+1)*(∑u,a u)/(D*p)+(∑i,∑u,η i u*b u)/(D*p):=by ring
  rw [heq]
  exact hh
end Oberwolfach
