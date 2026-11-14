module

public import Oberwolfach.OrdinaryMixedIdealTarget

@[expose] public section
/-! Normalize the ideal targets over a physical fiber when its categorical
state selects the indicated spoke or rim representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U:Type} [Fintype I] [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_mixed_active_spoke_fiber_target
    (π:Equiv.Perm V) (m D p:ℝ) (a b:U→ℝ) (η:I→U→ℝ)
    (σ:OrdinaryTypedResource V U→Bool) (x:V) (u:U)
    (hb:0<b u) (hbal:m*a u+(∑i,η i u)*b u=b u)
    (hactive:σ (Sum.inr (false,x,u))=true ∨ σ (Sum.inr (true,x,u))=true)
    (hdis:¬(σ (Sum.inr (false,x,u))=true ∧ σ (Sum.inr (true,x,u))=true)):
    ∑z∈Finset.univ.filter (fun z=>ordinaryMixedPhysicalResource π z=Sum.inr (x,u) ∧ σ z=true),
      ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z=1 :=by
  have hfilter:(∑z∈Finset.univ.filter (fun z=>ordinaryMixedPhysicalResource π z=Sum.inr (x,u) ∧ σ z=true),
      ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z)=
      ∑z∈Finset.univ.filter (fun z=>ordinaryMixedPhysicalResource π z=Sum.inr (x,u)),
        if σ z=true then ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z else 0 :=by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases he:ordinaryMixedPhysicalResource π z=Sum.inr (x,u) <;> by_cases hs:σ z=true <;> simp [he,hs]
  rw [hfilter,ordinary_physical_spoke_fiber_sum]
  rcases hactive with hzero|hone
  · have hn:σ (Sum.inr (true,x,u))≠true:=fun h=>hdis ⟨hzero,h⟩
    simp only [hzero,hn,Bool.false_eq_true,ite_true,ite_false,add_zero]
    exact ordinary_mixed_ideal_ordinary_spoke m D p a b η u x hb hbal
  · have hn:σ (Sum.inr (false,x,u))≠true:=fun h=>hdis ⟨h,hone⟩
    simp only [hn,hone,Bool.false_eq_true,ite_true,ite_false,zero_add]
    exact ordinary_mixed_ideal_interval_spoke m D p a b η u x

theorem ordinary_mixed_active_rim_fiber_target
    (π:Equiv.Perm V) (m D p:ℝ) (hD:0<D) (hp:0<p)
    (a b:U→ℝ) (η:I→U→ℝ) (hb:∀u,0<b u)
    (hbal:∀u,m*a u+(∑i,η i u)*b u=b u) (hpdef:(∑u,(a u+b u))=D*p)
    (σ:OrdinaryTypedResource V U→Bool) (x y:V) (hxy:x≠y)
    (h₁:σ (Sum.inl (Sum.inl (x,y)))=true)
    (h₂:σ (Sum.inl (Sum.inl (y,x)))=false)
    (h₃:σ (Sum.inl (Sum.inr (x,π.symm y)))=true)
    (h₄:σ (Sum.inl (Sum.inr (y,π.symm x)))=false):
    ∑z∈Finset.univ.filter (fun z=>ordinaryMixedPhysicalResource π z=Sum.inl s(x,y) ∧ σ z=true),
      ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z=1 :=by
  have hfilter:(∑z∈Finset.univ.filter (fun z=>ordinaryMixedPhysicalResource π z=Sum.inl s(x,y) ∧ σ z=true),
      ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z)=
      ∑z∈Finset.univ.filter (fun z=>ordinaryMixedPhysicalResource π z=Sum.inl s(x,y)),
        if σ z=true then ∑i:Option I,ordinaryMixedIdealTarget m D p a b η i z else 0 :=by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases he:ordinaryMixedPhysicalResource π z=Sum.inl s(x,y) <;> by_cases hs:σ z=true <;> simp [he,hs]
  rw [hfilter,ordinary_physical_rim_fiber_sum π x y hxy]
  simp only [h₁,h₂,h₃,h₄,Bool.false_eq_true,if_true,if_false,add_zero]
  exact ordinary_mixed_ideal_rim_two_representations m D p hD hp a b η hb hbal hpdef x y (π.symm y)
end Oberwolfach
