module

public import Oberwolfach.OrdinarySeedLift
public import Oberwolfach.OrdinaryLocalLoads
public import Oberwolfach.OrdinaryWheelRestriction

@[expose] public section

/-! Exact identification of a root-spoke-omitted wheel load with the local
cycle potential at its hub. The root spoke is not tested; neither the
candidate cycle family nor its coefficient function is changed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {P F:SimpleGraph V} {Hbase:V→U→Prop} {r:ℕ}

theorem ordinary_spoke_omitted_resources (W:OrdinaryWheel P F Hbase r)
    (Q:SimpleGraph V) (H:V→U→Prop) (v:V) (u:U) (hu:ordinaryWheelHub W=u):
    (∀ e∈ordinaryWheelResources W\{Sum.inr (v,u)},ordinaryResourceState Q H e=true) ↔
      ordinaryWheelRim W≤Q ∧ ∀ z∈(ordinaryWheelRim W).support,z≠v→H z u:=by
  constructor
  · intro h
    constructor
    · intro a b hab
      have hm:Sum.inl s(a,b)∈ordinaryWheelResources W\{Sum.inr (v,u)}:=by
        simp only [Finset.mem_sdiff,ordinaryWheelResources_rim,Finset.mem_singleton,Sum.inl_ne_inr,not_false_eq_true,and_true]
        exact hab
      simpa only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq,SimpleGraph.mem_edgeSet] using h _ hm
    · intro z hz hne
      have hm:Sum.inr (z,u)∈ordinaryWheelResources W\{Sum.inr (v,u)}:=by
        simp only [Finset.mem_sdiff,ordinaryWheelResources_spoke,Finset.mem_singleton,Sum.inr.injEq,Prod.mk.injEq]
        exact ⟨⟨hu,hz⟩,fun hh=>hne hh.1⟩
      simpa only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq] using h _ hm
  · rintro ⟨hQ,hH⟩ e he
    obtain ⟨he,hne⟩:=Finset.mem_sdiff.mp he
    cases e with
    | inl e=>
      have hh:=SimpleGraph.edgeSet_mono hQ ((ordinaryWheelResources_rim W e).mp he)
      simpa only [ordinaryResourceState,Sum.elim_inl,decide_eq_true_eq] using hh
    | inr zu=>
      rcases zu with ⟨z,t⟩
      obtain ⟨hh,hz⟩:=(ordinaryWheelResources_spoke W z t).mp he
      have ht:t=u:=hh.symm.trans hu
      have hv:z≠v:=by
        intro heq
        apply hne
        simpa only [Finset.mem_singleton,Sum.inr.injEq,Prod.mk.injEq] using And.intro heq ht
      simpa only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq,ht] using hH z hz hv

theorem ordinary_spoke_potential_eq_local (P Q F:SimpleGraph V) (H:V→U→Prop)
    (weight:OrdinaryCycle P r→ℝ) (D:ℝ) (v:V) (u:U):
    ordinaryPotentialLoad (ordinaryCycleWheelWeight P F r weight D) (Sum.inr (v,u)) Q H=
      ordinaryLocalPotential P Q F (Finset.univ.filter (fun z=>H z u)) (fun C=>weight C/D) v:=by
  let f:=fun (C:OrdinaryCycle P r) (a:U)=>
    if a=u then
      if v∈C.val.val.support ∧ C.val.val≤Q ∧ (∀ z∈C.val.val.support,z≠v→H z u)
        then weight C/D else 0
    else 0
  have heq:ordinaryPotentialLoad (ordinaryCycleWheelWeight P F r weight D) (Sum.inr (v,u)) Q H=
      ∑ W:OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r,f W.val.1 W.val.2:=by
    unfold ordinaryPotentialLoad
    congr 1
    · ext W
      simp only [Finset.mem_univ]
    · funext W
      by_cases hh:ordinaryWheelHub W=u
      · have he := ordinary_spoke_omitted_resources W Q H v u hh
        have hp:patternValue (ordinaryWheelResources W\{Sum.inr (v,u)}) (fun _=>true) (ordinaryResourceState Q H)=
            if ordinaryWheelRim W≤Q ∧ (∀ z∈(ordinaryWheelRim W).support,z≠v→H z u) then 1 else 0:=by
          rw [patternValue_indicator]
          by_cases hg:ordinaryWheelRim W≤Q ∧ (∀ z∈(ordinaryWheelRim W).support,z≠v→H z u)
          · have ht:=he.mpr hg
            exact (if_pos ht).trans (if_pos hg).symm
          · have ht:¬(∀ e∈ordinaryWheelResources W\{Sum.inr (v,u)},ordinaryResourceState Q H e=true):=fun ht=>hg (he.mp ht)
            exact (if_neg ht).trans (if_neg hg).symm
        calc
          _ = (if Sum.inr (v,u)∈ordinaryWheelResources W then ordinaryCycleWheelWeight P F r weight D W else 0)*
              (if ordinaryWheelRim W≤Q ∧ (∀ z∈(ordinaryWheelRim W).support,z≠v→H z u) then 1 else 0):=by
            convert congrArg (fun t=>(if Sum.inr (v,u)∈ordinaryWheelResources W then ordinaryCycleWheelWeight P F r weight D W else 0)*t) hp using 1 <;> congr!
          _ = f W.val.1 W.val.2:=by
            simp only [ordinaryWheelResources_spoke,ordinaryCycleWheelWeight,f]
            change (if ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support then weight W.val.1/D else 0)*
              (if ordinaryWheelRim W≤Q ∧ (∀ z∈(ordinaryWheelRim W).support,z≠v→H z u) then 1 else 0)=
              (if ordinaryWheelHub W=u then if v∈(ordinaryWheelRim W).support ∧ ordinaryWheelRim W≤Q ∧
                (∀ z∈(ordinaryWheelRim W).support,z≠v→H z u) then weight W.val.1/D else 0 else 0)
            split_ifs <;> simp only [zero_mul,mul_zero,mul_one] <;> tauto
      · have hroot:Sum.inr (v,u)∉ordinaryWheelResources W:=fun h=>hh ((ordinaryWheelResources_spoke W v u).mp h).1
        rw [if_neg hroot,zero_mul]
        exact (if_neg hh).symm
  rw [heq,ordinaryFullHubWheel_sum]
  unfold ordinaryLocalPotential
  apply Finset.sum_congr rfl
  intro C _
  dsimp only [f]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.mem_filter,true_and]
  split_ifs <;> first | rfl | tauto

end Oberwolfach
