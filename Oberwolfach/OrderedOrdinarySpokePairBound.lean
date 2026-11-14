module

public import Oberwolfach.OrderedOrdinaryRootGeometry
public import Oberwolfach.OrderedOrdinaryEventScales
public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section
/-! A spoke root fixes the hub; a second distinct request fixes at least
one further vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_spoke_rim_pair_bound (hm:2≤m) (hn:0<Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (v:V) (u:U) (x y:V):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inl (x,y))≤
      ((m:ℝ)+1)^2*B/(Fintype.card V:ℝ):=by
  let P:=fun W:OrderedOrdinaryWheel (U:=U) π b (m+1)=>
    Sum.inr (v,u)∈orderedOrdinaryResources W ∧ Sum.inl (x,y)∈orderedOrdinaryResources W
  have heq:resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inl (x,y))=
      ∑ W,if P W then w W else 0:=by
    unfold resourceOmittedPairWeight
    apply Finset.sum_congr rfl
    intro W _
    simp [P]
  rw [heq]
  by_cases hex:∃ W,P W
  · obtain ⟨W,hW⟩:=hex
    have hne:x≠y:=(orderedOrdinary_rim_endpoints W (by omega) x y hW.2).1
    have hc:({x,y}:Finset V).card=2:=by simp [hne]
    have hh:=orderedOrdinary_fixed_hub_event hn w B hB (fun W=>(hw W).2) {x,y} (by omega) (by omega) u P (by
      intro Z hZ
      have h1:=orderedOrdinary_spoke_endpoint Z v u hZ.1
      have h2:=orderedOrdinary_rim_endpoints Z (by omega) x y hZ.2
      refine ⟨?_,h1.2⟩
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl
      · exact h2.2.1
      · exact h2.2.2)
    simp only [hc,show 2-1=1 from rfl,pow_one] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs <;> rfl
  · have hf:∀ W,¬P W:=by simpa using hex
    simp only [hf,ite_false,Finset.sum_const_zero]
    positivity

theorem orderedOrdinary_spoke_spoke_pair_bound (hm:2≤m) (hn:0<Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (v x:V) (u t:U):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inr (x,t))≤
      ((m:ℝ)+1)^2*B/(Fintype.card V:ℝ):=by
  let P:=fun W:OrderedOrdinaryWheel (U:=U) π b (m+1)=>
    Sum.inr (v,u)∈orderedOrdinaryResources W ∧ Sum.inr (x,t)∈orderedOrdinaryResources W ∧ (x,t)≠(v,u)
  have heq:resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inr (x,t))=
      ∑ W,if P W then w W else 0:=by
    unfold resourceOmittedPairWeight
    apply Finset.sum_congr rfl
    intro W _
    simp only [P]
    have hneq : (Sum.inr (x,t) : (V×V)⊕(V×U)) ≠ Sum.inr (v,u) ↔ (x,t) ≠ (v,u) := by
      constructor
      · intro h he; apply h; exact congrArg Sum.inr he
      · intro h he; exact h (Sum.inr.inj he)
    split_ifs <;> simp_all
  rw [heq]
  by_cases hex:∃ W,P W
  · obtain ⟨W,hW⟩:=hex
    have h1:=orderedOrdinary_spoke_endpoint W v u hW.1
    have h2:=orderedOrdinary_spoke_endpoint W x t hW.2.1
    have hu:u=t:=h1.2.symm.trans h2.2
    have hv:v≠x:=by
      intro h
      apply hW.2.2
      exact Prod.ext h.symm hu.symm
    have hc:({v,x}:Finset V).card=2:=by simp [hv]
    have hh:=orderedOrdinary_fixed_hub_event hn w B hB (fun W=>(hw W).2) {v,x} (by omega) (by omega) u P (by
      intro Z hZ
      have ha:=orderedOrdinary_spoke_endpoint Z v u hZ.1
      have hb:=orderedOrdinary_spoke_endpoint Z x t hZ.2.1
      refine ⟨?_,ha.2⟩
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl
      · exact ha.1
      · exact hb.1)
    simp only [hc,show 2-1=1 from rfl,pow_one] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs <;> rfl
  · have hf:∀ W,¬P W:=by simpa using hex
    simp only [hf,ite_false,Finset.sum_const_zero]
    positivity
end Oberwolfach
