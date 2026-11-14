module

public import Oberwolfach.OrderedOrdinaryRootGeometry
public import Oberwolfach.OrderedOrdinaryEventScales

@[expose] public section
/-! Uniform potential load bound for ordered ordinary cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_root_load_bound (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (e:(V×V)⊕(V×U)):
    (∑ W,if e∈orderedOrdinaryResources W then w W else 0)≤((m:ℝ)+1)^2*B:=by
  cases e with
  | inl e=>
    obtain ⟨x,y⟩:=e
    by_cases hex:∃ W:OrderedOrdinaryWheel (U:=U) π b (m+1),Sum.inl (x,y)∈orderedOrdinaryResources W
    · obtain ⟨W,hW⟩:=hex
      have hne: x≠y:=(orderedOrdinary_rim_endpoints W (by omega) x y hW).1
      have hc:({x,y}:Finset V).card=2:=by simp [hne]
      have hh:=orderedOrdinary_free_hub_event hn hu w B hB (fun W=>(hw W).2) {x,y} (by omega) (by omega)
        (fun W=>Sum.inl (x,y)∈orderedOrdinaryResources W) (by
          intro Z hZ v hv
          have h:=orderedOrdinary_rim_endpoints Z (by omega) x y hZ
          simp only [Finset.mem_insert,Finset.mem_singleton] at hv
          rcases hv with rfl|rfl
          · exact h.2.1
          · exact h.2.2)
      simp only [hc,show 2-2=0 from rfl,pow_zero,div_one] at hh
      convert hh using 1
      apply Finset.sum_congr rfl
      intro W _
      split_ifs <;> rfl
    · have hf:∀ W:OrderedOrdinaryWheel (U:=U) π b (m+1),Sum.inl (x,y)∉orderedOrdinaryResources W:=by simpa using hex
      simp only [hf,ite_false,Finset.sum_const_zero]
      positivity
  | inr e=>
    obtain ⟨v,u⟩:=e
    have hh:=orderedOrdinary_fixed_hub_event hn w B hB (fun W=>(hw W).2) {v} (by simp) (by simp) u
      (fun W=>Sum.inr (v,u)∈orderedOrdinaryResources W) (by
        intro W hW
        have h:=orderedOrdinary_spoke_endpoint W v u hW
        refine ⟨?_,h.2⟩
        intro x hx
        have hx':x=v:=Finset.mem_singleton.mp hx
        exact hx' ▸ h.1)
    simp only [Finset.card_singleton,pow_one,show 1-1=0 from rfl,pow_zero,div_one] at hh
    have hm0:(0:ℝ)≤m:=Nat.cast_nonneg _
    convert hh.trans (mul_le_mul_of_nonneg_right (by nlinarith : (m:ℝ)+1≤((m:ℝ)+1)^2) hB) using 1
    apply Finset.sum_congr rfl
    intro W _
    split_ifs <;> rfl
end Oberwolfach
