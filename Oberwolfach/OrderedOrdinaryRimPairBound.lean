module

public import Oberwolfach.OrderedOrdinaryRootGeometry
public import Oberwolfach.OrderedOrdinaryEventScales
public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section
/-! Two different directed rim requests force three distinct vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_rim_pair_bound (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (x y a c:V):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inl (x,y)) (Sum.inl (a,c))≤
      ((m:ℝ)+1)^3*B/(Fintype.card V:ℝ):=by
  let P:=fun W:OrderedOrdinaryWheel (U:=U) π b (m+1)=>
    Sum.inl (x,y)∈orderedOrdinaryResources W ∧ Sum.inl (a,c)∈orderedOrdinaryResources W ∧ (a,c)≠(x,y)
  have heq:resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inl (x,y)) (Sum.inl (a,c))=
      ∑ W,if P W then w W else 0:=by
    unfold resourceOmittedPairWeight
    apply Finset.sum_congr rfl
    intro W _
    simp only [P]
    have hneq : (Sum.inl (a,c) : (V×V)⊕(V×U)) ≠ Sum.inl (x,y) ↔ (a,c) ≠ (x,y) := by
      constructor
      · intro h he; apply h; exact congrArg Sum.inl he
      · intro h he; exact h (Sum.inl.inj he)
    split_ifs <;> simp_all
  rw [heq]
  by_cases hex:∃ W,P W
  · obtain ⟨W,hW⟩:=hex
    have hne:(x,y)≠(a,c):=Ne.symm hW.2.2
    have hc:=orderedOrdinary_two_rims_three_vertices W (by omega) x y a c hW.1 hW.2.1 hne
    obtain ⟨S,hsub,hcard⟩:=Finset.exists_subset_card_eq hc
    have hh:=orderedOrdinary_free_hub_event hn hu w B hB (fun W=>(hw W).2) S (by omega) (by omega) P (by
      intro Z hZ v hv
      have hv':v∈({x,y,a,c}:Finset V):=hsub hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
      have h1:=orderedOrdinary_rim_endpoints Z (by omega) x y hZ.1
      have h2:=orderedOrdinary_rim_endpoints Z (by omega) a c hZ.2.1
      rcases hv' with rfl|rfl|rfl|rfl
      · exact h1.2.1
      · exact h1.2.2
      · exact h2.2.1
      · exact h2.2.2)
    simp only [hcard,show 3-2=1 from rfl,pow_one] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs <;> rfl
  · have hf:∀ W,¬P W:=by simpa using hex
    simp only [hf,ite_false,Finset.sum_const_zero]
    positivity
end Oberwolfach
