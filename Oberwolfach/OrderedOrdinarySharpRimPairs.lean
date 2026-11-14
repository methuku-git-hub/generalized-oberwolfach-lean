module

public import Oberwolfach.OrderedOrdinaryRimPairBound

@[expose] public section
/-! Two vertex-disjoint directed rim requests force four distinct wheel
vertices, giving the extra inverse-order factor needed for sparse deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem ordered_ordinary_disjoint_rims_four_vertices
    (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (x y a c:V) (hdis:Disjoint ({x,y}:Finset V) {a,c}):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inl (x,y)) (Sum.inl (a,c))≤
      ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2:=by
  let P:=fun W:OrderedOrdinaryWheel (U:=U) π b (m+1)=>
    Sum.inl (x,y)∈orderedOrdinaryResources W ∧ Sum.inl (a,c)∈orderedOrdinaryResources W ∧ (a,c)≠(x,y)
  have heq:resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inl (x,y)) (Sum.inl (a,c))=
      ∑ W,if P W then w W else 0:=by
    unfold resourceOmittedPairWeight
    apply Finset.sum_congr rfl
    intro W _
    simp only [P]
    have hneq:(Sum.inl (a,c):(V×V)⊕(V×U))≠Sum.inl (x,y)↔(a,c)≠(x,y):=by
      constructor
      · intro h he;apply h;exact congrArg Sum.inl he
      · intro h he;exact h (Sum.inl.inj he)
    split_ifs <;> simp_all
  rw [heq]
  by_cases hex:∃W,P W
  · obtain ⟨W,hW⟩:=hex
    have hxy:x≠y:=(orderedOrdinary_rim_endpoints W (by omega) x y hW.1).1
    have hac:a≠c:=(orderedOrdinary_rim_endpoints W (by omega) a c hW.2.1).1
    have hxa:x≠a:=by
      intro h
      exact Finset.disjoint_left.mp hdis (show x∈({x,y}:Finset V) from by simp)
        (show x∈({a,c}:Finset V) from by simp [h])
    have hxc:x≠c:=by
      intro h
      exact Finset.disjoint_left.mp hdis (show x∈({x,y}:Finset V) from by simp)
        (show x∈({a,c}:Finset V) from by simp [h])
    have hya:y≠a:=by
      intro h
      exact Finset.disjoint_left.mp hdis (show y∈({x,y}:Finset V) from by simp)
        (show y∈({a,c}:Finset V) from by simp [h])
    have hyc:y≠c:=by
      intro h
      exact Finset.disjoint_left.mp hdis (show y∈({x,y}:Finset V) from by simp)
        (show y∈({a,c}:Finset V) from by simp [h])
    have hc:({x,y,a,c}:Finset V).card=4:=by simp [hxy,hxa,hxc,hya,hyc,hac]
    have hh:=orderedOrdinary_free_hub_event hn hu w B hB (fun W=>(hw W).2)
      {x,y,a,c} (by rw [hc];omega) (by rw [hc];omega) P (by
        intro Z hZ v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        have h1:=orderedOrdinary_rim_endpoints Z (by omega) x y hZ.1
        have h2:=orderedOrdinary_rim_endpoints Z (by omega) a c hZ.2.1
        rcases hv with rfl|rfl|rfl|rfl
        · exact h1.2.1
        · exact h1.2.2
        · exact h2.2.1
        · exact h2.2.2)
    simp only [hc,show 4-2=2 from rfl,Nat.cast_ofNat] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs <;> rfl
  · have hf:∀W,¬P W:=by simpa using hex
    simp only [hf,ite_false,Finset.sum_const_zero]
    positivity
theorem ordered_ordinary_disjoint_rims_all_lengths
    (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (x y a c:V) (hdis:Disjoint ({x,y}:Finset V) {a,c}):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inl (x,y)) (Sum.inl (a,c))≤
      ((m:ℝ)+1)^4*B/(Fintype.card V:ℝ)^2:=by
  by_cases hm3:3≤m
  · exact ordered_ordinary_disjoint_rims_four_vertices hm3 hn hu w B hB hw x y a c hdis
  · have hm2:m=2:=by omega
    subst m
    let P:=fun W:OrderedOrdinaryWheel (U:=U) π b (2+1)=>
      Sum.inl (x,y)∈orderedOrdinaryResources W ∧ Sum.inl (a,c)∈orderedOrdinaryResources W
    have hno:∀W,¬P W:=by
      intro W hW
      have hxy:x≠y:=(orderedOrdinary_rim_endpoints W (by omega) x y hW.1).1
      have hac:a≠c:=(orderedOrdinary_rim_endpoints W (by omega) a c hW.2).1
      have hxa:x≠a:=by
        intro h
        exact Finset.disjoint_left.mp hdis (show x∈({x,y}:Finset V) from by simp)
          (show x∈({a,c}:Finset V) from by simp [h])
      have hxc:x≠c:=by
        intro h
        exact Finset.disjoint_left.mp hdis (show x∈({x,y}:Finset V) from by simp)
          (show x∈({a,c}:Finset V) from by simp [h])
      have hya:y≠a:=by
        intro h
        exact Finset.disjoint_left.mp hdis (show y∈({x,y}:Finset V) from by simp)
          (show y∈({a,c}:Finset V) from by simp [h])
      have hyc:y≠c:=by
        intro h
        exact Finset.disjoint_left.mp hdis (show y∈({x,y}:Finset V) from by simp)
          (show y∈({a,c}:Finset V) from by simp [h])
      have hc:({x,y,a,c}:Finset V).card=4:=by simp [hxy,hxa,hxc,hya,hyc,hac]
      have hsub:({x,y,a,c}:Finset V)⊆Finset.univ.image W.1.val:=by
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        have h1:=orderedOrdinary_rim_endpoints W (by omega) x y hW.1
        have h2:=orderedOrdinary_rim_endpoints W (by omega) a c hW.2
        have hr:v∈Set.range W.1.val:=by
          rcases hv with rfl|rfl|rfl|rfl
          · exact h1.2.1
          · exact h1.2.2
          · exact h2.2.1
          · exact h2.2.2
        obtain ⟨i,hi⟩:=hr
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
      have hlim:(Finset.univ.image W.1.val).card≤3:=(Finset.card_image_le).trans (by simp)
      have hh:=Finset.card_le_card hsub
      omega
    have heq:resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inl (x,y)) (Sum.inl (a,c))=0:=by
      unfold resourceOmittedPairWeight
      apply Finset.sum_eq_zero
      intro W _
      have hh:=hno W
      simp only [P,not_and] at hh
      by_cases h1:Sum.inl (x,y)∈orderedOrdinaryResources W
      · have h2:=hh h1
        simp [h2]
      · simp [h1]
    rw [heq]
    positivity
end Oberwolfach
