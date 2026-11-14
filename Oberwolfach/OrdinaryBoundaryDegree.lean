module

public import Oberwolfach.BoundaryGraphDegree
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! Physical degree accounting for the final ordinary boundary stage.
The membership bound is on the same joint family of hub and row domains
used by the mixed factor-selection theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq J]

theorem ordinary_boundary_degree (Q R:SimpleGraph V) (H S:V→U→Prop)
    (X:Finset V) (Z:Finset U) (x:I↪V) (u:J↪U)
    (hx:∀ i,x i∉X) (hu:∀ j,u j∉Z)
    (hxcover:∀ a∉X,∃ i,x i=a) (hucover:∀ z∉Z,∃ j,u j=z)
    (A:I→Finset V) (B:I→Finset U) (Y:J→Finset V)
    (hQr:∀ i a,Q.Adj (x i) a↔a∈A i)
    (hHr:∀ i z,H (x i) z↔z∈B i)
    (hHc:∀ j a,H a (u j)↔a∈Y j)
    (hRQ:R≤Q) (hSH:∀ a z,S a z→H a z)
    (hremain:(Q\R).support⊆(X:Set V))
    (hcross:∀ a z,H a z∧¬S a z→a∈X∧z∈Z)
    (d k:ℕ)
    (hinner:∀ w,(spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w≤d)
    (hmem:∀ w,(Finset.univ.filter (fun i:J⊕I=>
      w∈Sum.elim (fun j=>(Y j).image (Sum.inl:V→V⊕U))
        (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr) i)).card≤k):
    ∀ w∈ordinaryInnerVertices X Z,(ordinaryPhysicalGraph R S).degree w≤d+k:=by
  let roots:J⊕I↪V⊕U:=⟨Sum.elim (fun j=>Sum.inr (u j)) (fun i=>Sum.inl (x i)),by
    intro a b h
    cases a with
    | inl a=>
      cases b with
      | inl b=>exact congrArg Sum.inl (u.injective (Sum.inr.inj h))
      | inr b=>exact (Sum.inr_ne_inl h).elim
    | inr a=>
      cases b with
      | inl b=>exact (Sum.inl_ne_inr h).elim
      | inr b=>exact congrArg Sum.inr (x.injective (Sum.inl.inj h))⟩
  let domains:J⊕I→Finset (V⊕U):=Sum.elim (fun j=>(Y j).image Sum.inl)
    (fun i=>(A i).image Sum.inl∪(B i).image Sum.inr)
  have hrow (a b:V) (ha:a∉X):R.Adj a b↔Q.Adj a b:=by
    refine ⟨fun h=>hRQ h,fun h=>?_⟩
    by_contra hn
    exact ha (hremain (show a∈(Q\R).support from ⟨b,h,hn⟩))
  have hspoke (a:V) (z:U) (h:a∉X∨z∉Z):S a z↔H a z:=by
    refine ⟨hSH a z,fun haz=>?_⟩
    by_contra hn
    have hh:=hcross a z ⟨haz,hn⟩
    exact h.elim (fun ha=>ha hh.1) (fun hz=>hz hh.2)
  have hout:∀ z∉ordinaryInnerVertices X Z,∀ v,
      (ordinaryPhysicalGraph R S).Adj z v↔∃ i,roots i=z∧v∈domains i:=by
    intro z hz v
    cases z with
    | inl a=>
      have ha:a∉X:=fun h=>hz ((ordinaryInnerVertices_left X Z a).mpr h)
      obtain ⟨i,hi⟩:=hxcover a ha
      subst a
      cases v with
      | inl b=>
        change R.Adj (x i) b↔_
        rw [hrow _ _ (hx i),hQr]
        constructor
        · intro hb;exact ⟨Sum.inr i,rfl,by simp [domains,hb]⟩
        · rintro ⟨j,hj,hb⟩
          cases j with
          | inl j=>exact (Sum.inr_ne_inl hj).elim
          | inr j=>have he:j=i:=x.injective (Sum.inl.inj hj);subst j;simpa [domains] using hb
      | inr z=>
        change S (x i) z↔_
        rw [hspoke _ _ (Or.inl (hx i)),hHr]
        constructor
        · intro hb;exact ⟨Sum.inr i,rfl,by simp [domains,hb]⟩
        · rintro ⟨j,hj,hb⟩
          cases j with
          | inl j=>exact (Sum.inr_ne_inl hj).elim
          | inr j=>have he:j=i:=x.injective (Sum.inl.inj hj);subst j;simpa [domains] using hb
    | inr z=>
      have hz':z∉Z:=fun h=>hz ((ordinaryInnerVertices_right X Z z).mpr h)
      obtain ⟨j,hj⟩:=hucover z hz'
      subst z
      cases v with
      | inl a=>
        change S a (u j)↔_
        rw [hspoke _ _ (Or.inr (hu j)),hHc]
        constructor
        · intro ha;exact ⟨Sum.inl j,rfl,by simp [domains,ha]⟩
        · rintro ⟨i,hi,ha⟩
          cases i with
          | inl i=>have he:i=j:=u.injective (Sum.inr.inj hi);subst i;simpa [domains] using ha
          | inr i=>exact (Sum.inl_ne_inr hi).elim
      | inr z=>
        change False↔_
        refine ⟨False.elim,?_⟩
        rintro ⟨i,hi,ha⟩
        cases i with
        | inl i=>simpa [domains] using ha
        | inr i=>exact Sum.inl_ne_inr hi
  intro w hw
  exact boundary_graph_degree (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z) roots domains
    hout d k hinner hmem w hw

end Oberwolfach
