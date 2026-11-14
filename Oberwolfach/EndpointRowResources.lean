module

public import Oberwolfach.RawOrdinaryPatternSampling
public import Oberwolfach.EndpointMatchingMass

@[expose] public section

/-! The five physical resources in an endpoint row potential. The tested
rim edge xv is omitted, while the two other rims and all three spokes
retain the original raw sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def endpointRowResources (x v w:V) (u:U):Finset (Sym2 V⊕(V×U)):=
  ({x,v}:Finset V).image (fun a=>Sum.inl s(a,w)) ∪
    ({x,v,w}:Finset V).image (fun a=>Sum.inr (a,u))

theorem endpointRowResources_rim (x v w:V) (u:U) (e:Sym2 V):
    Sum.inl e∈endpointRowResources x v w u ↔ e=s(x,w)∨e=s(v,w):=by
  simp [endpointRowResources,eq_comm]

theorem endpointRowResources_spoke (x v w a:V) (u t:U):
    Sum.inr (a,t)∈endpointRowResources x v w u ↔ t=u∧a∈({x,v,w}:Finset V):=by
  simp [endpointRowResources,eq_comm,and_comm,and_or_left]

theorem endpointRowResources_card (x v w:V) (u:U):
    (endpointRowResources x v w u).card≤5:=by
  have h:=Finset.card_union_le
    (({x,v}:Finset V).image (fun a=>Sum.inl (β:=V×U) s(a,w)))
    (({x,v,w}:Finset V).image (fun a=>Sum.inr (α:=Sym2 V) (a,u)))
  have h₁:=Finset.card_image_le (s:=({x,v}:Finset V)) (f:=fun a=>Sum.inl (β:=V×U) s(a,w))
  have h₂:=Finset.card_image_le (s:=({x,v,w}:Finset V)) (f:=fun a=>Sum.inr (α:=Sym2 V) (a,u))
  have h₃:({x,v,w}:Finset V).card≤3:=(Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_le_two 1)
  change _≤5
  change (endpointRowResources x v w u).card≤_ at h
  have h₀:({x,v}:Finset V).card≤2:=Finset.card_le_two
  omega

theorem endpointRowResources_disjoint (π:Equiv.Perm V) (d:ℕ) (F:SimpleGraph V)
    (hF:permutationConflictGraph π (3*d)≤F) (x v w:V) (u:U)
    (hsep:∀ a∈({x,v,w}:Finset V),∀ b∈({x,v,w}:Finset V),¬F.Adj a b)
    (a b:Sym2 V⊕(V×U)) (ha:a∈endpointRowResources x v w u)
    (hb:b∈endpointRowResources x v w u) (hne:a≠b):
    Disjoint (rawWheelResourceCoordinates π d a) (rawWheelResourceCoordinates π d b):=by
  apply rawWheelResourceCoordinates_disjoint π d a b hne
  intro z s y t he hf
  subst a;subst b
  obtain ⟨hs,hz⟩:=(endpointRowResources_spoke x v w z u s).mp ha
  obtain ⟨ht,hy⟩:=(endpointRowResources_spoke x v w y u t).mp hb
  right
  intro hclose
  have hzy:z≠y:=by
    intro he
    exact hne (congrArg Sum.inr (Prod.ext he (hs.trans ht.symm)))
  exact hsep z hz y hy (hF ⟨hzy,hclose⟩)

theorem endpointRowResources_target {Color:Type} (P:SimpleGraph V)
    (s:U→Color→ℝ) (j:Color) (pR pH:ℝ) (x v w:V) (u:U)
    (hxv:x≠v) (hxw:x≠w) (hvw:v≠w) (hPxw:P.Adj x w) (hPvw:P.Adj v w) (hu:s u j=pH):
    (∏ e∈endpointRowResources x v w u,rawWheelMarginal P (fun _=>pR) s j e)=pR^2*pH^3:=by
  have hdis:Disjoint (({x,v}:Finset V).image (fun a=>Sum.inl (β:=V×U) s(a,w)))
      (({x,v,w}:Finset V).image (fun a=>Sum.inr (α:=Sym2 V) (a,u))):=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨b,_,hh⟩:=Finset.mem_image.mp hf
    cases hh
  unfold endpointRowResources
  rw [Finset.prod_union hdis]
  rw [Finset.prod_image (by
    intro a ha b hb he
    rcases Sym2.eq_iff.mp (Sum.inl.inj he) with h|h
    · exact h.1
    · exact h.1.trans h.2)]
  rw [Finset.prod_image (by intro a ha b hb he;exact (Prod.mk.inj (Sum.inr.inj he)).1)]
  have hr (a:V) (ha:a∈({x,v}:Finset V)):
      rawWheelMarginal P (fun _=>pR) s j (Sum.inl s(a,w))=pR:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> simp [rawWheelMarginal,hPxw,hPvw]
  rw [Finset.prod_congr rfl hr]
  simp [rawWheelMarginal,hu,hxv,hxw,hvw,pow_succ,mul_assoc]

abbrev EndpointRowCandidates (E:SimpleGraph V) (A:Finset V) (B:Finset U) (v:V):=
  {p:U×V//p.1∈B∧p.2∈A∧E.Adj v p.2}

theorem endpointRowCandidates_card (E:SimpleGraph V) (A:Finset V) (B:Finset U) (v:V):
    Fintype.card (EndpointRowCandidates E A B v)≤B.card*A.card:=by
  let f:EndpointRowCandidates E A B v→↥(B.product A):=fun p=>⟨p.val,Finset.mem_product.mpr ⟨p.property.1,p.property.2.1⟩⟩
  have hf:Function.Injective f:=by intro a b he;exact Subtype.ext (congrArg (fun z:↥(B.product A)=>z.val) he)
  have hh:=Fintype.card_le_of_injective f hf
  have he:Fintype.card ↥(B.product A)=B.card*A.card:=by
    rw [Fintype.card_coe]
    exact Finset.card_product B A
  exact hh.trans_eq he

theorem endpointRowCandidates_incidence (E:SimpleGraph V) (A:Finset V) (B:Finset U) (x v:V)
    (e:Sym2 V⊕(V×U)):
    (Finset.univ.filter (fun p:EndpointRowCandidates E A B v=>e∈endpointRowResources x v p.val.2 p.val.1)).card≤2*B.card+A.card:=by
  rw [←Fintype.card_subtype]
  let I:={p:EndpointRowCandidates E A B v//e∈endpointRowResources x v p.val.2 p.val.1}
  change Fintype.card I≤_
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ a b=>
      have hw (p:I):p.val.val.2∈({a,b}:Finset V):=by
        rcases (endpointRowResources_rim x v p.val.val.2 p.val.val.1 s(a,b)).mp p.property with he|he
        all_goals
          rcases Sym2.eq_iff.mp he with hh|hh
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hh.2.symm)
          · exact Finset.mem_insert.mpr (Or.inl hh.1.symm)
      let f:I→↥(B.product ({a,b}:Finset V)):=fun p=>⟨p.val.val,Finset.mem_product.mpr ⟨p.val.property.1,hw p⟩⟩
      have hf:Function.Injective f:=by intro p q he;exact Subtype.ext (Subtype.ext (congrArg (fun z:↥(B.product ({a,b}:Finset V))=>z.val) he))
      have hc:=Fintype.card_le_of_injective f hf
      have hprod:Fintype.card ↥(B.product ({a,b}:Finset V))=B.card*({a,b}:Finset V).card:=by
        rw [Fintype.card_coe]
        exact Finset.card_product B {a,b}
      rw [hprod] at hc
      have htwo:({a,b}:Finset V).card≤2:=Finset.card_le_two
      nlinarith only [hc,Nat.mul_le_mul_left B.card htwo]
  | inr av=>
    let f:I→A:=fun p=>⟨p.val.val.2,p.val.property.2.1⟩
    have hf:Function.Injective f:=by
      intro p q he
      have hp:=(endpointRowResources_spoke x v p.val.val.2 av.1 p.val.val.1 av.2).mp p.property
      have hq:=(endpointRowResources_spoke x v q.val.val.2 av.1 q.val.val.1 av.2).mp q.property
      exact Subtype.ext (Subtype.ext (Prod.ext (hp.1.symm.trans hq.1) (congrArg Subtype.val he)))
    have hc:=Fintype.card_le_of_injective f hf
    have hc':Fintype.card I≤A.card:=by simpa only [Fintype.card_coe] using hc
    exact hc'.trans (Nat.le_add_left A.card (2*B.card))

end Oberwolfach
