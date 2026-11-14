module

public import Oberwolfach.RawOrdinaryPatternSampling
public import Oberwolfach.EndpointIndexDeletion

@[expose] public section

/-! The index potential omits xu, and tests three rims and the two other
spokes. Its candidates are unordered eligible edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def endpointIndexResources (x:V) (u:U) (e:Sym2 V):Finset (Sym2 V⊕(V×U)):=
  insert (Sum.inl e) (e.toFinset.image (fun v=>Sum.inl s(x,v)) ∪
    e.toFinset.image (fun v=>Sum.inr (v,u)))

theorem endpointIndexResources_rim (x:V) (u:U) (e f:Sym2 V):
    Sum.inl f∈endpointIndexResources x u e ↔ f=e ∨ ∃ v∈e,f=s(x,v):=by
  simp [endpointIndexResources,eq_comm]

theorem endpointIndexResources_spoke (x a:V) (u t:U) (e:Sym2 V):
    Sum.inr (a,t)∈endpointIndexResources x u e ↔ t=u∧a∈e:=by
  simp [endpointIndexResources,eq_comm,and_comm]

theorem endpointIndexResources_card (x:V) (u:U) (e:Sym2 V):
    (endpointIndexResources x u e).card≤5:=by
  have he:e.toFinset.card≤2:=by rw [Sym2.card_toFinset];split_ifs <;> omega
  have hi:=Finset.card_insert_le (Sum.inl e)
    (e.toFinset.image (fun v=>Sum.inl (β:=V×U) s(x,v)) ∪ e.toFinset.image (fun v=>Sum.inr (α:=Sym2 V) (v,u)))
  have hu:=Finset.card_union_le (e.toFinset.image (fun v=>Sum.inl (β:=V×U) s(x,v)))
    (e.toFinset.image (fun v=>Sum.inr (α:=Sym2 V) (v,u)))
  have h₁:=Finset.card_image_le (s:=e.toFinset) (f:=fun v=>Sum.inl (β:=V×U) s(x,v))
  have h₂:=Finset.card_image_le (s:=e.toFinset) (f:=fun v=>Sum.inr (α:=Sym2 V) (v,u))
  change (endpointIndexResources x u e).card≤_ at hi
  omega

theorem endpointIndexResources_disjoint (π:Equiv.Perm V) (d:ℕ) (F:SimpleGraph V)
    (hF:permutationConflictGraph π (3*d)≤F) (x:V) (u:U) (e:Sym2 V)
    (hsep:∀ v∈e,∀ w∈e,¬F.Adj v w)
    (a b:Sym2 V⊕(V×U)) (ha:a∈endpointIndexResources x u e)
    (hb:b∈endpointIndexResources x u e) (hne:a≠b):
    Disjoint (rawWheelResourceCoordinates π d a) (rawWheelResourceCoordinates π d b):=by
  apply rawWheelResourceCoordinates_disjoint π d a b hne
  intro v s w t he hf
  subst a;subst b
  obtain ⟨hs,hv⟩:=(endpointIndexResources_spoke x v u s e).mp ha
  obtain ⟨ht,hw⟩:=(endpointIndexResources_spoke x w u t e).mp hb
  right
  intro hclose
  have hvw:v≠w:=by
    intro hh
    exact hne (congrArg Sum.inr (Prod.ext hh (hs.trans ht.symm)))
  exact hsep v hv w hw (hF ⟨hvw,hclose⟩)

theorem endpointIndexResources_target {Color:Type} (P:SimpleGraph V)
    (s:U→Color→ℝ) (j:Color) (pR pH:ℝ) (x v w:V) (u:U)
    (hxv:P.Adj x v) (hxw:P.Adj x w) (hvw:P.Adj v w) (hu:s u j=pH):
    (∏ e∈endpointIndexResources x u s(v,w),rawWheelMarginal P (fun _=>pR) s j e)=pR^3*pH^2:=by
  have hxv':x≠v:=hxv.ne
  have hxw':x≠w:=hxw.ne
  have hvw':v≠w:=hvw.ne
  have he₁:s(v,w)≠s(x,v):=by simp only [ne_eq,Sym2.eq_iff];tauto
  have he₂:s(v,w)≠s(x,w):=by simp only [ne_eq,Sym2.eq_iff];tauto
  have he₃:s(x,v)≠s(x,w):=by simp only [ne_eq,Sym2.eq_iff];tauto
  simp [endpointIndexResources,Sym2.toFinset_mk_eq,rawWheelMarginal,hxv,hxw,hvw,hu,
    he₁,he₂,he₃,hvw',pow_succ,mul_assoc,mul_comm,mul_left_comm]

theorem endpointIndexResources_value (R:SimpleGraph V) (H:V→U→Prop) (x:V) (u:U) (e:Sym2 V):
    patternValue (endpointIndexResources x u e) (fun _=>true) (ordinaryResourceState R H)=
      if e∈R.edgeSet ∧ ∀ v∈e,R.Adj x v ∧ H v u then (1:ℝ) else 0:=by
  rw [patternValue_indicator]
  congr 1
  apply propext
  simp only [endpointIndexResources,Finset.forall_mem_insert,Finset.forall_mem_union,
    Finset.forall_mem_image,Sym2.mem_toFinset,ordinaryResourceState,Sum.elim_inl,Sum.elim_inr,
    decide_eq_true_eq,SimpleGraph.mem_edgeSet]
  simp only [forall_and]

end Oberwolfach
