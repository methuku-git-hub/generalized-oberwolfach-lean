module

public import Oberwolfach.OrdinaryTransformerOldSpokes

@[expose] public section

/-! The hub-switch domains are indexed only by hubs incident with an
original spoke. Inactive hubs contribute zero to the exact identity.
No injectivity of the image map on hubs is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 def transformerSpokeRows (Q:SimpleGraph V) (H₀:V→U→Prop)
    (p:{e:V×U // H₀ e.1 e.2}→(Σ a:V,Σ c:V,Q.Walk a c)) (u:U):Finset V:=
    (Finset.univ.filter (fun i=>i.val.2=u)).biUnion (fun i=>(p i).2.2.support.toFinset)

 theorem transformerSpokeRows_mem (Q:SimpleGraph V) (H₀:V→U→Prop)
    (p:{e:V×U // H₀ e.1 e.2}→(Σ a:V,Σ c:V,Q.Walk a c)) (u:U) (v:V):
    v∈transformerSpokeRows Q H₀ p u↔∃ i:{e:V×U // H₀ e.1 e.2},i.val.2=u∧v∈(p i).2.2.support:=by
  simp only [transformerSpokeRows,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]

 theorem transformerSpokeRows_empty (Q:SimpleGraph V) (H₀:V→U→Prop)
    (p:{e:V×U // H₀ e.1 e.2}→(Σ a:V,Σ c:V,Q.Walk a c)) (u:U) (hu:¬∃ v,H₀ v u):
    transformerSpokeRows Q H₀ p u=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨i,hi,_⟩:=(transformerSpokeRows_mem Q H₀ p u v).mp hv
  exact hu ⟨i.val.1,hi ▸ i.property⟩

 theorem transformerSpokeRows_active_sum (Q:SimpleGraph V) (H₀:V→U→Prop) (ψ:U→U)
    (p:{e:V×U // H₀ e.1 e.2}→(Σ a:V,Σ c:V,Q.Walk a c)) (e:Sym2 V⊕(V×U)):
    (∑ u:U,((if e∈(transformerSpokeRows Q H₀ p u).image (fun v=>Sum.inr (v,u)) then (1:ℤ) else 0)-
      (if e∈(transformerSpokeRows Q H₀ p u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)))=
    ∑ i:{u:U // ∃ v,H₀ v u},((if e∈(transformerSpokeRows Q H₀ p i.val).image (fun v=>Sum.inr (v,i.val)) then (1:ℤ) else 0)-
      (if e∈(transformerSpokeRows Q H₀ p i.val).image (fun v=>Sum.inr (v,ψ i.val)) then 1 else 0)):=by
  let f:U→ℤ:=fun u=>(if e∈(transformerSpokeRows Q H₀ p u).image (fun v=>Sum.inr (v,u)) then 1 else 0)-
    (if e∈(transformerSpokeRows Q H₀ p u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)
  have hz:∑ u:{u:U // ¬∃ v,H₀ v u},f u.val=0:=by
    apply Finset.sum_eq_zero
    intro u _
    simp only [f,transformerSpokeRows_empty Q H₀ p u.val u.property,Finset.image_empty,
      Finset.notMem_empty,ite_false,sub_self]
  have hh:=Fintype.sum_subtype_add_sum_subtype (fun u=>∃ v,H₀ v u) f
  rw [hz,add_zero] at hh
  exact hh.symm

 theorem ordinary_transformer_hub_trade_spoke_avoidance
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U) (r:ℕ)
    (R:Finset V) (B:Finset U)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hpR:∀ i,∀ v∈(p i).2.2.support,v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hB:∀ i:{e:V×U // H₀ e.1 e.2},i.val.2∈B∧ψ i.val.2∈B)
    (hu:∀ u,(∃ v,H₀ v u)→u≠ψ u)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d)):
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
    ∀ u,∀ v∈transformerSpokeRows Q H₀ (fun i=>p (.inr i)) u,
      ¬wheelFamilySpokes Plus v (ψ u)∧¬wheelFamilySpokes Minus v u:=by
  dsimp only
  intro u v hv
  obtain ⟨i,hi,hvi⟩:=(transformerSpokeRows_mem Q H₀ _ u v).mp hv
  have hiu:∃ w,H₀ w u:=⟨i.val.1,hi ▸ i.property⟩
  have hz₀:u∈B:=hi ▸ (hB i).1
  have hz₁:ψ u∈B:=by simpa only [hi] using (hB i).2
  have hh:=ordinary_transformer_old_spokes G Q F H₀ H φ ψ r R B b σ p
    hbalance hroot hpR hdis E S D i v hvi
  constructor
  · intro hvu
    have he:ψ u=u:=((hh (ψ u) hz₁).1.mp hvu).trans hi
    exact hu u hiu he.symm
  · intro hvu
    have he:u=ψ u:=((hh u hz₀).2.mp hvu).trans (congrArg ψ hi)
    exact hu u hiu he

end Oberwolfach
