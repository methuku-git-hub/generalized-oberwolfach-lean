module

public import Oberwolfach.TransformerOriginalEdgeIdentity
public import Oberwolfach.DirectedIncidenceSums

@[expose] public section

/-! Group the exact free-spoke load by the original hub. Distinct private
path labels preserve multiplicity even when the map on old hubs identifies
vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U S:Type} [Fintype S] [Fintype U] [DecidableEq S] [DecidableEq V] [DecidableEq U]

 theorem disjoint_paths_joint_injective (m:ℕ) (p:S→(Fin m↪V))
    (hdis:∀ s t,s≠t→Disjoint (Finset.univ.image (p s)) (Finset.univ.image (p t))):
    Function.Injective (fun x:S×Fin m=>p x.1 x.2):=by
  rintro ⟨s,k⟩ ⟨t,l⟩ he
  have hst:s=t:=by
    by_contra hn
    exact Finset.disjoint_left.mp (hdis s t hn)
      (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
      (Finset.mem_image.mpr ⟨l,Finset.mem_univ _,he.symm⟩)
  subst t
  exact Prod.ext rfl ((p s).injective he)

 def spokePathHubVertices (m:ℕ) (p:S→(Fin m↪V)) (hub:S→U) (u:U):Finset V:=
    Finset.univ.biUnion (fun s:{s:S // hub s=u}=>Finset.univ.image (p s.val))

 theorem spokePathHubVertices_image (m:ℕ) (p:S→(Fin m↪V)) (hub:S→U) (u:U):
    spokePathHubVertices m p hub u=Finset.univ.image (fun x:({s:S // hub s=u}×Fin m)=>p x.1.val x.2):=by
  ext v
  simp only [spokePathHubVertices,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨s,k,hk⟩;exact ⟨(s,k),hk⟩
  · rintro ⟨⟨s,k⟩,hk⟩;exact ⟨s,k,hk⟩

 theorem marked_spoke_path_load_grouping (m:ℕ) (p:S→(Fin m↪V)) (hub:S→U) (ψ:U→U)
    (hdis:∀ s t,s≠t→Disjoint (Finset.univ.image (p s)) (Finset.univ.image (p t)))
    (e:Finset V⊕(V×U)):
    (∑ s:S,∑ k:Fin m,physicalIntDelta (Sum.inr (p s k,hub s)) (Sum.inr (p s k,ψ (hub s))) e)=
      ∑ u:U,((if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,u)) then (1:ℤ) else 0)-
        (if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)):=by
  have hp:=disjoint_paths_joint_injective m p hdis
  rw [←finite_function_fiber_sum hub (fun s=>∑ k:Fin m,
    physicalIntDelta (Sum.inr (p s k,hub s)) (Sum.inr (p s k,ψ (hub s))) e)]
  apply Finset.sum_congr rfl
  intro u hu
  have hlabel:Function.Injective (fun x:({s:S // hub s=u}×Fin m)=>p x.1.val x.2):=by
    rintro ⟨s,k⟩ ⟨t,l⟩ he
    have hh:(s.val,k)=(t.val,l):=hp he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun z:S×Fin m=>z.2) hh)
  have hi (u:U):Function.Injective (fun x:({s:S // hub s=u}×Fin m)=>(Sum.inr (p x.1.val x.2,u):Finset V⊕(V×U))):=by
    intro x y he
    have he':p x.1.val x.2=p y.1.val y.2:=congrArg Prod.fst (Sum.inr.inj he)
    have hh:(x.1.val,x.2)=(y.1.val,y.2):=hp he'
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun z:S×Fin m=>z.2) hh)
  have hi':Function.Injective (fun x:({s:S // hub s=u}×Fin m)=>(Sum.inr (p x.1.val x.2,ψ u):Finset V⊕(V×U))):=by
    intro x y he
    exact hlabel (congrArg Prod.fst (Sum.inr.inj he))
  have hh:=physical_delta_sum
    (fun x:({s:S // hub s=u}×Fin m)=>(Sum.inr (p x.1.val x.2,u):Finset V⊕(V×U)))
    (fun x:({s:S // hub s=u}×Fin m)=>(Sum.inr (p x.1.val x.2,ψ u):Finset V⊕(V×U))) (hi u) hi' e
  rw [Fintype.sum_prod_type] at hh
  have hs:(∑ s:{s:S // hub s=u},∑ k:Fin m,
      physicalIntDelta (Sum.inr (p s.val k,hub s.val)) (Sum.inr (p s.val k,ψ (hub s.val))) e)=
      ∑ s:{s:S // hub s=u},∑ k:Fin m,
      physicalIntDelta (Sum.inr (p s.val k,u)) (Sum.inr (p s.val k,ψ u)) e:=by
    apply Finset.sum_congr rfl
    intro s hs
    rw [s.property]
  have hh':(∑ s:{s:S // hub s=u},∑ k:Fin m,
      physicalIntDelta (Sum.inr (p s.val k,u)) (Sum.inr (p s.val k,ψ u)) e)=
      (if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,u)) then (1:ℤ) else 0)-
        (if e∈(spokePathHubVertices m p hub u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0):=by
    rw [spokePathHubVertices_image,Finset.image_image,Finset.image_image]
    exact hh
  convert hs.trans hh' using 1 <;> congr!

 theorem spokePathHubVertices_disjoint (m:ℕ) (p:S→(Fin m↪V)) (hub:S→U)
    (hdis:∀ s t,s≠t→Disjoint (Finset.univ.image (p s)) (Finset.univ.image (p t))):
    ∀ u u',u≠u'→Disjoint (spokePathHubVertices m p hub u) (spokePathHubVertices m p hub u'):=by
  intro u u' hne
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨s,_,hs⟩:=Finset.mem_biUnion.mp hv
  obtain ⟨t,_,ht⟩:=Finset.mem_biUnion.mp hv'
  have hst:s.val≠t.val:=by intro he;exact hne (s.property.symm.trans ((congrArg hub he).trans t.property))
  exact Finset.disjoint_left.mp (hdis s.val t.val hst) hs ht

end Oberwolfach
