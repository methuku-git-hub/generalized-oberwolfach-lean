module

public import Oberwolfach.OrdinaryActualAttachmentIdentity
public import Oberwolfach.OrdinaryTransformerSpokeSets
public import Oberwolfach.ResourceDecompositionCounts

@[expose] public section

/-! The remaining term in the edge/vertex-wheel identity is exactly the
sum over the hub-switch domains Z_u. The path supports are disjoint, so
this equality preserves multiplicity even when the hub map is not injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem transformer_spoke_defect_identity (Q:SimpleGraph V) (H₀:V→U→Prop) (ψ:U→U)
    (p:{e:V×U // H₀ e.1 e.2}→(Σ a:V,Σ c:V,Q.Walk a c))
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (e:Sym2 V⊕(V×U)):
    let Z:U→Finset V:=fun u=>(Finset.univ.filter (fun i:{e:V×U // H₀ e.1 e.2}=>i.val.2=u)).biUnion
      (fun i=>(p i).2.2.support.toFinset)
    (∑ i:{e:V×U // H₀ e.1 e.2},transformerPathSpokeDifference (p i) i.val.2 (ψ i.val.2) e)=
      ∑ u:U,((if e∈(Z u).image (fun v=>Sum.inr (v,u)) then (1:ℤ) else 0)-
        (if e∈(Z u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)):=by
  dsimp only
  let I:U→Finset {e:V×U // H₀ e.1 e.2}:=fun u=>Finset.univ.filter (fun i=>i.val.2=u)
  let Z:U→Finset V:=fun u=>(I u).biUnion (fun i=>(p i).2.2.support.toFinset)
  have hind (u:U) (v:V):
      (∑ i∈I u,if v∈(p i).2.2.support then (1:ℤ) else 0)=if v∈Z u then 1 else 0:=by
    have hh:=resource_decomposition_indicator (fun i=>(p i).2.2.support.toFinset) (I u) (Z u)
      (fun i _ j _ hij=>hdis i j hij) rfl v
    simp only [List.mem_toFinset] at hh
    exact_mod_cast hh
  have hf (u:U):
      (∑ i∈I u,transformerPathSpokeDifference (p i) i.val.2 (ψ i.val.2) e)=
      (if e∈(Z u).image (fun v=>Sum.inr (v,u)) then (1:ℤ) else 0)-
        (if e∈(Z u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0):=by
    have hrep:(∑ i∈I u,transformerPathSpokeDifference (p i) i.val.2 (ψ i.val.2) e)=
        ∑ i∈I u,transformerPathSpokeDifference (p i) u (ψ u) e:=by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [hrep]
    cases e with
    | inl f=>simp [transformerPathSpokeDifference]
    | inr vu=>
      rcases vu with ⟨v,z⟩
      have hmem (u':U):(Sum.inr (v,z):Sym2 V⊕(V×U))∈(Z u).image (fun a=>Sum.inr (a,u'))↔v∈Z u∧z=u':=by
        simp only [Finset.mem_image,Sum.inr.injEq,Prod.mk.injEq]
        constructor
        · rintro ⟨a,ha,he,hu⟩;exact ⟨he ▸ ha,hu.symm⟩
        · rintro ⟨hv,hu⟩;exact ⟨v,hv,rfl,hu.symm⟩
      simp only [transformerPathSpokeDifference,hmem,Finset.sum_sub_distrib]
      have hsingle (u':U):
          (∑ i∈I u,if v∈(p i).2.2.support∧z=u' then (1:ℤ) else 0)=
          if v∈Z u∧z=u' then 1 else 0:=by
        by_cases hh:z=u' <;> simp only [hh,and_true,and_false,ite_false,Finset.sum_const_zero,hind]
      rw [hsingle u,hsingle (ψ u)]
  have hs:=Finset.sum_fiberwise_of_maps_to (s:=(Finset.univ:Finset {e:V×U // H₀ e.1 e.2}))
    (t:=(Finset.univ:Finset U)) (g:=fun i=>i.val.2) (fun _ _=>Finset.mem_univ _)
    (fun i=>transformerPathSpokeDifference (p i) i.val.2 (ψ i.val.2) e)
  change (∑ u,∑ i∈I u,transformerPathSpokeDifference (p i) i.val.2 (ψ i.val.2) e)=_ at hs
  rw [←hs]
  exact Finset.sum_congr rfl (fun u _=>hf u)

end Oberwolfach
