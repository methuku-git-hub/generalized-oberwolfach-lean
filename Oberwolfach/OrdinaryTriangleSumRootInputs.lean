module

public import Oberwolfach.OrdinaryTwoDomainHostGeometry

@[expose] public section
/-! Original root stars and their exact balance become the corresponding
root hypotheses in the auxiliary single-type triangle graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_sum_root_inputs (P Q:SimpleGraph V) (J:V→U→Prop)
    (A X Z:Finset V) (B:Finset U) (n:ℕ) (x:Fin n→V) (pR pH η θ:ℝ)
    (hZA:Z⊆A) (hn:(n:ℝ)≤θ*A.card) (hx:Function.Injective x) (hX:∀i,x i∈X)
    (hZ:∀i,x i∉Z) (hroot:∀i,Q.neighborFinset (x i)⊆Z)
    (hJ:∀i u,J (x i) u→u∈B)
    (hbalance:∀i,|pR*(A∩P.neighborFinset (x i)).card/(2*B.card*pH)-1|≤η)
    (hbal:∀i,Q.degree (x i)=2*(Finset.univ.filter (J (x i))).card):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let A':=A.image (Sum.inl:V→V⊕U)
    let B':=ordinarySumHubSet (V:=V) B
    let X':=X.image (Sum.inl:V→V⊕U)
    let Z':=Z.image (Sum.inl:V→V⊕U)
    let x':Fin n→V⊕U:=fun i=>e (x i)
    let P':=P.map e
    let Q':=Q.map e
    let J':=ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧J v u);
    Z'⊆A' ∧ (n:ℝ)≤θ*A'.card ∧ Function.Injective x' ∧
    (∀i,x' i∈X') ∧ (∀i,x' i∉Z') ∧ (∀i,Q'.neighborFinset (x' i)⊆Z') ∧
    (∀i,|pR*(A'∩P'.neighborFinset (x' i)).card/(2*B'.card*pH)-1|≤η) ∧
    (∀i,Q'.degree (x' i)=2*J'.degree (x' i)):=by
  intro e A' B' X' Z' x' P' Q' J'
  have hA:A'.card=A.card:=Finset.card_image_of_injective _ Sum.inl_injective
  have hB:B'.card=B.card:=Finset.card_image_of_injective _ Sum.inr_injective
  refine ⟨Finset.image_subset_image hZA,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hA] using hn
  · exact Sum.inl_injective.comp hx
  · intro i;exact Finset.mem_image.mpr ⟨x i,hX i,rfl⟩
  · intro i hi
    obtain ⟨v,hv,he⟩:=Finset.mem_image.mp hi
    exact hZ i ((Sum.inl.inj he) ▸ hv)
  · intro i
    have he:=ordinary_sum_rim_full_neighbours (U:=U) Q (x i)
    change Q'.neighborFinset (x' i)=(Q.neighborFinset (x i)).image Sum.inl at he
    rw [he]
    exact Finset.image_subset_image (hroot i)
  · intro i
    have he:=ordinary_sum_rim_neighbours (U:=U) P A (x i)
    change A'∩P'.neighborFinset (x' i)=(A∩P.neighborFinset (x i)).image Sum.inl at he
    have hc:((A∩P.neighborFinset (x i)).image (Sum.inl:V→V⊕U)).card=(A∩P.neighborFinset (x i)).card:=
      Finset.card_image_of_injective _ Sum.inl_injective
    rw [he,hc,hB]
    exact hbalance i
  · intro i
    have hdeg:=SimpleGraph.degree_map_apply Q e (x i)
    have hdeg':Q'.degree (x' i)=Q.degree (x i):=by
      simpa only [←SimpleGraph.ncard_neighborSet] using hdeg
    have hsp:=ordinary_sum_spoke_root_degree J B (x i) (hJ i)
    have hsp':J'.degree (x' i)=(Finset.univ.filter (J (x i))).card:=by
      convert hsp using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [hdeg',hsp']
    exact hbal i
end Oberwolfach
