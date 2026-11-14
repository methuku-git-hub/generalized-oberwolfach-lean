module

public import Oberwolfach.OrdinaryActualSpokeCrossPacking
public import Oberwolfach.OrdinaryActualAttachmentIdentity
public import Oberwolfach.ResourceDecompositionCounts

@[expose] public section

/-! The complete edge/vertex-wheel stage as two actual physical
packings. Their difference is the old-graph difference plus the explicit
spoke-path term which the hub-factor trade must cancel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem wheelFamily_integer_indicator {I:Type} [Fintype I] [DecidableEq I]
    {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ} (W:I→OrdinaryWheel Q F H r)
    (hW:∀ i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j)))
    (e:Sym2 V⊕(V×U)):
    (∑ i,if e∈ordinaryWheelResources (W i) then (1:ℤ) else 0)=
      if e∈ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W) then 1 else 0:=by
  have hh:=resource_decomposition_indicator (fun i=>ordinaryWheelResources (W i)) Finset.univ
    (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W))
    (fun i _ j _ hij=>hW i j hij) (wheelFamily_resources W).symm e
  exact_mod_cast hh

 theorem sum_three_resource_families_disjoint {I J K X:Type} [DecidableEq X]
    (A:I→Finset X) (B:J→Finset X) (C:K→Finset X)
    (hA:∀ i j,i≠j→Disjoint (A i) (A j)) (hB:∀ i j,i≠j→Disjoint (B i) (B j))
    (hC:∀ i j,i≠j→Disjoint (C i) (C j))
    (hAB:∀ i j,Disjoint (A i) (B j)) (hAC:∀ i j,Disjoint (A i) (C j)) (hBC:∀ i j,Disjoint (B i) (C j)):
    ∀ i j:I⊕(J⊕K),i≠j→Disjoint (Sum.elim A (Sum.elim B C) i) (Sum.elim A (Sum.elim B C) j):=by
  intro i j hij
  cases i with
  | inl i=>
    cases j with
    | inl j=>exact hA i j (fun he=>hij (congrArg Sum.inl he))
    | inr j=>cases j with
      | inl j=>exact hAB i j
      | inr j=>exact hAC i j
  | inr i=>
    cases i with
    | inl i=>
      cases j with
      | inl j=>exact (hAB j i).symm
      | inr j=>cases j with
        | inl j=>exact hB i j (fun he=>hij (congrArg (fun z=>Sum.inr (Sum.inl z)) he))
        | inr j=>exact hBC i j
    | inr i=>
      cases j with
      | inl j=>exact (hAC j i).symm
      | inr j=>cases j with
        | inl j=>exact (hBC j i).symm
        | inr j=>exact hC i j (fun he=>hij (congrArg (fun z=>Sum.inr (Sum.inr z)) he))

 theorem ordinary_transformer_edge_stage (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (r:ℕ) (hr:3≤r) (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d))
    (hD:∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
        (transformerSpokeEndpoint G Q H₀ b p d),v∉W∧v≠φ d.1)
    (hDfirst:∀ d e,d≠e→Disjoint (ordinaryWheelResources (D d).first) (ordinaryWheelResources (D e).first))
    (hDsecond:∀ d e,d≠e→Disjoint (ordinaryWheelResources (D d).second) (ordinaryWheelResources (D e).second)):
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j))) ∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j))) ∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Plus) (wheelFamilySpokes Plus) r ∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Minus) (wheelFamilySpokes Minus) r ∧
    ∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
      (∑ i:G.edgeFinset,physicalIntDelta (.inl i.val) (.inl s(φ i.val.out.1,φ i.val.out.2)) e)+
      (∑ i:{e:V×U // H₀ e.1 e.2},physicalIntDelta (.inr i.val) (.inr (φ i.val.1,ψ i.val.2)) e)+
      ∑ i:{e:V×U // H₀ e.1 e.2},transformerPathSpokeDifference (p (.inr i)) i.val.2 (ψ i.val.2) e:=by
  dsimp only
  let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
  let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
  have hESD:=ordinary_actual_spoke_cross_packing G Q F H₀ H φ ψ r (by omega) R W B hRW b σ p
    hbalance hroot hcross hB hpW hdis E S D hD
  have hED:=ordinary_actual_rim_vertex_packing G Q F H₀ H φ b σ hσ p r (by omega) R W B hRW
    hroot hcross hpW hdis E D hD
  have hPlus:∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j)):=by
    have hh:=sum_three_resource_families_disjoint _ _ _ E.first_disjoint S.first_disjoint hDsecond
      (fun e f=>(hESD.1 e f).1) (fun e d=>(hED e d).1) (fun f d=>(hESD.2 f d).1)
    intro i j hij
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> exact hh _ _ hij
  have hMinus:∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j)):=by
    have hh:=sum_three_resource_families_disjoint _ _ _ E.second_disjoint S.second_disjoint hDfirst
      (fun e f=>(hESD.1 e f).2) (fun e d=>(hED e d).2) (fun f d=>(hESD.2 f d).2)
    intro i j hij
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> exact hh _ _ hij
  refine ⟨hPlus,hMinus,wheelFamily_decomposition Plus hPlus,wheelFamily_decomposition Minus hMinus,?_⟩
  intro e
  have hid:=ordinary_actual_attachment_identity G Q F H₀ H φ ψ r B b σ p hdis E S D e
  have hP:=wheelFamily_integer_indicator Plus hPlus e
  have hM:=wheelFamily_integer_indicator Minus hMinus e
  rw [←hP,←hM]
  simp only [Fintype.sum_sum_type,Plus,Minus,Sum.elim_inl,Sum.elim_inr]
  simp only [Finset.sum_sub_distrib] at hid
  linarith only [hid]

end Oberwolfach
