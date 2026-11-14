module

public import Oberwolfach.OrdinaryActualRimWheels
public import Oberwolfach.OrdinaryActualSpokeWheels
public import Oberwolfach.OrdinaryActualVertexWheels
public import Oberwolfach.ActualTransformerCancellation

@[expose] public section

/-! Identity (A) for the actual physical wheel indicators, rather than
for independent functions supplied as algebraic inputs. Every rim and
spoke difference is supplied by the constructed wheel pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 def physicalIntDelta {X:Type} [DecidableEq X] (a b x:X):ℤ:=
  (if x=a then 1 else 0)-(if x=b then 1 else 0)

 def transformerPathSpokeDifference {Q:SimpleGraph V}
    (p:Σ a:V,Σ b:V,Q.Walk a b) (u u':U) (e:Sym2 V⊕(V×U)):ℤ:=
  match e with
  | .inl _=>0
  | .inr z=>(if z.1∈p.2.2.support∧z.2=u then 1 else 0)-
      (if z.1∈p.2.2.support∧z.2=u' then 1 else 0)

 theorem ordinary_actual_attachment_identity (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (r:ℕ) (B:Finset U)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (E:OrdinaryActualRimWheels G Q F H₀ H φ r B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r p)
    (D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H r d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d))
    (e:Sym2 V⊕(V×U)):
    (∑ i:G.edgeFinset,((if e∈ordinaryWheelResources (E.first i) then (1:ℤ) else 0)-
      (if e∈ordinaryWheelResources (E.second i) then 1 else 0)))+
    (∑ i:{e:V×U // H₀ e.1 e.2},((if e∈ordinaryWheelResources (S.first i) then (1:ℤ) else 0)-
      (if e∈ordinaryWheelResources (S.second i) then 1 else 0)))-
    (∑ d:Σ v,G.neighborSet v,((if e∈ordinaryWheelResources (D d).first then (1:ℤ) else 0)-
      (if e∈ordinaryWheelResources (D d).second then 1 else 0)))=
    (∑ i:G.edgeFinset,physicalIntDelta (.inl i.val) (.inl s(φ i.val.out.1,φ i.val.out.2)) e)+
    (∑ i:{e:V×U // H₀ e.1 e.2},physicalIntDelta (.inr i.val) (.inr (φ i.val.1,ψ i.val.2)) e)+
    ∑ i:{e:V×U // H₀ e.1 e.2},transformerPathSpokeDifference (p (.inr i)) i.val.2 (ψ i.val.2) e:=by
  let rim:V→V→ℤ:=fun x a=>physicalIntDelta (.inl s(x,a)) (.inl s(φ x,a)) e
  let spoke:V→U→ℤ:=fun x u=>physicalIntDelta (.inr (x,u)) (.inr (φ x,u)) e
  let core:G.edgeFinset→ℤ:=fun i=>physicalIntDelta (.inl i.val) (.inl s(φ i.val.out.1,φ i.val.out.2)) e
  let cross:{e:V×U // H₀ e.1 e.2}→ℤ:=fun i=>physicalIntDelta (.inr i.val) (.inr (φ i.val.1,ψ i.val.2)) e
  let load:{e:V×U // H₀ e.1 e.2}→ℤ:=fun i=>transformerPathSpokeDifference (p (.inr i)) i.val.2 (ψ i.val.2) e
  have hE (i:G.edgeFinset):
      (if e∈ordinaryWheelResources (E.first i) then (1:ℤ) else 0)-
        (if e∈ordinaryWheelResources (E.second i) then 1 else 0)=
      core i+rim i.val.out.1 (p (.inl i)).1+rim i.val.out.2 (p (.inl i)).2.1+
        spoke i.val.out.1 (E.hub i)+spoke i.val.out.2 (E.hub i):=by
    cases e with
    | inl f=>
      have he:s(i.val.out.1,i.val.out.2)=i.val:=by rw [Sym2.mk];exact i.val.out_eq
      have hh:=E.rim_difference i f
      rw [he] at hh
      simp only [core,rim,spoke,physicalIntDelta,Sum.inl.injEq,Sum.inl_ne_inr,ite_false,sub_self] at *
      omega
    | inr vu=>
      have hh:=E.spoke_difference i vu.1 vu.2
      simp only [core,rim,spoke,physicalIntDelta,Sum.inr.injEq,Prod.eq_iff_fst_eq_snd_eq,Sum.inr_ne_inl,ite_false,sub_self] at *
      exact hh.trans (by abel)
  have hS (i:{e:V×U // H₀ e.1 e.2}):
      (if e∈ordinaryWheelResources (S.first i) then (1:ℤ) else 0)-
        (if e∈ordinaryWheelResources (S.second i) then 1 else 0)=
      cross i+rim i.val.1 (p (.inr i)).1+rim i.val.1 (p (.inr i)).2.1+load i:=by
    cases e with
    | inl f=>
      have hh:=S.rim_difference i f
      simp only [cross,rim,load,transformerPathSpokeDifference,physicalIntDelta,Sum.inl.injEq,Sum.inl_ne_inr,
        ite_false,sub_self] at *
      omega
    | inr vu=>
      have hh:=S.spoke_difference i vu.1 vu.2
      simp only [cross,rim,load,transformerPathSpokeDifference,physicalIntDelta,Sum.inr.injEq,Prod.eq_iff_fst_eq_snd_eq,
        Sum.inr_ne_inl,ite_false,sub_self] at *
      exact hh.trans (by abel)
  have hab (d:Σ v,G.neighborSet v):transformerRimEndpoint G Q H₀ p d≠transformerSpokeEndpoint G Q H₀ b p d:=by
    intro he
    have ha:=graphPathEndpoint_mem (p (.inl (rimIncidenceEquiv G d).1)) (rimIncidenceEquiv G d).2
    have hz:=graphPathEndpoint_mem (p (.inr (spokeEndpointEquiv G H₀ b d).1)) (spokeEndpointEquiv G H₀ b d).2
    change transformerRimEndpoint G Q H₀ p d∈_ at ha
    change transformerSpokeEndpoint G Q H₀ b p d∈_ at hz
    exact Finset.disjoint_left.mp (hdis _ _ Sum.inl_ne_inr) (List.mem_toFinset.mpr ha)
      (he.symm ▸ List.mem_toFinset.mpr hz)
  have hD (d:Σ v,G.neighborSet v):
      (if e∈ordinaryWheelResources (D d).first then (1:ℤ) else 0)-
        (if e∈ordinaryWheelResources (D d).second then 1 else 0)=
      rim d.1 (transformerRimEndpoint G Q H₀ p d)+rim d.1 (transformerSpokeEndpoint G Q H₀ b p d)+
        spoke d.1 (transformerAssignedHub G σ E.hub d):=by
    cases e with
    | inl f=>
      have hh:=(D d).rim_difference f
      rw [int_indicator_pair _ _ _ (fun he=>hab d (sym2_fixed_endpoint_injective d.1 he)),
        int_indicator_pair _ _ _ (fun he=>hab d (sym2_fixed_endpoint_injective (φ d.1) he))] at hh
      simp only [rim,spoke,physicalIntDelta,Sum.inl.injEq,Sum.inl_ne_inr,ite_false,sub_self] at *
      exact hh.trans (by abel)
    | inr vu=>
      have hh:=(D d).spoke_difference vu.1 vu.2
      simp only [rim,spoke,physicalIntDelta,Sum.inr.injEq,Prod.eq_iff_fst_eq_snd_eq,Sum.inr_ne_inl,ite_false,sub_self] at *
      exact hh.trans (by abel)
  simp_rw [hE,hS,hD]
  exact actual_transformer_attachment_cancellation G Q H₀ b σ E.hub p rim spoke core cross load

end Oberwolfach
