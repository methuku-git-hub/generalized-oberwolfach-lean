module

public import Oberwolfach.TransformerActualData

@[expose] public section

/-! Attachment cancellation for the actual selected paths. The sums are
reindexed by proved incidence equivalences, so the two ends of each
physical edge and the two ends of each spoke path are counted once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem actual_rim_attachment_sum (G Q:SimpleGraph V) (H₀:V→U→Prop)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (f:V→V→ℤ):
    (∑ e:G.edgeFinset,(f e.val.out.1 (p (.inl e)).1+f e.val.out.2 (p (.inl e)).2.1))=
      ∑ d:Σ v,G.neighborSet v,f d.1 (transformerRimEndpoint G Q H₀ p d):=by
  let g:G.edgeFinset×Fin 2→ℤ:=fun z=>
    f (if z.2=0 then z.1.val.out.1 else z.1.val.out.2) (graphPathEndpoint (p (.inl z.1)) z.2)
  have hh:=Equiv.sum_comp (rimIncidenceEquiv G) g
  have hleft:(∑ z:G.edgeFinset×Fin 2,g z)=
      ∑ e:G.edgeFinset,(f e.val.out.1 (p (.inl e)).1+f e.val.out.2 (p (.inl e)).2.1):=by
    rw [Fintype.sum_prod_type]
    simp [g,Fin.sum_univ_two,graphPathEndpoint]
  rw [hleft] at hh
  rw [←hh]
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [g,transformerRimEndpoint]
  rw [←rimIncidenceEquiv_root G d]

 theorem actual_spoke_attachment_sum (G Q:SimpleGraph V) (H₀:V→U→Prop)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (f:V→V→ℤ):
    (∑ e:{e:V×U // H₀ e.1 e.2},(f e.val.1 (p (.inr e)).1+f e.val.1 (p (.inr e)).2.1))=
      ∑ d:Σ v,G.neighborSet v,f d.1 (transformerSpokeEndpoint G Q H₀ b p d):=by
  let g:({e:V×U // H₀ e.1 e.2}×Fin 2)→ℤ:=fun z=>
    f z.1.val.1 (graphPathEndpoint (p (.inr z.1)) z.2)
  have hh:=Equiv.sum_comp (spokeEndpointEquiv G H₀ b) g
  have hleft:(∑ z,g z)=
      ∑ e:{e:V×U // H₀ e.1 e.2},(f e.val.1 (p (.inr e)).1+f e.val.1 (p (.inr e)).2.1):=by
    rw [Fintype.sum_prod_type]
    simp [g,Fin.sum_univ_two,graphPathEndpoint]
  rw [hleft] at hh
  rw [←hh]
  rfl

 theorem actual_shifted_hub_sum (G:SimpleGraph V)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (h:G.edgeFinset↪U) (f:V→U→ℤ):
    (∑ e:G.edgeFinset,(f e.val.out.1 (h e)+f e.val.out.2 (h e)))=
      ∑ d:Σ v,G.neighborSet v,f d.1 (transformerAssignedHub G σ h d):=by
  let g:G.edgeFinset×Fin 2→ℤ:=fun z=>
    f (if z.2=0 then z.1.val.out.1 else z.1.val.out.2) (h z.1)
  have hh:=Equiv.sum_comp (shiftedIncidenceEquiv G σ) g
  have hleft:(∑ z,g z)=∑ e:G.edgeFinset,(f e.val.out.1 (h e)+f e.val.out.2 (h e)):=by
    rw [Fintype.sum_prod_type]
    simp [g,Fin.sum_univ_two]
  rw [hleft] at hh
  rw [←hh]
  apply Finset.sum_congr rfl
  intro d _
  dsimp only [g,transformerAssignedHub]
  have hroot:=rimIncidenceEquiv_root G (incidenceShiftEquiv G σ d)
  change d.1=(if (shiftedIncidenceEquiv G σ d).2=0 then
      (shiftedIncidenceEquiv G σ d).1.val.out.1 else (shiftedIncidenceEquiv G σ d).1.val.out.2) at hroot
  rw [←hroot]

 theorem actual_transformer_attachment_cancellation (G Q:SimpleGraph V) (H₀:V→U→Prop)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (h:G.edgeFinset↪U)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (rim:V→V→ℤ) (spoke:V→U→ℤ) (core:G.edgeFinset→ℤ)
    (cross load:{e:V×U // H₀ e.1 e.2}→ℤ):
    (∑ e:G.edgeFinset,(core e+rim e.val.out.1 (p (.inl e)).1+rim e.val.out.2 (p (.inl e)).2.1+
      spoke e.val.out.1 (h e)+spoke e.val.out.2 (h e)))+
    (∑ e:{e:V×U // H₀ e.1 e.2},(cross e+rim e.val.1 (p (.inr e)).1+
      rim e.val.1 (p (.inr e)).2.1+load e))-
    (∑ d:Σ v,G.neighborSet v,(rim d.1 (transformerRimEndpoint G Q H₀ p d)+
      rim d.1 (transformerSpokeEndpoint G Q H₀ b p d)+spoke d.1 (transformerAssignedHub G σ h d)))=
    (∑ e:G.edgeFinset,core e)+(∑ e:{e:V×U // H₀ e.1 e.2},cross e)+
      ∑ e:{e:V×U // H₀ e.1 e.2},load e:=by
  have hr:=actual_rim_attachment_sum G Q H₀ p rim
  have hz:=actual_spoke_attachment_sum G Q H₀ b p rim
  have hs:=actual_shifted_hub_sum G σ h spoke
  simp_rw [Finset.sum_add_distrib] at hr hz hs ⊢
  rw [←hr,←hz,←hs]
  abel

end Oberwolfach
