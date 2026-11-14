module

public import Oberwolfach.EndpointPairingGraph
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! Pull a physical endpoint assignment back to its separate row and hub
types. The selected physical graph, endpoints and conflicts are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def finsetEmbeddingImageEquiv [DecidableEq W] (A:Finset V) (e:V↪W):A≃A.image e:=
  Equiv.ofBijective (fun v=>⟨e v.val,Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩)
    ⟨by intro v w he;exact Subtype.ext (e.injective (congrArg Subtype.val he)),by
      intro w;obtain ⟨v,hv,he⟩:=Finset.mem_image.mp w.property
      exact ⟨⟨v,hv⟩,Subtype.ext he⟩⟩

theorem finsetEmbeddingImageEquiv_val [DecidableEq W] (A:Finset V) (e:V↪W) (v:A):
    (finsetEmbeddingImageEquiv A e v).val=e v.val:=rfl

theorem typed_endpoint_pairing (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (P:EndpointPairing (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      (A.image Sum.inl) (B.image Sum.inr)):
    ∃ v w:B↪A,
      (∀ u,H (v u).val u.val ∧ H (w u).val u.val ∧ ¬F.Adj (v u).val (w u).val) ∧
      Disjoint (Set.range v) (Set.range w) ∧
      (∀ a:A,(∃ u,v u=a)∨∃ u,w u=a) ∧
      (∀ u,(P.left (finsetEmbeddingImageEquiv B ⟨Sum.inr,Sum.inr_injective⟩ u)).val=Sum.inl (v u).val ∧
        (P.right (finsetEmbeddingImageEquiv B ⟨Sum.inr,Sum.inr_injective⟩ u)).val=Sum.inl (w u).val) ∧
      P.graph=ordinaryPhysicalGraph (⊥:SimpleGraph V)
        (fun a z=>∃ u:B,z=u.val ∧ (a=(v u).val∨a=(w u).val)):=by
  let eA:A≃A.image (Sum.inl:V→V⊕U):=finsetEmbeddingImageEquiv A ⟨Sum.inl,Sum.inl_injective⟩
  let eB:B≃B.image (Sum.inr:U→V⊕U):=finsetEmbeddingImageEquiv B ⟨Sum.inr,Sum.inr_injective⟩
  let v:B↪A:=(eB.toEmbedding.trans P.left).trans eA.symm.toEmbedding
  let w:B↪A:=(eB.toEmbedding.trans P.right).trans eA.symm.toEmbedding
  have hv (u:B):(P.left (eB u)).val=Sum.inl (v u).val:=by
    have hh:=congrArg Subtype.val (eA.apply_symm_apply (P.left (eB u)))
    exact hh.symm
  have hw (u:B):(P.right (eB u)).val=Sum.inl (w u).val:=by
    have hh:=congrArg Subtype.val (eA.apply_symm_apply (P.right (eB u)))
    exact hh.symm
  have heB (u:B):(eB u).val=Sum.inr u.val:=rfl
  refine ⟨v,w,?_,?_,?_,fun u=>⟨hv u,hw u⟩,?_⟩
  · intro u
    have ha:=P.adjacent (eB u)
    have hf:=P.avoid (eB u)
    rw [hv,hw,heB] at ha
    rw [hv,hw] at hf
    exact ⟨ha.1,ha.2,hf⟩
  · apply Set.disjoint_left.mpr
    rintro a ⟨u,hu⟩ ⟨z,hz⟩
    apply Set.disjoint_left.mp P.disjoint_ranges ⟨eB u,rfl⟩
    refine ⟨eB z,?_⟩
    apply Subtype.ext
    rw [hw,hv,hz,hu]
  · intro a
    rcases P.cover (eA a) with ⟨u,hu⟩|⟨u,hu⟩
    · refine Or.inl ⟨eB.symm u,?_⟩
      change eA.symm (P.left (eB (eB.symm u)))=a
      rw [eB.apply_symm_apply,hu,eA.symm_apply_apply]
    · refine Or.inr ⟨eB.symm u,?_⟩
      change eA.symm (P.right (eB (eB.symm u)))=a
      rw [eB.apply_symm_apply,hu,eA.symm_apply_apply]
  · have hadj (a b:V⊕U):P.graph.Adj a b↔
        ∃ u:B,(a=Sum.inr u.val ∧ (b=Sum.inl (v u).val∨b=Sum.inl (w u).val)) ∨
          (b=Sum.inr u.val ∧ (a=Sum.inl (v u).val∨a=Sum.inl (w u).val)):=by
      constructor
      · rintro ⟨z,hz⟩
        obtain ⟨u,rfl⟩:=eB.surjective z
        exact ⟨u,by simpa only [heB,hv,hw] using hz⟩
      · rintro ⟨u,hu⟩
        exact ⟨eB u,by simpa only [heB,hv,hw] using hu⟩
    ext a b
    rw [hadj]
    cases a <;> cases b <;>
      simp only [ordinaryPhysicalGraph,SimpleGraph.bot_adj,Sum.inl_ne_inr,Sum.inr_ne_inl,
        Sum.inl.injEq,Sum.inr.injEq,false_and,false_or,or_false,and_false,exists_false]

end Oberwolfach
