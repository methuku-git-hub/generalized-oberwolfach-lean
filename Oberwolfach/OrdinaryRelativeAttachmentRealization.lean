module

public import Oberwolfach.OrdinaryRelativeAttachmentEmbedding
public import Oberwolfach.OrdinaryEmbeddedAttachmentAssembly

@[expose] public section

/-! The relative-host attachment with its actual extra-wheel decomposition
and exact physical-edge partition. No decomposition of the original remainder
is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U I:Type} [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq I]

theorem ordinary_relative_attachment_realization (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W R:Finset V) (B:Finset U) (φ:V₀↪V) (ψ:U₀↪U)
    (G₀:SimpleGraph V₀) (H₀:V₀→U₀→Prop) (ρ:I→V₀)
    (hφ:∀ a,φ a∈R) (hψ:∀ b,ψ b∈B)
    (hG₀:∀ a b,G₀.Adj a b→Q.Adj (φ a) (φ b)) (hH₀:∀ a b,H₀ a b→H (φ a) (ψ b))
    (r:ℕ) (hr:3≤r) (d c cH:ℝ) (hd:0≤d)
    (hF:∀ v,(F.degree v:ℝ)≤d)
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+Fintype.card I*r+r+6)*(d+1)<c)
    (hB:(B.card:ℝ)+Fintype.card I<cH) :
    ∃ (f:V₀⊕(I×Fin r)↪V) (g:U₀⊕I↪U),
      (∀ a,f (.inl a)=φ a) ∧ (∀ b,g (.inl b)=ψ b) ∧
      (∀ i w,f (.inr (i,w))∈A ∧ f (.inr (i,w))∉W ∧ f (.inr (i,w))∉R ∧
        ∀ z∈R,¬F.Adj (f (.inr (i,w))) z) ∧
      (∀ i,g (.inr i)∉B) ∧
      (∀ i j w w',¬F.Adj (f (.inr (i,w))) (f (.inr (j,w')))) ∧
      (∀ a b,(ordinaryAttachmentRim G₀ (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ).Adj a b→Q.Adj (f a) (f b)) ∧
      (∀ a b,ordinaryAttachmentSpokes H₀ ⟨0,by omega⟩ ρ a b→H (f a) (g b)) ∧
      let old:=ordinaryHostResources (G₀.map φ) (ordinaryMappedSpokes H₀ φ ψ)
      let extra:=ordinaryHostResources ((ordinaryAttachmentRim ⊥ (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ).map f)
        (ordinaryMappedSpokes (ordinaryAttachmentSpokes (fun (_:V₀) (_:U₀)=>False) ⟨0,by omega⟩ ρ) f g)
      let full:=ordinaryHostResources ((ordinaryAttachmentRim G₀ (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ).map f)
        (ordinaryMappedSpokes (ordinaryAttachmentSpokes H₀ ⟨0,by omega⟩ ρ) f g)
      full=old∪extra ∧ Disjoint old extra ∧
        HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) extra := by
  obtain ⟨f,g,hf,hg,hpriv,hnewhub,hprivF,hQ,hH⟩:=ordinary_relative_attachment_embedding Q F H A W R B φ ψ G₀ H₀ ρ
    hφ hψ hG₀ hH₀ r hr d c cH hd hF hcount hhub hbudget hB
  refine ⟨f,g,hf,hg,hpriv,hnewhub,hprivF,hQ,hH,?_⟩
  obtain ⟨he,hd⟩:=ordinary_embedded_attachment_resources G₀ H₀ (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ φ ψ f g hf hg
  refine ⟨he,hd,?_⟩
  have hC:IsEmbeddedCycle (SimpleGraph.cycleGraph r) r:=by
    refine ⟨hr,Function.Embedding.refl _,?_⟩
    change SimpleGraph.cycleGraph r=(SimpleGraph.cycleGraph r).map id
    rw [SimpleGraph.map_id]
  have hfull:∀ w:Fin r,w∈(SimpleGraph.cycleGraph r).support:=by
    intro w;rw [cycleGraph_support_eq_univ hr];exact Set.mem_univ _
  apply ordinary_attachment_extra_host_decomposition Q F H (SimpleGraph.cycleGraph r) hC hfull ⟨0,by omega⟩ ρ f g
  · intro a b hab
    apply hQ a b
    rw [ordinaryAttachment_rim_union]
    exact Or.inr hab
  · intro a b hab
    apply hH a b
    rw [ordinaryAttachment_spoke_union]
    exact Or.inr hab
  · intro i w a
    rw [hf]
    exact (hpriv i w).2.2.2 (φ a) (hφ a)
  · exact hprivF

end Oberwolfach
