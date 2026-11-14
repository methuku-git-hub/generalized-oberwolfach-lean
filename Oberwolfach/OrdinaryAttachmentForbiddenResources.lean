module

public import Oberwolfach.OrdinaryRootResources
public import Oberwolfach.OrdinaryEmbeddedAttachmentAssembly

@[expose] public section

/-! Added attachment wheels contain no resource supported entirely on
forbidden old rows and hubs. The original graph is removed by the exact,
disjoint resource partition, rather than by a new existence assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U I W:Type}
    [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype I] [Fintype W]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq W]

theorem ordinary_attachment_forbidden_resources (G:SimpleGraph V₀) (H:V₀→U₀→Prop)
    (C:SimpleGraph W) (z:W) (ρ:I→V₀)
    (φ:V₀↪V) (ψ:U₀↪U) (f:V₀⊕(I×W)↪V) (g:U₀⊕I↪U)
    (hf:∀ a,f (.inl a)=φ a) (hg:∀ a,g (.inl a)=ψ a)
    (S:Finset V) (B:Finset U) (hfn:∀ i w,f (.inr (i,w))∉S) (hgn:∀ i,g (.inr i)∉B)
    (extra:Finset (Sym2 V⊕(V×U)))
    (hpart:ordinaryHostResources ((ordinaryAttachmentRim G C z ρ).map f)
        (ordinaryMappedSpokes (ordinaryAttachmentSpokes H z ρ) f g)=
      ordinaryHostResources (G.map φ) (ordinaryMappedSpokes H φ ψ)∪extra)
    (hdis:Disjoint (ordinaryHostResources (G.map φ) (ordinaryMappedSpokes H φ ψ)) extra) :
    Disjoint extra (ordinaryRootResources S B) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  have hfull:e∈ordinaryHostResources ((ordinaryAttachmentRim G C z ρ).map f)
      (ordinaryMappedSpokes (ordinaryAttachmentSpokes H z ρ) f g):=by
    rw [hpart];exact Finset.mem_union_right _ he
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      obtain ⟨hv,hw⟩:=(ordinaryRootResources_rim_iff S B v w).mp he'
      obtain ⟨a,b,hab,ha,hb⟩:=(SimpleGraph.map_adj _ _ _ _).mp ((ordinaryHostResources_rim _ _ _).mp hfull)
      cases a with
      | inr p=>exact hfn p.1 p.2 (by simpa only [ha] using hv)
      | inl a=>
        cases b with
        | inr p=>exact hfn p.1 p.2 (by simpa only [hb] using hw)
        | inl b=>
          have hold:Sum.inl s(v,w)∈ordinaryHostResources (G.map φ) (ordinaryMappedSpokes H φ ψ):=by
            apply (ordinaryHostResources_rim _ _ _).mpr
            exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨a,b,hab,(hf a).symm.trans ha,(hf b).symm.trans hb⟩
          exact Finset.disjoint_left.mp hdis hold he
  | inr p=>
    rcases p with ⟨v,u⟩
    obtain ⟨hv,hu⟩:=(ordinaryRootResources_spoke_iff S B v u).mp he'
    obtain ⟨a,b,hab,ha,hb⟩:=(ordinaryHostResources_spoke _ _ _ _).mp hfull
    cases a with
    | inr p=>exact hfn p.1 p.2 (by simpa only [ha] using hv)
    | inl a=>
      cases b with
      | inr b=>exact hgn b (by simpa only [hb] using hu)
      | inl b=>
        have hold:Sum.inr (v,u)∈ordinaryHostResources (G.map φ) (ordinaryMappedSpokes H φ ψ):=
          (ordinaryHostResources_spoke _ _ _ _).mpr ⟨a,b,hab,(hf a).symm.trans ha,(hg b).symm.trans hb⟩
        exact Finset.disjoint_left.mp hdis hold he

end Oberwolfach
