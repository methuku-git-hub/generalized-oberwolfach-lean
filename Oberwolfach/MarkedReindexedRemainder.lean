module

public import Oberwolfach.MarkedCoverDownNextState

@[expose] public section

/-! The canonical next-level remainder statement, as a predicate on its
fixed raw outcome and spoke relation. This keeps equality transport of the
whole dependent finite sample explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

def MarkedReindexedRemainder
    (f:W↪oV) (g:Z↪U) (P:SimpleGraph W) (ρ:Equiv.Perm W) (d m:ℕ)
    (σ₀:RawMarkedOutcome W Z Γ Color) (H₀:Bool → W → Z → Prop)
    (X:Finset W) (Y:Finset Z) (F L:Finset (Finset V⊕(V×U))) (γ σloss:ℝ) : Prop :=
    let E₀:=MarkedSampleArc P ρ (3*d) (fun e=>σ₀ (Sum.inl e)) false
    let K₀:=MarkedSampleArc P ρ (3*d) (fun e=>σ₀ (Sum.inl e)) true
    let S₀:=Finset.univ.filter (fun z:W×Z=>H₀ false z.1 z.2∨H₀ true z.1 z.2)
    let B₀:=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ Finset.univ S₀;
    ∃ F₀⊆B₀,∃ FA : Finset (E₀⊕K₀),∃ FS⊆S₀,
      markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ FA FS=F₀ ∧
      F₀.image (markedResourceEmbedding f.toEmbedding g)=F ∧
      (B₀\F₀).image (markedResourceEmbedding f.toEmbedding g)=L ∧
      F₀.filter (markedInnerResource X Y)=∅ ∧
      (∀ physical x,(((markedIncidentEdges (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) physical x).filter
        (fun e=>markedActivePhysical (fun e:E₀=>e.val.1) (fun e=>e.val.2)
          (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) e∈F₀)).card:ℝ)≤γ) ∧
      (∀ physical x,(((markedIncidentEdges (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) physical x).filter
        (fun e=>markedActivePhysical (fun e:E₀=>e.val.1) (fun e=>e.val.2)
          (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ (H₀ false) (H₀ true) e∈F₀.filter (markedStarResource X Y))).card:ℝ)≤σloss) ∧
      let σNext := rawMarkedDeleteRims σ₀ (markedSampleArcSetGraph P ρ d σ₀ FA).edgeFinset
      let HNext := markedDeletePhysicalSpokes H₀ (markedFiniteSpokeGraph FS)
      let ENext := MarkedSampleArc P ρ (3*d) (fun e=>σNext (Sum.inl e)) false
      let KNext := MarkedSampleArc P ρ (3*d) (fun e=>σNext (Sum.inl e)) true;
      MarkedRemainderDivisible (fun e:ENext=>e.val.1) (fun e=>e.val.2)
        (fun e:KNext=>e.val.1) (fun e=>e.val.2) (HNext true) Finset.univ
        (Finset.univ.filter (fun s:W×Z=>HNext false s.1 s.2∨HNext true s.1 s.2)) m

end Oberwolfach
