module

public import Oberwolfach.RawMarkedRestrictionGeometry
public import Oberwolfach.MarkedEmbeddedHostGeometry

@[expose] public section

/-! The arcs of the actual restricted sample embed into the original
sample. Their direction, type, endpoint labels and physical image agree
exactly, rather than merely in distribution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V U Gamma Color:Type} [Fintype W] [Fintype V] [Fintype U] [Fintype Gamma] [Fintype Color]
  [LinearOrder W] [LinearOrder V] [DecidableEq U]

def markedSampleArcEmbedding (f:W↪oV) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (b:ℕ)
    (σ:RawMarkedOutcome V U Gamma Color) (j:Bool):
    MarkedSampleArc (P.comap f) ρ b (fun e=>rawMarkedRestrictVertices f σ (Sum.inl e)) j↪
      MarkedSampleArc P π b (fun e=>σ (Sum.inl e)) j where
  toFun e:=⟨(f e.val.1,f e.val.2),
    (markedPhysicalRim_orderEmbedding f π ρ hf P b (fun e=>σ (Sum.inl e)) j e.val.1 e.val.2).mp e.property⟩
  inj' a b he:=by
    apply Subtype.ext
    apply Prod.ext
    · exact f.injective (congrArg (fun a=>a.val.1) he)
    · exact f.injective (congrArg (fun a=>a.val.2) he)

theorem markedSampleArcEmbedding_endpoints (f:W↪oV) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (b:ℕ)
    (σ:RawMarkedOutcome V U Gamma Color) (j:Bool)
    (e:MarkedSampleArc (P.comap f) ρ b (fun e=>rawMarkedRestrictVertices f σ (Sum.inl e)) j):
    (markedSampleArcEmbedding f π ρ hf P b σ j e).val=(f e.val.1,f e.val.2):=rfl

theorem markedSampleArcEmbedding_physical (f:W↪oV) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (b:ℕ)
    (σ:RawMarkedOutcome V U Gamma Color)
    (e:MarkedSampleArc (P.comap f) ρ b (fun e=>rawMarkedRestrictVertices f σ (Sum.inl e)) false⊕
      MarkedSampleArc (P.comap f) ρ b (fun e=>rawMarkedRestrictVertices f σ (Sum.inl e)) true):
    markedPhysicalEdge
      (fun e:MarkedSampleArc P π b (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π b (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π
      (Sum.map (markedSampleArcEmbedding f π ρ hf P b σ false)
        (markedSampleArcEmbedding f π ρ hf P b σ true) e)=
    (markedPhysicalEdge
      (fun e:MarkedSampleArc (P.comap f) ρ b (fun e=>rawMarkedRestrictVertices f σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc (P.comap f) ρ b (fun e=>rawMarkedRestrictVertices f σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) ρ e).image f:=by
  cases e <;> simp only [Sum.map_inl,Sum.map_inr,markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,
    markedSampleArcEmbedding,Finset.image_insert,Finset.image_singleton,hf,Function.Embedding.coeFn_mk]

end Oberwolfach
