module

public import Oberwolfach.MarkedWheelVertexEmbeddingLoads
public import Oberwolfach.MarkedRestrictedSampleArcRange

@[expose] public section

/-! Exact transport of the supplied tuple coefficients to the actual active
sample after every surviving endpoint lies in its retained domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A U B Γ Color:Type} [Fintype V] [Fintype A] [Fintype U] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_restricted_sample_seed_loads
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hA:∀ j,∀ e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) j,
      e.val.1∈Finset.univ.image f∧e.val.2∈Finset.univ.image f)
    (hS:∀ v u,H false v u∨H true v u→v∈Finset.univ.image f∧u∈Finset.univ.image g)
    (weight:(Fin (m+1)→V)→ℝ):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σA:=rawMarkedRestrictPair f g σ
    let EA₀:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let EA₁:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true
    let e:=markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
    let k:=markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true
    let ψ:=fun W:MarkedWheel (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E₁=>a.val.1) (fun a=>a.val.2) m π (3*d) (H false) (H true)=>weight W.1.val
    let ψA:=fun W:MarkedWheel (fun a:EA₀=>a.val.1) (fun a=>a.val.2)
      (fun a:EA₁=>a.val.1) (fun a=>a.val.2) m ρ (3*d)
      (fun v u=>H false (f v) (g u)) (fun v u=>H true (f v) (g u))=>weight (f∘W.1.val)
    (∀ a:EA₀⊕EA₁,markedWheelRimLoad ψA a=markedWheelRimLoad ψ (Sum.map e k a))∧
    (∀ j v u,markedWheelSpokeLoad ψA j v u=markedWheelSpokeLoad ψ j (f v) (g u)):=by
  intro E₀ E₁ σA EA₀ EA₁ e k ψ ψA
  have hsurj (j:Bool):Function.Surjective (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j):=by
    intro a
    have hr:Finset.univ.image (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j)=Finset.univ:=by
      rw [markedRestrictedSampleArcEmbedding_range]
      exact Finset.filter_true_of_mem (fun a _=>hA j a)
    have ha:a∈Finset.univ.image (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j):=by
      rw [hr];exact Finset.mem_univ _
    simpa only [Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and] using ha
  have hrows (C:MarkedCycleTuple (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E₁=>a.val.1) (fun a=>a.val.2) m π (3*d)) (i:Fin (m+1)):
      C.val i∈Set.range f.toEmbedding:=by
    let a:=markedCycleTypedEdge (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E₁=>a.val.1) (fun a=>a.val.2) m π (3*d) C i
    have hh:= (markedCycleTypedEdge_endpoints (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E₁=>a.val.1) (fun a=>a.val.2) m π (3*d) C i).1
    have ha:Sum.elim (fun a:E₀=>a.val.1) (fun a:E₁=>a.val.1) a∈Finset.univ.image f:=by
      cases a with
      | inl a=>exact (hA false a).1
      | inr a=>exact (hA true a).1
    rw [hh] at ha
    obtain ⟨x,_,hx⟩:=Finset.mem_image.mp ha
    exact ⟨x,hx⟩
  have hhubs (W:MarkedWheel (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E₁=>a.val.1) (fun a=>a.val.2) m π (3*d) (H false) (H true)):
      W.2.val∈Set.range g:=by
    have hh:=(hS (W.1.val 0) W.2.val (Or.inr W.2.property.1)).2
    simpa only [Set.mem_range,Finset.mem_image,Finset.mem_univ,true_and] using hh
  have hF:=markedWheelVertexEmbedding_surjective f.toEmbedding g hf e k (hsurj false) (hsurj true)
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (fun _ _=>Iff.rfl) (fun _ _=>Iff.rfl) hrows hhubs
  have hh:=markedWheelVertexEmbedding_loads f.toEmbedding g hf e k
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (fun _ _ h=>h) (fun _ _ h=>h) hF ψ
  exact hh

end Oberwolfach
