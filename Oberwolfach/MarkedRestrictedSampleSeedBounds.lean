module

public import Oberwolfach.MarkedRestrictedSampleSeedLoads
public import Oberwolfach.MarkedSpokeResiduals

@[expose] public section

/-! Transfer both load errors and individual coefficient bounds to the actual
active sample. The same tuple coefficients and numerical bounds are retained. -/
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

theorem marked_restricted_sample_seed_bounds
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hA:∀ j,∀ e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) j,
      e.val.1∈Finset.univ.image f∧e.val.2∈Finset.univ.image f)
    (hS:∀ v u,H false v u∨H true v u→v∈Finset.univ.image f∧u∈Finset.univ.image g)
    (weight:(Fin (m+1)→V)→ℝ) (η lo hi:ℝ):
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
    (∀ a:E₀⊕E₁,|markedWheelRimLoad ψ a-1|≤η)→
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η)→
    (∀ W,lo≤ψ W∧ψ W≤hi)→
    (∀ a:EA₀⊕EA₁,|markedWheelRimLoad ψA a-1|≤η)∧
    (∀ j v u,|markedSpokeResidual ψA j v u|≤η)∧
    (∀ W,lo≤ψA W∧ψA W≤hi):=by
  intro E₀ E₁ σA EA₀ EA₁ e k ψ ψA hR hSp hψ
  obtain ⟨hRload,hSload⟩:=marked_restricted_sample_seed_loads f g π ρ hf P d m σ H hA hS weight
  refine ⟨?_,?_,?_⟩
  · intro a
    rw [hRload a]
    exact hR (Sum.map e k a)
  · intro j v u
    have he:markedSpokeResidual ψA j v u=markedSpokeResidual ψ j (f v) (g u):=by
      unfold markedSpokeResidual
      rw [hSload j v u]
    rw [he]
    exact hSp j (f v) (g u)
  · intro W
    let F : MarkedWheel (fun a:EA₀=>a.val.1) (fun a=>a.val.2)
        (fun a:EA₁=>a.val.1) (fun a=>a.val.2) m ρ (3*d)
        (fun v u=>H false (f v) (g u)) (fun v u=>H true (f v) (g u)) ↪
      MarkedWheel (fun a:E₀=>a.val.1) (fun a=>a.val.2)
        (fun a:E₁=>a.val.1) (fun a=>a.val.2) m π (3*d) (H false) (H true) :=
      markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g hf e k
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    exact hψ (F W)

end Oberwolfach
