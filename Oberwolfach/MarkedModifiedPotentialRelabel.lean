module

public import Oberwolfach.MarkedRetainedPotentialLoadRelabel

@[expose] public section
/-! Relabel a possibly modified raw host and its typed spokes, preserving the
fixed potential-wheel weights and every root-omitted load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_modified_potential_load_relabel
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _ => True) (fun _ _ => True) → ℝ)
    (root : ((W×W)⊕(W×W))⊕(Bool×W×Z)) :
    let e := f.prodCongr f
    let M := markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    typedMarkedPotentialLoad (fun W=>w (M W))
      (rawMarkedPairRims (P.comap F) ρ d (rawMarkedRestrictPair f g σ))
      (fun b x u=>H b (f x) (g u)) root =
    typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) H
      (markedTypedResourceEquiv f g e e root) := by
  intro e M
  have he : (f:W→V)=F := funext hf
  have hcomm : ∀ x,F (ρ x)=π (F x) := by
    intro x
    simpa only [← he] using hc x
  have hR : ∀ x, rawMarkedPairRims (P.comap F) ρ d (rawMarkedRestrictPair f g σ) x ↔
      rawMarkedPairRims P π d σ (Sum.map e e x) := by
    intro x
    simpa only [e,Equiv.prodCongr_apply,he] using rawMarkedRestrictPair_rims F g π ρ hcomm P d σ x
  have hH : ∀ b x u,H b (f x) (g u) ↔ H b (f x) (g u) := fun _ _ _=>Iff.rfl
  have hinjW : Function.Injective (fun a:W×W => (a.1,a.2)) := by intro x y h; cases x; cases y; simpa using h
  have hinjV : Function.Injective (fun a:V×V => (a.1,a.2)) := by intro x y h; cases x; cases y; simpa using h
  exact marked_typed_root_omitted_load_relabel f g hc e e
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (fun _ _=>Iff.rfl) (fun _ _=>Iff.rfl) hinjW hinjW hinjV hinjV w _ _ _ H hR hH root
theorem marked_modified_parent_load_bound_relabel
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d m : ℕ) (c : Γ) (j : Color)
    (p k : ℝ) (q : U → Γ → ℝ) (s : U → Color → ℝ) (error : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _ => True) (fun _ _ => True) → ℝ) :
    let e := f.prodCongr f
    let M := markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    (∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) H root-1|≤error) →
    ∀ root,rawMarkedWheelMarginal (P.comap F) ρ d p k (fun u=>q (g u)) (fun u=>s (g u)) c j root≠0 →
      |typedMarkedPotentialLoad (fun W=>w (M W))
        (rawMarkedPairRims (P.comap F) ρ d (rawMarkedRestrictPair f g σ))
        (fun b x u=>H b (f x) (g u)) root-1|≤error := by
  intro e M hparent root hroot
  have hload := marked_modified_potential_load_relabel F f hf g π ρ hc P d m σ H w root
  rw [hload]
  apply hparent
  have hmarginal := raw_marked_marginal_relabel f.toEmbedding g π ρ hc P d p k q s c j root
  have he : (f.toEmbedding : W → V) = F := funext hf
  rw [he] at hmarginal
  intro hz
  apply hroot
  apply hmarginal.trans
  cases root with
  | inl root =>
    cases root with
    | inl xy => cases xy; simpa [e, markedTypedResourceEquiv, hf] using hz
    | inr xy => cases xy; simpa [e, markedTypedResourceEquiv, hf] using hz
  | inr root =>
    rcases root with ⟨b,x,u⟩
    simpa [e, markedTypedResourceEquiv, hf] using hz
end Oberwolfach
