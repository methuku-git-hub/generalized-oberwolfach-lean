module

public import Oberwolfach.MarkedTypedRootLoadsRelabel
public import Oberwolfach.MarkedRetainedTypedRestriction
public import Oberwolfach.MarkedMarginalRelabel

@[expose] public section
/-! Exact root-omitted potential-wheel load for the actual retained marked
sample under bijective domain relabelling. The original weight is pulled
back along the wheel map, and the root remains omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_potential_load_relabel
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d m : ℕ) (a c : Γ) (j : Color)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _ => True) (fun _ _ => True) → ℝ)
    (root : ((W×W)⊕(W×W))⊕(Bool×W×Z)) :
    let z' := markedRetainedPairRestriction f g π ρ hc d a z
    let e := f.prodCongr f
    let hT : ∀ (_ : W) (_ : Z), (True ↔ True) := fun _ _ => Iff.rfl
    let M := markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    let H := retainedRawMarkedSpokes π d (fun e => z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e => z.1 (Sum.inr e)) a)) z.2 c j
    let H' := retainedRawMarkedSpokes ρ d (fun e => z'.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet ρ d (fun e => z'.1 (Sum.inr e)) a)) z'.2 c j
    typedMarkedPotentialLoad (fun W=>w (M W)) (rawMarkedPairRims (P.comap F) ρ d z'.1) H' root =
      typedMarkedPotentialLoad w (rawMarkedPairRims P π d z.1) H
        (markedTypedResourceEquiv f g e e root) := by
  intro z' e hT M H H'
  have hfun : (f : W → V) = F := funext hf
  have hR : ∀ x, rawMarkedPairRims (P.comap F) ρ d z'.1 x ↔
      rawMarkedPairRims P π d z.1 (Sum.map e e x) := by
    intro x
    simpa only [z',e,Equiv.prodCongr_apply,hfun] using
      marked_retained_rim_restriction F f hf g π ρ hc P d a z x
  have hH : ∀ b x u,H' b x u ↔ H b (f x) (g u) := by
    intro b x u
    exact marked_retained_spoke_restriction f g π ρ hc d a c j z.1 z.2 b x u
  have hinjW : Function.Injective (fun a:W×W => (a.1,a.2)) := by intro x y h; cases x; cases y; simpa using h
  have hinjV : Function.Injective (fun a:V×V => (a.1,a.2)) := by intro x y h; cases x; cases y; simpa using h
  exact marked_typed_root_omitted_load_relabel f g hc e e
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    hT hT hinjW hinjW hinjV hinjV w _ _ H' H hR hH root
theorem marked_retained_parent_load_bound_relabel
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d m : ℕ) (a c : Γ) (j : Color)
    (p k : ℝ) (q : U → Γ → ℝ) (s : U → Color → ℝ) (error : ℝ)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _ => True) (fun _ _ => True) → ℝ) :
    let z' := markedRetainedPairRestriction f g π ρ hc d a z
    let e := f.prodCongr f
    let M := markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    let H := retainedRawMarkedSpokes π d (fun e => z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e => z.1 (Sum.inr e)) a)) z.2 c j
    let H' := retainedRawMarkedSpokes ρ d (fun e => z'.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet ρ d (fun e => z'.1 (Sum.inr e)) a)) z'.2 c j
    (∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d z.1) H root-1|≤error) →
    ∀ root,rawMarkedWheelMarginal (P.comap F) ρ d p k (fun u=>q (g u)) (fun u=>s (g u)) c j root≠0 →
      |typedMarkedPotentialLoad (fun W=>w (M W)) (rawMarkedPairRims (P.comap F) ρ d z'.1) H' root-1|≤error := by
  intro z' e M H H' hparent root hroot
  have hload := marked_retained_potential_load_relabel F f hf g π ρ hc P d m a c j z w root
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
theorem marked_retained_parent_load_event_relabel
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d m : ℕ) (a c : Γ) (j : Color)
    (p k : ℝ) (q : U → Γ → ℝ) (s : U → Color → ℝ) (error : ℝ)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _ => True) (fun _ _ => True) → ℝ)
    (μ : FiniteLaw (RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a))
    (Extra : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a → Prop) :
    let e := f.prodCongr f
    let M := markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    let parent := fun z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a =>
      let H := retainedRawMarkedSpokes π d (fun e => z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e => z.1 (Sum.inr e)) a)) z.2 c j
      ∀ root,rawMarkedWheelMarginal P π d p k q s c j root≠0 →
        |typedMarkedPotentialLoad w (rawMarkedPairRims P π d z.1) H root-1|≤error
    let localBound := fun z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a =>
      let z' := markedRetainedPairRestriction f g π ρ hc d a z
      let H' := retainedRawMarkedSpokes ρ d (fun e => z'.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet ρ d (fun e => z'.1 (Sum.inr e)) a)) z'.2 c j
      ∀ root,rawMarkedWheelMarginal (P.comap F) ρ d p k (fun u=>q (g u)) (fun u=>s (g u)) c j root≠0 →
        |typedMarkedPotentialLoad (fun W=>w (M W)) (rawMarkedPairRims (P.comap F) ρ d z'.1) H' root-1|≤error
    μ.probability (fun z=>Extra z ∧ parent z) ≤ μ.probability (fun z=>Extra z ∧ localBound z) := by
  intro e M parent localBound
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1, ?_⟩
  exact marked_retained_parent_load_bound_relabel F f hf g π ρ hc P d m a c j p k q s error z w hz.2
end Oberwolfach
