module

public import Oberwolfach.MarkedRetainedRimRelabel
public import Oberwolfach.MarkedSampleArcs

@[expose] public section
/-! The typed sample-arc types are equivalent under a full-domain relabelling;
endpoints are transported by the same vertex equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_arc_predicate_relabel
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d : ℕ) (a : Γ)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (b : Bool) (w x : W) :
    markedPhysicalRim (P.comap F) ρ (3*d)
      (fun e => (markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) b w x = 1 ↔
    markedPhysicalRim P π (3*d) (fun e => z.1 (Sum.inl e)) b (f w) (f x) = 1 := by
  cases b with
  | false =>
    simpa only [rawMarkedPairRims, Sum.elim_inl, Sum.map_inl, Prod.map_apply, ← hf] using
      marked_retained_rim_restriction F f hf g π ρ hc P d a z (Sum.inl (w,x))
  | true =>
    simpa only [rawMarkedPairRims, Sum.elim_inr, Sum.map_inr, Prod.map_apply, ← hf] using
      marked_retained_rim_restriction F f hf g π ρ hc P d a z (Sum.inr (w,x))

def markedRetainedSampleArcEquiv
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d : ℕ) (a : Γ)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) (b : Bool) :
    MarkedSampleArc (P.comap F) ρ (3*d)
      (fun e => (markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) b ≃
    MarkedSampleArc P π (3*d) (fun e => z.1 (Sum.inl e)) b :=
  (Equiv.prodCongr f f).subtypeEquiv (fun xy =>
    marked_retained_arc_predicate_relabel F f hf g π ρ hc P d a z b xy.1 xy.2)

theorem marked_retained_arc_equiv_endpoints
    (F : W ↪o V) (f : W ≃ V) (hf : ∀ w, f w = F w) (g : Z ≃ U)
    (π : Equiv.Perm V) (ρ : Equiv.Perm W) (hc : ∀ w, f (ρ w) = π (f w))
    (P : SimpleGraph V) (d : ℕ) (a : Γ)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) (b : Bool)
    (e : MarkedSampleArc (P.comap F) ρ (3*d)
      (fun e => (markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) b) :
    (markedRetainedSampleArcEquiv F f hf g π ρ hc P d a z b e).val =
      (f e.val.1,f e.val.2) := rfl
theorem marked_relabel_physical_twist
    (f : W ≃ V) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hc : ∀ w, f (ρ w) = π (f w)) (x y : W) :
    ({x,ρ y} : Finset W).image f = ({f x,π (f y)} : Finset V) := by
  simp only [Finset.image_insert, Finset.image_singleton, hc]
end Oberwolfach
