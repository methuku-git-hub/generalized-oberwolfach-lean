module

public import Oberwolfach.MarkedProtectedActiveConfigurationLowerBounds

@[expose] public section

/-! Common cycle, root-omitted path and compatible-hub inputs after the
actual active restriction, with one simultaneous original-order allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_active_configurations_from_scale
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d r:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (β kappa:ℝ)
    (hβ:0≤β) (hκ:0≤kappa)
    (hDR:∀ x,((DR.comap f).degree x:ℝ)≤kappa*Fintype.card V)
    (hDSrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤kappa*Fintype.card V)
    (hDScol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤kappa*Fintype.card V)
    (hparent:MarkedCommonConfigurationsWithSpokes r P π d β kappa σ H)
    (hRsize:((Finset.univ\Finset.univ.image f).card:ℝ)≤kappa*Fintype.card V)
    (hUsize:((Finset.univ\Finset.univ.image g).card:ℝ)≤kappa*Fintype.card V)
    (hcycle:8*(r+5:ℝ)*kappa≤12*β)
    (hhub:(1+2*(r+5:ℝ))*kappa≤28*β):
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u)
    let EA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let KA:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true;
    (∀ C:MarkedCycleTuple (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
      (r+4) ρ (3*d),4*β*Fintype.card W≤(Fintype.card {u // MarkedHubCompatible (HA false) (HA true) C.val u}:ℝ))∧
    (∀ u u':Z,u≠u'→4*β*(Fintype.card W:ℝ)^(r+5)≤
      (Fintype.card (CommonMarkedCycle (fun e:EA=>e.val.1) (fun e=>e.val.2) (fun e:KA=>e.val.1) (fun e=>e.val.2)
        (r+4) ρ (3*d) (HA false) (HA true) u u'):ℝ))∧
    (∀ j (x x':W) (u u':Z),x≠x'→u≠u'→4*β*(Fintype.card W:ℝ)^(r+4)≤
      (Fintype.card (CanonicalCommonMarkedPath (fun e:EA=>e.val.1) (fun e=>e.val.2)
        (fun e:KA=>e.val.1) (fun e=>e.val.2) (r+4) ρ (3*d) (HA false) (HA true)
        ((markedRootOrder (r+4) j).symm 0) x x' u u'):ℝ)) :=by
  have hn:0≤(Fintype.card V:ℝ):=Nat.cast_nonneg _
  have hcycleN:=mul_le_mul_of_nonneg_right hcycle hn
  have hhubN:=mul_le_mul_of_nonneg_right hhub hn
  have hR:=mul_le_mul_of_nonneg_left hRsize (show 0≤2*(r+5:ℝ) by positivity)
  apply marked_protected_active_configuration_lower_bounds f g π ρ hf P d r σ H DR DS β kappa
    (kappa*Fintype.card V) hβ hκ (by positivity) hDR hDSrow hDScol hparent
  · nlinarith only [hR,hcycleN]
  · nlinarith only [hUsize,hhubN]

end Oberwolfach
