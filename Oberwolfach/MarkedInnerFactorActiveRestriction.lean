module

public import Oberwolfach.MarkedInnerFactorInputsAfterBothPackings
public import Oberwolfach.RawMarkedRestrictionComposition

@[expose] public section

/-! The fixed inner coefficients and the original outcome are evaluated on
the same vertices whether the inner or the active restriction is taken first. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V VA W U UA Γ Color:Type} [Fintype V] [Fintype VA] [Fintype W] [Fintype U] [Fintype UA]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder VA] [LinearOrder W]
  [DecidableEq U] [DecidableEq UA]

theorem marked_inner_factor_active_restriction
    (f:VA↪oV) (i:W↪oVA) (g:UA↪U) (P:SimpleGraph V) (ρ:Equiv.Perm W)
    (d r:ℕ) (D p k s₀ t eta beta:ℝ) (weight:(Fin (r+4+1)→W)→ℝ)
    (Q:UA→Γ→ℝ) (S:UA→Color→ℝ) (a:Γ) (c:Color)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hrows:MarkedRowsWithSpokes (P.comap (fun x:W=>f (i x))) ρ d 1 Finset.univ p k Q S a c
      ((t/2)*Fintype.card W) (rawMarkedRestrictPair (fun x:W=>f (i x)) g σ) (fun b x u=>H b (f (i x)) (g u)))
    (hconfigs:MarkedLocalConfigurationsWithSpokes r (P.comap (fun x:W=>f (i x))) ρ d Finset.univ beta beta
      (rawMarkedRestrictPair (fun x:W=>f (i x)) g σ) (fun b x u=>H b (f (i x)) (g u)))
    (hload:MarkedLocalSpokeLoadsWithSpokes (P.comap (fun x:W=>f (i x))) ρ d (r+4) D p k s₀ weight eta
      (rawMarkedRestrictPair (fun x:W=>f (i x)) g σ) (fun b x u=>H b (f (i x)) (g u))):
    let σA:=rawMarkedRestrictPair f g σ
    let HA:=fun b x u=>H b (f x) (g u);
    MarkedRowsWithSpokes ((P.comap f).comap i) ρ d 1 Finset.univ p k Q S a c
      ((t/2)*Fintype.card W) (rawMarkedRestrictVertices i σA) (fun b x u=>HA b (i x) u)∧
    MarkedLocalConfigurationsWithSpokes r ((P.comap f).comap i) ρ d Finset.univ beta beta
      (rawMarkedRestrictVertices i σA) (fun b x u=>HA b (i x) u)∧
    MarkedLocalSpokeLoadsWithSpokes ((P.comap f).comap i) ρ d (r+4) D p k s₀ weight eta
      (rawMarkedRestrictVertices i σA) (fun b x u=>HA b (i x) u):=by
  intro σA HA
  have hP:((P.comap f).comap i)=P.comap (fun x:W=>f (i x)):=by ext x y;rfl
  have hσ:rawMarkedRestrictVertices i σA=rawMarkedRestrictPair (fun x:W=>f (i x)) g σ:=
    rawMarkedRestrictVertices_pair_comp f i g σ
  rw [hP,hσ]
  exact ⟨hrows,hconfigs,hload⟩

end Oberwolfach
