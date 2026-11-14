module

public import Oberwolfach.MarkedReferenceParentAndLocalLoad
public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section
/-! Apply the marked reference-load implication on a fixed vortex level,
with the original raw outcome and fixed weights restricted through its
actual vertex and hub embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z Γ Color:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
theorem marked_vortex_local_parent_loads_from_adaptive
    (P:SimpleGraph V) (f:W↪oV) (g:Z↪U) (ρ:Equiv.Perm W) (d r:ℕ)
    (rho t kappa theta τ εLoad ζLoad ζLocal ρstar sstar Bload Kload:ℝ)
    (weight:(Fin (r+4+1)→W)→ℝ) (a:Γ) (j:Color)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let Pi:=P.comap f
    let σi:=rawMarkedRestrictPair f g σ
    let Hi:=fun b x z=>H b (f x) (g z)
    let qi:=fun z=>q (g z)
    let si:=fun z=>s (g z)
    let base:=(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))
    let err:=τ+εLoad+11*base*Kload*ζLoad
    let localErr:=τ+εLoad+5*base*Kload*ζLocal
    let C:=33*base
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card Z/rho;
    err≤kappa/4 → localErr≤theta/4 →
    (∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph W) (DS:SimpleGraph (W⊕Z)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes Pi ρ d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight a j
        (Equiv.refl Z) qi si (err+C*δ/Fintype.card W)
        (rawMarkedDeleteRims σi DR.edgeFinset) (markedDeletePhysicalSpokes Hi DS)) →
    MarkedLocalSpokeLoadsWithSpokes Pi ρ d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight localErr σi Hi →
    let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd (r+4) ρ (3*d)
      (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weight X.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
    (∀ root,rawMarkedWheelMarginal Pi ρ d pRef kRef qi si a j root≠0 →
      |typedMarkedPotentialLoad seed (rawMarkedPairRims Pi ρ d σi) Hi root-1|≤kappa/4) ∧
    MarkedLocalSpokeLoadsWithSpokes Pi ρ d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weight (theta/4) σi Hi := by
  intro Pi σi Hi qi si base err localErr C pRef kRef DRef herr hlocal hpack hspoke seed
  exact marked_reference_parent_and_local_load_from_adaptive Pi ρ d r rho t kappa theta τ εLoad ζLoad ζLocal ρstar sstar Bload Kload weight a j qi si σi Hi herr hlocal hpack hspoke
end Oberwolfach
