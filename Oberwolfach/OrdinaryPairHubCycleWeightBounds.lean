module

public import Oberwolfach.OrdinaryLocalCycleWeightBounds
public import Oberwolfach.PairHubDensityBounds
public import Oberwolfach.OrdinaryPairHubLocalDegreeHigh

@[expose] public section
/-! One fixed pair-independent bound for all two-hub local cycle coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] {r:ℕ}
theorem ordinary_pair_hub_cycle_weight_bounds
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (j:Color) (s:U→Color→ℝ) (p pmin smin a b D:ℝ)
    (hr:2≤r) (hn:0<(Fintype.card V:ℝ))
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1) (hsmin:0<smin)
    (hslo:∀ u,smin≤s u j) (hshi:∀ u,s u j≤1) (ha:0≤a) (hb:0≤b)
    (weight:OrdinaryCycle P r→ℝ)
    (hwlo:∀ C,a/(Fintype.card V:ℝ)^(r-2)≤weight C)
    (hwhi:∀ C,weight C≤b/(Fintype.card V:ℝ)^(r-2)):
    let cmin:=pmin^r*(smin*smin)^(r-1);
    ∀ u u',
    let Q:=rawWheelGraph P σ\F
    let H:=ordinaryPairHubSpokes π d σ j u u'
    let T:=Finset.univ.filter (fun z=>H z ())
    let hQP:Q≤P:=sdiff_le.trans (retainedGraph_le P (fun e=>σ (Sum.inl e)))
    let c:=p^r*(s u j*s u' j)^(r-1);
    ∀ C:LocalOrdinaryCycle Q F T r,
      a/(Fintype.card V:ℝ)^(r-1)≤weight (localOrdinaryParent hQP C)/(D/2)/c ∧
      weight (localOrdinaryParent hQP C)/(D/2)/c≤(4*b/cmin)/(Fintype.card V:ℝ)^(r-1) := by
  intro cmin u u' Q H T hQP c C
  have hc:=pair_hub_density_bounds r p pmin (s u j) (s u' j) smin hpmin hp hp1 hsmin
    (hslo u) (hslo u') (hshi u) (hshi u')
  exact ordinary_local_cycle_weight_bounds P Q F T hQP weight D c cmin a b hr hn hDlo hDhi
    hc.1 hc.2.1 hc.2.2 ha hb hwlo hwhi C
end Oberwolfach
