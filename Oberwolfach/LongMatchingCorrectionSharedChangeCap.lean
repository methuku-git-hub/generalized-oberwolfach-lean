module

public import Oberwolfach.LongCorrectedChangeGraphEventualCap

@[expose] public section
/-! Apply the eventual numerical budget to the two physical change graphs
produced by the same matching and residual correction. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_matching_correction_shared_change_cap
    (d:ℕ) (θ a γ ξClass δglobal Δ ζSpoke rho eta cap:ℝ)
    (hζ:ζSpoke≤cap)
    (hgap:2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<cap):
    ∃N:ℕ,∀n:ℕ,N≤n→∀{U:Type} [Fintype U] [DecidableEq U]
      (FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)) (ηphys ηdel ηtype:ℝ),
      ηphys≤(2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal)*n+
        (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)→
      ηdel≤Δ*n→ηtype≤(1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)→
      (∀v,(FR.degree v:ℝ)≤ηphys+ηdel+ηtype)→
      (∀z,(FS.degree z:ℝ)≤ζSpoke*n)→
      (∀v,(FR.degree v:ℝ)≤cap*n) ∧ (∀z,(FS.degree z:ℝ)≤cap*n):=by
  obtain ⟨N,hN⟩:=long_corrected_change_graph_eventual_cap d θ a γ ξClass δglobal Δ ζSpoke rho eta cap hζ hgap
  refine ⟨N,?_⟩
  intro n hn U _ _ FR FS ηphys ηdel ηtype hp hd ht hFR hFS
  obtain ⟨hb,hsp⟩:=hN n hn
  constructor
  · intro v
    have hh:=hFR v
    linarith only [hp,hd,ht,hh,hb]
  · intro z
    exact (hFS z).trans hsp
end Oberwolfach
