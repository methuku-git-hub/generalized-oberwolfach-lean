module

public import Oberwolfach.OrientationDisagreementGraph
public import Oberwolfach.OrientationMargins

@[expose] public section
/-! The orientation correction is absorbed by any previously chosen
positive linear deletion budget by increasing only the order threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem eventually_orientation_correction_le {δ:ℝ} (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→4*(n:ℝ)^(4/5:ℝ)≤δ*n:=by
  obtain ⟨N,hN⟩:=eventually_orientation_numeric hδ
  refine ⟨N,fun n hn=>?_⟩
  have h:=hN n hn
  have hpow:0≤(n:ℝ)^(3/5:ℝ):=Real.rpow_nonneg (by positivity) _
  have hceil:((n:ℝ)^(4/5:ℝ))≤Nat.ceil ((n:ℝ)^(4/5:ℝ)):=Nat.le_ceil _
  have hdiv:0≤(n:ℝ)*(n:ℝ)^(3/5:ℝ)/Nat.ceil ((n:ℝ)^(4/5:ℝ)):=by positivity
  have hδn:0≤δ*(n:ℝ):=by positivity
  nlinarith [h.2.2.1]

theorem orientation_disagreement_fits_deletion
    {V:Type} [Fintype V] [LinearOrder V] (G:SimpleGraph V) (bits:Sym2 V→Bool) (M:V→V→ℕ)
    (δ:ℝ) (hsize:∀v,((Finset.univ.filter (fun w=>M v w≠sampledOrientation G bits v w ∨
      M w v≠sampledOrientation G bits w v)).card:ℝ)≤4*(Fintype.card V:ℝ)^(4/5:ℝ))
    (hmargin:4*(Fintype.card V:ℝ)^(4/5:ℝ)≤δ*Fintype.card V):
    ∀v,((orientationDisagreementGraph G bits M).degree v:ℝ)≤δ*Fintype.card V:=by
  intro v
  have hdeg:=orientation_disagreement_degree_le G bits M v
  have hcast:((orientationDisagreementGraph G bits M).degree v:ℝ)≤
      ((Finset.univ.filter (fun w=>M v w≠sampledOrientation G bits v w ∨
        M w v≠sampledOrientation G bits w v)).card:ℝ):=by exact_mod_cast hdeg
  exact hcast.trans ((hsize v).trans hmargin)
end Oberwolfach
