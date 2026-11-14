module

public import Oberwolfach.OrdinaryFullHostSeedMeans
public import Oberwolfach.OrdinarySeedNormalization

@[expose] public section

/-! The positive seed coefficient bounds have no dependence on the later
interval parameter. The original parent cycle coefficients are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
namespace Oberwolfach
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (P F : SimpleGraph V) (r : ℕ) (hr : 2≤r)
    (weight : OrdinaryCycle P r → ℝ) (pR pH ω p c B : ℝ)
    (hn : 0<Fintype.card V) (hm : 0<Fintype.card U)
    (hω : 0<ω) (hp : 0<p)
    (hmlo : ω*(Fintype.card V:ℝ)≤Fintype.card U) (hmhi : Fintype.card U≤Fintype.card V)
    (hRlo : p≤pR) (hRhi : pR≤1) (hHlo : p≤pH) (hHhi : pH≤1)
    (hc : 0≤c) (hB : 0≤B)
    (hw : ∀ C,c/(Fintype.card V:ℝ)^(r-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(r-2))
include hr hn hm hω hp hmlo hmhi hRlo hRhi hHlo hHhi hc hB hw

theorem ordinaryFullHostSeed_bounds (W : OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r) :
    c/(Fintype.card V:ℝ)^(r-1)≤ordinaryFullHostSeed P F r weight pR pH W ∧
    ordinaryFullHostSeed P F r weight pR pH W≤(B/(ω*p^(2*r-1)))/(Fintype.card V:ℝ)^(r-1) := by
  exact ordinary_seed_coefficient_bounds r hr (Fintype.card V) (Fintype.card U) ω p pR pH c B (weight W.val.1)
    (by exact_mod_cast hn) (by exact_mod_cast hm) hω hp hmlo (by exact_mod_cast hmhi)
    hRlo hRhi hHlo hHhi hc hB (hw W.val.1).1 (hw W.val.1).2

theorem ordinaryFullHostSeed_nonneg_upper (W : OrdinaryWheel P F (fun _ : V=>fun _ : U=>True) r) :
    0≤ordinaryFullHostSeed P F r weight pR pH W ∧
    ordinaryFullHostSeed P F r weight pR pH W≤(B/(ω*p^(2*r-1)))/(Fintype.card V:ℝ)^(r-1) := by
  have hh := ordinaryFullHostSeed_bounds P F r hr weight pR pH ω p c B hn hm hω hp hmlo hmhi
    hRlo hRhi hHlo hHhi hc hB hw W
  exact ⟨(by positivity : 0≤c/(Fintype.card V:ℝ)^(r-1)).trans hh.1,hh.2⟩

end Oberwolfach
