module

public import Oberwolfach.RetentionDirectionLaw
public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section

/-! The physical marginal of the original wheel experiment, after adding
independent directions, is exactly a retained and oriented graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawWheel_orientation_probability
    {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P : SimpleGraph V) (p : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (E : (V→V→ℕ)→Prop) :
    ((FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>hp) (fun _=>hp1)
      d hd q hq hQ s hs hS)).prod
      (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin))).probability
      (fun z=>E (sampledOrientation (rawWheelGraph P z.1) z.2))=
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection (retentionColourProbability p)
      (retentionColourProbability_nonneg p hp hp1) (retentionColourProbability_sum p))).probability
      (fun σ=>E (sampledColourOrientation P σ 0)) := by
  let μ := rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin)
  have hh := finiteLaw_prod_map_left_probability (FiniteLaw.pi μ) ν (fun σ e=>σ (Sum.inl e))
    (fun c b=>E (sampledOrientation (retainedGraph P c) b))
  rw [finiteLaw_pi_injective_projection μ Sum.inl Sum.inl_injective] at hh
  change ((FiniteLaw.pi μ).prod ν).probability
    (fun z=>E (sampledOrientation (rawWheelGraph P z.1) z.2))=
    ((FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.retentionCoin p hp hp1)).prod ν).probability
      (fun z=>E (sampledOrientation (retainedGraph P z.1) z.2)) at hh
  exact hh.trans (retention_orientation_probability P p hp hp1 E)

end Oberwolfach
