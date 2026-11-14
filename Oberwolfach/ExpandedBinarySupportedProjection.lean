module

public import Oberwolfach.FiniteLawSupportProbabilityMono
public import Oberwolfach.ExpandedBinaryColourProjection

@[expose] public section
/-! Project a supported common event to the original binary class colouring,
preserving a conclusion uniform over every later admissible choice. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_binary_common_event_on_support
    {V U Γ Color X Y:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)→Prop) (admissible:(Sym2 V→Fin 2)→X→Prop)
    (conclusion:(Sym2 V→Fin 2)→X→Y→Prop):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    (∀z,0<(μ.sigma ν).mass z→E z→∀x,
      admissible (fun e=>(expandedBinaryClass (z.1 (Sum.inl e))).1) x→
      ∃y,conclusion (fun e=>(expandedBinaryClass (z.1 (Sum.inl e))).1) x y)→
    (μ.sigma ν).probability E≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categorical (expandedBinaryProbability p k p₂ k₂ u)
        (expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
        (expanded_binary_probability_sum p k p₂ k₂ u))).probability
        (fun γ=>∀x,admissible γ x→∃y,conclusion γ x y) := by
  intro μ hE
  rw [←expanded_binary_colour_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν]
  exact finiteLaw_probability_mono_on_support (μ.sigma ν) E _ hE
end Oberwolfach
