module

public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteUniform

@[expose] public section
/-! At density one, the unused physical state has zero mass even after an
arbitrary retention law is sampled. Every positive-mass outcome therefore
places every physical edge in one of the first five states. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_density_one_support
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hone:2*p+2*k+2*p₂+2*k₂+u=1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (z:Σσ,R σ)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).mass z):
    ∀e:Sym2 V,(z.1 (Sum.inl e)).1≠5:=by
  intro e he
  have hzero:(rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS (Sum.inl e)).mass (z.1 (Sum.inl e))=0:=by
    simp [rawExpandedMarkedWheelLaw,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,he]
    linarith
  have hpizero:(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).mass z.1=0:=by
    change (∏i,(rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS i).mass (z.1 i))=0
    exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl e)) hzero
  change 0<(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).mass z.1 * (ν z.1).mass z.2 at hpos
  rw [hpizero,zero_mul] at hpos
  exact (lt_irrefl 0) hpos
end Oberwolfach
