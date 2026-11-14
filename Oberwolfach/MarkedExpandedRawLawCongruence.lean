module

public import Oberwolfach.MarkedExpandedRawLaw

@[expose] public section
/-! Replacing interval and spoke functions by equal functions leaves the
expanded product law unchanged. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem marked_expanded_raw_law_congr (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q q':U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (hq':∀u g,0≤q' u g) (hQ':∀u,∑g,q' u g≤1/8)
    (s s':U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hs':∀u j,0≤s' u j)
    (hS':∀u,∑j,s' u j≤ intervalUncoveredProbability d (∑g,q' u g))
    (hqeq:q=q') (hseq:s=s'):
    rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS =
    rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q' hq' hQ' s' hs' hS' :=by
  subst q'
  subst s'
  rfl
end Oberwolfach
