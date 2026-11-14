module

public import Oberwolfach.ExpandedDensityOneClassFromSample
public import Oberwolfach.GroupedRegularClassTransfer

@[expose] public section
/-! In the density-one branch the positive-mass sample itself supplies the
regular class, preserving every protected edge and requiring no edits. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_density_one_protected_regular_class
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hone:2*p+2*k+2*p₂+2*k₂+u=1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (P Z:SimpleGraph V) (kclass:ℕ) (hreg:P.IsRegularOfDegree (2*kclass))
    (ξ:ℝ) (hξ:0≤ξ) (z:Σσ,R σ)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).mass z):
    ∀A:SimpleGraph V, ∃S:SimpleGraph V, S≤P ∧ S.IsRegularOfDegree (2*kclass) ∧
      (∀x y,(Z⊔A).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*Fintype.card V):=by
  have hclass:=expanded_density_one_class_eq_host p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hone d hd q hq hQ s hs hS ν P z hpos
  intro A
  refine ⟨P,le_rfl,hreg,?_,?_⟩
  · intro x y h; rw [hclass]
  · intro v
    rw [hclass]
    simp only [changed, Finset.sdiff_self, Finset.union_empty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hξ (Nat.cast_nonneg _)
end Oberwolfach
