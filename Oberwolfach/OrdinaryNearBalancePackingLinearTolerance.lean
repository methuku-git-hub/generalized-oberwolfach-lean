module

public import Oberwolfach.OrdinaryExplicitPackingToleranceLinear

@[expose] public section
/-! A cleanup tolerance chosen later retains a uniform linear lower bound
for the balance tolerance used in ordinary near-balanced packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_near_balance_wheel_packing_linear_tolerance (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ k : ℕ,N≤k → ∀ ω β bminus bplus h δ : ℝ,
      0<ω → 0<β → 0<bminus → 0<bplus → 0<h → 0<δ → δ<1/4 →
      ∃ εstar cLinear : ℝ,0<εstar ∧ 0<cLinear ∧ ∀ γ : ℝ,0<γ → γ≤1 →
      ∃ η : ℝ,0<η ∧ cLinear*γ≤η ∧ ∃ n₀ : ℕ,
      ∀ (V U : Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
      ∀ (P Q F : SimpleGraph V) (H : V → U → Prop) (A : V → V → ℕ),
      Q≤P\F → (∀ x y,A x y+A y x=if Q.Adj x y then 1 else 0) →
      BipartiteLargeCut A δ h → BipartiteLargeCut (fun v u=>if H v u then 1 else 0) δ h →
      (∀ v,β*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ)) →
      (∀ v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V) →
      (∀ x y,Q.Adj x y → β*(Fintype.card V:ℝ)^(k-1)≤
        (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k (max (1/2) (cycleThreshold r)) (α/4) x y):ℝ)) →
      (∀ v (i j : {u // H v u}),i.val≠j.val → β*(Fintype.card V:ℝ)^(r^2)≤
        (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)) →
      ∀ w : OrdinaryWheel Q F H r → ℝ,
      (∀ W,bminus/(Fintype.card V:ℝ)^(r-1)≤w W ∧ w W≤bplus/(Fintype.card V:ℝ)^(r-1)) →
      (∀ x y,Q.Adj x y → |ordinaryRimLoad w x y-1|≤εstar) →
      (∀ v u,H v u → |ordinarySpokeLoad w v u-1|≤εstar) →
      ∃ M : Finset (OrdinaryWheel Q F H r),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      ∀ x : V⊕U,((ordinaryIncidentEdges Q H x \ M.biUnion ordinaryActiveResources).card:ℝ)≤
        γ*Fintype.card V := by
  obtain ⟨N,hN⟩:=ordinary_near_balance_wheel_packing_explicit r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β bminus bplus h δ hω hβ hbm hbp hh hδ hδsmall
  obtain ⟨εstar,cStar,hε,hc,hpack⟩:=hN k hk ω β bminus bplus h δ hω hβ hbm hbp hh hδ hδsmall
  let c:=ordinaryPackingLinearConstant h β cStar r
  have hcpos:0<c:=by
    have hhlin:=ordinary_explicit_packing_tolerance_linear r (by omega) δ ω h β cStar 0 hδ hω hh hβ hc (by norm_num) (by norm_num)
    exact hhlin.1
  refine ⟨εstar,δ*ω*c/1000,hε,by positivity,?_⟩
  intro γ hγ hγone
  let ξ:=min (min (h/100) (γ/20)) (min (β/160) (min (β/(100*(r:ℝ)^4)) cStar))
  let η:=δ*ω*ξ/1000
  obtain ⟨hη,n₀,hN⟩:=hpack γ hγ
  have hlin:=ordinary_explicit_packing_tolerance_linear r (by omega) δ ω h β cStar γ hδ hω hh hβ hc hγ.le hγone
  exact ⟨η,hη,hlin.2,n₀,hN⟩
end Oberwolfach
