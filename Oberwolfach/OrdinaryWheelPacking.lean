module

public import Oberwolfach.FractionalResourceMatching
public import Oberwolfach.OrdinaryIncidentResources

@[expose] public section

/-! A physical ordinary-wheel packing with a local leftover bound. This
version has at most as many hubs as rim vertices, as in the main assembly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_wheel_packing_bounded_hubs (r : ℕ) (hr : 3≤r)
    (C γ : ℝ) (hC : 0<C) (hγ : 0<γ) :
    ∃ n₀ : ℕ,∀ (V U : Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (Q F : SimpleGraph V) (H : V → U → Prop) (w : OrdinaryWheel Q F H r → ℝ),
      (∀ W,0≤w W ∧ w W≤C/(Fintype.card V : ℝ)^(r-1)) →
      (∀ x y,ordinaryRimLoad w x y=if Q.Adj x y then 1 else 0) →
      (∀ v u,ordinarySpokeLoad w v u=if H v u then 1 else 0) →
    ∃ M : Finset (OrdinaryWheel Q F H r),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
      ∀ x : V⊕U,((ordinaryIncidentEdges Q H x \ M.biUnion ordinaryActiveResources).card : ℝ)≤
        γ*Fintype.card V := by
  classical
  let ε := min (1/2) (γ/4)
  have hε : 0<ε := lt_min (by norm_num) (by positivity)
  have hεγ : ε≤γ/4 := min_le_right _ _
  have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  obtain ⟨η,hη,N,hN⟩ := fractional_resource_matching (2*r) 3 (by omega) (by omega)
    ((r : ℝ)^4*C) (γ/2) ε (by positivity) (by positivity) hε
  refine ⟨max N 2,?_⟩
  intro V U _ _ _ _ hn hu Q F H w hw hrim hspoke
  let n := Fintype.card V
  have hn2 : 2≤n := (le_max_right _ _).trans hn
  have hn0 : 0<n := by omega
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn0
  let R := ordinaryActiveResources (Q:=Q) (F:=F) (H:=H) (r:=r)
  let I := {x : V⊕U // (γ/2)*(n : ℝ)≤(ordinaryIncidentEdges Q H x).card}
  let S (i : I) := ordinaryIncidentEdges Q H i.val
  have hI : Fintype.card I≤n^3 := by
    have hh := Fintype.card_subtype_le (fun x : V⊕U=>(γ/2)*(n : ℝ)≤(ordinaryIncidentEdges Q H x).card)
    simp only [Fintype.card_sum] at hh
    change Fintype.card I≤_ at hh
    have hu' : Fintype.card U≤n := hu
    change Fintype.card I≤n^3
    change Fintype.card I≤n+Fintype.card U at hh
    calc
      _ ≤ 2*n := by omega
      _ ≤ n*n := Nat.mul_le_mul_right n hn2
      _ = n^2 := (pow_two n).symm
      _ ≤ n^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hRcard : Fintype.card (OrdinaryActiveEdge Q H)≤n^3 := by
    have hh := ordinaryActiveEdge_card_bound Q H
    change _≤n^2+n*Fintype.card U at hh
    have hu' : Fintype.card U≤n := hu
    nlinarith
  have hdegree (e : OrdinaryActiveEdge Q H) :
      1-η≤hypergraphWeightedDegree R w e ∧ hypergraphWeightedDegree R w e≤1+η := by
    have he := ordinary_active_exact_loads w hrim hspoke e
    change hypergraphWeightedDegree R w e=1 at he
    rw [he]
    constructor <;> linarith
  obtain ⟨M,hM,hleft,_,_⟩ := hN n ((le_max_left _ _).trans hn)
    (OrdinaryActiveEdge Q H) (OrdinaryWheel Q F H r) Empty I
    R w (fun i=>Empty.elim i) S hRcard (by simp) hI
    (fun W=>by rw [ordinaryActiveResources_card];exact ⟨by omega,le_refl _⟩)
    (fun W=>(hw W).1) hdegree
    (fun e f hef=>ordinary_active_pair_loads (by omega) hn0 hu w C hC.le hw e f hef)
    (fun i=>i.property) (fun i=>Empty.elim i) (fun i=>Empty.elim i)
  refine ⟨M,ordinaryActiveResources_matching_physical M hM,?_⟩
  intro x
  by_cases hx : (γ/2)*(n : ℝ)≤(ordinaryIncidentEdges Q H x).card
  · have hh := hleft ⟨x,hx⟩
    have hsize := ordinaryIncidentEdges_card_bound Q H x
    have hsizeR : ((ordinaryIncidentEdges Q H x).card : ℝ)≤2*n := by
      have hh' : (ordinaryIncidentEdges Q H x).card≤2*n := by
        change (ordinaryIncidentEdges Q H x).card≤2*Fintype.card V
        nlinarith
      exact_mod_cast hh'
    change ((ordinaryIncidentEdges Q H x \ M.biUnion R).card : ℝ)≤ε*(ordinaryIncidentEdges Q H x).card at hh
    change ((ordinaryIncidentEdges Q H x \ M.biUnion R).card : ℝ)≤γ*n
    have he := mul_le_mul_of_nonneg_right hεγ (Nat.cast_nonneg (ordinaryIncidentEdges Q H x).card)
    have hs := mul_le_mul_of_nonneg_left hsizeR (show 0≤γ/4 by positivity)
    nlinarith
  · have hh : ((ordinaryIncidentEdges Q H x \ M.biUnion R).card : ℝ)≤(ordinaryIncidentEdges Q H x).card := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s:=ordinaryIncidentEdges Q H x) (t:=M.biUnion R))
    change ((ordinaryIncidentEdges Q H x \ M.biUnion R).card : ℝ)≤γ*n
    nlinarith [lt_of_not_ge hx]

end Oberwolfach
