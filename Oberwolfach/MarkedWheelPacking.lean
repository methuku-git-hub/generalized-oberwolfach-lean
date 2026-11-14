module

public import Oberwolfach.FractionalResourceMatching
public import Oberwolfach.MarkedIncidentResources
public import Oberwolfach.MarkedWheelPairLoads

@[expose] public section

/-! Marked-wheel packing with simultaneous auxiliary and physical leftover
bounds. Both families of incident-edge sets are fixed before one matching
is selected, and the supplied permutation and wheel weights are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_wheel_packing_bounded_hubs (m : ℕ) (hm : 3≤m)
    (C γ : ℝ) (hC : 0<C) (hγ : 0<γ) :
    ∃ n₀ : ℕ,∀ (V U E K : Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) (b : ℕ)
      (H₀ Hₖ : V → U → Prop),
      Function.Injective (markedPhysicalEdge tail head ktail khead π) →
      (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    ∀ (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ),
      (∀ W,0≤w W ∧ w W≤C/(Fintype.card V : ℝ)^m) →
      (∀ e,markedWheelRimLoad w e=1) →
      (∀ j v u,markedWheelSpokeLoad w j v u=
        if j then (if Hₖ v u then 1 else 0) else (if H₀ v u then 1 else 0)) →
    ∃ M : Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x : V⊕U,((markedIncidentEdges tail head ktail khead π H₀ Hₖ false x \
        M.biUnion markedActiveResources).card : ℝ)≤γ*Fintype.card V) ∧
      (∀ x : V⊕U,((markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x \
        M.biUnion markedWheelPhysicalResources).card : ℝ)≤γ*Fintype.card V) := by
  classical
  let ε := min (1/2) (γ/10)
  have hε : 0<ε := lt_min (by norm_num) (by positivity)
  have hεγ : ε≤γ/10 := min_le_right _ _
  obtain ⟨η,hη,N,hN⟩ := fractional_resource_matching (2*(m+1)) 3 (by omega) (by omega)
    (((m : ℝ)+1)^4*C) (γ/2) ε (by positivity) (by positivity) hε
  refine ⟨max N 4,?_⟩
  intro V U E K _ _ _ _ _ _ hn hu tail head ktail khead π b H₀ Hₖ hp hdisj w hw hrim hspoke
  let n := Fintype.card V
  have hn4 : 4≤n := (le_max_right _ _).trans hn
  have hn0 : 0<n := by omega
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn0
  let R := markedActiveResources (tail:=tail) (head:=head) (ktail:=ktail)
    (khead:=khead) (π:=π) (m:=m) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ)
  let S₀ (i : Bool×(V⊕U)) := markedIncidentEdges tail head ktail khead π H₀ Hₖ i.1 i.2
  let I := {i : Bool×(V⊕U) // (γ/2)*(n : ℝ)≤(S₀ i).card}
  let S (i : I) := S₀ i.val
  have hI : Fintype.card I≤n^3 := by
    have hh := Fintype.card_subtype_le (fun i : Bool×(V⊕U)=>(γ/2)*(n : ℝ)≤(S₀ i).card)
    simp only [Fintype.card_prod,Fintype.card_sum,Fintype.card_bool] at hh
    change Fintype.card I≤2*(n+Fintype.card U) at hh
    have hu' : Fintype.card U≤n := hu
    calc
      _ ≤ 4*n := by omega
      _ ≤ n*n := Nat.mul_le_mul_right n hn4
      _ = n^2 := (pow_two n).symm
      _ ≤ n^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hRcard : Fintype.card (MarkedActiveEdge E K H₀ Hₖ)≤n^3 := by
    have hh := markedActiveEdge_card_bound tail head ktail khead π H₀ Hₖ hp
    change _≤2*n^2+n*Fintype.card U at hh
    have hu' : Fintype.card U≤n := hu
    have hprod := Nat.mul_le_mul_left n hu'
    have hn3 : 3≤n := by omega
    calc
      _ ≤ 3*n^2 := by nlinarith
      _ ≤ n*n^2 := Nat.mul_le_mul_right (n^2) hn3
      _ = n^3 := by ring
  have hdegree (e : MarkedActiveEdge E K H₀ Hₖ) :
      1-η≤hypergraphWeightedDegree R w e ∧ hypergraphWeightedDegree R w e≤1+η := by
    have he := marked_active_exact_loads hp hdisj w hrim hspoke e
    change hypergraphWeightedDegree R w e=1 at he
    rw [he]
    constructor <;> linarith
  obtain ⟨M,hM,hleft,_,_⟩ := hN n ((le_max_left _ _).trans hn)
    (MarkedActiveEdge E K H₀ Hₖ) (MarkedWheel tail head ktail khead m π b H₀ Hₖ) Empty I
    R w (fun i=>Empty.elim i) S hRcard (by simp) hI
    (fun W=>by rw [markedActiveResources_card hp];exact ⟨by omega,le_refl _⟩)
    (fun W=>(hw W).1) hdegree
    (fun e f hef=>marked_wheel_active_pair_load hm hp hn0 hu w C hC.le (fun W=>(hw W).2) e f hef)
    (fun i=>i.property) (fun i=>Empty.elim i) (fun i=>Empty.elim i)
  have hboth (physical : Bool) (x : V⊕U) :
      ((markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x \
        M.biUnion R).card : ℝ)≤γ*n := by
    by_cases hx : (γ/2)*(n : ℝ)≤(S₀ (physical,x)).card
    · have hh := hleft ⟨(physical,x),hx⟩
      have hsize := markedIncidentEdges_card_bound tail head ktail khead π H₀ Hₖ hp physical x
      have hsizeR : ((S₀ (physical,x)).card : ℝ)≤5*n := by
        have hh' : (S₀ (physical,x)).card≤5*n := by
          change (markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x).card≤5*Fintype.card V
          omega
        exact_mod_cast hh'
      change ((S₀ (physical,x) \ M.biUnion R).card : ℝ)≤ε*(S₀ (physical,x)).card at hh
      change ((S₀ (physical,x) \ M.biUnion R).card : ℝ)≤γ*n
      have he := mul_le_mul_of_nonneg_right hεγ (Nat.cast_nonneg (S₀ (physical,x)).card)
      have hs := mul_le_mul_of_nonneg_left hsizeR (show 0≤γ/10 by positivity)
      nlinarith
    · have hh : ((S₀ (physical,x) \ M.biUnion R).card : ℝ)≤(S₀ (physical,x)).card := by
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s:=S₀ (physical,x)) (t:=M.biUnion R))
      change ((S₀ (physical,x) \ M.biUnion R).card : ℝ)≤γ*n
      nlinarith [lt_of_not_ge hx]
  refine ⟨M,markedActiveResources_matching_physical tail head ktail khead π H₀ Hₖ hp M hM,
    fun x=>hboth false x,?_⟩
  intro x
  rw [← marked_leftover_card_physical tail head ktail khead π H₀ Hₖ hp M x]
  exact hboth true x

end Oberwolfach
