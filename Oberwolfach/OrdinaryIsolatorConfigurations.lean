module

public import Oberwolfach.SignedIsolatorOnSubset
public import Oberwolfach.OrdinaryIsolatorLift
public import Oberwolfach.FixedSubsets

@[expose] public section

/-! The bounded induced subgraphs used in rim isolation. The configuration
records its hub and vertex set; all graph and minimum-degree conditions are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure OrdinaryIsolatorConfiguration {V U : Type*} [Fintype V] [DecidableEq V]
    (P Q F : SimpleGraph V) (H : V → U → Prop) (k : ℕ) (θ α : ℝ) (x y : V) where
  hub : U
  vertices : FixedSubset V k
  endpoints : x∈vertices.val ∧ y∈vertices.val
  rim_edges : spanningRestriction P vertices.val≤Q
  spokes : ∀ z∈vertices.val,H z hub
  independent : ∀ z∈vertices.val,∀ w∈vertices.val,¬F.Adj z w
  density : ∀ z∈vertices.val,(θ+α)*k≤((P.neighborFinset z∩vertices.val).card:ℝ)

theorem OrdinaryIsolatorConfiguration.encoding_injective {V U : Type*} [Fintype V] [DecidableEq V]
    {P Q F : SimpleGraph V} {H : V → U → Prop} {k : ℕ} {θ α : ℝ} {x y : V} :
    Function.Injective (fun T : OrdinaryIsolatorConfiguration P Q F H k θ α x y => (T.hub,T.vertices)) := by
  intro T T' h
  have hu := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  cases T
  cases T'
  cases hu
  cases hs
  rfl

instance {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {P Q F : SimpleGraph V} {H : V → U → Prop} {k : ℕ} {θ α : ℝ} {x y : V} :
    Fintype (OrdinaryIsolatorConfiguration P Q F H k θ α x y) :=
  Fintype.ofInjective _ OrdinaryIsolatorConfiguration.encoding_injective

theorem ordinary_isolator_configuration_weights (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V U : Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (P Q F : SimpleGraph V) (H : V → U → Prop) (k : ℕ),N≤k →
      ∀ θ : ℝ,cycleThreshold r≤θ → ∀ x y,P.Adj x y →
      ∀ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
      ∃ ψ : OrdinaryWheel Q F H r → ℝ,
        (∀ D,|ψ D|≤1) ∧
        (∀ D,ψ D≠0 → ordinaryWheelHub D=T.hub ∧ (ordinaryWheelRim D).support⊆(T.vertices.val:Set V)) ∧
        (∀ a b,ordinaryRimLoad ψ a b=if (SimpleGraph.edge x y).Adj a b then 1 else 0) ∧
        (∀ z h,ordinarySpokeLoad ψ z h=
          (if h=T.hub then (1:ℝ) else 0)*(1/2)*(if z=x ∨ z=y then 1 else 0)) := by
  obtain ⟨N,hN⟩ := signed_cycle_edge_isolator_on_subset r hr α hα
  refine ⟨N,?_⟩
  intro V U _ _ _ _ P Q F H k hk θ hθ x y hxy T
  obtain ⟨I,hs,hb,he,hv⟩ := hN V P T.vertices.val (by simpa only [T.vertices.property] using hk) (by
    intro z hz
    have hh := T.density z hz
    rw [T.vertices.property]
    nlinarith [mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg (α:=ℝ) k)])
    x y T.endpoints.1 T.endpoints.2 hxy
  exact signed_isolator_wheel_lift P Q F H r T.vertices.val T.hub
    T.rim_edges T.spokes T.independent x y I hs hb he hv

end Oberwolfach
