module

public import Oberwolfach.SignedCycleRestriction
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Lifting a signed cycle isolator inside S to wheels at a fixed hub.
The map is injective, so its coefficient bound is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def isolatorWheel {V U : Type*} (P Q F : SimpleGraph V) (H : V → U → Prop)
    (r : ℕ) (S : Finset V) (u : U)
    (hQ : spanningRestriction P S≤Q) (hH : ∀ v∈S,H v u)
    (hF : ∀ x∈S,∀ y∈S,¬F.Adj x y)
    (C : OrdinaryCycle (spanningRestriction P S) r) : OrdinaryWheel Q F H r :=
  ⟨(⟨C.val,C.property.trans hQ⟩,u),by
    have hs : C.val.val.support⊆(S:Set V) :=
      (SimpleGraph.support_mono C.property).trans (spanningRestriction_support P S)
    exact ⟨fun v hv => hH v (hs hv),fun x hx y hy => hF x (hs hx) y (hs hy)⟩⟩

theorem isolatorWheel_injective {V U : Type*} (P Q F : SimpleGraph V) (H : V → U → Prop)
    (r : ℕ) (S : Finset V) (u : U)
    (hQ : spanningRestriction P S≤Q) (hH : ∀ v∈S,H v u)
    (hF : ∀ x∈S,∀ y∈S,¬F.Adj x y) :
    Function.Injective (isolatorWheel P Q F H r S u hQ hH hF) := by
  intro C D h
  have he := congrArg ordinaryWheelRim h
  exact Subtype.ext (Subtype.ext he)

theorem signed_isolator_wheel_lift {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    (P Q F : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (S : Finset V) (u : U)
    (hQ : spanningRestriction P S≤Q) (hH : ∀ v∈S,H v u)
    (hF : ∀ x∈S,∀ y∈S,¬F.Adj x y) (x y : V)
    (I : SimpleGraph V → ℝ)
    (hs : ∀ C,I C≠0 → C≤spanningRestriction P S ∧ IsEmbeddedCycle C r)
    (hb : ∀ C,|I C|≤1)
    (he : ∀ a b,(∑ C,if C.Adj a b then I C else 0)=
      if (SimpleGraph.edge x y).Adj a b then 1 else 0)
    (hv : ∀ z,(∑ C,if z∈C.support then I C else 0)=
      (1/2:ℝ)*(if z=x ∨ z=y then 1 else 0)) :
    ∃ ψ : OrdinaryWheel Q F H r → ℝ,
      (∀ D,|ψ D|≤1) ∧
      (∀ D,ψ D≠0 → ordinaryWheelHub D=u ∧ (ordinaryWheelRim D).support⊆(S:Set V)) ∧
      (∀ a b,ordinaryRimLoad ψ a b=if (SimpleGraph.edge x y).Adj a b then 1 else 0) ∧
      (∀ z h,ordinarySpokeLoad ψ z h=
        (if h=u then (1:ℝ) else 0)*(1/2)*(if z=x ∨ z=y then 1 else 0)) := by
  let W := isolatorWheel P Q F H r S u hQ hH hF
  let a (C : OrdinaryCycle (spanningRestriction P S) r) := I C.val.val
  let ψ := indexedWheelWeight W a
  refine ⟨ψ,fun D => indexedWheelWeight_injective_bound W
    (isolatorWheel_injective P Q F H r S u hQ hH hF) a 1 (by norm_num) (fun C => hb _) D,?_,?_,?_⟩
  · intro D hD
    have hex : ∃ C,W C=D := by
      by_contra hn
      apply hD
      unfold ψ indexedWheelWeight
      apply Finset.sum_eq_zero
      intro C _
      exact if_neg (fun hC => hn ⟨C,hC⟩)
    obtain ⟨C,rfl⟩ := hex
    exact ⟨rfl,(SimpleGraph.support_mono C.property).trans (spanningRestriction_support P S)⟩
  · intro v w
    rw [indexedWheelWeight_rim]
    have hh := signed_cycle_test_restrict (spanningRestriction P S) r I
      (fun C => if C.Adj v w then (1:ℝ) else 0) hs
    calc
      _ = ∑ C : SimpleGraph V,I C*(if C.Adj v w then (1:ℝ) else 0) := hh
      _ = _ := by simpa only [mul_ite,mul_one,mul_zero] using he v w
  · intro z h
    rw [indexedWheelWeight_fixed_hub W a u (fun _ => rfl)]
    have hh := signed_cycle_test_restrict (spanningRestriction P S) r I
      (fun C => if z∈C.support then (1:ℝ) else 0) hs
    have hvertex : (∑ C : OrdinaryCycle (spanningRestriction P S) r,
        a C*(if z∈(ordinaryWheelRim (W C)).support then (1:ℝ) else 0))=
        (1/2:ℝ)*(if z=x ∨ z=y then 1 else 0) := by
      calc
        _ = ∑ C : SimpleGraph V,I C*(if z∈C.support then (1:ℝ) else 0) := hh
        _ = _ := by simpa only [mul_ite,mul_one,mul_zero] using hv z
    rw [hvertex]
    simp only [eq_comm]
    ring

end Oberwolfach
