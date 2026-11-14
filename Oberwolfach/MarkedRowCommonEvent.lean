module

public import Oberwolfach.MarkedRowCounts
public import Oberwolfach.BoundedFinsetCardinality
public import Oberwolfach.ConditionalRealization

@[expose] public section

/-! One original-law event for every marked row pattern of bounded size.
The finite enumeration is fixed before the sample; no new event is selected
when the roots or their parent-neighbour conditions are later used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def RawMarkedRows (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ)
    (A : Finset V) (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ)
    (g : Γ) (j : Color) (t : ℝ) (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  ∀ (S T : Finset (Bool×Bool×V)) (J : Finset (Bool×U)),
    S.card≤h → T.card≤h → J.card≤h → Set.InjOn (fun a : Bool×U=>a.2) J →
    |rawMarkedRowCount P π d (markedRowDomain P π (3*d) A S T) S J g j σ-
      (∏ a∈S,if a.1 then k else p)*(∏ a∈J,if a.1 then q a.2 g else s a.2 j)*
        (markedRowDomain P π (3*d) A S T).card|<t

theorem rawMarkedRows_common_event
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (A : Finset V) (hA : A.Nonempty) (h : ℕ) (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    1-(4*(Fintype.card V:ℝ)+1)^(2*h)*(2*(Fintype.card U:ℝ)+1)^h*
        (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(2*(2*(h:ℝ)+1)*A.card))))≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
        (RawMarkedRows P π d h A p k q s g j t) := by
  let RR := {S : Finset (Bool×Bool×V) // S.card≤h}
  let JJ := {J : Finset (Bool×U) // J.card≤h ∧ Set.InjOn (fun a : Bool×U=>a.2) J}
  let I := RR×RR×JJ
  let Bad := fun (i : I) (σ : RawMarkedOutcome V U Γ Color)=>t≤
    |rawMarkedRowCount P π d (markedRowDomain P π (3*d) A i.1.val i.2.1.val) i.1.val i.2.2.val g j σ-
      (∏ a∈i.1.val,if a.1 then k else p)*(∏ a∈i.2.2.val,if a.1 then q a.2 g else s a.2 j)*
        (markedRowDomain P π (3*d) A i.1.val i.2.1.val).card|
  let err := 2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(2*(2*(h:ℝ)+1)*A.card)))
  have htail (i : I) : (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability (Bad i)≤err := by
    have hh := rawMarkedRowCount_tail P π d hd p k hp hk hsum q hq hQ s hs hS hnoshort A hA
      i.1.val i.2.1.val i.2.2.val i.2.2.property.2 (2*h)
      (by have h1 := i.1.property;have h2 := i.2.2.property.1;omega) g j t ht
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  have hcardR : Fintype.card RR≤(4*Fintype.card V+1)^h := by
    have hh := boundedFinset_card (A:=Bool×Bool×V) h
    norm_num only [Fintype.card_prod,Fintype.card_bool,← Nat.mul_assoc] at hh
    exact hh
  have hcardJ : Fintype.card JJ≤(2*Fintype.card U+1)^h := by
    let f : JJ→{J : Finset (Bool×U) // J.card≤h} := fun a=>⟨a.val,a.property.1⟩
    have hf : Function.Injective f := by intro a b he;exact Subtype.ext (congrArg (fun a : {J : Finset (Bool×U) // J.card≤h}=>a.val) he)
    apply (Fintype.card_le_of_injective f hf).trans
    simpa only [Fintype.card_prod,Fintype.card_bool] using boundedFinset_card (A:=Bool×U) h
  have hcard : Fintype.card I≤(4*Fintype.card V+1)^(2*h)*(2*Fintype.card U+1)^h := by
    dsimp [I]
    rw [Fintype.card_prod,Fintype.card_prod]
    calc
      _≤(4*Fintype.card V+1)^h*((4*Fintype.card V+1)^h*(2*Fintype.card U+1)^h) := Nat.mul_le_mul hcardR (Nat.mul_le_mul hcardR hcardJ)
      _=_ := by rw [show 2*h=h+h by omega,pow_add];ring
  have hcard' : (Fintype.card I:ℝ)≤(4*(Fintype.card V:ℝ)+1)^(2*h)*(2*(Fintype.card U:ℝ)+1)^h := by exact_mod_cast hcard
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS))
    Finset.univ Bad (fun _=>err) (fun i _=>htail i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  apply (sub_le_sub_left (mul_le_mul_of_nonneg_right hcard' (by dsimp [err];positivity)) 1 |>.trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ S T J hSS hTT hJJ hJ
  exact not_le.mp (hσ (⟨S,hSS⟩,⟨T,hTT⟩,⟨J,hJJ,hJ⟩))

end Oberwolfach
