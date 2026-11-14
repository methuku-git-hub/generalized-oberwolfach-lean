module

public import Oberwolfach.MarkedIndexCounts
public import Oberwolfach.BoundedFinsetCardinality
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section

/-! Simultaneous index estimates for all separated typed label sets of
bounded cardinality. The supplied hub-dependent marginals are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def RawMarkedIndices (π : Equiv.Perm V) (d h : ℕ) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (t : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  ∀ J : Finset (Bool×V),J.card≤h →
    (∀ a∈J,∀ b∈J,a≠b → ¬PermutationClose π (3*d) a.2 b.2) →
    |rawMarkedIndexCount π d B J g j σ-∑ u∈B,∏ a∈J,if a.1 then q u g else s u j|<t

theorem rawMarkedIndices_common_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (B : Finset U) (hB : B.Nonempty) (h : ℕ) (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    1-(2*(Fintype.card V:ℝ)+1)^h*
        (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((h:ℝ)+1)*B.card))))≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
        (RawMarkedIndices π d h B q s g j t) := by
  let I := {J : Finset (Bool×V) // J.card≤h ∧
    ∀ a∈J,∀ b∈J,a≠b → ¬PermutationClose π (3*d) a.2 b.2}
  let Bad := fun (J : I) (σ : RawMarkedOutcome V U Γ Color)=>t≤
    |rawMarkedIndexCount π d B J.val g j σ-∑ u∈B,∏ a∈J.val,if a.1 then q u g else s u j|
  let err := 2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((h:ℝ)+1)*B.card)))
  have htail (J : I) : (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability (Bad J)≤err :=
    rawMarkedIndexCount_tail ⊥ π d hd p k hp hk hsum q hq hQ s hs hS hnoshort B hB
      J.val J.property.2 h J.property.1 g j t ht
  have hcard : Fintype.card I≤(2*Fintype.card V+1)^h := by
    let f : I→{J : Finset (Bool×V) // J.card≤h} := fun a=>⟨a.val,a.property.1⟩
    have hf : Function.Injective f := by
      intro a b he
      exact Subtype.ext (congrArg (fun a : {J : Finset (Bool×V) // J.card≤h}=>a.val) he)
    apply (Fintype.card_le_of_injective f hf).trans
    simpa only [Fintype.card_prod,Fintype.card_bool] using boundedFinset_card (A:=Bool×V) h
  have hcard' : (Fintype.card I:ℝ)≤(2*(Fintype.card V:ℝ)+1)^h := by exact_mod_cast hcard
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS))
    Finset.univ Bad (fun _=>err) (fun J _=>htail J)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies] at hh
  apply (sub_le_sub_left (mul_le_mul_of_nonneg_right hcard' (by dsimp [err];positivity)) 1 |>.trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ J hJ hsep
  exact not_le.mp (hσ ⟨J,hJ,hsep⟩)

def markedIndicesExponent (h d : ℕ) (ε : ℝ) : ℝ :=
  2*ε^2/((8*(d:ℝ)+6)^2*((h:ℝ)+1))

theorem markedIndicesExponent_pos (h d : ℕ) (ε : ℝ) (hε : 0<ε) :
    0<markedIndicesExponent h d ε := by unfold markedIndicesExponent;positivity

theorem rawMarkedIndices_exponential_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (B : Finset U) (hB : B.Nonempty) (K ε : ℝ) (hK : 1≤K) (hε : 0<ε)
    (hV : (Fintype.card V:ℝ)≤K*B.card) (h : ℕ) (g : Γ) (j : Color) :
    1-2*(2*K+1)^h*(B.card:ℝ)^h*Real.exp (-markedIndicesExponent h d ε*B.card)≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
        (RawMarkedIndices π d h B q s g j (ε*B.card)) := by
  have hb : (0:ℝ)<B.card := by exact_mod_cast hB.card_pos
  have hb1 : (1:ℝ)≤B.card := by exact_mod_cast hB.card_pos
  have hcard : (2*(Fintype.card V:ℝ)+1)^h≤(2*K+1)^h*(B.card:ℝ)^h := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [hV,hb1]
  have herr := linear_deviation_failure_exponential ((2*K+1)^h)
    ((8*(d:ℝ)+6)^2*((h:ℝ)+1)) ε (by positivity) hε h B.card hB.card_pos
    ((2*(Fintype.card V:ℝ)+1)^h) ((8*(d:ℝ)+6)^2*(((h:ℝ)+1)*B.card))
    (by positivity) hcard (by positivity) (by exact le_of_eq (by ring))
  have hh := rawMarkedIndices_common_event π d hd p k hp hk hsum q hq hQ s hs hS hnoshort
    B hB h g j (ε*B.card) (by positivity)
  exact (sub_le_sub_left herr 1).trans hh

end Oberwolfach
