module

public import Oberwolfach.ThinnedMarkedLaw

@[expose] public section

/-! Exact two-exposure form of the marked experiment with thinning coins.
First expose pair coordinates and coins, then the original categorical
physical-edge states. This is an equality of laws, not only of marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

abbrev ThinnedMarkedPairOutcome (V U Γ Color : Type) :=
  RawIntervalFamilyOutcome V U Γ Color × (V→Bool)

def thinnedMarkedJoin (ρ : ThinnedMarkedPairOutcome V U Γ Color)
    (τ : Sym2 V→Option (Bool×Bool)) : ThinnedMarkedOutcome V U Γ Color
  | Sum.inl (Sum.inl e)=>τ e
  | Sum.inl (Sum.inr e)=>ρ.1 e
  | Sum.inr v=>ρ.2 v

def thinnedMarkedPairPart (σ : ThinnedMarkedOutcome V U Γ Color) : ThinnedMarkedPairOutcome V U Γ Color :=
  (fun e=>σ (Sum.inl (Sum.inr e)),fun v=>σ (Sum.inr v))

def thinnedMarkedPhysicalPart (σ : ThinnedMarkedOutcome V U Γ Color) : Sym2 V→Option (Bool×Bool) :=
  fun e=>σ (Sum.inl (Sum.inl e))

theorem thinnedMarkedJoin_parts (σ : ThinnedMarkedOutcome V U Γ Color) :
    thinnedMarkedJoin (thinnedMarkedPairPart σ) (thinnedMarkedPhysicalPart σ)=σ := by
  funext e
  rcases e with (e|e)|e <;> rfl

def thinnedMarkedPairLaw (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) : FiniteLaw (ThinnedMarkedPairOutcome V U Γ Color) :=
  (FiniteLaw.pi (rawIntervalFamilyLaw d hd q hq hQ s hs hS)).prod
    (FiniteLaw.pi (fun _ : V=>FiniteLaw.retentionCoin θ hθ hθ1))

theorem thinnedMarked_two_exposures
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (E : ThinnedMarkedOutcome V U Γ Color→Prop) :
    (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability E=
      ((thinnedMarkedPairLaw d hd q hq hQ s hs hS θ hθ hθ1).prod
        (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hphys))).probability
        (fun z=>E (thinnedMarkedJoin z.1 z.2)) := by
  let e : ThinnedMarkedOutcome V U Γ Color≃
      (ThinnedMarkedPairOutcome V U Γ Color×(Sym2 V→Option (Bool×Bool))) :=
    { toFun := fun σ=>((fun a=>σ (Sum.inl (Sum.inr a)),fun v=>σ (Sum.inr v)),fun a=>σ (Sum.inl (Sum.inl a)))
      invFun := fun z=>thinnedMarkedJoin z.1 z.2
      left_inv := by intro σ;funext a;rcases a with (a|a)|a <;> rfl
      right_inv := by intro z;rcases z with ⟨⟨σ,κ⟩,τ⟩;rfl }
  unfold FiniteLaw.probability
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  change (if E (thinnedMarkedJoin z.1 z.2) then
    ∏ a,(thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1 a).mass
      (thinnedMarkedJoin z.1 z.2 a) else 0)=
    if E (thinnedMarkedJoin z.1 z.2) then
      ((∏ a,(rawIntervalFamilyLaw d hd q hq hQ s hs hS a).mass (z.1.1 a))*
        (∏ v : V,(FiniteLaw.retentionCoin θ hθ hθ1).mass (z.1.2 v)))*
      (∏ a : Sym2 V,(markedPhysicalLaw p k hp hk hphys).mass (z.2 a)) else 0
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp only [thinnedMarkedLaw,rawMarkedWheelLaw,thinnedMarkedJoin]
  split_ifs <;> ring

theorem thinnedMarked_first_probability
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (E : ThinnedMarkedPairOutcome V U Γ Color→Prop) :
    (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability
      (fun σ=>E (thinnedMarkedPairPart σ))=
      (thinnedMarkedPairLaw d hd q hq hQ s hs hS θ hθ hθ1).probability E := by
  rw [thinnedMarked_two_exposures p k hp hk hphys d hd q hq hQ s hs hS θ hθ hθ1]
  exact finiteLaw_prod_first_probability _ _ E

end Oberwolfach
