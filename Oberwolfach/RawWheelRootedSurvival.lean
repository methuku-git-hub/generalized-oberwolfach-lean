module

public import Oberwolfach.OrdinaryRawIntervalSampling
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.RootedConditionalRetention

@[expose] public section

/-! The two-exposure survival theorem in the original raw wheel product
law, preserving the possibly unequal physical-edge retention probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color J : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype J]
    [DecidableEq V] [DecidableEq U]

variable (P : SimpleGraph V)
    (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))

local notation "μwheel" => rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS
local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawWheelRootedSurvival_common_event
    {I : RawIntervalFamilyOutcome V U Γ Color → J → Type} [∀ ω j,Fintype (I ω j)] {k : ℕ}
    (S : ∀ ω j,I ω j → FixedSubset V k) (hinj : ∀ ω j,Function.Injective (S ω j))
    (x y : J → V) (hxy : ∀ j,x j≠y j) (hk : 4≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ ω j i,x j∈(S ω j i).val ∧ y j∈(S ω j i).val)
    (Good : RawIntervalFamilyOutcome V U Γ Color → Prop) (b : ℝ)
    (hgood : 1-b≤(FiniteLaw.pi μfamily).probability Good)
    (p t : ℝ) (c : J → ℝ) (hp : 0≤p) (hp1 : p≤1) (ht : 0<t)
    (hprob : ∀ e∈P.edgeFinset,p≤ρ e)
    (hmany : ∀ ω,Good ω → ∀ j,c j*(Fintype.card V:ℝ)^(k-2)≤Fintype.card (I ω j)) :
    1-b-Fintype.card J*(2*Real.exp (-2*t^2/((k:ℝ)^2/Fintype.card V)))≤
      (FiniteLaw.pi μwheel).probability (fun σ=>Good (fun e=>σ (Sum.inr e)) ∧ ∀ j,
        p^(k^2)*c j-t<rootedInducedSurvivalSum P (S (fun e=>σ (Sum.inr e)) j) s(x j,y j)
          (fun e=>σ (Sum.inl e))) := by
  have he := finiteLaw_pi_sum_probability μwheel
    (fun ω τ=>Good ω ∧ ∀ j,p^(k^2)*c j-t<rootedInducedSurvivalSum P (S ω j) s(x j,y j) τ)
  rw [he]
  exact rootedInducedSurvivalSum_two_exposures P S hinj x y hxy hk hn hroot
    (FiniteLaw.pi μfamily) Good b hgood (fun e=>FiniteLaw.retentionCoin (ρ e) (hρ e) (hρ1 e))
    p t c hp hp1 ht (by intro e he;exact hprob e he) hmany

end Oberwolfach
