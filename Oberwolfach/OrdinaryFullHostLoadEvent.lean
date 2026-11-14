module

public import Oberwolfach.OrdinaryFullHostSeedBounds
public import Oberwolfach.OrdinaryConflictDeletion

@[expose] public section

/-! A single event for all potential rim and spoke loads of the full-host
ordinary completion sample. Roots are omitted, and conflict edges are deleted
from the physical sample without changing the fixed seed coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem ordinaryFullHostSeed_common_event
    (P F : SimpleGraph V) (r : ℕ) (hr : 2≤r)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (pR pH ω p c B L D₀ ε : ℝ)
    (hn : 0<Fintype.card V) (hm : 0<Fintype.card U)
    (hω : 0<ω) (hp : 0<p)
    (hmlo : ω*(Fintype.card V:ℝ)≤Fintype.card U) (hmhi : Fintype.card U≤Fintype.card V)
    (hRlo : p≤pR) (hRhi : pR≤1) (hHlo : p≤pH) (hHhi : pH≤1)
    (hc : 0≤c) (hB : 0<B) (hL : 0≤L) (hdegF : ∀ v,(F.degree v:ℝ)≤L)
    (hD : (Fintype.card V:ℝ)/2≤D₀) (hε : 0≤ε)
    (hdegP : ∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V)
    (hbalance : pR*D₀=2*(Fintype.card U:ℝ)*pH)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j : Color) (hj : ∀ u,s u j=pH)
    (weight : OrdinaryCycle P r → ℝ)
    (hw : ∀ C,c/(Fintype.card V:ℝ)^(r-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (he : ∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (t : ℝ) (ht : 0<t) :
    let μ := rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>(hp.trans_le hRlo).le) (fun _=>hRhi)
      d hd q hq hQ s hs hS
    let w := ordinaryFullHostSeed (U:=U) P F r weight pR pH
    let Bplus := B/(ω*p^(2*r-1))
    1-(Fintype.card (Sym2 V⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((r:ℝ)^4*Bplus/Fintype.card V)*(2*r)*((r:ℝ)^2*Bplus))))≤
      (FiniteLaw.pi μ).probability (fun σ=>
        (∀ x y,P.Adj x y → ¬F.Adj x y →
          |ordinaryPotentialLoad w (Sum.inl s(x,y)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤
            t+5*(r:ℝ)^4*B*L/Fintype.card V) ∧
        (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤
          t+2*ε+12*(r:ℝ)^4*B*L/Fintype.card V)) := by
  intro μ w Bplus
  have hn0 : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hD0 : 0<D₀ := (half_pos hn0).trans_le hD
  have hBp : 0<Bplus := by dsimp [Bplus];positivity
  have hseed := ordinaryFullHostSeed_nonneg_upper P F r hr weight pR pH ω p c B
    hn hm hω hp hmlo hmhi hRlo hRhi hHlo hHhi hc hB.le hw
  have hw0 (C : OrdinaryCycle P r) : 0≤weight C :=
    (by positivity : 0≤c/(Fintype.card V:ℝ)^(r-2)).trans (hw C).1
  have hh := ordinaryPotentialLoad_supported_common_event P F (fun _ : V=>fun _ : U=>True)
    r hr hn hmhi w Bplus hBp.le hseed μ (rawWheelGraph P) (fun σ=>rawWheelSpokes π d σ j)
    (rawWheelResourceCoordinates π d) (rawWheelResourceState_supported P π d j)
    (4*(d:ℝ)+3) (by positivity) hBp
    (by intro a;exact_mod_cast rawWheelResourceCoordinates_card π d a)
    (by intro e;exact_mod_cast rawWheelResourceCoordinates_reverse_card π d e) t ht
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  constructor
  · intro x y hxy hFxy
    rw [ordinaryPotentialLoad_delete_conflicts]
    have hmean := ordinaryFullHostSeed_rim_mean_error P F r (by omega) π d hd hF hnoshort
      pR pH (hp.trans_le hRlo) hRhi (hp.trans_le hHlo) hm q hq hQ s hs hS j hj
      weight hr hn hw0 B hB.le (fun C=>(hw C).2) L hdegF he x y hxy hFxy
    calc
      _ ≤ |ordinaryPotentialLoad w (Sum.inl s(x,y)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j)-
          (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inl s(x,y)) (rawWheelGraph P τ) (rawWheelSpokes π d τ j))|+
          |(FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inl s(x,y)) (rawWheelGraph P τ) (rawWheelSpokes π d τ j))-1| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hσ _).le hmean
  · intro v u
    rw [ordinaryPotentialLoad_delete_conflicts]
    have hmean := ordinaryFullHostSeed_spoke_mean_error P F r (by omega) π d hd hF hnoshort
      pR pH (hp.trans_le hRlo) hRhi (hp.trans_le hHlo) hm q hq hQ s hs hS j hj
      weight hr hn hw0 B hB.le (fun C=>(hw C).2) L hdegF he D₀ hD0 hbalance v u
    have htarget := ordinary_seed_mean_spoke_error (Fintype.card V) D₀ (P.degree v) ε
      ((r:ℝ)^4*B*L)
      ((FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inr (v,u)) (rawWheelGraph P τ) (rawWheelSpokes π d τ j)))
      hn0 hD hε (by positivity) (hdegP v) (by convert hmean using 1 <;> ring)
    calc
      _ ≤ |ordinaryPotentialLoad w (Sum.inr (v,u)) (rawWheelGraph P σ) (rawWheelSpokes π d σ j)-
          (FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inr (v,u)) (rawWheelGraph P τ) (rawWheelSpokes π d τ j))|+
          |(FiniteLaw.pi μ).expectation (fun τ=>ordinaryPotentialLoad w (Sum.inr (v,u)) (rawWheelGraph P τ) (rawWheelSpokes π d τ j))-1| := abs_sub_le _ _ _
      _ ≤ t+(2*ε+12*((r:ℝ)^4*B*L)/Fintype.card V) := add_le_add (hσ _).le htarget
      _ = _ := by ring

end Oberwolfach
