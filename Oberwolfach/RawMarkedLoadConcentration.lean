module

public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.TypedMarkedExternalSpokeConcentration

@[expose] public section

/-! Concentration about the unconditional mean for the actual raw marked law.
The external spoke statement has no upper bound on the number of hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

variable (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))

local notation "μmark" => rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS

theorem rawMarkedPotentialLoad_mean_event
    (m : ℕ) (hm : 3≤m) (H₀ Hₖ : V→U→Prop)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (B : ℝ) (hB : 0<B) (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    1-(Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
    (FiniteLaw.pi μmark).probability (fun σ=>∀ root,
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
        (FiniteLaw.pi μmark).expectation (fun τ=>typedMarkedPotentialLoad w
          (rawMarkedPairRims P π d τ) (rawMarkedPairSpokes π d τ g j) root)|<t) := by
  letI : DecidableEq (V×V) := Classical.decEq _
  have hh := typedMarkedPotentialLoad_supported_common_event hm hn hu w B hB.le hw μmark
    (rawMarkedPairRims P π d) (fun σ=>rawMarkedPairSpokes π d σ g j) (rawMarkedResourceCoordinates π d)
    (by intro a σ τ ha;exact congrArg (fun Q : Prop=>decide Q) (propext (rawMarkedResourceState_supported P π d g j a σ τ ha)))
    (8*(d:ℝ)+6) (by positivity) hB
    (by intro a;exact_mod_cast rawMarkedResourceCoordinates_card π d a)
    (by intro e;exact_mod_cast rawMarkedResourceCoordinates_reverse_card π d e) t ht
  exact hh

theorem rawMarkedSpokeLoad_mean_event
    (m : ℕ) (hm : 3≤m) (H₀ Hₖ : V→U→Prop)
    (hn : 0<Fintype.card V) 
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (B : ℝ) (hB : 0<B) (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    1-(Fintype.card (Bool×V×U):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
    (FiniteLaw.pi μmark).probability (fun σ=>∀ root : Bool×V×U,
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr root)-
        (FiniteLaw.pi μmark).expectation (fun τ=>typedMarkedPotentialLoad w
          (rawMarkedPairRims P π d τ) (rawMarkedPairSpokes π d τ g j) (Sum.inr root))|<t) := by
  letI : DecidableEq (V×V) := Classical.decEq _
  have hh := typedMarkedSpoke_supported_common_event hm hn w B hB.le hw μmark
    (rawMarkedPairRims P π d) (fun σ=>rawMarkedPairSpokes π d σ g j) (rawMarkedResourceCoordinates π d)
    (by intro a σ τ ha;exact congrArg (fun Q : Prop=>decide Q) (propext (rawMarkedResourceState_supported P π d g j a σ τ ha)))
    (8*(d:ℝ)+6) (by positivity) hB
    (by intro a;exact_mod_cast rawMarkedResourceCoordinates_card π d a)
    (by intro e;exact_mod_cast rawMarkedResourceCoordinates_reverse_card π d e) t ht
  exact hh

end Oberwolfach
