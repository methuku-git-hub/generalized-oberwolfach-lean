module

public import Oberwolfach.ThinnedMarkedGeometry

@[expose] public section

/-! Root-omitted expectations and concentration for two common hub columns
with independent ordinary-class thinning. These use the exact original
marked coordinates rather than a new model with independent spoke entries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
  (P : SimpleGraph V) (π : Equiv.Perm V)
  (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
  (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
  (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
  (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
  (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U)
local notation "μthin" => thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1
local notation "Qthin" => (fun σ : ThinnedMarkedOutcome V U Γ Color=>rawMarkedPairRims P π d (fun e=>σ (Sum.inl e)))
local notation "Hthin" => thinnedMarkedSpokes π d g j u u'
local notation "φthin" => rawMarkedWheelMarginal P π d p k
  (fun (_ : Unit) a=>q u a*q u' a) (fun (_ : Unit) j=>s u j*s u' j*θ) g j

theorem thinnedMarkedResource_probability
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x) (hu : u≠u')
    (a : ((V×V)⊕(V×V))⊕(Bool×V×Unit)) :
    (FiniteLaw.pi μthin).probability (fun σ=>typedMarkedResourceState (Qthin σ) (Hthin σ) a=true)=φthin a := by
  cases a with
  | inl e=>
    have hproj := thinnedMarked_raw_projection (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)
      θ hθ hθ1 (fun σ=>typedMarkedResourceState (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inl e)=true)
    change (FiniteLaw.pi μthin).probability (fun σ=>decide (Qthin σ e)=true)=_ at hproj ⊢
    rw [hproj]
    have hh := rawMarkedResource_probability P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort g j (Sum.inl e)
    cases e <;> simpa only [rawMarkedWheelMarginal] using hh
  | inr a=>
    rcases a with ⟨b,v,z⟩
    cases z
    simpa only [typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq,rawMarkedWheelMarginal] using
      thinnedMarked_spoke_probability P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort θ hθ hθ1 g j u u' hu b v

theorem thinnedMarkedPotentialLoad_expectation
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x) (hu : u≠u')
    (m : ℕ) (hm : 2≤m) (H₀ Hₖ : V→Unit→Prop)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (root : ((V×V)⊕(V×V))⊕(Bool×V×Unit)) :
    (FiniteLaw.pi μthin).expectation (fun σ=>typedMarkedPotentialLoad w (Qthin σ) (Hthin σ) root)=
      ∑ W,(if root∈typedMarkedOccurrenceResources W then w W else 0)*
        ∏ a∈typedMarkedOccurrenceResources W\{root},φthin a := by
  letI : DecidableEq (V×V) := Classical.decEq _
  have hsup := thinnedMarkedResourceState_supported P π d g j u u'
  have hh := resourcePatternLoad_supported_expectation μthin typedMarkedOccurrenceResources w
    (fun _ _=>true) (thinnedMarkedResourceCoordinates π d u u')
    (fun σ=>typedMarkedResourceState (Qthin σ) (Hthin σ)) hsup root (by
      intro W _ a ha b hb hab
      exact thinnedMarkedCoordinates_candidate_disjoint (by omega) hm W a b
        (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab u u')
  simp_rw [typedMarkedPotentialLoad_eq_pattern]
  refine Eq.trans hh ?_
  apply Finset.sum_congr rfl
  intro W _
  apply congrArg₂ (fun x y : ℝ=>x*y)
  · split_ifs <;> rfl
  · exact Finset.prod_congr (by ext a;simp)
      (fun a _=>thinnedMarkedResource_probability P π p k hp hk hphys d hd q hq hQ s hs hS θ hθ hθ1 g j u u' hnoshort hu a)

theorem thinnedMarkedPotentialLoad_mean_event
    (m : ℕ) (hm : 3≤m) (H₀ Hₖ : V→Unit→Prop) (hn : 0<Fintype.card V)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (B : ℝ) (hB : 0<B) (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (ε : ℝ) (hε : 0<ε) :
    1-(Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×Unit)):ℝ)*
      (2*Real.exp (-2*ε^2/((16*(d:ℝ)+14)^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
    (FiniteLaw.pi μthin).probability (fun σ=>∀ root,
      |typedMarkedPotentialLoad w (Qthin σ) (Hthin σ) root-
        (FiniteLaw.pi μthin).expectation (fun τ=>typedMarkedPotentialLoad w (Qthin τ) (Hthin τ) root)|<ε) := by
  letI : DecidableEq (V×V) := Classical.decEq _
  apply typedMarkedPotentialLoad_supported_common_event hm hn (by simpa only [Fintype.card_unique] using Nat.succ_le_of_lt hn)
    w B hB.le hw μthin Qthin Hthin (thinnedMarkedResourceCoordinates π d u u')
    (thinnedMarkedResourceState_supported P π d g j u u') (16*(d:ℝ)+14) (by positivity) hB
  · intro a
    exact_mod_cast thinnedMarkedResourceCoordinates_card π d u u' a
  · intro e
    have hh := thinnedMarkedResourceCoordinates_reverse_card π d u u' e
    have hh' : ((Finset.univ.filter (fun a=>e∈thinnedMarkedResourceCoordinates π d u u' a)).card:ℝ)≤16*(d:ℝ)+14 := by
      exact_mod_cast hh
    convert hh' using 1 <;> congr!
  · exact hε

end Oberwolfach
