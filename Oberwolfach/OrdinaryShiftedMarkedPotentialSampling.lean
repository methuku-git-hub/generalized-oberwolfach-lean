module

public import Oberwolfach.OrdinaryShiftedMarkedResourceState
public import Oberwolfach.TypedMarkedPotentialConcentration

@[expose] public section
/-! Root-omitted load expectations and concentration for the ordinary
shifted closing arc, sharing the ordinary physical sampling state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

variable (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))

local notation "μmark" => rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS

theorem ordinary_shifted_resource_probability
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (g : Γ) (j : Color) (a : ((V×V)⊕(V×V))⊕(Bool×V×U)) :
    (FiniteLaw.pi μmark).probability (fun σ=>
      typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) a=true)=
      rawMarkedWheelMarginal P π d p p q s g j a := by
  cases a with
  | inl a=>
    cases a with
    | inl xy=>
      have heq (σ : RawMarkedOutcome V U Γ Color) :
          typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inl (Sum.inl xy))=true ↔
          (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 xy.2) ∧
          σ (Sum.inl s(xy.1,xy.2))=some (false,orientationBit xy.1 xy.2) := by
        simp only [typedMarkedResourceState,decide_eq_true_eq,Sum.elim_inl,rawMarkedPairRims,
          ordinaryShiftedPairRims]
        change (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 xy.2 ∧ _) ↔ _
        aesop
      simp only [heq,rawMarkedWheelMarginal]
      by_cases he : ¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 xy.2
      · simp only [he,not_false_eq_true,true_and,and_true,ite_true]
        rw [finiteLaw_pi_coordinate_probability μmark (Sum.inl s(xy.1,xy.2)) (some (false,orientationBit xy.1 xy.2))]
        rfl
      · simp [he,FiniteLaw.probability]
    | inr xy=>
      have heq (σ : RawMarkedOutcome V U Γ Color) :
          typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inl (Sum.inr xy))=true ↔
          (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 (π xy.2)) ∧
          σ (Sum.inl s(xy.1,π xy.2))=some (false,orientationBit xy.1 (π xy.2)) := by
        simp only [typedMarkedResourceState,decide_eq_true_eq,Sum.elim_inl,Sum.elim_inr,rawMarkedPairRims,
          ordinaryShiftedPairRims]
        change (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 (π xy.2) ∧ _) ↔ _
        aesop
      simp only [heq,rawMarkedWheelMarginal]
      by_cases he : ¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 (π xy.2)
      · simp only [he,not_false_eq_true,true_and,and_true,ite_true]
        rw [finiteLaw_pi_coordinate_probability μmark (Sum.inl s(xy.1,π xy.2)) (some (false,orientationBit xy.1 (π xy.2)))]
        rfl
      · simp [he,FiniteLaw.probability]
  | inr a=>
    obtain ⟨a,v,u⟩ := a
    cases a
    · simp only [typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq,rawMarkedPairSpokes,rawMarkedSpokes,rawMarkedWheelMarginal,Bool.false_eq_true,ite_false]
      rw [finiteLaw_pi_injective_projection_event μmark Sum.inr Sum.inr_injective
        (fun σ=>rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j))]
      exact rawIntervalFamily_label_probability π d hd q hq hQ s hs hS hnoshort (v,u) j
    · simp only [typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq,rawMarkedPairSpokes,rawMarkedSpokes,rawMarkedWheelMarginal,ite_true]
      rw [finiteLaw_pi_injective_projection_event μmark Sum.inr Sum.inr_injective
        (fun σ=>rawIntervalFamilyState π d σ (v,u)=some (Sum.inl g))]
      exact rawIntervalFamily_interval_probability π d hd q hq hQ s hs hS hnoshort (v,u) g

theorem ordinary_shifted_potential_expectation
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (m : ℕ) (hm : 2≤m) (H₀ Hₖ : V→U→Prop)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (g : Γ) (j : Color) (root : ((V×V)⊕(V×V))⊕(Bool×V×U)) :
    (FiniteLaw.pi μmark).expectation (fun σ=>
      typedMarkedPotentialLoad w (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root)=
      ∑ W,(if root∈typedMarkedOccurrenceResources W then w W else 0)*
        ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p p q s g j a := by
  letI : DecidableEq (V×V) := Classical.decEq _
  have hsup : ∀ (a : ((V×V)⊕(V×V))⊕(Bool×V×U)) (σ τ : RawMarkedOutcome V U Γ Color),(∀ e∈rawMarkedResourceCoordinates π d a,σ e=τ e) →
      typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) a=
        typedMarkedResourceState (ordinaryShiftedPairRims P π d τ) (rawMarkedPairSpokes π d τ g j) a := by
    intro a σ τ ha
    exact congrArg (fun Q : Prop=>decide Q) (propext (ordinary_shifted_resource_state_supported P π d g j a σ τ ha))
  have hh := resourcePatternLoad_supported_expectation μmark typedMarkedOccurrenceResources w
    (fun _ _=>true) (rawMarkedResourceCoordinates π d)
    (fun σ=>typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j))
    hsup root (by
      intro W _ a ha b hb hab
      exact rawMarkedCoordinates_candidate_disjoint d (by omega) hm W a b
        (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab)
  simp_rw [typedMarkedPotentialLoad_eq_pattern]
  refine Eq.trans hh ?_
  apply Finset.sum_congr rfl
  intro W _
  apply congrArg₂ (fun x y : ℝ=>x*y)
  · split_ifs <;> rfl
  · exact Finset.prod_congr (by ext a;simp) (fun a _=>ordinary_shifted_resource_probability P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort g j a)

theorem ordinary_shifted_potential_common_event
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (m : ℕ) (hm : 3≤m) (H₀ Hₖ : V→U→Prop)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (B : ℝ) (hB : 0<B) (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    1-(Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
    (FiniteLaw.pi μmark).probability (fun σ=>∀ root,
      |typedMarkedPotentialLoad w (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then w W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p p q s g j a|<t) := by
  letI : DecidableEq (V×V) := Classical.decEq _
  have hh := typedMarkedPotentialLoad_supported_common_event hm hn hu w B hB.le hw μmark
    (ordinaryShiftedPairRims P π d) (fun σ=>rawMarkedPairSpokes π d σ g j) (rawMarkedResourceCoordinates π d)
    (by intro a σ τ ha;exact congrArg (fun Q : Prop=>decide Q) (propext (ordinary_shifted_resource_state_supported P π d g j a σ τ ha)))
    (8*(d:ℝ)+6) (by positivity) hB
    (by intro a;exact_mod_cast rawMarkedResourceCoordinates_card π d a)
    (by intro e;exact_mod_cast rawMarkedResourceCoordinates_reverse_card π d e) t ht
  simpa only [ordinary_shifted_potential_expectation P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m (by omega) H₀ Hₖ w g j] using hh

end Oberwolfach
