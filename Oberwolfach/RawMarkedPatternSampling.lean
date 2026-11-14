module

public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.SupportedPatternSums
public import Oberwolfach.FinitePatternIncidence

@[expose] public section

/-! Mixed rim and spoke patterns in the original product experiment.
The expected product is used only after physical-edge distinctness and
interval-coordinate disjointness have been verified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

abbrev MarkedResource (V U : Type) := ((V×V)⊕(V×V))⊕(Bool×V×U)

theorem rawMarkedResourceCoordinates_disjoint
    (π : Equiv.Perm V) (d : ℕ) (a b : MarkedResource V U)
    (h : match a,b with
      | Sum.inl e,Sum.inl f=>markedPairPhysical π e≠markedPairPhysical π f
      | Sum.inr x,Sum.inr y=>x.2.2≠y.2.2 ∨ ¬PermutationClose π (3*d) x.2.1 y.2.1
      | _,_=>True) :
    Disjoint (rawMarkedResourceCoordinates π d a) (rawMarkedResourceCoordinates π d b) := by
  cases a with
  | inl a=>cases b with
    | inl b=>simpa only [rawMarkedResourceCoordinates,Finset.disjoint_singleton,ne_eq,Sum.inl.injEq] using h
    | inr b=>simp [rawMarkedResourceCoordinates]
  | inr a=>cases b with
    | inl b=>simp [rawMarkedResourceCoordinates]
    | inr b=>
      apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp he
      obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp hf
      have hxy := Sum.inr.inj (he.trans hf.symm)
      exact Finset.disjoint_left.mp (rawIntervalFamilyCoordinates_disjoint π d a.2 b.2 h) hx (hxy ▸ hy)

variable (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μmark" => rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS

def rawMarkedPatternSum {I : Type} [Fintype I]
    (R : I→Finset (MarkedResource V U)) (w : I→ℝ) (g : Γ) (j : Color)
    (σ : RawMarkedOutcome V U Γ Color) : ℝ :=
  supportedPatternSum R w (fun _ _=>true)
    (fun σ=>typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)) σ

theorem rawMarkedPatternSum_expectation
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    {I : Type} [Fintype I] (R : I→Finset (MarkedResource V U)) (w : I→ℝ)
    (hdisj : ∀ i,∀ a∈R i,∀ b∈R i,a≠b →
      Disjoint (rawMarkedResourceCoordinates π d a) (rawMarkedResourceCoordinates π d b))
    (g : Γ) (j : Color) :
    (FiniteLaw.pi μmark).expectation (rawMarkedPatternSum P π d R w g j)=
      ∑ i,w i*∏ a∈R i,rawMarkedWheelMarginal P π d p k q s g j a := by
  unfold rawMarkedPatternSum
  have hh := supportedPatternSum_expectation μmark R w (fun _ _=>true)
    (rawMarkedResourceCoordinates π d)
    (fun σ=>typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j))
    (by intro a σ τ ha;exact congrArg (fun Q : Prop=>decide Q) (propext (rawMarkedResourceState_supported P π d g j a σ τ ha))) hdisj
  simpa only [rawMarkedResource_probability P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort g j] using hh

theorem rawMarkedPatternSum_tail
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    {I : Type} [Fintype I] (R : I→Finset (MarkedResource V U)) (w : I→ℝ) (hw : ∀ i,0≤w i)
    (hdisj : ∀ i,∀ a∈R i,∀ b∈R i,a≠b →
      Disjoint (rawMarkedResourceCoordinates π d a) (rawMarkedResourceCoordinates π d b))
    (g : Γ) (j : Color) (a r L : ℝ) (ha : 0<a) (hr : 0<r) (hL : 0<L)
    (hsize : ∀ i,((R i).card:ℝ)≤r) (htotal : (∑ i,w i)≤L)
    (hload : ∀ e,(∑ i,if e∈R i then w i else 0)≤a) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μmark).probability (fun σ=>t≤
      |rawMarkedPatternSum P π d R w g j σ-
        ∑ i,w i*∏ e∈R i,rawMarkedWheelMarginal P π d p k q s g j e|)≤
      2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(a*r*L))) := by
  rw [← rawMarkedPatternSum_expectation P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort R w hdisj g j]
  apply supportedPatternSum_tail μmark R w hw (fun _ _=>true)
    (rawMarkedResourceCoordinates π d)
    (fun σ=>typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j))
    (by intro e σ τ he;exact congrArg (fun Q : Prop=>decide Q) (propext (rawMarkedResourceState_supported P π d g j e σ τ he)))
    (8*(d:ℝ)+6) (a*r*L) (by positivity) (by positivity)
    (by intro e;exact_mod_cast rawMarkedResourceCoordinates_card π d e)
    (by intro e;exact_mod_cast rawMarkedResourceCoordinates_reverse_card π d e)
  · exact finite_pattern_incidence_square_sum R w hw a r L ha.le hr.le hsize htotal hload
  · exact ht

end Oberwolfach
