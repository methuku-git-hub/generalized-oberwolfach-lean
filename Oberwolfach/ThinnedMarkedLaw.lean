module

public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.EdgeRetention
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.FiniteProductRegrouping

@[expose] public section

/-! The original marked experiment together with independent vertex coins.
For a fixed pair of distinct hubs the ordinary common class uses a coin,
whereas the marked common class does not. The virtual Unit hub merely
records the common class; its root omission removes both original spokes
and the coin at that vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

abbrev ThinnedMarkedCoordinateState (Γ Color : Type) : RawWheelCoordinate V U⊕V→Type
  | Sum.inl e=>RawMarkedCoordinateState Γ Color e
  | Sum.inr _=>Bool
instance thinnedMarkedCoordinateStateFintype (e : RawWheelCoordinate V U⊕V) :
    Fintype (ThinnedMarkedCoordinateState Γ Color e) := by
  cases e <;> exact inferInstance
abbrev ThinnedMarkedOutcome (V U Γ Color : Type) :=
  ∀ e : RawWheelCoordinate V U⊕V,ThinnedMarkedCoordinateState Γ Color e

def thinnedMarkedLaw (μ : ∀ e : RawWheelCoordinate V U,FiniteLaw (RawMarkedCoordinateState Γ Color e))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) :
    ∀ e : RawWheelCoordinate V U⊕V,FiniteLaw (ThinnedMarkedCoordinateState Γ Color e)
  | Sum.inl e=>μ e
  | Sum.inr _=>FiniteLaw.retentionCoin θ hθ hθ1

def thinnedMarkedSpokes (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color) (u u' : U)
    (σ : ThinnedMarkedOutcome V U Γ Color) (b : Bool) (v : V) (_ : Unit) : Prop :=
  rawMarkedPairSpokes π d (fun e=>σ (Sum.inl e)) g j b v u ∧
  rawMarkedPairSpokes π d (fun e=>σ (Sum.inl e)) g j b v u' ∧
  (b=false → σ (Sum.inr v)=true)

theorem thinnedMarked_raw_projection
    (μ : ∀ e : RawWheelCoordinate V U,FiniteLaw (RawMarkedCoordinateState Γ Color e))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (E : RawMarkedOutcome V U Γ Color→Prop) :
    (FiniteLaw.pi (thinnedMarkedLaw μ θ hθ hθ1)).probability (fun σ=>E (fun e=>σ (Sum.inl e)))=
      (FiniteLaw.pi μ).probability E :=
  finiteLaw_pi_injective_projection_event (thinnedMarkedLaw μ θ hθ hθ1) Sum.inl Sum.inl_injective E

theorem thinnedMarked_coin_probability
    (μ : ∀ e : RawWheelCoordinate V U,FiniteLaw (RawMarkedCoordinateState Γ Color e))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (v : V) :
    (FiniteLaw.pi (thinnedMarkedLaw μ θ hθ hθ1)).probability (fun σ=>σ (Sum.inr v)=true)=θ := by
  rw [finiteLaw_pi_coordinate_probability]
  rfl

theorem thinnedMarked_raw_coin_independent
    (μ : ∀ e : RawWheelCoordinate V U,FiniteLaw (RawMarkedCoordinateState Γ Color e))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (E : RawMarkedOutcome V U Γ Color→Prop) (v : V) :
    (FiniteLaw.pi (thinnedMarkedLaw μ θ hθ hθ1)).probability
      (fun σ=>E (fun e=>σ (Sum.inl e)) ∧ σ (Sum.inr v)=true)=
      (FiniteLaw.pi μ).probability E*θ := by
  have hh := finiteLaw_disjoint_supported_events (thinnedMarkedLaw μ θ hθ hθ1)
    (Finset.univ.image Sum.inl) {Sum.inr v} (by simp)
    (fun σ=>E (fun e=>σ (Sum.inl e))) (fun σ=>σ (Sum.inr v)=true)
    (by intro σ τ h;have he : (fun e=>σ (Sum.inl e))=(fun e=>τ (Sum.inl e)) :=
          funext (fun e=>h _ (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩))
        rw [he])
    (by intro σ τ h;rw [h _ (Finset.mem_singleton_self _)])
  simpa only [thinnedMarked_raw_projection,thinnedMarked_coin_probability] using hh

theorem rawMarked_distinct_hubs_probability
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (g : Γ) (j : Color) (u u' : U) (hu : u≠u') (b : Bool) (v : V) :
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability
      (fun σ=>rawMarkedPairSpokes π d σ g j b v u ∧ rawMarkedPairSpokes π d σ g j b v u')=
      (if b then q u g*q u' g else s u j*s u' j) := by
  let μ := rawMarkedWheelLaw (V:=V) p k hp hk hphys d hd q hq hQ s hs hS
  have hdis : Disjoint (rawMarkedResourceCoordinates π d (Sum.inr (b,v,u)))
      (rawMarkedResourceCoordinates π d (Sum.inr (b,v,u'))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hf
    have hxy' := Sum.inr.inj hxy
    exact Finset.disjoint_left.mp
      (rawIntervalFamilyCoordinates_disjoint π d (v,u) (v,u') (Or.inl hu)) hx (hxy' ▸ hy)
  have hh := finiteLaw_disjoint_supported_events μ _ _ hdis
    (fun σ=>rawMarkedPairSpokes π d σ g j b v u)
    (fun σ=>rawMarkedPairSpokes π d σ g j b v u')
    (fun σ τ h=>rawMarkedResourceState_supported P π d g j (Sum.inr (b,v,u)) σ τ h)
    (fun σ τ h=>rawMarkedResourceState_supported P π d g j (Sum.inr (b,v,u')) σ τ h)
  have hprob (w : U) : (FiniteLaw.pi μ).probability (fun σ=>rawMarkedPairSpokes π d σ g j b v w)=
      if b then q w g else s w j := by
    simpa only [typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq,rawMarkedWheelMarginal] using
      rawMarkedResource_probability P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort g j (Sum.inr (b,v,w))
  rw [hh,hprob,hprob]
  cases b <;> rfl

theorem thinnedMarked_spoke_probability
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1)
    (g : Γ) (j : Color) (u u' : U) (hu : u≠u') (b : Bool) (v : V) :
    (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability
      (fun σ=>thinnedMarkedSpokes π d g j u u' σ b v ())=
      if b then q u g*q u' g else s u j*s u' j*θ := by
  cases b
  · simp only [thinnedMarkedSpokes,true_implies,Bool.false_eq_true,ite_false]
    have he : (fun σ : ThinnedMarkedOutcome V U Γ Color=>
        rawMarkedPairSpokes π d (fun e=>σ (Sum.inl e)) g j false v u ∧
        rawMarkedPairSpokes π d (fun e=>σ (Sum.inl e)) g j false v u' ∧ σ (Sum.inr v)=true)=
        (fun σ=> (rawMarkedPairSpokes π d (fun e=>σ (Sum.inl e)) g j false v u ∧
        rawMarkedPairSpokes π d (fun e=>σ (Sum.inl e)) g j false v u') ∧ σ (Sum.inr v)=true) := by
      funext σ;exact propext (and_assoc.symm)
    rw [he,thinnedMarked_raw_coin_independent
      (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1
      (fun σ=>rawMarkedPairSpokes π d σ g j false v u ∧ rawMarkedPairSpokes π d σ g j false v u') v,
      rawMarked_distinct_hubs_probability P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort g j u u' hu false v]
    rfl
  · simp only [thinnedMarkedSpokes,Bool.true_eq_false,false_implies,and_true,ite_true]
    rw [thinnedMarked_raw_projection
      (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1
      (fun σ=>rawMarkedPairSpokes π d σ g j true v u ∧ rawMarkedPairSpokes π d σ g j true v u'),
      rawMarked_distinct_hubs_probability P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort g j u u' hu true v]
    rfl

end Oberwolfach
