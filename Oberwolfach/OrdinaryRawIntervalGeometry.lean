module

public import Oberwolfach.RawIntervalFamily
public import Oberwolfach.OrdinaryPotentialConcentration

@[expose] public section

/-! Primitive coordinates for independent physical rim retention and the
original interval experiment on all spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

abbrev RawWheelCoordinate (V U : Type) := Sym2 V⊕(U×RawIntervalCoordinate V)

abbrev RawWheelCoordinateState (Γ Color : Type) : RawWheelCoordinate V U → Type
  | Sum.inl _=>Bool
  | Sum.inr e=>RawIntervalCoordinateState Γ Color e.2

instance rawWheelCoordinateStateFintype (e : RawWheelCoordinate V U) :
    Fintype (RawWheelCoordinateState Γ Color e) := by
  cases e with
  | inl e=>exact inferInstanceAs (Fintype Bool)
  | inr e=>exact inferInstanceAs (Fintype (RawIntervalCoordinateState Γ Color e.2))

abbrev RawWheelOutcome (V U Γ Color : Type) :=
  ∀ e : RawWheelCoordinate V U,RawWheelCoordinateState Γ Color e

def rawWheelGraph (P : SimpleGraph V) (σ : RawWheelOutcome V U Γ Color) : SimpleGraph V :=
  retainedGraph P (fun e=>σ (Sum.inl e))

def rawWheelSpokes (π : Equiv.Perm V) (d : ℕ) (σ : RawWheelOutcome V U Γ Color)
    (j : Color) (v : V) (u : U) : Prop :=
  rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (v,u)=some (Sum.inr j)

def rawWheelResourceCoordinates (π : Equiv.Perm V) (d : ℕ) :
    Sym2 V⊕(V×U) → Finset (RawWheelCoordinate V U)
  | Sum.inl e=>{Sum.inl e}
  | Sum.inr a=>(rawIntervalFamilyCoordinates π d a).image Sum.inr

theorem rawWheelResourceCoordinates_card (π : Equiv.Perm V) (d : ℕ) (a : Sym2 V⊕(V×U)) :
    (rawWheelResourceCoordinates π d a).card≤4*d+3 := by
  cases a with
  | inl e=>simp only [rawWheelResourceCoordinates,Finset.card_singleton];omega
  | inr a=>exact Finset.card_image_le.trans (rawIntervalFamilyCoordinates_card π d a)

theorem rawWheelResourceCoordinates_reverse_card (π : Equiv.Perm V) (d : ℕ)
    (e : RawWheelCoordinate V U) :
    (Finset.univ.filter (fun a=>e∈rawWheelResourceCoordinates π d a)).card≤4*d+3 := by
  cases e with
  | inl e=>
    have he : Finset.univ.filter (fun a : Sym2 V⊕(V×U)=>Sum.inl e∈rawWheelResourceCoordinates π d a)={Sum.inl e} := by
      ext a
      cases a <;> simp [rawWheelResourceCoordinates,eq_comm]
    rw [he,Finset.card_singleton]
    omega
  | inr e=>
    have he : Finset.univ.filter (fun a=>Sum.inr e∈rawWheelResourceCoordinates π d a)=
        (Finset.univ.filter (fun a : V×U=>e∈rawIntervalFamilyCoordinates π d a)).image Sum.inr := by
      ext a
      cases a <;> simp [rawWheelResourceCoordinates]
    rw [he]
    exact Finset.card_image_le.trans (rawIntervalFamilyCoordinates_reverse_card π d e)

theorem rawWheelResourceState_supported (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (j : Color) (a : Sym2 V⊕(V×U)) (σ τ : RawWheelOutcome V U Γ Color)
    (ha : ∀ e∈rawWheelResourceCoordinates π d a,σ e=τ e) :
    ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j) a=
      ordinaryResourceState (rawWheelGraph P τ) (rawWheelSpokes π d τ j) a := by
  cases a with
  | inl e=>
    have hh := ha (Sum.inl e) (Finset.mem_singleton_self _)
    induction e using Sym2.ind with
    | _ x y=>simp only [ordinaryResourceState,Sum.elim_inl,rawWheelGraph,SimpleGraph.mem_edgeSet,
        retainedGraph,hh]
  | inr a=>
    have hh := rawIntervalFamilyState_supported π d (fun e=>σ (Sum.inr e))
      (fun e=>τ (Sum.inr e)) a (by
        intro e he
        exact ha (Sum.inr e) (Finset.mem_image.mpr ⟨e,he,rfl⟩))
    simpa only [ordinaryResourceState,Sum.elim_inr,rawWheelSpokes,Prod.mk.eta,hh]

theorem rawWheelResourceCoordinates_disjoint (π : Equiv.Perm V) (d : ℕ)
    (a b : Sym2 V⊕(V×U)) (hne : a≠b)
    (hsep : ∀ v u w z,a=Sum.inr (v,u) → b=Sum.inr (w,z) →
      u≠z ∨ ¬PermutationClose π (3*d) v w) :
    Disjoint (rawWheelResourceCoordinates π d a) (rawWheelResourceCoordinates π d b) := by
  cases a with
  | inl a=>
    cases b with
    | inl b=>
      apply Finset.disjoint_singleton.mpr
      intro he
      exact hne (congrArg Sum.inl (Sum.inl.inj he))
    | inr b=>simp [rawWheelResourceCoordinates]
  | inr a=>
    cases b with
    | inl b=>simp [rawWheelResourceCoordinates]
    | inr b=>
      apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp he
      obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp hf
      have hxy:=Sum.inr.inj (he.trans hf.symm)
      exact Finset.disjoint_left.mp (rawIntervalFamilyCoordinates_disjoint π d a b
        (hsep a.1 a.2 b.1 b.2 rfl rfl)) hx (hxy ▸ hy)

def permutationConflictGraph (π : Equiv.Perm V) (b : ℕ) : SimpleGraph V where
  Adj x y:=x≠y ∧ PermutationClose π b x y
  symm:=⟨fun _ _ h=>⟨Ne.symm h.1,(permutationClose_symm π b _ _).mp h.2⟩⟩
  loopless:=⟨fun _ h=>h.1 rfl⟩

theorem rawWheelCoordinates_candidate_disjoint (P F : SimpleGraph V) (Hbase : V → U → Prop)
    (π : Equiv.Perm V) (d r : ℕ) (hF : permutationConflictGraph π (3*d)≤F)
    (W : OrdinaryWheel P F Hbase r) (a b : Sym2 V⊕(V×U))
    (ha : a∈ordinaryWheelResources W) (hb : b∈ordinaryWheelResources W) (hne : a≠b) :
    Disjoint (rawWheelResourceCoordinates π d a) (rawWheelResourceCoordinates π d b) := by
  apply rawWheelResourceCoordinates_disjoint π d a b hne
  intro v u w z he hf
  subst a
  subst b
  rw [ordinaryWheelResources_spoke] at ha hb
  right
  intro hclose
  have hvw : v≠w := by
    intro he
    apply hne
    exact congrArg Sum.inr (Prod.ext he (ha.1.symm.trans hb.1))
  exact W.property.2 v ha.2 w hb.2 (hF ⟨hvw,hclose⟩)

end Oberwolfach
