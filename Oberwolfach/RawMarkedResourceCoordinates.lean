module

public import Oberwolfach.OrdinaryRawIntervalGeometry
public import Oberwolfach.RawMarkedHubCounts
public import Oberwolfach.MarkedSampleArcs

@[expose] public section

/-! Primitive coordinates for all potential typed arcs and spokes. Physical
edge coordinates can affect four potential arcs, and interval coordinates
can affect both spoke types. No potential root is required to be present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

abbrev RawMarkedCoordinateState (Γ Color : Type) : RawWheelCoordinate V U → Type
  | Sum.inl _=>Option (Bool×Bool)
  | Sum.inr e=>RawIntervalCoordinateState Γ Color e.2

instance rawMarkedCoordinateStateFintype (e : RawWheelCoordinate V U) :
    Fintype (RawMarkedCoordinateState Γ Color e) := by
  cases e with
  | inl e=>exact inferInstanceAs (Fintype (Option (Bool×Bool)))
  | inr e=>exact inferInstanceAs (Fintype (RawIntervalCoordinateState Γ Color e.2))

abbrev RawMarkedOutcome (V U Γ Color : Type) :=
  ∀ e : RawWheelCoordinate V U,RawMarkedCoordinateState Γ Color e

def markedPairPhysical (π : Equiv.Perm V) : (V×V)⊕(V×V) → Sym2 V :=
  Sum.elim (fun xy=>s(xy.1,xy.2)) (fun xy=>s(xy.1,π xy.2))

def rawMarkedPairRims (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) : (V×V)⊕(V×V) → Prop :=
  Sum.elim
    (fun xy=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false xy.1 xy.2=1)
    (fun xy=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true xy.1 xy.2=1)

def rawMarkedPairSpokes (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g : Γ) (j : Color) : Bool→V→U→Prop :=
  rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j

def rawMarkedResourceCoordinates (π : Equiv.Perm V) (d : ℕ) :
    ((V×V)⊕(V×V))⊕(Bool×V×U) → Finset (RawWheelCoordinate V U)
  | Sum.inl e=>{Sum.inl (markedPairPhysical π e)}
  | Sum.inr a=>(rawIntervalFamilyCoordinates π d a.2).image Sum.inr

theorem markedPairPhysical_fiber_card (π : Equiv.Perm V) (e : Sym2 V) :
    (Finset.univ.filter (fun a=>markedPairPhysical π a=e)).card≤4 := by
  induction e using Sym2.ind with
  | _ x y=>
    let T : Finset ((V×V)⊕(V×V)) :=
      {Sum.inl (x,y),Sum.inl (y,x),Sum.inr (x,π.symm y),Sum.inr (y,π.symm x)}
    have hsub : Finset.univ.filter (fun a=>markedPairPhysical π a=s(x,y))⊆T := by
      intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      cases a with
      | inl a=>
        rcases Sym2.eq_iff.mp ha' with ⟨hx,hy⟩|⟨hx,hy⟩
        · simp [T,← hx,← hy]
        · simp [T,← hx,← hy]
      | inr a=>
        rcases Sym2.eq_iff.mp ha' with ⟨hx,hy⟩|⟨hx,hy⟩
        · have hy' : a.2=π.symm y := (Equiv.eq_symm_apply π).mpr hy
          simp [T,← hx,← hy']
        · have hy' : a.2=π.symm x := (Equiv.eq_symm_apply π).mpr hy
          simp [T,← hx,← hy']
    apply (Finset.card_le_card hsub).trans
    dsimp [T]
    have h₁ := Finset.card_insert_le (Sum.inl (x,y))
      ({Sum.inl (y,x),Sum.inr (x,π.symm y),Sum.inr (y,π.symm x)}:Finset ((V×V)⊕(V×V)))
    have h₂ := Finset.card_insert_le (Sum.inl (y,x))
      ({Sum.inr (x,π.symm y),Sum.inr (y,π.symm x)}:Finset ((V×V)⊕(V×V)))
    have h₃ : ({Sum.inr (x,π.symm y),Sum.inr (y,π.symm x)}:Finset ((V×V)⊕(V×V))).card≤2 := Finset.card_le_two
    omega

theorem rawMarkedResourceCoordinates_card (π : Equiv.Perm V) (d : ℕ)
    (a : ((V×V)⊕(V×V))⊕(Bool×V×U)) :
    (rawMarkedResourceCoordinates π d a).card≤8*d+6 := by
  cases a with
  | inl e=>simp only [rawMarkedResourceCoordinates,Finset.card_singleton];omega
  | inr a=>
    have hh := (Finset.card_image_le (s:=rawIntervalFamilyCoordinates π d a.2)
      (f:=Sum.inr (α:=Sym2 V))).trans (rawIntervalFamilyCoordinates_card π d a.2)
    exact hh.trans (by omega)

theorem rawMarkedResourceCoordinates_reverse_card (π : Equiv.Perm V) (d : ℕ)
    (e : RawWheelCoordinate V U) :
    (Finset.univ.filter (fun a=>e∈rawMarkedResourceCoordinates π d a)).card≤8*d+6 := by
  cases e with
  | inl e=>
    have he : Finset.univ.filter (fun a=>Sum.inl e∈rawMarkedResourceCoordinates π d a)=
        (Finset.univ.filter (fun a=>markedPairPhysical π a=e)).image (Sum.inl (β:=Bool×V×U)) := by
      ext a
      cases a <;> simp [rawMarkedResourceCoordinates,eq_comm]
    rw [he]
    exact (Finset.card_image_le.trans (markedPairPhysical_fiber_card π e)).trans (by omega)
  | inr e=>
    let T := Finset.univ.filter (fun a : V×U=>e∈rawIntervalFamilyCoordinates π d a)
    have he : Finset.univ.filter (fun a=>Sum.inr e∈rawMarkedResourceCoordinates π d a)=
        (Finset.univ×ˢT).image (fun a : Bool×(V×U)=>Sum.inr (α:=(V×V)⊕(V×V)) a) := by
      ext a
      cases a <;> simp [rawMarkedResourceCoordinates,T]
    rw [he]
    have hh := Finset.card_image_le (s:=Finset.univ×ˢT)
      (f:=fun a : Bool×(V×U)=>Sum.inr (α:=(V×V)⊕(V×V)) a)
    rw [Finset.card_product,Finset.card_univ,Fintype.card_bool] at hh
    have hc := rawIntervalFamilyCoordinates_reverse_card π d e
    change T.card≤4*d+3 at hc
    omega

theorem rawMarkedResourceState_supported (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (g : Γ) (j : Color) (a : ((V×V)⊕(V×V))⊕(Bool×V×U))
    (σ τ : RawMarkedOutcome V U Γ Color)
    (ha : ∀ e∈rawMarkedResourceCoordinates π d a,σ e=τ e) :
    Sum.elim (rawMarkedPairRims P π d σ) (fun jvu=>rawMarkedPairSpokes π d σ g j jvu.1 jvu.2.1 jvu.2.2) a ↔
      Sum.elim (rawMarkedPairRims P π d τ) (fun jvu=>rawMarkedPairSpokes π d τ g j jvu.1 jvu.2.1 jvu.2.2) a := by
  cases a with
  | inl a=>
    have hh := ha (Sum.inl (markedPairPhysical π a)) (Finset.mem_singleton_self _)
    cases a with
    | inl xy=>
      change σ (Sum.inl s(xy.1,xy.2))=τ (Sum.inl s(xy.1,xy.2)) at hh
      simp only [rawMarkedPairRims,Sum.elim_inl,markedPhysicalRim_eq_one_iff]
      change (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 xy.2 ∧
        σ (Sum.inl s(xy.1,xy.2))=some (false,orientationBit xy.1 xy.2)) ↔
        (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 xy.2 ∧
        τ (Sum.inl s(xy.1,xy.2))=some (false,orientationBit xy.1 xy.2))
      rw [hh]
    | inr xy=>
      change σ (Sum.inl s(xy.1,π xy.2))=τ (Sum.inl s(xy.1,π xy.2)) at hh
      simp only [rawMarkedPairRims,Sum.elim_inl,Sum.elim_inr,markedPhysicalRim_eq_one_iff]
      change (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 (π xy.2) ∧
        σ (Sum.inl s(xy.1,π xy.2))=some (true,orientationBit xy.1 (π xy.2))) ↔
        (¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 (π xy.2) ∧
        τ (Sum.inl s(xy.1,π xy.2))=some (true,orientationBit xy.1 (π xy.2)))
      rw [hh]
  | inr a=>
    have hh := rawIntervalFamilyState_supported π d (fun e=>σ (Sum.inr e))
      (fun e=>τ (Sum.inr e)) a.2 (by
        intro e he
        exact ha (Sum.inr e) (Finset.mem_image.mpr ⟨e,he,rfl⟩))
    obtain ⟨a,v,u⟩ := a
    cases a <;> simpa only [Sum.elim_inr,rawMarkedPairSpokes,rawMarkedSpokes,hh]

end Oberwolfach
