module

public import Oberwolfach.RawIntervalDistribution
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! The original interval experiment in all hub columns. The scalar trials
are independent across hubs; label states within a column retain their
local dependence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

abbrev RawIntervalFamilyOutcome (V U Γ Color : Type) :=
  ∀ e : U×RawIntervalCoordinate V,RawIntervalCoordinateState Γ Color e.2

def rawIntervalFamilyState (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (a : V×U) : Option (Γ⊕Color) :=
  rawIntervalState π d (fun e=>σ (a.2,e)) a.1

def rawIntervalFamilyCoordinates (π : Equiv.Perm V) (d : ℕ) (a : V×U) :
    Finset (U×RawIntervalCoordinate V) :=
  (rawIntervalStateCoordinates π d a.1).image (fun e=>(a.2,e))

theorem rawIntervalFamilyCoordinates_card (π : Equiv.Perm V) (d : ℕ) (a : V×U) :
    (rawIntervalFamilyCoordinates π d a).card≤4*d+3 :=
  Finset.card_image_le.trans (rawIntervalStateCoordinates_card π d a.1)

theorem rawIntervalFamilyCoordinates_reverse_card (π : Equiv.Perm V) (d : ℕ)
    (e : U×RawIntervalCoordinate V) :
    (Finset.univ.filter (fun a=>e∈rawIntervalFamilyCoordinates π d a)).card≤4*d+3 := by
  have he : Finset.univ.filter (fun a=>e∈rawIntervalFamilyCoordinates π d a)=
      (Finset.univ.filter (fun x=>e.2∈rawIntervalStateCoordinates π d x)).image (fun x=>(x,e.1)) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,rawIntervalFamilyCoordinates,
      Finset.mem_image,Prod.mk.injEq]
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨a.1,hb,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨e.2,hx,rfl⟩
  rw [he]
  exact Finset.card_image_le.trans (rawIntervalStateCoordinates_reverse_card π d e.2)

theorem rawIntervalFamilyState_supported (π : Equiv.Perm V) (d : ℕ)
    (σ τ : RawIntervalFamilyOutcome V U Γ Color) (a : V×U)
    (ha : ∀ e∈rawIntervalFamilyCoordinates π d a,σ e=τ e) :
    rawIntervalFamilyState π d σ a=rawIntervalFamilyState π d τ a := by
  apply rawIntervalState_supported
  intro e he
  exact ha (a.2,e) (Finset.mem_image.mpr ⟨e,he,rfl⟩)

theorem rawIntervalFamilyCoordinates_disjoint (π : Equiv.Perm V) (d : ℕ) (a b : V×U)
    (hab : a.2≠b.2 ∨ ¬PermutationClose π (3*d) a.1 b.1) :
    Disjoint (rawIntervalFamilyCoordinates π d a) (rawIntervalFamilyCoordinates π d b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp he
  obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp hf
  have hh := Prod.mk.inj (he.trans hf.symm)
  rcases hab with hu|hfar
  · exact hu hh.1
  · exact Finset.disjoint_left.mp (rawIntervalStateCoordinates_disjoint π d a.1 b.1 hfar)
      hx (hh.2 ▸ hy)

def rawIntervalFamilyLaw (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) :
    ∀ e : U×RawIntervalCoordinate V,FiniteLaw (RawIntervalCoordinateState Γ Color e.2) :=
  fun e=>rawIntervalCoordinateLaw d hd (q e.1) (hq e.1) (hQ e.1) (s e.1) (hs e.1) (hS e.1) e.2

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))

local notation "μfamily" => rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS

theorem rawIntervalFamily_column_event (u : U) (A : RawIntervalOutcome V Γ Color → Prop) :
    (FiniteLaw.pi μfamily).probability (fun σ=>A (fun e=>σ (u,e)))=
      (FiniteLaw.pi (rawIntervalCoordinateLaw (V:=V) d hd (q u) (hq u) (hQ u)
        (s u) (hs u) (hS u))).probability A := by
  exact finiteLaw_pi_injective_projection_event μfamily (fun e=>(u,e))
    (fun _ _ h=>(Prod.mk.inj h).2) A

theorem rawIntervalFamily_label_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (a : V×U) (j : Color) :
    (FiniteLaw.pi μfamily).probability (fun σ=>rawIntervalFamilyState π d σ a=some (Sum.inr j))=s a.2 j := by
  unfold rawIntervalFamilyState
  rw [rawIntervalFamily_column_event d hd q hq hQ s hs hS a.2
    (fun τ=>rawIntervalState π d τ a.1=some (Sum.inr j))]
  exact rawIntervalState_label_probability π d hd (q a.2) (hq a.2) (hQ a.2)
    (s a.2) (hs a.2) (hS a.2) hnoshort a.1 j

theorem rawIntervalFamily_interval_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (a : V×U) (g : Γ) :
    (FiniteLaw.pi μfamily).probability (fun σ=>rawIntervalFamilyState π d σ a=some (Sum.inl g))=q a.2 g := by
  unfold rawIntervalFamilyState
  rw [rawIntervalFamily_column_event d hd q hq hQ s hs hS a.2
    (fun τ=>rawIntervalState π d τ a.1=some (Sum.inl g))]
  exact rawIntervalState_interval_probability π d hd (q a.2) (hq a.2) (hQ a.2)
    (s a.2) (hs a.2) (hS a.2) hnoshort a.1 g

theorem rawIntervalFamily_column_independence
    (A : U → RawIntervalOutcome V Γ Color → Prop) (T : Finset U) :
    (FiniteLaw.pi μfamily).probability (fun σ=>∀ u∈T,A u (fun e=>σ (u,e)))=
      ∏ u∈T,(FiniteLaw.pi (rawIntervalCoordinateLaw (V:=V) d hd (q u) (hq u) (hQ u)
        (s u) (hs u) (hS u))).probability (A u) := by
  rw [← Finset.prod_congr rfl (fun u (_ : u∈T)=>rawIntervalFamily_column_event d hd q hq hQ s hs hS u (A u))]
  apply finiteLaw_disjoint_supported_family μfamily
    (fun u=>Finset.univ.image (fun e : RawIntervalCoordinate V=>(u,e)))
    (fun u σ=>A u (fun e=>σ (u,e)))
  · intro u σ τ ha
    have hh : (fun e=>σ (u,e))=(fun e=>τ (u,e)) := by
      funext e;exact ha (u,e) (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩)
    rw [hh]
  · intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,_,he⟩ := Finset.mem_image.mp he
    obtain ⟨y,_,hf⟩ := Finset.mem_image.mp hf
    exact huv (Prod.mk.inj (he.trans hf.symm)).1

theorem rawIntervalFamily_labels_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (T : Finset (V×U)) (j : V×U → Color)
    (hsep : ∀ a∈T,∀ b∈T,a≠b → a.2≠b.2 ∨ ¬PermutationClose π (3*d) a.1 b.1) :
    (FiniteLaw.pi μfamily).probability (fun σ=>∀ a∈T,rawIntervalFamilyState π d σ a=some (Sum.inr (j a)))=
      ∏ a∈T,s a.2 (j a) := by
  have hh := finiteLaw_disjoint_supported_family μfamily (rawIntervalFamilyCoordinates π d)
    (fun a σ=>rawIntervalFamilyState π d σ a=some (Sum.inr (j a)))
    (by intro a σ τ ha;rw [rawIntervalFamilyState_supported π d σ τ a ha]) T
    (fun a ha b hb hab=>rawIntervalFamilyCoordinates_disjoint π d a b (hsep a ha b hb hab))
  rw [hh]
  exact Finset.prod_congr rfl (fun a _=>rawIntervalFamily_label_probability π d hd q hq hQ s hs hS hnoshort a (j a))

end Oberwolfach
