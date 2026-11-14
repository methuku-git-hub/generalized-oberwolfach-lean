module

public import Oberwolfach.RawIntervalLabelGraphs
public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section

/-! One common lower-count event for the endpoint spokes of all ordinary
isolator roots. The fixed conflict graph contains every forbidden close pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawWheelCommonHubs_event
    (π : Equiv.Perm V) (F : SimpleGraph V)
    (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hm : 0<Fintype.card U) (j : Color) (pH : ℝ) (hj : ∀ u,s u j=pH)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}:ℝ)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x y : V,x≠y → ¬F.Adj x y →
          |(Fintype.card {u : U // rawWheelSpokes π d σ j x u ∧ rawWheelSpokes π d σ j y u}:ℝ)-
            pH^2*Fintype.card U|<t) := by
  let I := {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}
  let T (a : I) : Finset V := {a.val.1,a.val.2}
  have hsep : ∀ a : I,∀ x∈T a,∀ y∈T a,x≠y → ¬PermutationClose π (3*d) x y := by
    intro a x hx y hy hxy hclose
    have hxyF := hF ⟨hxy,hclose⟩
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact hxy rfl
    · exact a.property.2 hxyF
    · exact a.property.2 hxyF.symm
    · exact hxy rfl
  have hcard : ∀ a : I,(T a).card=2 := by intro a;simp only [T,Finset.card_pair a.property.1]
  have hh := rawIntervalCommonHubs_common_event π d hd q hq hQ s hs hS hnoshort hm j pH hj
    T hsep (fun a=>Finset.insert_nonempty _ _) 2 (by omega) (fun a=>(hcard a).le) t ht
  have hproj := finiteLaw_pi_injective_projection_event
    (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS) Sum.inr Sum.inr_injective
    (fun ω=>∀ a : I,|(Fintype.card {u : U // ∀ v∈T a,rawIntervalFamilyState π d ω (v,u)=some (Sum.inr j)}:ℝ)-
      pH^(T a).card*Fintype.card U|<t)
  erw [← hproj] at hh
  simp only [Nat.cast_ofNat] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy hfxy
  have hi := hσ ⟨(x,y),hxy,hfxy⟩
  rw [hcard] at hi
  convert hi using 1
  congr 3
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun u=>by simp only [T,Finset.mem_insert,Finset.mem_singleton,
    forall_eq_or_imp,forall_eq,rawWheelSpokes])

end Oberwolfach
