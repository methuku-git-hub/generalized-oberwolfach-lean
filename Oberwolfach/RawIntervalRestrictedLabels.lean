module

public import Oberwolfach.RawIntervalHubRestriction

@[expose] public section

/-! Simultaneous index counts on an arbitrary fixed hub domain. The
vertex labels may lie outside a later inner vertex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalSelectedLabelCountOn (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : V→Γ⊕Color) (T : Finset V) (B : Finset U) : ℝ :=
  ∑ u∈B,if ∀ v∈T,rawIntervalFamilyState π d σ (v,u)=some (j v) then 1 else 0

theorem rawIntervalSelectedLabelCount_restrict_hubs (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : V→Γ⊕Color) (T : Finset V) (B : Finset U) :
    rawIntervalSelectedLabelCount π d (rawIntervalRestrictHubs (fun u : B=>u.val) σ) j T=
      rawIntervalSelectedLabelCountOn π d σ j T B := by
  unfold rawIntervalSelectedLabelCount rawIntervalSelectedLabelCountOn
  simp only [rawIntervalRestrictHubs_state]
  exact Finset.sum_coe_sort B (fun u : U=>if ∀ v∈T,rawIntervalFamilyState π d σ (v,u)=some (j v) then (1:ℝ) else 0)

theorem rawIntervalSelectedLabelCountOn_common_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (B : Finset U) (hB : B.Nonempty)
    {I : Type} [Fintype I] (j : I→V→Γ⊕Color) (T : I→Finset V)
    (hsep : ∀ i,∀ x∈T i,∀ y∈T i,x≠y → ¬PermutationClose π (3*d) x y)
    (hT : ∀ i,(T i).Nonempty) (k : ℕ) (hk : 0<k) (hsize : ∀ i,(T i).card≤k)
    (t : ℝ) (ht : 0<t) :
    1-(Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*B.card))))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ i,|rawIntervalSelectedLabelCountOn π d σ (j i) (T i) B-
        ∑ u∈B,∏ v∈T i,Sum.elim (q u) (s u) (j i v)|<t) := by
  let E := fun τ : RawIntervalFamilyOutcome V B Γ Color=>∀ i,
    |rawIntervalSelectedLabelCount π d τ (j i) (T i)-
      ∑ u : B,∏ v∈T i,Sum.elim (q u.val) (s u.val) (j i v)|<t
  have hh := rawIntervalSelectedLabelCount_common_event π d hd
    (fun u : B=>q u.val) (fun u=>hq u.val) (fun u=>hQ u.val)
    (fun u : B=>s u.val) (fun u=>hs u.val) (fun u=>hS u.val) hnoshort
    (by simpa only [Fintype.card_coe] using hB.card_pos) j T hsep hT k hk hsize t ht
  rw [← rawInterval_hub_restriction_probability (fun u : B=>u.val) Subtype.val_injective
    d hd q hq hQ s hs hS E] at hh
  have hsum (i : I) : (∑ u : B,∏ v∈T i,Sum.elim (q u.val) (s u.val) (j i v))=
      ∑ u∈B,∏ v∈T i,Sum.elim (q u) (s u) (j i v) := Finset.sum_coe_sort B (fun u : U=>∏ v∈T i,Sum.elim (q u) (s u) (j i v))
  simpa only [E,Fintype.card_coe,rawIntervalSelectedLabelCount_restrict_hubs,hsum] using hh

end Oberwolfach
