module

public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section

/-! Exact potential-load expectations and a simultaneous concentration
event for the original ordinary full-host sampling experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawWheelLaw (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) :
    ∀ e : RawWheelCoordinate V U,FiniteLaw (RawWheelCoordinateState Γ Color e)
  | Sum.inl e=>FiniteLaw.retentionCoin (ρ e) (hρ e) (hρ1 e)
  | Sum.inr e=>rawIntervalFamilyLaw d hd q hq hQ s hs hS e

def rawWheelMarginal (P : SimpleGraph V) (ρ : Sym2 V → ℝ) (s : U → Color → ℝ)
    (j : Color) : Sym2 V⊕(V×U) → ℝ
  | Sum.inl e=>if e∈P.edgeSet then ρ e else 0
  | Sum.inr a=>s a.2 j

variable (P : SimpleGraph V) (π : Equiv.Perm V)
    (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))

local notation "μwheel" => rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS

theorem rawWheelResource_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (j : Color) (a : Sym2 V⊕(V×U)) :
    (FiniteLaw.pi μwheel).probability (fun σ=>
      ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j) a=true)=
      rawWheelMarginal P ρ s j a := by
  cases a with
  | inl e=>
    induction e using Sym2.ind with
    | _ x y=>
      by_cases hp : P.Adj x y
      · simp only [ordinaryResourceState,Sum.elim_inl,rawWheelGraph,SimpleGraph.mem_edgeSet,
          retainedGraph,hp,true_and,decide_eq_true_eq,rawWheelMarginal,ite_true]
        rw [finiteLaw_pi_coordinate_probability μwheel (Sum.inl s(x,y)) true]
        rfl
      · simp [ordinaryResourceState,rawWheelGraph,retainedGraph,hp,rawWheelMarginal,
          SimpleGraph.mem_edgeSet,FiniteLaw.probability]
  | inr a=>
    simp only [ordinaryResourceState,Sum.elim_inr,decide_eq_true_eq,rawWheelSpokes,rawWheelMarginal]
    have hh := finiteLaw_pi_injective_projection_event μwheel Sum.inr Sum.inr_injective
      (fun σ=>rawIntervalFamilyState π d σ a=some (Sum.inr j))
    rw [hh]
    exact rawIntervalFamily_label_probability π d hd q hq hQ s hs hS hnoshort a j

theorem ordinaryRawPotentialLoad_expectation
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (F : SimpleGraph V) (Hbase : V → U → Prop) (r : ℕ)
    (hF : permutationConflictGraph π (3*d)≤F)
    (w : OrdinaryWheel P F Hbase r → ℝ) (j : Color) (root : Sym2 V⊕(V×U)) :
    (FiniteLaw.pi μwheel).expectation (fun σ=>
      ordinaryPotentialLoad w root (rawWheelGraph P σ) (rawWheelSpokes π d σ j))=
      ∑ W,(if root∈ordinaryWheelResources W then w W else 0)*
        ∏ a∈ordinaryWheelResources W\{root},rawWheelMarginal P ρ s j a := by
  have hh := resourcePatternLoad_supported_expectation μwheel ordinaryWheelResources w
    (fun _ _=>true) (rawWheelResourceCoordinates π d)
    (fun σ=>ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j))
    (rawWheelResourceState_supported P π d j) root
    (by
      intro W _ a ha b hb hab
      exact rawWheelCoordinates_candidate_disjoint P F Hbase π d r hF W a b
        (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab)
  change (FiniteLaw.pi μwheel).expectation (fun σ=>
    ordinaryPotentialLoad w root (rawWheelGraph P σ) (rawWheelSpokes π d σ j))=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro W _
  congr 1
  exact Finset.prod_congr rfl (fun a _=>rawWheelResource_probability P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort j a)

theorem ordinaryRawPotentialLoad_common_event
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (F : SimpleGraph V) (Hbase : V → U → Prop) (r : ℕ)
    (hF : permutationConflictGraph π (3*d)≤F) (hr : 2≤r)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel P F Hbase r → ℝ) (B : ℝ) (hB : 0<B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (j : Color) (t : ℝ) (ht : 0<t) :
    1-(Fintype.card (Sym2 V⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))))≤
      (FiniteLaw.pi μwheel).probability (fun σ=>∀ root,
        |ordinaryPotentialLoad w root (rawWheelGraph P σ) (rawWheelSpokes π d σ j)-
          ∑ W,(if root∈ordinaryWheelResources W then w W else 0)*
            ∏ a∈ordinaryWheelResources W\{root},rawWheelMarginal P ρ s j a|<t) := by
  have hh := ordinaryPotentialLoad_supported_common_event P F Hbase r hr hn hu w B hB.le hw
    μwheel (rawWheelGraph P) (fun σ=>rawWheelSpokes π d σ j) (rawWheelResourceCoordinates π d)
    (rawWheelResourceState_supported P π d j) (4*(d:ℝ)+3) (by positivity) hB
    (by intro a;exact_mod_cast rawWheelResourceCoordinates_card π d a)
    (by intro e;exact_mod_cast rawWheelResourceCoordinates_reverse_card π d e) t ht
  simpa only [ordinaryRawPotentialLoad_expectation P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort F Hbase r hF w j] using hh

/-- The same event controls every subsequent modification on the fixed
vertex domains. Its realised degree cost has no sampling-density factor. -/
theorem ordinaryRawPotentialLoad_adaptive_common_event
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (F : SimpleGraph V) (Hbase : V → U → Prop) (r : ℕ)
    (hF : permutationConflictGraph π (3*d)≤F) (hr : 2≤r)
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel P F Hbase r → ℝ) (B : ℝ) (hB : 0<B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (j : Color) (t a : ℝ) (ht : 0<t) (ha : 0≤a) :
    1-(Fintype.card (Sym2 V⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((r:ℝ)^4*B/Fintype.card V)*(2*r)*((r:ℝ)^2*B))))≤
      (FiniteLaw.pi μwheel).probability (fun σ=>∀ (Q' : SimpleGraph V) (H' : V → U → Prop),
        (∀ x,(∑ y,bipAdj (fun x y=>¬((rawWheelGraph P σ).Adj x y↔Q'.Adj x y)) x y)≤a) →
        (∀ x,(∑ u,bipAdj (fun x u=>¬(rawWheelSpokes π d σ j x u↔H' x u)) x u)≤a) →
        (∀ u,(∑ x,bipAdj (fun x u=>¬(rawWheelSpokes π d σ j x u↔H' x u)) x u)≤a) →
        (∀ x y,x≠y → |ordinaryPotentialLoad w (Sum.inl s(x,y)) Q' H'-
          ∑ W,(if Sum.inl s(x,y)∈ordinaryWheelResources W then w W else 0)*
            ∏ e∈ordinaryWheelResources W\{Sum.inl s(x,y)},rawWheelMarginal P ρ s j e|≤
              t+8*(r:ℝ)^4*B*a/Fintype.card V) ∧
        (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) Q' H'-
          ∑ W,(if Sum.inr (v,u)∈ordinaryWheelResources W then w W else 0)*
            ∏ e∈ordinaryWheelResources W\{Sum.inr (v,u)},rawWheelMarginal P ρ s j e|≤
              t+4*(r:ℝ)^4*B*a/Fintype.card V)) := by
  have hh := ordinaryPotentialLoad_adaptive_common_event P F Hbase r hr hn hu w B hB.le hw
    μwheel (rawWheelGraph P) (fun σ=>rawWheelSpokes π d σ j) (rawWheelResourceCoordinates π d)
    (rawWheelResourceState_supported P π d j) (4*(d:ℝ)+3) (by positivity) hB
    (by intro e;exact_mod_cast rawWheelResourceCoordinates_card π d e)
    (by intro e;exact_mod_cast rawWheelResourceCoordinates_reverse_card π d e) t a ht ha
  simpa only [ordinaryRawPotentialLoad_expectation P π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort F Hbase r hF w j] using hh

end Oberwolfach
