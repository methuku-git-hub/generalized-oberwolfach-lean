module

public import Oberwolfach.RawIntervalAllPairCodegree
public import Oberwolfach.ActualReservedPairListsFromCommonIndices
public import Oberwolfach.ActualReservedMatchingOuterSlack

@[expose] public section
/-! One event supplies matching lists for every later choice of the bounded
reserved set, inner indices, bad graph, old images and forbidden indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalOrdinaryOuter (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (j:Color) (u:U):Finset V:=
  Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr j))

def rawIntervalReservedMatchingEvent (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (j:Color) (α:ℝ):Prop :=
  let Outer:=rawIntervalOrdinaryOuter π d σ j;
        (∀x y:V,x≠y→2*α*Fintype.card V≤
          ((((Finset.univ:Finset U).filter (fun u=>x∈Outer u))∩
            ((Finset.univ:Finset U).filter (fun u=>y∈Outer u))).card:ℝ)) ∧
        ∀ (C:Finset (Finset V⊕(V×U))) (Hold:Bool→V→U→Prop) (Inner:Finset U)
          (K:SimpleGraph V) (Old:U→Finset V) (Bad:V→Finset U),
          (Inner.card:ℝ)+2*C.card≤α*Fintype.card V→
          (∀u,Disjoint (Old u) (Outer u))→
          let S:=fun e=>commonOuterPairIndices Outer e\Inner;
          let A:=actualReservedOrdinarySpokeLabels C Hold;
          let L:=reservedSpokeMatchingList S A;
          (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
          (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
          (∀u e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old u→u∈L e→u∈Bad v) ∧
          (∀e∈K.edgeFinset,∀v∈e.toFinset,∀u∈L e,v∉A u)

theorem raw_interval_actual_reserved_matching_common_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hm:0<Fintype.card U) (j:Color) (s₀:ℝ) (hs₀:0≤s₀) (hsl:∀u,s₀≤s u j)
    (t α:ℝ) (ht:0<t)
    (hmargin:2*α*Fintype.card V+t≤(5/8:ℝ)*s₀^2*Fintype.card U):
    1-(Fintype.card V:ℝ)^2*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>rawIntervalReservedMatchingEvent π d σ j α) :=by
  have hh:=raw_interval_all_pair_spoke_codegree_event π d hd q hq hQ s hs hS hnoshort hm j s₀ hs₀ hsl t ht
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  unfold rawIntervalReservedMatchingEvent
  dsimp only
  let Outer:=rawIntervalOrdinaryOuter π d σ j
  have hPairs:∀x y:V,x≠y→2*α*Fintype.card V≤
    ((((Finset.univ:Finset U).filter (fun u=>x∈Outer u))∩
      ((Finset.univ:Finset U).filter (fun u=>y∈Outer u))).card:ℝ):=by
    intro x y hxy
    have hx:=hσ x y hxy
    have heq:((Finset.univ:Finset U).filter (fun u=>x∈Outer u))∩
       ((Finset.univ:Finset U).filter (fun u=>y∈Outer u))=
       (Finset.univ.filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr j) ∧
         rawIntervalFamilyState π d σ (y,u)=some (Sum.inr j))):=by
      ext u
      simp [Outer,rawIntervalOrdinaryOuter]
    rw [heq]
    linarith
  refine ⟨hPairs,?_⟩
  intro C Hold Inner K Old Bad hLoss hOld
  have hCommon:=actual_common_outer_pair_slack_from_codegrees C Outer Inner K α hPairs hLoss
  have hLists:=actual_outer_pair_lists_from_common_slack C Outer Inner K α hCommon
  exact actual_reserved_matching_inputs_from_outer_slack C Hold
    (fun e=>commonOuterPairIndices Outer e\Inner) K Inner Old Outer Bad α hLists.2.2 hLists.1 hLists.2.1 hOld
end Oberwolfach
