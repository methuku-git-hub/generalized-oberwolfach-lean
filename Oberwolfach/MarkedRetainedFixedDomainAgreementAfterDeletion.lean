module

public import Oberwolfach.MarkedRetainedFixedDomainAgreementWithEvent
public import Oberwolfach.MarkedReferenceDomainAgreementDeletion
public import Oberwolfach.MarkedRetainedFixedDomainAgreementEvent
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! On one original retained sample, raw and retained spoke relations
agree up to the prescribed row and column errors on every fixed domain,
including at roots outside that domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_fixed_domain_agreement_after_deletion_with_event (d:ℕ) (hd:2≤d)
    (C Q pstar ζ:ℝ) (hpstar:0<pstar) (hζ:0<ζ):
    ∃ m N:ℕ,1≤m∧1≤N∧∀ (V U Γ Color I:Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
      (Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^C →
    ∀ (π:Equiv.Perm V),(∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
      (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g:Γ) (t₀:ℝ),(∀ u,q u g=t₀) → pstar*Fintype.card V≤t₀*Fintype.card U →
    ∀ (S:I→Finset V) (T:I→Finset U),
      (∀ i x,π x∈S i↔x∈S i) → (∀ i,m≤(S i).card) → (∀ i,m≤(T i).card) →
    ∀ j:Color,∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g→Prop) (δ:ℝ),
    1-δ≤(rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability E →
    1-δ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>E z ∧ ∀ i,
          (∀ b u,(∑ v∈S i,bipAdj (fun x u=>¬(rawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g j b x u ↔
            retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j b x u)) v u)≤ζ*(S i).card) ∧
          (∀ b v,(∑ u∈T i,bipAdj (fun x u=>¬(rawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g j b x u ↔
            retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j b x u)) v u)≤ζ*(T i).card) ∧
          (∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (δ:ℝ),(∀ z,(DS.degree z:ℝ)≤δ) →
            let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j;
            (∀ b v,(∑ u∈T i,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims z.1 DR.edgeFinset) g j b v u↔markedDeletePhysicalSpokes H DS b v u) then (1:ℝ) else 0)≤ζ*(T i).card+δ) ∧
            (∀ b u,(∑ v∈S i,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims z.1 DR.edgeFinset) g j b v u↔markedDeletePhysicalSpokes H DS b v u) then (1:ℝ) else 0)≤ζ*(S i).card+δ))) := by
  obtain ⟨m,N,hm,hN,hgood⟩:=marked_retained_fixed_domain_agreement_with_event d hd C Q pstar ζ hpstar hζ
  refine ⟨m,N,hm,hN,?_⟩
  intro V U Γ Color I _ _ _ _ _ _ _ _ hn hu hI π hπ p k hp hk hphys q hq hQ s hs hS g t₀ hg hmass S T hInv hSc hTc j E δ hE
  have hG:=hgood V U Γ Color I hn hu hI π hπ p k hp hk hphys q hq hQ s hs hS g t₀ hg hmass S T hInv hSc hTc j E δ hE
  apply hG.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  intro i
  refine ⟨(hz.2 i).1,(hz.2 i).2,?_⟩
  intro DR DS δD hDS
  let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
  have hcol:∀ b u,(∑ v∈S i,if ¬(rawMarkedPairSpokes π d z.1 g j b v u↔H b v u) then (1:ℝ) else 0)≤ζ*(S i).card:=by
    intro b u
    have hh:=(hz.2 i).1 b u
    convert hh using 1
    apply Finset.sum_congr rfl
    intro v _
    simp only [bipAdj,rawMarkedPairSpokes,H]
    split_ifs <;> rfl
  have hrow:∀ b v,(∑ u∈T i,if ¬(rawMarkedPairSpokes π d z.1 g j b v u↔H b v u) then (1:ℝ) else 0)≤ζ*(T i).card:=by
    intro b v
    have hh:=(hz.2 i).2 b v
    convert hh using 1
    apply Finset.sum_congr rfl
    intro u _
    simp only [bipAdj,rawMarkedPairSpokes,H]
    split_ifs <;> rfl
  exact marked_spoke_reference_change_after_deletion_on_fixed_domains π d z.1 g j H DR DS
    (S i) (T i) (ζ*(T i).card) (ζ*(S i).card) δD hrow hcol hDS
end Oberwolfach
