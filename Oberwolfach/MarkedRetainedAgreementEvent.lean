module

public import Oberwolfach.MarkedReferenceInputStability
public import Oberwolfach.MarkedFullNeighbourhoodEvent
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.MarkedNeighbourhoodSpokeChanges
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section

/-! The same retained outcome satisfies all row and index inequalities.
Retention losses are bounded by realised changed spokes. Product targets
and the original outer-domain error scales are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_full_neighbourhood_with_agreement_event (h d Q:ℕ) (hd:2≤d) (ω ε pret:ℝ)
    (hω:0<ω) (hε:0<ε) (hpret:0<pret):
    ∃ M N:ℕ,1≤M∧2≤N∧∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V→M≤Fintype.card V→M≤Fintype.card U→Fintype.card U≤Fintype.card V→
      ω*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),(∀ x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
      (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (g:Γ) (j:Color)
      (t₀:ℝ),(∀ u,q u g=t₀)→pret*Fintype.card V≤t₀*Fintype.card U→
    1-1/(Fintype.card V:ℝ)^Q≤
      (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>let H:Bool→V→U→Prop := retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
          MarkedRowsWithSpokes P π d h Finset.univ p k q s g j (ε*Fintype.card V) z.1 H∧
          MarkedIndicesWithSpokes π d h Finset.univ q s g j (ε*Fintype.card U) z.1 H ∧
          (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d z.1 g j b x u↔H b x u) then (1:ℝ) else 0)≤(ε/(2*((h:ℝ)+1)))*Fintype.card U) ∧
          (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d z.1 g j b x u↔H b x u) then (1:ℝ) else 0)≤(ε/(2*((h:ℝ)+1)))*Fintype.card V) ∧
          (∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (δ:ℝ),(∀ z,(DS.degree z:ℝ)≤δ) →
            (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims z.1 DR.edgeFinset) g j b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤(ε/(2*((h:ℝ)+1)))*Fintype.card U+δ) ∧
            (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims z.1 DR.edgeFinset) g j b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤(ε/(2*((h:ℝ)+1)))*Fintype.card V+δ))):=by
  let ζ:=ε/(2*((h:ℝ)+1))
  have hζ:0<ζ:=by dsimp[ζ];positivity
  have hfrac:(h:ℝ)*ζ≤ε/2:=by
    dsimp[ζ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity:0<2*((h:ℝ)+1))).mpr
    nlinarith only [hε]
  obtain ⟨Nr,hNr,hr⟩:=marked_full_neighbourhood_common_event h d (Q+1) hd ω (ε/2) hω (by positivity)
  obtain ⟨M,Nt,hM,hNt,ht⟩:=raw_marked_retention_common_event d hd 0 ((Q+1:ℕ):ℝ) pret ζ hpret hζ
  refine ⟨M,max Nr Nt,hM,hNr.trans (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hMV hMU hU hωU P π hπ p k hp hk hphys q hq hQ s hs hS g j t₀ ht₀ hmass
  let E:=fun σ:RawMarkedOutcome V U Γ Color=>
    RawMarkedRows P π d h Finset.univ p k q s g j ((ε/2)*Fintype.card V) σ∧
    RawMarkedIndices π d h Finset.univ q s g j ((ε/2)*Fintype.card U) σ
  have hE:1-1/(Fintype.card V:ℝ)^(Q+1)≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E:=
    hr V U Γ Color (by omega) hU hωU P π hπ p k hp hk hphys q hq hQ s hs hS g j
  have hb:=ht V U Γ Color Unit (by omega) hU (by simp) π hπ p k hp hk hphys q hq hQ s hs hS
    g t₀ ht₀ hmass (fun _=>Finset.univ) (fun _=>Finset.univ) (by simp)
    (by simpa using hMV) (by simpa using hMU) E (1/(Fintype.card V:ℝ)^(Q+1)) hE
  have heq:(Fintype.card V:ℝ)^(-((Q+1:ℕ):ℝ))=1/(Fintype.card V:ℝ)^(Q+1):=by
    rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_natCast,one_div]
  rw [heq] at hb
  have hn2:2≤Fintype.card V:=by omega
  have hn0:0<Fintype.card V:=by omega
  have hnum:=scaled_inverse_power_le (Fintype.card V) Q hn0 2 (by exact_mod_cast hn2)
  have hnum' : 2*(1/(Fintype.card V:ℝ)^(Q+1))≤1/(Fintype.card V:ℝ)^Q:=by
    convert hnum using 1 <;> ring
  have hbound:1-1/(Fintype.card V:ℝ)^Q≤1-1/(Fintype.card V:ℝ)^(Q+1)-1/(Fintype.card V:ℝ)^(Q+1):=by
    linarith only [hnum']
  apply (hbound.trans hb).trans
  apply finiteLaw_probability_mono
  intro z hz
  let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
  obtain ⟨hc,hi⟩:=retainedMarkedSpokes_restriction_changes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2
    (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ hz.2.2 g j ()
  have hcol:∀ a u,(∑ x∈(Finset.univ:Finset V),if ¬(rawMarkedPairSpokes π d z.1 g j a x u↔H a x u) then (1:ℝ) else 0)≤ζ*Fintype.card V:=by
    intro a u
    have hh:=hc a u
    simp only [Finset.card_univ] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro x _
    simp only [bipAdj,rawMarkedPairSpokes,H]
    split_ifs <;> rfl
  have hrow:∀ a x,(∑ u∈(Finset.univ:Finset U),if ¬(rawMarkedPairSpokes π d z.1 g j a x u↔H a x u) then (1:ℝ) else 0)≤ζ*Fintype.card U:=by
    intro a x
    have hh:=hi a x
    simp only [Finset.card_univ] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro u _
    simp only [bipAdj,rawMarkedPairSpokes,H]
    split_ifs <;> rfl
  have hR:=markedRows_spoke_changes P π d h Finset.univ p k q s g j ((ε/2)*Fintype.card V)
    (ζ*Fintype.card V) (by positivity) z.1 H hz.1.1 hcol
  have hI:=markedIndices_spoke_changes π d h Finset.univ q s g j ((ε/2)*Fintype.card U)
    (ζ*Fintype.card U) (by positivity) z.1 H hz.1.2 hrow
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro S T J hS hT hJ hInj
    exact (hR S T J hS hT hJ hInj).trans_le (by nlinarith only [mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg (Fintype.card V))])
  · intro J hJ hsep
    exact (hI J hJ hsep).trans_le (by nlinarith only [mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg (Fintype.card U))])
  · intro b x; simpa [ζ] using hrow b x
  · intro b u; simpa [ζ] using hcol b u
  · intro DR DS δ hDS
    exact marked_spoke_reference_change_after_deletion π d z.1 g j H DR DS
      (ζ*Fintype.card U) (ζ*Fintype.card V) δ hrow hcol hDS

end Oberwolfach
