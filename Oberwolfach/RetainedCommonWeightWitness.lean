module

public import Oberwolfach.CommonWeightWitnessBounds
public import Oberwolfach.RawMarkedRetentionEvent
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section

/-! One retained-host event for all common-weight witnesses. The selectors
are obtained on a common raw event, then kept fixed through the original
global retention. No selector or coefficient is resampled after a deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem commonPotentialSpokeLoads_change
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (hm : 3≤m) (hn : 0<Fintype.card V)
    (D τ A B p k sbar pstar : ℝ) (hB : 0≤B)
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (hpstar : 0<pstar) (hpmin : pstar≤p) (hkmin : pstar≤k) (hsmin : pstar≤sbar)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : sbar≤1)
    (weight : (Fin (m+1)→V)→ℝ) (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (ε δ : ℝ) (hδ : 0≤δ) (σ : RawMarkedOutcome V U Γ Color)
    (H H' : Bool→V→U→Prop) (κ : V→Bool) (u u' : U)
    (hraw : CommonPotentialSpokeLoads P π d m D p k sbar weight ε σ H κ u u')
    (hc : ∀ b z,(∑ x,if ¬(H b x z↔H' b x z) then (1:ℝ) else 0)≤δ) :
    CommonPotentialSpokeLoads P π d m D p k sbar weight
      (ε+10*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*δ/Fintype.card V) σ H' κ u u' := by
  let Parent := MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_ : V) (_ : Unit)=>True) (fun _ _=>True)
  let seed := fun W : Parent=>weight W.1.val/(D*p^m*k*sbar^m)
  have hseed (W : Parent) := successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
    p k sbar pstar hpstar hpmin hkmin hsmin hp1 hk1 hs1 hB W.1.val
  intro b v
  have hh := commonThinnedSpokes_potential_load_change hm hn seed (2*B/pstar^(2*m+1)) (by positivity)
    hseed (rawMarkedPairRims P π d σ) H H' κ u u' δ hδ hc b v
  exact (abs_sub_le _ _ _).trans ((add_le_add hh (hraw b v)).trans_eq (by ring))

theorem retainedMarked_common_weight_event
    (m d : ℕ) (hm : 3≤m) (hd : 2≤d) (B pstar ε Q pret ζ : ℝ)
    (hB : 0<B) (hpstar : 0<pstar) (hε : 0<ε) (hpret : 0<pret) (hζ : 0<ζ) :
    ∃ M N : ℕ,1≤M ∧ 1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V → M≤Fintype.card V → M≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (D τ A : ℝ) (weight : (Fin (m+1)→V)→ℝ),
      SuccessorSequenceWeightConditions P π (3*d) D τ A B weight →
      (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    ∀ (p k s₀ : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1),
      0<s₀ → pstar≤p → pstar≤k → pstar≤s₀*s₀/m → p≤1 → k≤1 → s₀*s₀/m≤1 →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (j : Color),(∀ u,q u g=s₀/m) → (∀ u,s u j=s₀) →
      pret*Fintype.card V≤(s₀/m)*Fintype.card U →
    1-8*(Fintype.card V:ℝ)^4*Real.exp
        (-commonWeightLoadExponent m d (2*B/pstar^(2*m+1)) ε*Fintype.card V)-(Fintype.card V:ℝ)^(-Q)≤
    (rawMarkedRetentionLaw π d hd g p k hp.le hk.le hphys q hq hQ s hs hS).probability
      (fun z=>∀ u u',u≠u' → ∃ κ,CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight
        (τ+ε+10*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*ζ) z.1
        (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j) κ u u') := by
  obtain ⟨M,N,hM,hN,hret⟩ := raw_marked_retention_common_event d hd 0 Q pret ζ hpret hζ
  refine ⟨M,N,hM,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hMV hMU hu P π hnoshort D τ A weight hw hDlo hDhi
    p k s₀ hp hk hphys hs₀ hpmin hkmin hsmin hp1 hk1 hs1 q hq hQ s hs hS g j hq₀ hs₀' hmass
  have hnpos : 0<Fintype.card V := by omega
  let err := 8*(Fintype.card V:ℝ)^4*Real.exp
      (-commonWeightLoadExponent m d (2*B/pstar^(2*m+1)) ε*Fintype.card V)
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ u u',u≠u' → ∃ κ,
    CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight (τ+ε) σ (rawMarkedPairSpokes π d σ g j) κ u u'
  have hE : 1-err≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS)).probability E :=
    rawMarked_common_weight_exponential_event P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
      m hm g j s₀ D τ A B hs₀ hB hq₀ hs₀' weight hw hnpos hu hDlo hDhi pstar hpstar hpmin hkmin hsmin hp1 hk1 hs1 ε hε
  have hb := hret V U Γ Color Unit hn hu (by simp)
    π hnoshort p k hp.le hk.le hphys q hq hQ s hs hS g (s₀/m) hq₀ hmass
    (fun _=>Finset.univ) (fun _=>Finset.univ) (by simp)
    (by simpa using hMV) (by simpa using hMU) E err hE
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz u u' huu
  obtain ⟨κ,hκ⟩ := hz.1 u u' huu
  refine ⟨κ,?_⟩
  have hc := (retainedMarkedSpokes_restriction_changes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2
    (fun _ : Unit=>Finset.univ) (fun _ : Unit=>Finset.univ) ζ hz.2.2 g j ()).1
  have hh := commonPotentialSpokeLoads_change P π d m hm hnpos D τ A B p k (s₀*s₀/m) pstar hB.le
    hDlo hDhi hpstar hpmin hkmin hsmin hp1 hk1 hs1 weight hw (τ+ε) (ζ*Fintype.card V) (by positivity)
    z.1 (rawMarkedPairSpokes π d z.1 g j)
    (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j) κ u u' hκ (by
      intro b z'
      have hh := hc b z'
      simp only [Finset.card_univ] at hh
      convert hh using 1
      apply Finset.sum_congr rfl
      intro x hx
      simp only [bipAdj,rawMarkedPairSpokes]
      split_ifs <;> first | rfl | (exfalso; tauto))
  have he : τ+ε+10*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*(ζ*Fintype.card V)/Fintype.card V=
      τ+ε+10*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*ζ := by
    have hn0 : (Fintype.card V:ℝ)≠0 := (Nat.cast_pos.mpr hnpos).ne'
    field_simp
  rw [he] at hh
  exact hh

end Oberwolfach
