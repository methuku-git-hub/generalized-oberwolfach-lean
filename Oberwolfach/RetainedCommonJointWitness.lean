module

public import Oberwolfach.CommonWitnessTransfer

@[expose] public section

/-! The complete common witness in the original globally retained sample.
The raw selector certifies all required quantities at once and is held
fixed when the interval family is trimmed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retainedMarked_common_joint_witness_event
    (r : ℕ) (hr : 1≤r) (α astar pstar B εsize εload pret ζ : ℝ)
    (hα : 0<α) (hα1 : α≤1/2) (hastar : 0<astar) (hpstar : 0<pstar)
    (hB : 0<B) (hεsize : 0<εsize) (hεload : 0<εload) (hpret : 0<pret) (hζ : 0<ζ)
    (d Q : ℕ) (hd : 2≤d) :
    ∃ M N : ℕ,1≤M ∧ 1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U],
      N≤Fintype.card V → M≤Fintype.card V → M≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1),pstar≤p → pstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (j : Color) (s₀ D τ A : ℝ),0<s₀ →
      (∀ u,q u g=s₀/((r+4:ℕ):ℝ)) → (∀ u,s u j=s₀) →
      pstar≤s₀*s₀/((r+4:ℕ):ℝ) → s₀*s₀/((r+4:ℕ):ℝ)≤1 →
      astar≤(s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) → astar≤s₀*s₀/((r+4:ℕ):ℝ) →
      pret*Fintype.card V≤(s₀/((r+4:ℕ):ℝ))*Fintype.card U →
    ∀ weight : (Fin (r+4+1)→V)→ℝ,
      SuccessorSequenceWeightConditions P π (3*d) D τ A B weight →
      (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    1-2/(Fintype.card V:ℝ)^Q≤
      (rawMarkedRetentionLaw π d hd g p k hp.le hk.le hphys q hq hQ s hs hS).probability
        (fun z=>∀ u u',u≠u' → ∃ κ,
          CommonWitnessEstimates P π d r D p k s₀ (εsize+2*ζ) (4*ζ)
            (τ+εload+10*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*ζ)
            (pstar^(r+5)*(α*(astar/2)/4)^(r+5)/2-2*(r+5:ℕ)*ζ)
            (pstar^(r+7)*(α*(astar/2)/4)^(r+4)/2-2*(r+4:ℕ)*ζ) weight z.1
            (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j) κ u u') := by
  obtain ⟨N₀,hN₀pos,hN₀⟩ := rawMarked_common_joint_witness_event r hr α astar pstar B εsize εload
    hα hα1 hastar hpstar hB hεsize hεload d Q hd
  obtain ⟨M,N₁,hM,hN₁,hret⟩ := raw_marked_retention_common_event d hd 0 (Q:ℝ) pret ζ hpret hζ
  refine ⟨M,max N₀ N₁,hM,hN₀pos.trans (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hMV hMU huCard P π hP hnoshort p k hp hk hphys hpmin hkmin q hq hQ s hs hS g j s₀ D τ A hs₀ hq₀ hs₀' hsmin hs1 hqclass hsclass hmass weight hw hDlo hDhi
  have hnpos : 0<Fintype.card V := by omega
  let E := fun σ : RawMarkedOutcome V U Γ Color=>∀ u u',u≠u' → ∃ κ,
    RawCommonWitness P π d r α astar pstar D p k s₀ εsize (τ+εload) weight g j u u' σ κ
  have hE : 1-1/(Fintype.card V:ℝ)^Q≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS)).probability E :=
    hN₀ V U Γ Color (by omega) huCard P π hP hnoshort p k hp hk hphys hpmin hkmin
      q hq hQ s hs hS g j s₀ D τ A hs₀ hq₀ hs₀' hsmin hs1 hqclass hsclass weight hw hDlo hDhi
  have hb := hret V U Γ Color Unit (by omega) huCard (by simp)
    π hnoshort p k hp.le hk.le hphys q hq hQ s hs hS g (s₀/((r+4:ℕ):ℝ)) hq₀ hmass
    (fun _=>Finset.univ) (fun _=>Finset.univ) (by simp)
    (by simpa using hMV) (by simpa using hMU) E (1/(Fintype.card V:ℝ)^Q) hE
  have heq : (Fintype.card V:ℝ)^(-(Q:ℝ))=1/(Fintype.card V:ℝ)^Q := by
    rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_natCast,one_div]
  rw [heq] at hb
  have he : 1-2/(Fintype.card V:ℝ)^Q=1-1/(Fintype.card V:ℝ)^Q-1/(Fintype.card V:ℝ)^Q := by ring
  rw [he]
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz u u' huu
  obtain ⟨κ,hκ⟩ := hz.1 u u' huu
  refine ⟨κ,?_⟩
  have hc := (retainedMarkedSpokes_restriction_changes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2
    (fun _ : Unit=>Finset.univ) (fun _ : Unit=>Finset.univ) ζ hz.2.2 g j ()).1
  apply rawCommonWitness_transfer P π d r hr hnpos α astar pstar D p k s₀ τ A B εsize εload ζ
    hB.le hζ.le hpstar hpmin hkmin hsmin (by linarith) (by linarith) hs1 weight hw hDlo hDhi
    g j z.1 _ κ u u' hκ
  intro b z'
  have hh := hc b z'
  simp only [Finset.card_univ] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  simp only [bipAdj,rawMarkedPairSpokes]
  split_ifs <;> first | rfl | (exfalso;tauto)

end Oberwolfach
