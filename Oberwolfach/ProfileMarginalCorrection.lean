module

public import Oberwolfach.ProfileTradeCorrection
public import Oberwolfach.AbsorberTradeSpread

@[expose] public section

/-! The manuscript's vertex-sum correction, with the signed-trade spread
proved from actual labelled absorbers. No trade or counting hypothesis
is added to the original abundance and multiplicity assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
universe uV uC
variable {I T : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T]

theorem profile_marginal_correction (a : I → ℕ) (c J : ℕ) (hc : 1 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (Acoef b B : ℝ) (hAcoef : 0 < Acoef) (hb : 0 < b) :
    ∃ η₀ : ℝ,0 < η₀ ∧ ∀ (V : I → Type uV) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
      (C : Type uC) [Fintype C] [DecidableEq C] (k η : ℝ),2 ≤ k → 0 ≤ η → η ≤ η₀ →
      (∀ i,(Fintype.card (V i):ℝ)=(a i:ℝ)*k) →
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ),
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J) →
      (∀ C₀,b/k^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/k^(c-1)) →
      (∀ i v,|1-hypergraphWeightedDegree R w ⟨i,v⟩| ≤ η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),
        ∃ A : Finset (LabelledAbsorberFamily R S (profileRootSet σ)),Acoef*k^(c*c) ≤ A.card) →
      ∃ ψ : C → ℝ,(∀ v,hypergraphWeightedDegree R ψ v=1) ∧
        ∀ C₀,(b/2)/k^(c-1) ≤ ψ C₀ ∧ ψ C₀ ≤ (B+b/2)/k^(c-1) := by
  let K := (absorberTradeCountConstant c J (Fintype.card T):ℝ)*(c:ℝ)^(c*c)/Acoef
  let D := (1+4*(c:ℝ))*K*(c+1)
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hD : 0 ≤ D := by dsimp [D];positivity
  refine ⟨b/(2*(D+1)),by positivity,?_⟩
  intro V _ _ C _ _ k η hk hη hη₀ hn R w hR hJ hw herr habs
  have hk0 : 0 < k := by linarith
  letI : ∀ i,Nonempty (FixedSubset (V i) (a i)) := fun i => by
    have hai : (0:ℝ) < a i := by exact_mod_cast (show 0<a i by have hh:=ha i;omega)
    have hle : a i ≤ Fintype.card (V i) := by
      have hh : (a i:ℝ) ≤ Fintype.card (V i) := by rw [hn i];nlinarith
      exact_mod_cast hh
    obtain ⟨U,hU⟩ := Finset.exists_subset_card_eq hle
    exact ⟨⟨U,hU.2⟩⟩
  choose A hA using habs
  have hcard (C₀ : C) : (R C₀).card=c := by
    rw [sigma_finset_card];simp only [hR];exact hsize
  have hnall : (Fintype.card (Σ i,V i):ℝ)=c*k := by
    simp only [Fintype.card_sigma,Nat.cast_sum,hn,← Finset.sum_mul]
    have he : (∑ i,(a i:ℝ))=c := by exact_mod_cast hsize
    rw [he]
  have htrade (σ : ∀ i,FixedSubset (V i) (a i)) (v : Σ i,V i) :
      hypergraphWeightedDegree R (labelledFamilyTrade R S (profileRootSet σ) (A σ)) v=
        if v∈profileRootSet σ then 1 else 0 := by
    have hpos : 0 < (A σ).card := by
      have hh : (0:ℝ) < (A σ).card := lt_of_lt_of_le (by positivity) (hA σ)
      exact_mod_cast hh
    exact labelled_family_trade_incidence R S (profileRootSet σ) (A σ) (Finset.card_pos.mp hpos) v
  have hspread (σ : ∀ i,FixedSubset (V i) (a i)) (C₀ : C) :
      |labelledFamilyTrade R S (profileRootSet σ) (A σ) C₀| ≤ K/k^c+
        (if (R C₀∩profileRootSet σ).Nonempty then K/k^(c-1) else 0) :=
    labelled_family_trade_spread hc R S (profileRootSet σ) (by rw [profileRootSet_card,hsize])
      J hJ (A σ) Acoef k hAcoef hk0 hnall (hA σ) C₀ (hcard C₀)
  have hsize' : ∑ i,a i=c-1+1 := by omega
  have hec : c-1+1=c := by omega
  obtain ⟨ψ,hψ,herrψ⟩ := profile_trade_correction a (c-1) ha hsize' k η K hk hη hK hn R w hR herr
    (fun σ => labelledFamilyTrade R S (profileRootSet σ) (A σ)) htrade (by simpa only [hec] using hspread)
  have he : (∑ i,(a i:ℝ))=c := by exact_mod_cast hsize
  have he' : (c-1:ℕ)+2=c+1 := by omega
  have hscale : D*η ≤ b/2 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<2*(D+1))).mp hη₀
    nlinarith
  refine ⟨ψ,hψ,?_⟩
  intro C₀
  have hd : |ψ C₀-w C₀| ≤ (b/2)/k^(c-1) := by
    have hh := herrψ C₀
    rw [he] at hh
    have hcR : (c-1:ℕ)=(c:ℝ)-1 := by rw [Nat.cast_sub hc,Nat.cast_one]
    have hbound : (1+4*(c:ℝ))*K*((c-1:ℕ)+2)*η/k^(c-1)=D*η/k^(c-1) := by
      dsimp [D]
      rw [hcR]
      ring
    rw [hbound] at hh
    exact hh.trans (div_le_div_of_nonneg_right hscale (by positivity))
  have hab := abs_le.mp hd
  constructor
  · have hh := (hw C₀).1
    have heq : b/k^(c-1)=2*((b/2)/k^(c-1)) := by ring
    rw [heq] at hh
    linarith
  · have hh := (hw C₀).2
    have heq : (B+b/2)/k^(c-1)=B/k^(c-1)+(b/2)/k^(c-1) := by ring
    rw [heq]
    linarith

end Oberwolfach
