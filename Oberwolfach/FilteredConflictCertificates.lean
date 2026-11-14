module

public import Oberwolfach.CoinConflictCertificates
public import Oberwolfach.FiniteWitnessCertificatesOn

@[expose] public section

/-! Combining the clique-conflict certificate with additional witnessed
conditions at the counted vertices. New vertices satisfying the conditions
do not cancel the charge for a previously counted vertex that is lost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def filteredCoinConflictSet {V C : Type*} (G : SimpleGraph V) (T : Finset V)
    (P : V → (V → C×Bool) → Prop) (σ : V → C×Bool) : Finset V :=
  coinConflictSet G (T.filter (fun v=>P v σ)) σ

theorem filteredCoinConflict_certificate
    {V C : Type*} [Fintype V] (G : SimpleGraph V) (T : Finset V)
    (hT : ∀ u∈T,∀ v∈T,u≠v → G.Adj u v)
    (P : V → (V → C×Bool) → Prop) (W : (V → C×Bool) → V → Finset V)
    {k : ℕ} {c : ℝ}
    (hsize : ∀ σ v,v∈T → P v σ → (W σ v).card≤k)
    (hload : ∀ σ i,((T.filter (fun v=>P v σ ∧ i∈W σ v)).card : ℝ)≤c)
    (hkeep : ∀ σ v,v∈T → P v σ → ∀ τ,(∀ i∈W σ v,σ i=τ i) → P v τ) :
    HasCoordinateCertificateBound
      (fun σ=>((filteredCoinConflictSet G T P σ).card : ℝ))
      (2+c) ((3+(k : ℝ))*(T.card : ℝ)) := by
  classical
  intro σ
  let S := T.filter (fun v=>P v σ)
  have hST : S⊆T := Finset.filter_subset _ _
  have hS : ∀ u∈S,∀ v∈S,u≠v → G.Adj u v :=
    fun u hu v hv hne=>hT u (hST hu) v (hST hv) hne
  obtain ⟨w₁,hw₁,hs₁,hchange₁⟩ := coinConflict_certificate G S hS σ
  have hqrange (τ : V → C×Bool) :
      ((S.filter (fun v=>P v τ)).card : ℝ)≤T.card := by
    exact_mod_cast (Finset.card_le_card ((Finset.filter_subset _ _).trans hST))
  have hqsize (τ : V → C×Bool) (v : V) (hv : v∈S) (hp : P v τ) : (W τ v).card≤k :=
    hsize τ v (hST hv) hp
  have hqload (τ : V → C×Bool) (i : V) :
      ((S.filter (fun v=>P v τ ∧ i∈W τ v)).card : ℝ)≤c := by
    have hsub : S.filter (fun v=>P v τ ∧ i∈W τ v)⊆
        T.filter (fun v=>P v τ ∧ i∈W τ v) := by
      intro v hv
      obtain ⟨hvS,hvP,hi⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨hST hvS,hvP,hi⟩
    exact (show ((S.filter (fun v=>P v τ ∧ i∈W τ v)).card : ℝ)≤
      (T.filter (fun v=>P v τ ∧ i∈W τ v)).card by
        exact_mod_cast Finset.card_le_card hsub).trans (hload τ i)
  have hqkeep (τ : V → C×Bool) (v : V) (hv : v∈S) (hp : P v τ)
      (τ' : V → C×Bool) (he : ∀ i∈W τ v,τ i=τ' i) : P v τ' :=
    hkeep τ v (hST hv) hp τ' he
  obtain ⟨w₂,hw₂,hs₂,hchange₂⟩ :=
    finiteWitness_coordinate_certificate_on S P W hqrange hqsize hqload hqkeep σ
  refine ⟨fun i=>w₁ i+w₂ i,?_,?_,?_⟩
  · intro i
    constructor <;> linarith [(hw₁ i).1,(hw₁ i).2,(hw₂ i).1,(hw₂ i).2]
  · rw [Finset.sum_add_distrib]
    have hcard : (S.card : ℝ)≤T.card := by exact_mod_cast Finset.card_le_card hST
    nlinarith
  · intro τ
    let B := coinConflictSet G S τ
    let A := S.filter (fun v=>P v τ)
    let R := filteredCoinConflictSet G T P τ
    have hBS : B⊆S := Finset.filter_subset _ _
    have hAS : A⊆S := Finset.filter_subset _ _
    have hInter : B∩A⊆R := by
      intro v hv
      obtain ⟨hvB,hvA⟩ := Finset.mem_inter.mp hv
      obtain ⟨hvS,hbad⟩ := Finset.mem_filter.mp hvB
      have hP := (Finset.mem_filter.mp hvA).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hST hvS,hP⟩,hbad⟩
    have hUnion : B∪A⊆S := Finset.union_subset hBS hAS
    have hcount : B.card+A.card≤R.card+S.card := by
      have h := Finset.card_union_add_card_inter B A
      have h₁ := Finset.card_le_card hInter
      have h₂ := Finset.card_le_card hUnion
      omega
    have hcountR : (B.card : ℝ)+(A.card : ℝ)≤(R.card : ℝ)+(S.card : ℝ) := by
      exact_mod_cast hcount
    have hAtStart : S.filter (fun v=>P v σ)=S := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact And.left
      · intro hv
        exact ⟨hv,(Finset.mem_filter.mp hv).2⟩
    have hfirst := hchange₁ τ
    have hsecond := hchange₂ τ
    have hstart : ((S.filter (fun v=>P v σ)).card : ℝ)=(S.card : ℝ) :=
      congrArg (fun F : Finset V=>(F.card : ℝ)) hAtStart
    have hstart' : ((filteredCoinConflictSet G T P σ).card : ℝ)=
        ((coinConflictSet G S σ).card : ℝ) := rfl
    have hchanges : (∑ i,if σ i≠τ i then w₁ i+w₂ i else 0)=
        (∑ i,if σ i≠τ i then w₁ i else 0)+(∑ i,if σ i≠τ i then w₂ i else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    change ((filteredCoinConflictSet G T P σ).card : ℝ)≤(R.card : ℝ)+_
    change ((coinConflictSet G S σ).card : ℝ)≤(B.card : ℝ)+_ at hfirst
    change ((S.filter (fun v=>P v σ)).card : ℝ)≤(A.card : ℝ)+_ at hsecond
    rw [hstart] at hsecond
    have hf : ((coinConflictSet G S σ).card : ℝ)≤(B.card : ℝ)+
        (∑ i,if σ i≠τ i then w₁ i else 0) := by
      convert hfirst using 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : σ i=τ i <;> simp [he]
    have hs : (S.card : ℝ)≤(A.card : ℝ)+
        (∑ i,if σ i≠τ i then w₂ i else 0) := by
      convert hsecond using 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : σ i=τ i <;> simp [he]
    have hmain : ((filteredCoinConflictSet G T P σ).card : ℝ)≤
        (R.card : ℝ)+((∑ i,if σ i≠τ i then w₁ i else 0)+
          (∑ i,if σ i≠τ i then w₂ i else 0)) := by
      rw [hstart']
      linarith only [hf,hs,hcountR]
    calc
      _ ≤ _ := hmain
      _ = (R.card : ℝ)+(∑ i,if σ i≠τ i then w₁ i+w₂ i else 0) :=
        congrArg (fun z=>(R.card : ℝ)+z) hchanges.symm
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases he : σ i=τ i <;> simp [he]

end Oberwolfach
