module

public import Oberwolfach.CertificateConcentration
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

/-! Certificates for the number of vertices in a clique whose tentative
colours conflict with a neighbour. Witnesses are chosen from the actual
conflicts of the realised colouring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V]

def cliqueConflictSet (G : SimpleGraph V) (T : Finset V) (σ : V → C) : Finset V :=
  T.filter (fun v=>∃ u,G.Adj v u ∧ σ u=σ v)

def cliqueConflictWitness (G : SimpleGraph V) (T : Finset V) (σ : V → C) (v : V) : V :=
  if hv : v∈cliqueConflictSet G T σ then
    Classical.choose (Finset.mem_filter.mp hv).2 else v

theorem cliqueConflictWitness_spec
    (G : SimpleGraph V) (T : Finset V) (σ : V → C)
    {v : V} (hv : v∈cliqueConflictSet G T σ) :
    G.Adj v (cliqueConflictWitness G T σ v) ∧
      σ (cliqueConflictWitness G T σ v)=σ v := by
  unfold cliqueConflictWitness
  rw [dif_pos hv]
  exact Classical.choose_spec (Finset.mem_filter.mp hv).2

def cliqueWitnessWeight (T W : Finset V) (v : V) : ℝ :=
  if v∈T then 2 else if v∈W then 1 else 0

theorem cliqueWitnessWeight_bounds (T W : Finset V) (v : V) :
    0≤cliqueWitnessWeight T W v ∧ cliqueWitnessWeight T W v≤2 := by
  unfold cliqueWitnessWeight
  split_ifs <;> norm_num

theorem cliqueWitnessWeight_changed_sum (T W E : Finset V) :
    (∑ v,if v∈E then cliqueWitnessWeight T W v else 0)=
      2*((T∩E).card : ℝ)+(((W\T)∩E).card : ℝ) := by
  classical
  have he (v : V) :
      (if v∈E then cliqueWitnessWeight T W v else 0)=
        2*(if v∈T∩E then (1 : ℝ) else 0)+
          (if v∈(W\T)∩E then (1 : ℝ) else 0) := by
    by_cases ht : v∈T <;> by_cases hw : v∈W <;> by_cases hE : v∈E <;>
      simp [cliqueWitnessWeight,ht,hw,hE]
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp
  have hT : Finset.univ.filter (fun v=>v∈T ∧ v∈E)=T∩E := by ext;simp
  have hW : Finset.univ.filter (fun v=>(v∈W ∧ v∉T) ∧ v∈E)=(W\T)∩E := by ext;simp
  rw [hT,hW]

theorem cliqueConflict_certificate
    (G : SimpleGraph V) (T : Finset V)
    (hclique : ∀ u∈T,∀ v∈T,u≠v → G.Adj u v) :
    HasCoordinateCertificateBound (fun σ : V → C=>(cliqueConflictSet G T σ).card) 2
      (3*(T.card : ℝ)) := by
  classical
  intro σ
  let B := cliqueConflictSet G T σ
  let f := cliqueConflictWitness G T σ
  let W := B.image f
  let w := cliqueWitnessWeight T W
  have hBT : B⊆T := Finset.filter_subset _ _
  refine ⟨w,cliqueWitnessWeight_bounds T W,?_,?_⟩
  · have hh := cliqueWitnessWeight_changed_sum T W Finset.univ
    simp only [Finset.mem_univ,ite_true,Finset.inter_univ] at hh
    have hW : W.card≤T.card := (Finset.card_image_le).trans (Finset.card_le_card hBT)
    have hd : (W\T).card≤W.card := Finset.card_le_card Finset.sdiff_subset
    change (∑ v,cliqueWitnessWeight T W v)≤_
    rw [hh]
    have hWr : (W.card : ℝ)≤T.card := by exact_mod_cast hW
    have hdr : ((W\T).card : ℝ)≤W.card := by exact_mod_cast hd
    linarith
  · intro τ
    let B' := cliqueConflictSet G T τ
    let E := Finset.univ.filter (fun v=>σ v≠τ v)
    let L := (B\B').filter (fun v=>σ v=τ v)
    have hL (v : V) (hv : v∈L) : v∈B ∧ v∉B' ∧ σ v=τ v := by
      obtain ⟨hs,he⟩ := Finset.mem_filter.mp hv
      exact ⟨(Finset.mem_sdiff.mp hs).1,(Finset.mem_sdiff.mp hs).2,he⟩
    have hchanged (v : V) (hv : v∈L) : f v∈E := by
      have h := hL v hv
      have hw := cliqueConflictWitness_spec G T σ h.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro heq
      apply h.2.1
      apply Finset.mem_filter.mpr
      refine ⟨hBT h.1,f v,hw.1,?_⟩
      change τ (f v)=τ v
      have hs : σ (f v)=σ v := hw.2
      exact heq.symm.trans (hs.trans h.2.2)
    have hinj : Set.InjOn f (L : Set V) := by
      intro u hu v hv huv
      by_contra hne
      have hU := hL u hu
      have hV := hL v hv
      have hwu := cliqueConflictWitness_spec G T σ hU.1
      have hwv := cliqueConflictWitness_spec G T σ hV.1
      have hcol : σ u=σ v := by
        calc
          _ = σ (f u) := hwu.2.symm
          _ = σ (f v) := congrArg σ huv
          _ = _ := hwv.2
      apply hU.2.1
      apply Finset.mem_filter.mpr
      refine ⟨hBT hU.1,v,hclique u (hBT hU.1) v (hBT hV.1) hne,?_⟩
      exact hV.2.2.symm.trans (hcol.symm.trans hU.2.2)
    have himage : L.image f⊆(T∩E)∪((W\T)∩E) := by
      intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      have he := hchanged v hv
      by_cases ht : f v∈T
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ht,he⟩)
      · apply Finset.mem_union_right
        exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_image.mpr ⟨v,(hL v hv).1,rfl⟩,ht⟩,he⟩
    have hLcard : L.card≤(T∩E).card+((W\T)∩E).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact (Finset.card_le_card himage).trans (Finset.card_union_le _ _)
    have hcover : B⊆(B'∪(T∩E))∪L := by
      intro v hv
      by_cases hv' : v∈B'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv')
      · by_cases he : σ v=τ v
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨hv,hv'⟩,he⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hBT hv,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩))
    have hBcard : B.card≤B'.card+(T∩E).card+L.card :=
      (Finset.card_le_card hcover).trans
        ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hcount : B.card≤B'.card+2*(T∩E).card+((W\T)∩E).card := by omega
    have heq : (∑ i,if σ i≠τ i then w i else 0)=
        2*((T∩E).card : ℝ)+(((W\T)∩E).card : ℝ) := by
      have hh := cliqueWitnessWeight_changed_sum T W E
      simpa only [E,Finset.mem_filter,Finset.mem_univ,true_and] using hh
    change (B.card : ℝ)≤(B'.card : ℝ)+_
    rw [heq]
    exact_mod_cast (show B.card≤B'.card+(2*(T∩E).card+((W\T)∩E).card) by omega)

end Oberwolfach
