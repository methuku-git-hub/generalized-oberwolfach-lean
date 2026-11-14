module

public import Oberwolfach.ColourRetentionCoins
public import Oberwolfach.CliqueConflictCertificates

@[expose] public section

/-! A certificate for uncoloured vertices in a clique, with a
colour-dependent rejection coin at every vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V]

def coinConflictSet (G : SimpleGraph V) (T : Finset V) (σ : V → C×Bool) : Finset V :=
  T.filter (fun v=>¬coinColourSurvives G σ v)

theorem coinConflict_certificate
    (G : SimpleGraph V) (T : Finset V)
    (hclique : ∀ u∈T,∀ v∈T,u≠v → G.Adj u v) :
    HasCoordinateCertificateBound (fun σ : V → C×Bool=>(coinConflictSet G T σ).card) 2
      (3*(T.card : ℝ)) := by
  classical
  intro σ
  let B := coinConflictSet G T σ
  let f := cliqueConflictWitness G T (fun v=>(σ v).1)
  let W := B.image f
  let w := cliqueWitnessWeight T W
  have hBT : B⊆T := Finset.filter_subset _ _
  refine ⟨w,cliqueWitnessWeight_bounds T W,?_,?_⟩
  · have hh := cliqueWitnessWeight_changed_sum T W Finset.univ
    simp only [Finset.mem_univ,ite_true,Finset.inter_univ] at hh
    have hW : W.card≤T.card := Finset.card_image_le.trans (Finset.card_le_card hBT)
    have hd : (W\T).card≤W.card := Finset.card_le_card Finset.sdiff_subset
    change (∑ v,cliqueWitnessWeight T W v)≤_
    rw [hh]
    have hWr : (W.card : ℝ)≤T.card := by exact_mod_cast hW
    have hdr : ((W\T).card : ℝ)≤W.card := by exact_mod_cast hd
    linarith
  · intro τ
    let B' := coinConflictSet G T τ
    let E := Finset.univ.filter (fun v=>σ v≠τ v)
    let L := (B\B').filter (fun v=>σ v=τ v)
    have hL (v : V) (hv : v∈L) : v∈B ∧ v∉B' ∧ σ v=τ v := by
      obtain ⟨hs,he⟩ := Finset.mem_filter.mp hv
      exact ⟨(Finset.mem_sdiff.mp hs).1,(Finset.mem_sdiff.mp hs).2,he⟩
    have hgood (v : V) (hv : v∈L) : coinColourSurvives G τ v := by
      have h := hL v hv
      by_contra hn
      exact h.2.1 (Finset.mem_filter.mpr ⟨hBT h.1,hn⟩)
    have hwitness (v : V) (hv : v∈L) : G.Adj v (f v) ∧ (σ (f v)).1=(σ v).1 := by
      have h := hL v hv
      have hcoin : (σ v).2=true := by rw [h.2.2];exact (hgood v hv).1
      have hbad : ¬coinColourSurvives G σ v := (Finset.mem_filter.mp h.1).2
      have hconf : ∃ u,G.Adj v u ∧ (σ u).1=(σ v).1 := by
        by_contra hn
        apply hbad
        refine ⟨hcoin,?_⟩
        intro u hu he
        exact hn ⟨u,hu,he⟩
      exact cliqueConflictWitness_spec G T (fun v=>(σ v).1)
        (Finset.mem_filter.mpr ⟨hBT h.1,hconf⟩)
    have hchanged (v : V) (hv : v∈L) : f v∈E := by
      have h := hL v hv
      have hw := hwitness v hv
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro heq
      apply (hgood v hv).2 (f v) hw.1
      exact (congrArg Prod.fst heq).symm.trans
        (hw.2.trans (congrArg Prod.fst h.2.2))
    have hinj : Set.InjOn f (L : Set V) := by
      intro u hu v hv huv
      by_contra hne
      have hU := hL u hu
      have hV := hL v hv
      have hwu := hwitness u hu
      have hwv := hwitness v hv
      have hcol : (σ u).1=(σ v).1 := by
        calc
          _ = (σ (f u)).1 := hwu.2.symm
          _ = (σ (f v)).1 := congrArg (fun z=>(σ z).1) huv
          _ = _ := hwv.2
      apply (hgood u hu).2 v (hclique u (hBT hU.1) v (hBT hV.1) hne)
      exact (congrArg Prod.fst hV.2.2).symm.trans
        (hcol.symm.trans (congrArg Prod.fst hU.2.2))
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
    calc
      _ ≤ (B'.card : ℝ)+(2*((T∩E).card : ℝ)+(((W\T)∩E).card : ℝ)) := by
        exact_mod_cast (show B.card≤B'.card+(2*(T∩E).card+((W\T)∩E).card) by omega)
      _ = _ := congrArg (fun z=>(B'.card : ℝ)+z) heq.symm
    apply le_of_eq
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases he : σ i=τ i <;> simp [he]

end Oberwolfach
