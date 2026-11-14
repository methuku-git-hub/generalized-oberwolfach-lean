module

public import Oberwolfach.LabelledAbsorberReservoir
public import Oberwolfach.ProfileRootPartitionSigma
public import Oberwolfach.ResourceClassCounts
public import Oberwolfach.UniversalAbsorberReservoir

@[expose] public section

/-! A small reservoir with exact class proportions absorbs every later
small leftover having those proportions. All configuration counts are
derived from the labelled-absorber and cycle-multiplicity hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem profile_absorber_reservoir (a : I → ℕ) (c J : ℕ) (hc : 1 ≤ c)
    (hsize : ∑ i,a i=c) (S : T → VertexAbsorberTemplate c) (a₀ δ : ℝ)
    (ha₀ : 0 < a₀) (hδ : 0 < δ) :
    ∃ γ : ℝ,0 < γ ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V : I → Type*) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type*) [Fintype C] [DecidableEq C],
      (∀ i,Fintype.card (V i)=a i*k) →
      ∀ R : C → Finset (Σ i,V i),
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),
        a₀*(k:ℝ)^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ))) →
      ∃ A₀ : Finset (Σ i,V i),∃ q₀ : ℕ,
        (A₀.card:ℝ) ≤ δ*k ∧
        (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A₀)).card=a i*q₀) ∧
        HasResourceDecomposition R A₀ ∧
        ∀ W : Finset (Σ i,V i),∀ q : ℕ,(W.card:ℝ) ≤ γ*k → Disjoint W A₀ →
          (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈W)).card=a i*q) →
          HasResourceDecomposition R (A₀∪W) := by
  let L := (c:ℝ)^c+1
  have hL : 0 < L := by dsimp [L];positivity
  obtain ⟨γ,hγ,k₀,hk₀⟩ := labelled_absorber_configuration_reservoir c J hc S a₀ L δ ha₀ hL hδ
  refine ⟨γ,hγ,k₀,?_⟩
  intro k hk V _ _ C _ _ hn R hR hJ habs
  let U := Σ i,V i
  let Roots := ∀ i,FixedSubset (V i) (a i)
  have hnall : Fintype.card U=c*k := by
    simp only [U,Fintype.card_sigma,hn,← Finset.sum_mul,hsize]
  have hroots : (Fintype.card Roots:ℝ) ≤ L*(k:ℝ)^c := by
    have hh : (Fintype.card Roots:ℝ) ≤ (Fintype.card U:ℝ)^c := by
      exact_mod_cast profile_root_family_card (V:=V) a c hsize
    rw [hnall,Nat.cast_mul,mul_pow] at hh
    have hn0 : 0 ≤ (k:ℝ)^c := by positivity
    dsimp [L];nlinarith only [hh,hn0]
  obtain ⟨M,hsmall,hMM,hcompat⟩ := hk₀ k hk U C Roots (by exact_mod_cast hnall) hroots R
    profileRootSet hJ (fun σ => (profileRootSet_card σ).trans hsize) habs
  let A := freeFamilyVertices R S
  let A₀ := M.biUnion A
  have hclass (F : FreeAbsorberFamily R S) (i : I) :
      ((A F).filter (fun v => v.1=i)).card=c*a i := by
    exact free_absorber_class_card R (S F.1) F.2 Sigma.fst a
      (fun C₀ i => (sigma_finset_class_card (R C₀) i).trans (hR C₀ i)) i
  have hdec (F : FreeAbsorberFamily R S) : HasResourceDecomposition R (A F) :=
    free_absorber_internal_factor R (S F.1) F.2
  refine ⟨A₀,c*M.card,hsmall,?_,resource_decomposition_biUnion R A M (fun F _ => hdec F) hMM,?_⟩
  · intro i
    rw [← sigma_finset_class_card]
    have hh := resource_biUnion_class_card A M Sigma.fst (fun i => c*a i) hMM (fun F _ i => hclass F i) i
    change (A₀.filter (fun v => v.1=i)).card=_ at hh
    rw [hh];ring
  · intro W q hW hdisj hprofile
    obtain ⟨σ,hU,hσσ⟩ := profile_root_partition_sigma a W q hprofile
    have hq : (q:ℝ) ≤ γ*k := by
      have hWcard : W.card=c*q := by
        rw [sigma_finset_card]
        simp only [hprofile,← Finset.sum_mul,hsize]
      have hcq : q ≤ c*q := by nlinarith
      have hh : (q:ℝ) ≤ W.card := by rw [hWcard];exact_mod_cast hcq
      exact hh.trans hW
    let AA (F : M) := A F.val
    have hchoices (j : Fin q) : Fintype.card (Fin q) ≤
        (Finset.univ.filter (fun F : M => HasResourceDecomposition R (AA F∪profileRootSet (σ j)))).card := by
      let B := M∩compatibleFreeAbsorbers R S (profileRootSet (σ j))
      let f (F : B) : {F : M // HasResourceDecomposition R (AA F∪profileRootSet (σ j))} :=
        ⟨⟨F.val,(Finset.mem_inter.mp F.property).1⟩,
          (compatible_free_absorber_absorbs R S (profileRootSet (σ j)) F.val
            (Finset.mem_inter.mp F.property).2).2.2⟩
      have hf : Function.Injective f := by
        intro F G he
        apply Subtype.ext
        exact congrArg (fun z => z.val.val) he
      have hb := Fintype.card_le_of_injective f hf
      have hb' : B.card ≤
          (Finset.univ.filter (fun F : M => HasResourceDecomposition R (AA F∪profileRootSet (σ j)))).card := by
        simpa only [Fintype.card_coe,Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter] using hb
      have hlow : (q:ℝ) ≤ B.card := hq.trans (hcompat (σ j))
      rw [Fintype.card_fin]
      exact (by exact_mod_cast hlow : q ≤ B.card).trans hb'
    have habs := absorber_reservoir_of_many_choices R (fun j => profileRootSet (σ j)) AA
      hσσ (fun F G hne => hMM F.val F.property G.val G.property (fun he => hne (Subtype.ext he)))
      (fun j F => hdisj.mono (by
        intro v hv;rw [← hU];exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hv⟩)
        (resource_subset_union A M F.val F.property)) (fun F => hdec F.val) hchoices
    have heA : Finset.univ.biUnion AA=A₀ := biUnion_finset_subtype M A
    rw [hU,heA] at habs
    exact habs.2.2

end Oberwolfach
