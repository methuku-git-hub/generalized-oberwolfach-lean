module

public import Oberwolfach.PairedAbsorberRecords
public import Oberwolfach.ProfileFactorExtraction

@[expose] public section

/-! The class-profile factor theorem with the explicit paired absorber
family. The only conversion is the proved injective template map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem paired_profile_factor_extraction (a : I → ℕ) (c J : ℕ) [NeZero c] (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type) [Fintype C] [DecidableEq C],
      (∀ i,Fintype.card (V i)=a i*k) →
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ),
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J) →
      (∀ C₀,b/(k:ℝ)^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/(k:ℝ)^(c-1)) →
      (∀ v,|1-hypergraphWeightedDegree R w v| ≤ η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),
        a₀*(k:ℝ)^(c*c) ≤ Fintype.card (PairedCycleRecord (c:=c) R (profileRootSet σ))) →
      HasResourceDecomposition R Finset.univ := by
  let S : Unit → VertexAbsorberTemplate c := fun _ => pairedAbsorberTemplate c
  obtain ⟨η,hη,k₀,hk₀⟩ := profile_factor_extraction a c J hc ha hsize S a₀ b B ha₀ hb hB
  refine ⟨η,hη,k₀,?_⟩
  intro k hk V _ _ C _ _ hn R w hR hJ hw herr habs
  apply hk₀ k hk V C hn R w hR hJ hw herr
  intro σ
  have hpair := paired_absorber_template_count (c:=c) R (profileRootSet σ)
  let f (D : LabelledCycleRecord R (pairedAbsorberTemplate c).val (profileRootSet σ)) :
      LabelledAbsorberFamily R S (profileRootSet σ) := ⟨(),D⟩
  have hf : Function.Injective f := by
    intro D E he
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hh := Fintype.card_le_of_injective f hf
  have hb : Fintype.card (PairedCycleRecord (c:=c) R (profileRootSet σ)) ≤
      Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ)) := hpair.trans hh
  exact (habs σ).trans (by exact_mod_cast hb)

end Oberwolfach
