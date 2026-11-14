module

public import Oberwolfach.AbsorberFreeConflicts
public import Oberwolfach.AbsorberFreeCompatibility
public import Oberwolfach.ConfigurationReservoirOrder

@[expose] public section

/-! Sparse disjoint configurations selected from actual labelled
absorbers. The order and reservoir constants are uniform in all host
sets, root sets and resource families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem labelled_absorber_configuration_reservoir (c J : ℕ) (hc : 1 ≤ c)
    (S : T → VertexAbsorberTemplate c) (a L δ : ℝ)
    (ha : 0 < a) (hL : 0 < L) (hδ : 0 < δ) :
    ∃ γ : ℝ,0 < γ ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V C I : Type*) [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype I],
      (Fintype.card V:ℝ)=c*k → (Fintype.card I:ℝ) ≤ L*(k:ℝ)^c →
      ∀ (R : C → Finset V) (X : I → Finset V),
      (∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) →
      (∀ i,(X i).card=c) →
      (∀ i,a*(k:ℝ)^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S (X i))) →
      ∃ M : Finset (FreeAbsorberFamily R S),
        ((M.biUnion (freeFamilyVertices R S)).card:ℝ) ≤ δ*k ∧
        (∀ F∈M,∀ G∈M,F≠G → Disjoint (freeFamilyVertices R S F) (freeFamilyVertices R S G)) ∧
        ∀ i,γ*k ≤ ((M∩compatibleFreeAbsorbers R S (X i)).card:ℝ) := by
  let K := (Fintype.card T:ℝ)*(c:ℝ)^(c*c)*(J:ℝ)^c+1
  let K' := (Fintype.card T:ℝ)^2*((c*c:ℕ):ℝ)^2*(J:ℝ)^(2*c)*(c:ℝ)^(2*(c*c)-1)+1
  let D := (Fintype.card T:ℝ)*(c:ℝ)^c*(J:ℝ)^(c+1)+1
  have hK : 0 < K := by dsimp [K];positivity
  have hK' : 0 < K' := by dsimp [K'];positivity
  have hD : 0 < D := by dsimp [D];positivity
  have hh : 1 ≤ c*c := by nlinarith
  have he₁ : c*c-1+1=c*c := by omega
  have he₂ : 2*(c*c-1)+1=2*(c*c)-1 := by omega
  obtain ⟨γ,hγ,k₀,hk₀⟩ := configuration_reservoir_order (c*c-1) c K K' (a/D) L δ
    hK hK' (by positivity) hL hδ
  refine ⟨γ,hγ,k₀,?_⟩
  intro k hk V C I _ _ _ _ _ hn hI R X hJ hX habs
  let F := FreeAbsorberFamily R S
  let A := freeFamilyVertices R S
  let P : Finset (F×F) := Finset.univ.filter (fun p => p.1≠p.2 ∧ ¬Disjoint (A p.1) (A p.2))
  have hP : ∀ p∈P,p.1≠p.2 := by intro p hp;exact (Finset.mem_filter.mp hp).2.1
  have hconf : ∀ F G,F≠G → ¬Disjoint (A F) (A G) → (F,G)∈P := by
    intro F G hne hd;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,hd⟩
  have hAc : ∀ F,(A F).card ≤ c*c-1+1 := by
    intro F;rw [he₁];exact (free_absorber_vertex_count R (S F.1) F.2).le
  have hFc : (Fintype.card F:ℝ) ≤ K*(k:ℝ)^(c*c-1+1) := by
    have hb : (Fintype.card F:ℝ) ≤ (Fintype.card T:ℝ)*(Fintype.card V:ℝ)^(c*c)*(J:ℝ)^c := by
      exact_mod_cast free_absorber_family_card R S J hJ
    rw [hn,mul_pow] at hb
    rw [he₁]
    have hkp : 0 ≤ (k:ℝ)^(c*c) := by positivity
    dsimp [K]
    nlinarith only [hb,hkp]
  have hPc : (P.card:ℝ) ≤ K'*(k:ℝ)^(2*(c*c-1)+1) := by
    have hsub : P⊆Finset.univ.filter (fun p : F×F => ¬Disjoint (A p.1) (A p.2)) := by
      intro p hp;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.2⟩
    have hb : P.card ≤ (Fintype.card T)^2*(c*c)^2*J^(2*c)*Fintype.card V^(2*(c*c)-1) := by
      have hh := free_absorber_intersecting_pairs_count hc R S J hJ
      have he : (Finset.univ.filter (fun p : F×F => ¬Disjoint (A p.1) (A p.2))).card=
          Fintype.card {p : F×F // ¬Disjoint (A p.1) (A p.2)} := by
        rw [Fintype.card_subtype]
      exact (Finset.card_le_card hsub).trans (he ▸ hh)
    have hbR : (P.card:ℝ) ≤ (Fintype.card T:ℝ)^2*((c*c:ℕ):ℝ)^2*(J:ℝ)^(2*c)*
        (Fintype.card V:ℝ)^(2*(c*c)-1) := by exact_mod_cast hb
    rw [hn,mul_pow] at hbR
    rw [he₂]
    dsimp [K']
    have hkp : 0 ≤ (k:ℝ)^(2*(c*c)-1) := by positivity
    nlinarith only [hbR,hkp]
  have hcompat (i : I) : (a/D)*(k:ℝ)^(c*c-1+1) ≤
      ((compatibleFreeAbsorbers R S (X i)).card:ℝ) := by
    have hb := compatible_free_absorber_count R S (X i) J hJ
    rw [hX] at hb
    have hbR : (Fintype.card (LabelledAbsorberFamily R S (X i)):ℝ) ≤
        ((compatibleFreeAbsorbers R S (X i)).card:ℝ)*((Fintype.card T:ℝ)*(c:ℝ)^c*(J:ℝ)^(c+1)) := by
      exact_mod_cast hb
    have hnon : (0:ℝ) ≤ (compatibleFreeAbsorbers R S (X i)).card := Nat.cast_nonneg _
    have hbound : a*(k:ℝ)^(c*c) ≤ ((compatibleFreeAbsorbers R S (X i)).card:ℝ)*D := by
      have hh := habs i
      dsimp [D]
      nlinarith only [hh,hbR,hnon]
    rw [he₁,div_mul_eq_mul_div]
    exact (div_le_iff₀ hD).mpr hbound
  exact hk₀ k hk F I V A (fun i => compatibleFreeAbsorbers R S (X i)) P
    hP hconf hAc hFc hPc hI hcompat

end Oberwolfach
