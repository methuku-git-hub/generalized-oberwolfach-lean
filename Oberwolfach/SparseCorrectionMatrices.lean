module

public import Oberwolfach.SparseCorrectionDemands
public import Oberwolfach.ResidueDegreeDemands
public import Oberwolfach.NormalizedDemands

@[expose] public section

/-! Integral allowed-edge matrices for sparse ordinary degree correction. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- The normalized large-cut inequality, including unequal part sizes. -/
def BipartiteLargeCut {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (L : X → Y → ℕ) (δ h : ℝ) : Prop :=
  ∀ (S : Finset X) (T : Finset Y),
    1-2*δ<(S.card : ℝ)/Fintype.card X+(T.card : ℝ)/Fintype.card Y →
    h*Fintype.card X*Fintype.card Y*
      min ((S.card : ℝ)/Fintype.card X) ((T.card : ℝ)/Fintype.card Y)≤
        ((∑ x,∑ y,if x∈S ∧ y∈T then L x y else 0 : ℕ) : ℝ)

theorem near_uniform_matrix_degrees {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (L : X → Y → ℕ) (f : X → ℕ) (g : Y → ℕ) {δ M h : ℝ}
    (hn : 0<Fintype.card X) (hs : 0<Fintype.card Y)
    (hδ : 0≤δ) (hδsmall : δ<1/4) (hM : 0≤M)
    (hMC : M≤h*Fintype.card X*Fintype.card Y/2)
    (hf : (∑ x,(f x : ℝ))=M) (hg : (∑ y,(g y : ℝ))=M)
    (hfb : ∀ x,(f x : ℝ)≤(1+δ)*M/Fintype.card X)
    (hgb : ∀ y,(g y : ℝ)≤(1+δ)*M/Fintype.card Y)
    (hcut : BipartiteLargeCut L δ h) :
    ∃ J : X → Y → ℕ,(∀ x y,J x y≤L x y) ∧
      (∀ x,∑ y,J x y=f x) ∧ (∀ y,∑ x,J x y=g y) := by
  classical
  have hc := nearUniform_cutCondition
    (fun e : BipartiteEdges L=>e.1) (fun e=>e.2.1) f g
    hn hs hδ le_rfl hδsmall hM hMC hf hg hfb hgb
    (fun S T ht=>by
      rw [bipartiteEdges_filter_card L (fun x y=>x∈S ∧ y∈T)]
      exact hcut S T ht)
  apply bipartite_prescribedMultiplicity L f g
  · exact_mod_cast hf.trans hg.symm
  · intro S T
    have hh := hc S T
    rw [bipartiteEdges_filter_card L (fun x y=>x∈S ∧ y∉T)] at hh
    exact hh

/-- Simultaneous integer deletions in the rim orientation and the spoke
incidence graph, with their original allowed matrices left unchanged. -/
theorem sparse_integer_correction_matrices {V U : Type*}
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (A : V → V → ℕ) (H : V → U → ℕ) (d : U → ℕ) (b : V → ℤ)
    (base r : ℕ) (hr : 0<r) {ω δ h e : ℝ}
    (hn : 0<Fintype.card V) (hs : 0<Fintype.card U)
    (hsn : Fintype.card U≤Fintype.card V)
    (hω : 0<ω) (hωn : ω*Fintype.card V≤Fintype.card U)
    (hδ : 0≤δ) (hδsmall : δ<1/4) (he : 0≤e)
    (hrδ : (r : ℝ)≤δ*base) (hunit : 1≤δ*ω*base)
    (hpositive : e+2≤2*ω*base)
    (hrelative : 3/2+e≤δ*(ω*base-e/2))
    (hcapacity : (base : ℝ)+r+e/2≤h*Fintype.card V/2)
    (hb : ∀ v,|(b v : ℝ)|≤e) (hbeven : Even (∑ v,b v))
    (hcutA : BipartiteLargeCut A δ h) (hcutH : BipartiteLargeCut H δ h) :
    ∃ (J : V → V → ℕ) (K : V → U → ℕ),
      (∀ x y,J x y≤A x y) ∧ (∀ v u,K v u≤H v u) ∧
      (∀ v,((∑ w,J v w)+(∑ w,J w v) : ℤ)-2*(∑ u,K v u : ℕ)=b v) ∧
      (∀ u,(∑ v,K v u)%r=d u%r) ∧
      (∀ v,((∑ w,J v w)+(∑ w,J w v) : ℝ)≤2*((base : ℝ)+r+1)+e) ∧
      (∀ v,((∑ u,K v u : ℕ) : ℝ)≤base+r+1) ∧
      (∀ u,((∑ v,K v u : ℕ) : ℝ)≤base+r) := by
  classical
  obtain ⟨k,f,T,hk,hkT,hfT,hTlo,hThi,hferr,hkrel,hfrel⟩ :=
    residue_degree_demands hn hs hsn d base r hr hω hωn hδ hrδ hunit
  have hnR : (0 : ℝ)<Fintype.card V := by exact_mod_cast hn
  have hsR : (0 : ℝ)<Fintype.card U := by exact_mod_cast hs
  have hfTR : (∑ v,(f v : ℝ))=T := by exact_mod_cast hfT
  have hkTR : (∑ u,(k u : ℝ))=T := by exact_mod_cast hkT
  have hTcap : (T : ℝ)≤h*Fintype.card V*Fintype.card U/2 := by
    have hksum : (T : ℝ)≤Fintype.card U*((base : ℝ)+r) := by
      rw [← hkTR]
      calc
        _ ≤ ∑ _ : U,((base : ℝ)+r) := by
          apply Finset.sum_le_sum
          intro u _
          exact_mod_cast (hk u).2.1.le
        _ = _ := by simp;ring
    have hh := mul_le_mul_of_nonneg_left hcapacity hsR.le
    have he' := mul_nonneg hsR.le he
    nlinarith
  obtain ⟨K,hK,hKrow,hKcol⟩ := near_uniform_matrix_degrees H f k hn hs
    hδ hδsmall (Nat.cast_nonneg T) hTcap hfTR hkTR hfrel hkrel hcutH
  obtain ⟨gp,gm,hbalance,hequal,hmean,hgp,hgm⟩ := signed_balanced_degree_demands
    hn f b hbeven he (T:=(T : ℝ)/Fintype.card V) (by rw [hfTR]) hferr hb
    (by linarith)
  let M : ℝ := ∑ v,(gp v : ℝ)
  have hM : 0≤M := Finset.sum_nonneg (fun v _=>Nat.cast_nonneg _)
  have hMlo : ω*base-e/2≤M/Fintype.card V := by
    have hh := (abs_le.mp hmean).1
    change -(e/2)≤M/Fintype.card V-(T : ℝ)/Fintype.card V at hh
    linarith
  have hMhi : M/Fintype.card V≤(base : ℝ)+r+e/2 := by
    have hh := (abs_le.mp hmean).2
    change M/Fintype.card V-(T : ℝ)/Fintype.card V≤e/2 at hh
    linarith
  have hMcap : M≤h*Fintype.card V*Fintype.card V/2 := by
    have hh := (div_le_iff₀ hnR).mp (hMhi.trans hcapacity)
    nlinarith
  have hMrel : 3/2+e≤δ*(M/Fintype.card V) :=
    hrelative.trans (mul_le_mul_of_nonneg_left hMlo hδ)
  have hgpRel (v : V) : (gp v : ℝ)≤(1+δ)*M/Fintype.card V := by
    have hh := (abs_le.mp (hgp v)).2
    change (gp v : ℝ)-M/Fintype.card V≤3/2+e at hh
    calc
      _ ≤ (1+δ)*(M/Fintype.card V) := by nlinarith
      _ = _ := by ring
  have hgmRel (v : V) : (gm v : ℝ)≤(1+δ)*M/Fintype.card V := by
    have hh := (abs_le.mp (hgm v)).2
    change (gm v : ℝ)-M/Fintype.card V≤3/2+e at hh
    calc
      _ ≤ (1+δ)*(M/Fintype.card V) := by nlinarith
      _ = _ := by ring
  have hgmTotal : (∑ v,(gm v : ℝ))=M := by
    dsimp [M]
    exact_mod_cast hequal.symm
  obtain ⟨J,hJ,hJrow,hJcol⟩ := near_uniform_matrix_degrees A gp gm hn hn hδ hδsmall
    hM hMcap rfl hgmTotal hgpRel hgmRel hcutA
  have hfupper (v : V) : (f v : ℝ)≤base+r+1 := by
    have := (abs_le.mp (hferr v)).2
    linarith
  refine ⟨J,K,hJ,hK,?_,?_,?_,?_,?_⟩
  · intro v
    simp only [hJrow,hJcol,hKrow]
    have hh := hbalance v
    omega
  · intro u
    rw [hKcol]
    exact (hk u).2.2
  · intro v
    have hh : (gp v : ℝ)+gm v=2*(f v : ℝ)+b v := by exact_mod_cast hbalance v
    have hb' := (abs_le.mp (hb v)).2
    simp only [hJrow,hJcol]
    linarith [hfupper v]
  · intro v
    rw [hKrow]
    exact hfupper v
  · intro u
    rw [hKcol]
    exact_mod_cast (hk u).2.1.le

end Oberwolfach
