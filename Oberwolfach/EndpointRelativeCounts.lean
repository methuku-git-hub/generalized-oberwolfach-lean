module

public import Oberwolfach.DenseCommonNeighbourBounds
public import Oberwolfach.RawPhysicalCuts

@[expose] public section

/-! Quantitative endpoint neighbourhood estimates on the original row domain.
The conflict loss is removed before the density product, and all roots may
be external to that domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_common_iff {I : Type*} (A : Finset V) (X : Finset I) (N : I→Finset V) (v : V) :
    v∈common A X N ↔ v∈A ∧ ∀ i∈X,v∈N i := by simp only [common,Finset.mem_filter]

theorem common_neighbour_deletion_lower (P F : SimpleGraph V) (A X : Finset V) (δ L : ℝ)
    (hdeg : ∀ v∈X,δ*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hF : ∀ v∈X,(F.degree v:ℝ)≤L) :
    (1-(X.card:ℝ)*(1-δ))*A.card-X.card*L≤
      ((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ) := by
  let D := X.biUnion (fun v=>F.neighborFinset v)
  have hsub : common A X (fun v=>P.neighborFinset v)⊆
      common A X (fun v=>(P\F).neighborFinset v)∪D := by
    intro z hz
    by_cases hd : z∈D
    · exact Finset.mem_union_right _ hd
    · apply Finset.mem_union_left
      obtain ⟨hzA,hzP⟩ := (mem_common_iff _ _ _ _).mp hz
      apply (mem_common_iff _ _ _ _).mpr
      refine ⟨hzA,?_⟩
      intro v hv
      simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]
      refine ⟨(P.mem_neighborFinset v z).mp (hzP v hv),?_⟩
      intro h
      exact hd (Finset.mem_biUnion.mpr ⟨v,hv,(F.mem_neighborFinset v z).mpr h⟩)
  have hD : (D.card:ℝ)≤X.card*L := by
    calc
      _ ≤ ∑ v∈X,((F.neighborFinset v).card:ℝ) := by exact_mod_cast (Finset.card_biUnion_le : D.card≤_)
      _ ≤ ∑ _v∈X,L := Finset.sum_le_sum (fun v hv=>by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hF v hv)
      _ = _ := by simp
  have hcard : ((common A X (fun v=>P.neighborFinset v)).card:ℝ)≤
      (common A X (fun v=>(P\F).neighborFinset v)).card+D.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith only [common_neighbour_card_lower A X (fun v=>P.neighborFinset v) δ hdeg,hD,hcard]

theorem endpoint_surviving_common_lower (P F : SimpleGraph V) (A X : Finset V) (L : ℝ)
    (hX : X.card≤3) (hL : 0≤L) (hLa : L≤(A.card:ℝ)/24)
    (hdeg : ∀ v∈X,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hF : ∀ v∈X,(F.degree v:ℝ)≤L) :
    (A.card:ℝ)/8≤((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ) := by
  have hh := common_neighbour_deletion_lower P F A X (3/4) L hdeg hF
  have hXr : (X.card:ℝ)≤3 := by exact_mod_cast hX
  have hcoef : 1-(X.card:ℝ)*(1-(3/4:ℝ))≥1/4 := by linarith only [hXr]
  have hmul := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg A.card)
  have hloss := mul_le_mul_of_nonneg_right hXr hL
  nlinarith only [hh,hmul,hloss,hLa]

theorem endpoint_relative_row_lower (P R H F : SimpleGraph V) (A X J : Finset V)
    (p q s ε L : ℝ) (hp : 0<p) (hp1 : p≤1) (hq : p≤q) (hs : p≤s)
    (hX : X.card≤3) (hXJ : X.card+J.card≤4) (hL : 0≤L) (hLa : L≤(A.card:ℝ)/24)
    (hε : ε≤p^4/16)
    (hdeg : ∀ v∈X,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hF : ∀ v∈X,(F.degree v:ℝ)≤L)
    (hrelative : q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-ε*A.card≤
      ((common (common A X (fun v=>R.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ)) :
    (p^4/16)*A.card≤
      ((common (common A X (fun v=>R.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ) := by
  have hc := endpoint_surviving_common_lower P F A X L hX hL hLa hdeg hF
  have hprod : p^4≤q^X.card*s^J.card := by
    calc
      _ ≤ p^(X.card+J.card) := pow_le_pow_of_le_one hp.le hp1 hXJ
      _ = p^X.card*p^J.card := pow_add _ _ _
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hp.le hq _) (pow_le_pow_left₀ hp.le hs _)
        (pow_nonneg hp.le _) (pow_nonneg (hp.le.trans hq) _)
  have hm := mul_le_mul hprod hc (by positivity : (0:ℝ)≤A.card/8)
    (mul_nonneg (pow_nonneg (hp.le.trans hq) _) (pow_nonneg (hp.le.trans hs) _))
  have he := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg A.card)
  nlinarith only [hm,he,hrelative]

theorem endpoint_relative_index_lower (H : SimpleGraph V) (B X : Finset V)
    (p s ε : ℝ) (hp : 0<p) (hp1 : p≤1) (hs : p≤s) (hX : X.card≤3)
    (hε : ε≤p^3/2)
    (hrelative : (s^X.card-ε)*B.card≤((common B X (fun v=>H.neighborFinset v)).card:ℝ)) :
    (p^3/2)*B.card≤((common B X (fun v=>H.neighborFinset v)).card:ℝ) := by
  have hpow : p^3≤s^X.card := (pow_le_pow_of_le_one hp.le hp1 hX).trans (pow_le_pow_left₀ hp.le hs _)
  exact (mul_le_mul_of_nonneg_right (by linarith only [hpow,hε] : p^3/2≤s^X.card-ε)
    (Nat.cast_nonneg _)).trans hrelative

end Oberwolfach
