module

public import Oberwolfach.DenseCommonNeighbourBounds
public import Oberwolfach.RawPhysicalCuts

@[expose] public section

/-! The manuscript's lower relative neighbourhood estimates imply positive
linear candidate bounds, including the empty root set and external roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ordinary_relative_common_lower (P Q F : SimpleGraph V) (T S : Finset V)
    (h j : ℕ) (δ μ p q s ε : ℝ)
    (hδ : δ≤1) (hμ : 0≤μ) (hp : 0<p) (hp1 : p≤1) (hq : p≤q) (hs : p≤s)
    (hS : S.card≤h) (hj : j≤2)
    (hdeg : ∀ v,(δ+μ)*Fintype.card V≤(P.degree v:ℝ))
    (hF : ∀ v,(F.degree v:ℝ)≤μ*Fintype.card V)
    (hmargin : 0≤1-(h:ℝ)*(1-δ))
    (hrelative : q^S.card*s^j*((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ)-
      ε*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ)) :
    (p^(h+2)*(1-(h:ℝ)*(1-δ))-ε)*Fintype.card V≤
      ((common T S (fun x=>Q.neighborFinset x)).card:ℝ) := by
  have hdeg' (v : V) : δ*Fintype.card V≤((P\F).degree v:ℝ) := by
    have hh : (P.degree v:ℝ)≤(P\F).degree v+F.degree v := by
      exact_mod_cast graph_degree_le_sdiff_add P F v
    nlinarith only [hh,hdeg v,hF v]
  have hc := common_neighbour_card_lower (Finset.univ : Finset V) S
    (fun x=>(P\F).neighborFinset x) δ (fun v _=>by
      simpa only [Finset.inter_univ,Finset.univ_inter,Finset.card_univ,
        SimpleGraph.card_neighborFinset_eq_degree] using hdeg' v)
  simp only [Finset.card_univ] at hc
  have hSr : (S.card:ℝ)≤h := by exact_mod_cast hS
  have hcoef : 1-(h:ℝ)*(1-δ)≤1-(S.card:ℝ)*(1-δ) := by
    nlinarith only [mul_le_mul_of_nonneg_right hSr (sub_nonneg.mpr hδ)]
  have hc' : (1-(h:ℝ)*(1-δ))*Fintype.card V≤
      ((common Finset.univ S (fun x=>(P\F).neighborFinset x)).card:ℝ) :=
    (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)).trans hc
  have hpq : p^S.card≤q^S.card := pow_le_pow_left₀ hp.le hq _
  have hps : p^j≤s^j := pow_le_pow_left₀ hp.le hs _
  have hpowers : p^(h+2)≤q^S.card*s^j := by
    calc
      _ ≤ p^(S.card+j) := pow_le_pow_of_le_one hp.le hp1 (Nat.add_le_add hS hj)
      _ = p^S.card*p^j := pow_add _ _ _
      _ ≤ _ := mul_le_mul hpq hps (by positivity) (pow_nonneg (hp.le.trans hq) _)
  have hm := mul_le_mul hpowers hc' (mul_nonneg hmargin (Nat.cast_nonneg _))
    (mul_nonneg (pow_nonneg (hp.le.trans hq) _) (pow_nonneg (hp.le.trans hs) _))
  nlinarith only [hm,hrelative]

/-- A uniform density margin for the triangle and longer-cycle cases. -/
def ordinaryLocalBaseDegree (m : ℕ) : ℝ := if m=2 then 3/4 else 1/2

def ordinaryLocalRootBound (m : ℕ) : ℕ := if m=2 then 3 else 2

theorem ordinary_local_margin (m : ℕ) (α : ℝ) (hα : 0<α) :
    let u := min α (1/4)
    let δ := ordinaryLocalBaseDegree m+u/2
    δ≤1 ∧ 0<1-(ordinaryLocalRootBound m:ℝ)*(1-δ) := by
  dsimp
  have hu : 0<min α (1/4:ℝ) := lt_min hα (by norm_num)
  have hu1 : min α (1/4:ℝ)≤1/4 := min_le_right _ _
  unfold ordinaryLocalBaseDegree ordinaryLocalRootBound
  split_ifs <;> norm_num <;> constructor <;> linarith

end Oberwolfach
