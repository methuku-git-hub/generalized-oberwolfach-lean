module

public import Oberwolfach.RetainedCoinCountsCommonEvent

@[expose] public section

/-! Degree identities after removing the whole inner pair and sampled
boundary. At an outside root the deterministic centre is B0 - p B1;
at an inner root it is (1-p)(B0-B1). Signed coefficients remain fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E J:Type} [DecidableEq E] [Fintype J]

def reservationRemaining (A I:Finset E) (inner:Bool) (σ:E→Bool):Finset E:=
  if inner then (A\I).filter (fun e=>σ e=false) else A\(I.filter (fun e=>σ e=true))

theorem reservation_remaining_outer_count (A I:Finset E) (hI:I⊆A) (σ:E→Bool):
    ((reservationRemaining A I false σ).card:ℝ)=A.card-(I.filter (fun e=>σ e=true)).card:=by
  have hh:=Finset.card_sdiff_add_card_eq_card ((Finset.filter_subset (fun e=>σ e=true) I).trans hI)
  have h:(((A\I.filter (fun e=>σ e=true)).card:ℕ):ℝ)+(I.filter (fun e=>σ e=true)).card=A.card:=by exact_mod_cast hh
  change ((A\I.filter (fun e=>σ e=true)).card:ℝ)=_
  linarith only [h]

theorem reservation_remaining_inner_count (A I:Finset E) (hI:I⊆A) (σ:E→Bool):
    ((reservationRemaining A I true σ).card:ℝ)=
      (A.card:ℝ)-I.card-((A\I).filter (fun e=>σ e=true)).card:=by
  have hh:=Finset.card_filter_add_card_filter_not (s:=A\I) (fun e=>σ e=true)
  have he:(A\I).filter (fun e=>¬σ e=true)=(A\I).filter (fun e=>σ e=false):=by
    ext e;simp
  rw [he] at hh
  have h:(((A\I).filter (fun e=>σ e=true)).card:ℝ)+((A\I).filter (fun e=>σ e=false)).card=(A\I).card:=by exact_mod_cast hh
  have hs:((A\I).card:ℝ)+I.card=A.card:=by exact_mod_cast Finset.card_sdiff_add_card_eq_card hI
  change (((A\I).filter (fun e=>σ e=false)).card:ℝ)=_
  linarith only [h,hs]

theorem weighted_pointwise_error (w x y:J→ℝ) (ε:ℝ) (h:∀ j,|x j-y j|≤ε):
    |(∑ j,w j*x j)-(∑ j,w j*y j)|≤(∑ j,|w j|)*ε:=by
  calc
    _=|∑ j,w j*(x j-y j)|:=by congr 1;rw [←Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro j _;ring
    _≤∑ j,|w j*(x j-y j)|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑ j,|w j| * ε:=Finset.sum_le_sum (fun j _=>by rw [abs_mul];exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _))
    _=_:=by rw [Finset.sum_mul]

theorem reservation_remaining_balance (A I:J→Finset E) (hI:∀ j,I j⊆A j)
    (w:J→ℝ) (p ε:ℝ) (inner:Bool) (σ:E→Bool)
    (hdev:∀ j,|(((if inner then A j\I j else I j).filter (fun e=>σ e=true)).card:ℝ)-
      p*(if inner then (A j\I j).card else (I j).card)|≤ε):
    |(∑ j,w j*(reservationRemaining (A j) (I j) inner σ).card)-
      (if inner then (1-p)*((∑ j,w j*(A j).card)-(∑ j,w j*(I j).card))
        else (∑ j,w j*(A j).card)-p*(∑ j,w j*(I j).card))|≤(∑ j,|w j|)*ε:=by
  cases inner
  · have he (j):|((reservationRemaining (A j) (I j) false σ).card:ℝ)-
        ((A j).card-p*(I j).card)|≤ε:=by
      rw [reservation_remaining_outer_count _ _ (hI j)]
      have h:=hdev j
      simp only [Bool.false_eq_true,ite_false] at h
      convert h using 1
      rw [show ((A j).card:ℝ)-(I j|>.filter (fun e=>σ e=true)).card-
        ((A j).card-p*(I j).card)= -(((I j).filter (fun e=>σ e=true)).card-p*(I j).card) by ring,abs_neg]
    have hh:=weighted_pointwise_error w
      (fun j=>(reservationRemaining (A j) (I j) false σ).card)
      (fun j=>(A j).card-p*(I j).card) ε he
    have hc:(∑ j,w j*((A j).card-p*(I j).card))=
        (∑ j,w j*(A j).card)-p*(∑ j,w j*(I j).card):=by
      calc
        _=∑ j,(w j*(A j).card-p*(w j*(I j).card)):=by apply Finset.sum_congr rfl;intro j _;ring
        _=_:=by rw [Finset.sum_sub_distrib,Finset.mul_sum]
    rw [hc] at hh
    exact hh
  · have he (j):|((reservationRemaining (A j) (I j) true σ).card:ℝ)-
        ((1-p)*((A j).card-(I j).card))|≤ε:=by
      rw [reservation_remaining_inner_count _ _ (hI j)]
      have h:=hdev j
      simp only [ite_true] at h
      have hs:((A j\I j).card:ℝ)+(I j).card=(A j).card:=by exact_mod_cast Finset.card_sdiff_add_card_eq_card (hI j)
      have heq:((A j).card:ℝ)-(I j).card-((A j\I j).filter (fun e=>σ e=true)).card-
          ((1-p)*((A j).card-(I j).card))=
          -(((A j\I j).filter (fun e=>σ e=true)).card-p*(A j\I j).card):=by
        have hs':((A j).card:ℝ)-(I j).card=(A j\I j).card:=by linarith only [hs]
        rw [hs'];ring
      rw [heq,abs_neg];exact h
    have hh:=weighted_pointwise_error w
      (fun j=>(reservationRemaining (A j) (I j) true σ).card)
      (fun j=>(1-p)*((A j).card-(I j).card)) ε he
    have hc:(∑ j,w j*((1-p)*((A j).card-(I j).card)))=
        (1-p)*((∑ j,w j*(A j).card)-(∑ j,w j*(I j).card)):=by
      calc
        _=∑ j,(1-p)*(w j*(A j).card-w j*(I j).card):=by apply Finset.sum_congr rfl;intro j _;ring
        _=_:=by rw [←Finset.mul_sum,Finset.sum_sub_distrib]
    rw [hc] at hh
    exact hh
end Oberwolfach
