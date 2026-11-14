module

public import Oberwolfach.ResidualSpokeCardinality
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
/-! Exact residual directed degrees from disjoint factor arc images. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_slice_card_of_single_incidence
    {E U:Type*} [DecidableEq E] [Fintype U]
    (H:Finset E) (D:U→Finset E) (P:U→Prop)
    (hsub:∀w,D w⊆H)
    (hdis:∀w z,w≠z→Disjoint (D w) (D z))
    (hH:H.card=Fintype.card U)
    (hD:∀w,(D w).card=if P w then 1 else 0):
    (H\Finset.univ.biUnion D).card=(Finset.univ.filter (fun w=>¬P w)).card:=by
  classical
  have hU:Finset.univ.biUnion D⊆H:=by
    intro e he
    obtain ⟨w,_,hw⟩:=Finset.mem_biUnion.mp he
    exact hsub w hw
  have hcard:(Finset.univ.biUnion D).card=(Finset.univ.filter P).card:=by
    rw [Finset.card_biUnion (by intro w _ z _ h;exact hdis w z h)]
    simp only [hD]
    simpa only [Nat.cast_id] using (Finset.sum_boole (R:=ℕ) P Finset.univ)
  have hp:=Finset.card_filter_add_card_filter_not (s:=(Finset.univ:Finset U)) P
  rw [Finset.card_sdiff_of_subset hU,hcard,hH]
  simp only [Finset.card_univ] at hp
  omega

theorem residual_directed_degree_balance
    {V U:Type*} [DecidableEq V] [Fintype U]
    (H:Finset (V×V)) (D:U→Finset (V×V))
    (Z B T:U→Finset V)
    (hsub:∀w,D w⊆H)
    (hdis:∀w z,w≠z→Disjoint (D w) (D z))
    (hHout:∀v,(H.filter (fun e=>e.1=v)).card=Fintype.card U)
    (hHin:∀v,(H.filter (fun e=>e.2=v)).card=Fintype.card U)
    (hout:∀w v,((D w).filter (fun e=>e.1=v)).card=if v∈Z w∪B w then 1 else 0)
    (hin:∀w v,((D w).filter (fun e=>e.2=v)).card=if v∈Z w∪T w then 1 else 0)
    (hbalanced:∀v,(Finset.univ.filter (fun w=>v∉Z w∪T w)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪B w)).card):
    ∀v,(((H\Finset.univ.biUnion D).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪B w)).card) ∧
      (((H\Finset.univ.biUnion D).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉Z w∪B w)).card):=by
  classical
  intro v
  have hfilter (f:V×V→Prop):
      (H\Finset.univ.biUnion D).filter f=(H.filter f)\Finset.univ.biUnion (fun w=>(D w).filter f):=by
    ext e
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_univ,true_and]
    aesop
  have hsub' (f:V×V→Prop):∀w,(D w).filter f⊆H.filter f:=by
    intro w e he
    exact Finset.mem_filter.mpr ⟨hsub w (Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩
  have hdis' (f:V×V→Prop):∀w z,w≠z→Disjoint ((D w).filter f) ((D z).filter f):=by
    intro w z hwz
    exact (hdis w z hwz).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  constructor
  · have hh:=residual_slice_card_of_single_incidence (H.filter (fun e=>e.1=v))
      (fun w=>(D w).filter (fun e=>e.1=v)) (fun w=>v∈Z w∪B w)
      (by intro w e he; exact Finset.mem_filter.mpr ⟨hsub w (Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩)
      (by intro w z hwz; exact (hdis w z hwz).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (hHout v) (by intro w; by_cases hv:v∈Z w∪B w <;> simpa [hv] using hout w v)
    convert hh using 1
    · apply congrArg Finset.card
      ext e
      simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_univ,true_and]
      aesop
    · apply congrArg Finset.card
      ext w
      simp only [Finset.mem_filter]
  · have hh:=residual_slice_card_of_single_incidence (H.filter (fun e=>e.2=v))
      (fun w=>(D w).filter (fun e=>e.2=v)) (fun w=>v∈Z w∪T w)
      (by intro w e he; exact Finset.mem_filter.mpr ⟨hsub w (Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩)
      (by intro w z hwz; exact (hdis w z hwz).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (hHin v) (by intro w; by_cases hv:v∈Z w∪T w <;> simpa [hv] using hin w v)
    calc
      ((H\Finset.univ.biUnion D).filter (fun e=>e.2=v)).card =
          (Finset.univ.filter (fun w=>v∉Z w∪T w)).card := by
        convert hh using 1
        · apply congrArg Finset.card
          ext e
          simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_univ,true_and]
          aesop
        · apply congrArg Finset.card
          ext w
          simp only [Finset.mem_filter]
      _ = (Finset.univ.filter (fun w=>v∉Z w∪B w)).card := hbalanced v
end Oberwolfach
