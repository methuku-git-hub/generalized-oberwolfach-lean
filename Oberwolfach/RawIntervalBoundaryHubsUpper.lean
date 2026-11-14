module

public import Oberwolfach.RawStartEndColumnLocalEvent

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawIntervalBoundaryHubSet {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Color] (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (J:Finset U) (x:V):Finset U:=
  J.filter (fun w=> ∃g:Bool,rawIntervalColouredStart π d (fun e=>σ (w,e)) x g ∨
    rawIntervalColouredStart π d (fun e=>σ (w,e)) ((π^d).symm x) g)

theorem raw_interval_boundary_hubs_upper
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (q:U→Bool→ℝ) (A:Finset V) (J:Finset U) (t:ℝ)
    (hq:∀u g,q u g≤1)
    (hStart:∀v∈A,∀g,|rawIntervalStartColumnCount π d σ v g J-∑u∈J,q u g/(d:ℝ)|<t ∧
      |rawIntervalStartColumnCount π d σ ((π^d).symm v) g J-∑u∈J,q u g/(d:ℝ)|<t):
    ∀v∈A,((rawIntervalBoundaryHubSet π d σ J v).card:ℝ)≤4*(J.card:ℝ)/d+4*t:=by
  have hdR:(0:ℝ)<d:=by exact_mod_cast hd
  have hmean:∀g,(∑u∈J,q u g/(d:ℝ))≤(J.card:ℝ)/d:=by
    intro g
    calc
      _ ≤ ∑_u∈J,(1/(d:ℝ)) := Finset.sum_le_sum (fun u hu=>div_le_div_of_nonneg_right (hq u g) hdR.le)
      _ = _ := by simp [div_eq_mul_inv]
  intro v hv
  let B:=fun (g:Bool) (b:Bool)=>J.filter (fun w=>rawIntervalColouredStart π d (fun e=>σ (w,e)) (if b then v else (π^d).symm v) g)
  have hone:∀g b,((B g b).card:ℝ)≤(J.card:ℝ)/d+t:=by
    intro g b
    have hcard:((B g b).card:ℝ)=rawIntervalStartColumnCount π d σ (if b then v else (π^d).symm v) g J:=by
      simp [B,rawIntervalStartColumnCount,Finset.sum_ite]
    rw [hcard]
    cases b with
    | false => have hh:=(abs_lt.mp (hStart v hv g).2).2; simp only [Bool.false_eq_true,if_false]; linarith [hmean g]
    | true => have hh:=(abs_lt.mp (hStart v hv g).1).2; simp only [if_true]; linarith [hmean g]
  have hsub:rawIntervalBoundaryHubSet π d σ J v ⊆ (B false false ∪ B false true) ∪ (B true false ∪ B true true):=by
    intro w hw
    have ⟨hwJ,g,hg⟩:=(Finset.mem_filter.mp hw)
    cases g <;> rcases hg with hx|hx <;> simp only [B,Finset.mem_union,Finset.mem_filter,Bool.false_eq_true,ite_false,ite_true]
    · exact Or.inl (Or.inr ⟨hwJ,hx⟩)
    · exact Or.inl (Or.inl ⟨hwJ,hx⟩)
    · exact Or.inr (Or.inr ⟨hwJ,hx⟩)
    · exact Or.inr (Or.inl ⟨hwJ,hx⟩)
  have hcard₁:=Finset.card_union_le (B false false) (B false true)
  have hcard₂:=Finset.card_union_le (B true false) (B true true)
  have hcard₃:=Finset.card_union_le (B false false ∪ B false true) (B true false ∪ B true true)
  have hcard₄:=Finset.card_le_card hsub
  have hcard:(rawIntervalBoundaryHubSet π d σ J v).card ≤ (B false false).card+(B false true).card+(B true false).card+(B true true).card:=by omega
  have hcardR:((rawIntervalBoundaryHubSet π d σ J v).card:ℝ) ≤ (B false false).card+(B false true).card+(B true false).card+(B true true).card:=by exact_mod_cast hcard
  have h₁:=hone false false
  have h₂:=hone false true
  have h₃:=hone true false
  have h₄:=hone true true
  have heq:4*(J.card:ℝ)/d=4*((J.card:ℝ)/d):=by ring
  rw [heq]
  linarith
end Oberwolfach
