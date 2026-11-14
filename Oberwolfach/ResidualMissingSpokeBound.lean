module

public import Oberwolfach.ResidualActualFullSelection

@[expose] public section
/-! Missing ordinary positions inject into the uncovered marked spokes whenever
sampled interval positions are distinct and covered positions are selected. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_missing_positions_le_uncovered_spokes
    {I V:Type} [DecidableEq I] [Fintype V] [DecidableEq V]
    (s₂:Finset I) (d:ℕ) (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d)
    (f:I→ℕ→V) (Available Covered:Finset V)
    (hvalid:∀i∈s₂,∀j<d,f i j∈Available)
    (hinj:∀i∈s₂,∀j<d,∀i'∈s₂,∀j'<d,f i j=f i' j'→i=i' ∧ j=j')
    (hcovered:∀i∈s₂,∀j<d,f i j∈Covered→j∈T i):
    (∑i∈s₂,(d-(T i).card))≤(Available\Covered).card:=by
  let Missing:=s₂.sigma (fun i=>(Finset.range d)\T i)
  let g:(Σ _ : I, ℕ)→V:=fun p=>f p.1 p.2
  have hcard:Missing.card=∑i∈s₂,(d-(T i).card):=by
    rw [show Missing=s₂.sigma (fun i=>(Finset.range d)\T i) from rfl,Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.card_sdiff_of_subset (hT i hi),Finset.card_range]
  have hmaps:Missing.image g⊆Available\Covered:=by
    intro x hx
    obtain ⟨⟨i,j⟩,hij,rfl⟩:=Finset.mem_image.mp hx
    have hi:i∈s₂:=(Finset.mem_sigma.mp hij).1
    have hj:=Finset.mem_sdiff.mp (Finset.mem_sigma.mp hij).2
    have hjd:j<d:=Finset.mem_range.mp hj.1
    refine Finset.mem_sdiff.mpr ⟨hvalid i hi j hjd,?_⟩
    intro hc
    exact hj.2 (hcovered i hi j hjd hc)
  have hinj':Set.InjOn g ↑Missing:=by
    intro a ha b hb hab
    rcases a with ⟨i,j⟩;rcases b with ⟨i',j'⟩
    have hi: i∈s₂:=(Finset.mem_sigma.mp ha).1
    have hi': i'∈s₂:=(Finset.mem_sigma.mp hb).1
    have hj:j<d:=Finset.mem_range.mp (Finset.mem_sdiff.mp (Finset.mem_sigma.mp ha).2).1
    have hj':j'<d:=Finset.mem_range.mp (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hb).2).1
    obtain ⟨rfl,rfl⟩:=hinj i hi j hj i' hi' j' hj' hab
    rfl
  have hh:=Finset.card_le_card hmaps
  rw [Finset.card_image_iff.mpr hinj',hcard] at hh
  exact hh
end Oberwolfach
