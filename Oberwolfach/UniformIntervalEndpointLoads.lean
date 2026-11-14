module

public import Oberwolfach.MarkedIntervalEndpointSeparation
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
/-! Uniform root loads convert the rowwise interval boundary identity into
pointwise equality of start and finish loads. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_root_load_endpoint_balance
    {V U:Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (π:Equiv.Perm V) (Y B T:U→Finset V)
    (hrow:∀w,Y w∪B w=(Y w).image π∪T w)
    (hYB:∀w,Disjoint (Y w) (B w))
    (hπT:∀w,Disjoint ((Y w).image π) (T w))
    (huniform:∀v z,(Finset.univ.filter (fun w=>v∈Y w)).card=
      (Finset.univ.filter (fun w=>z∈Y w)).card):
    ∀v,(Finset.univ.filter (fun w=>v∈B w)).card=
      (Finset.univ.filter (fun w=>v∈T w)).card:=by
  classical
  intro v
  have hpoint (w:U):
      (if v∈Y w then 1 else 0)+(if v∈B w then 1 else 0)=
      (if π.symm v∈Y w then 1 else 0)+(if v∈T w then 1 else 0):=by
    have heq:(v∈Y w∨v∈B w)↔(v∈(Y w).image π∨v∈T w):=by
      have hh:=congrArg (fun s:Finset V=>v∈s) (hrow w)
      simp only [Finset.mem_union] at hh
      exact Iff.of_eq hh
    have hi:v∈(Y w).image π ↔ π.symm v∈Y w:=by
      constructor
      · intro h
        obtain ⟨a,ha,hav⟩:=Finset.mem_image.mp h
        rw [←hav,Equiv.symm_apply_apply]
        exact ha
      · intro h
        exact Finset.mem_image.mpr ⟨π.symm v,h,π.apply_symm_apply v⟩
    have hn1:¬(v∈Y w ∧ v∈B w):=fun h=>Finset.disjoint_left.mp (hYB w) h.1 h.2
    have hn2:¬(π.symm v∈Y w ∧ v∈T w):=fun h=>Finset.disjoint_left.mp (hπT w) (hi.mpr h.1) h.2
    rw [hi] at heq
    by_cases h₁:v∈Y w <;> by_cases h₂:v∈B w <;>
      by_cases h₃:π.symm v∈Y w <;> by_cases h₄:v∈T w <;>
      simp_all
  have hs:=Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun w _=>hpoint w)
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id] at hs
  have hu:=huniform v (π.symm v)
  omega
end Oberwolfach
