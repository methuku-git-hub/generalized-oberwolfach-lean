module

public import Oberwolfach.RawIntervalAssignedLabelColumn
public import Oberwolfach.RawIntervalStartColumnCount
public import Oberwolfach.RawUnassignedColumnLocalEvent

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_start_end_column_local_event
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (A:Finset V) (J:Finset U) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-8*(A.card:ℝ)*Real.exp (-2*t^2/(J.card:ℝ))≤
      μ.probability (fun σ=>∀v∈A,∀g,
        |rawIntervalStartColumnCount π d σ v g J-∑u∈J,q u g/(d:ℝ)|<t ∧
        |rawIntervalStartColumnCount π d σ ((π^d).symm v) g J-∑u∈J,q u g/(d:ℝ)|<t):=by
  intro μ
  let T:=A.product (Finset.univ : Finset (Bool×Bool))
  let E:=fun (z:V×(Bool×Bool)) (σ:RawIntervalFamilyOutcome V U Bool Color) =>
    if z.2.2 then t≤|rawIntervalStartColumnCount π d σ z.1 z.2.1 J-∑u∈J,q u z.2.1/(d:ℝ)|
    else t≤|rawIntervalStartColumnCount π d σ ((π^d).symm z.1) z.2.1 J-∑u∈J,q u z.2.1/(d:ℝ)|
  have hh:=finiteLaw_common_event_lower μ T E
    (fun _=>2*Real.exp (-2*t^2/(J.card:ℝ))) (by
      intro z hz
      dsimp only [E]
      split
      · exact raw_interval_start_column_tail π d hd q hq hQ s hs hS hnoshort z.1 z.2.1 J t ht.le
      · exact raw_interval_start_column_tail π d hd q hq hQ s hs hS hnoshort ((π^d).symm z.1) z.2.1 J t ht.le)
  simp only [Finset.sum_const,nsmul_eq_mul,not_le] at hh
  have hh':1-8*(A.card:ℝ)*Real.exp (-2*t^2/(J.card:ℝ)) ≤
      μ.probability (fun σ=>∀z∈T,¬E z σ):=by
    convert hh using 1 <;> simp [T] <;> ring
  refine hh'.trans ?_
  apply finiteLaw_probability_mono
  intro σ h v hv g
  have h₁:=h (v,(g,true)) (Finset.mem_product.mpr ⟨hv,Finset.mem_univ _⟩)
  have h₂:=h (v,(g,false)) (Finset.mem_product.mpr ⟨hv,Finset.mem_univ _⟩)
  exact ⟨by simpa [E,not_le] using h₁, by simpa [E,not_le] using h₂⟩
end Oberwolfach
