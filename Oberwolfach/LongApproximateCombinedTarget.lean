module

public import Oberwolfach.LongApproximateCombinedLoads
public import Oberwolfach.FiniteCombinedUnitLoad

@[expose] public section
/-! Add the independently estimated marked and ordinary contributions at
a fixed root, retaining the original factor-frequency coefficients. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_approximate_spoke_load_from_components {U I:Type} [Fintype I]
    (m:ℕ) (a b:U→ℝ) (f:I→U→ℝ)
    (hb:∀u,0<b u) (hbalance:∀u,b u=(m:ℝ)*a u+∑i,f i u)
    (u:U) (marked:ℝ) (ordinary:I→ℝ) (τ t:ℝ)
    (hm:|marked-(m:ℝ)*a u/b u|≤t+τ*((m:ℝ)*a u/b u))
    (ho:∀i,|ordinary i-f i u/b u|≤t+τ*(f i u/b u)):
    |marked+(∑i,ordinary i)-1|≤((Fintype.card I:ℝ)+1)*t+τ:=by
  let c:Option I→ℝ:=fun o=>match o with | none=>(m:ℝ)*a u/b u | some i=>f i u/b u
  let v:Option I→ℝ:=fun o=>match o with | none=>marked | some i=>ordinary i
  have hs:∑i,c i=1:=by
    simpa [c,Fintype.sum_option] using long_approximate_spoke_coefficients_sum_one m a b f hb hbalance u
  have ht:∀i,|v i-c i|≤t+τ*c i:=by intro i;cases i <;> simp_all [v,c]
  have hh:=finite_combined_unit_load c v τ t hs ht
  simpa [v,Fintype.sum_option,Fintype.card_option,Nat.cast_add,Nat.cast_one] using hh

theorem long_approximate_rim_load_from_components {U I:Type} [Fintype U] [Fintype I]
    (m:ℕ) (D p k:ℝ) (hD:0<D) (hp:0<p)
    (a b:U→ℝ) (f:I→U→ℝ)
    (hbalance:∀u,b u=(m:ℝ)*a u+∑i,f i u)
    (hpdef:p=(∑u,b u)/D) (hkdef:k=(∑u,a u)/D)
    (marked:ℝ) (ordinary:I→ℝ) (τ t:ℝ)
    (hm:|marked-(m:ℝ)*k/p|≤t+τ*((m:ℝ)*k/p))
    (ho:∀i,|ordinary i-(∑u,f i u)/(D*p)|≤t+τ*((∑u,f i u)/(D*p))):
    |marked+(∑i,ordinary i)-1|≤((Fintype.card I:ℝ)+1)*t+τ:=by
  let c:Option I→ℝ:=fun o=>match o with | none=>(m:ℝ)*k/p | some i=>(∑u,f i u)/(D*p)
  let v:Option I→ℝ:=fun o=>match o with | none=>marked | some i=>ordinary i
  have hs:∑i,c i=1:=by
    simpa [c,Fintype.sum_option] using long_approximate_ordinary_rim_coefficients_sum_one m D p k hD hp a b f hbalance hpdef hkdef
  have ht:∀i,|v i-c i|≤t+τ*c i:=by intro i;cases i <;> simp_all [v,c]
  have hh:=finite_combined_unit_load c v τ t hs ht
  simpa [v,Fintype.sum_option,Fintype.card_option,Nat.cast_add,Nat.cast_one] using hh
end Oberwolfach
