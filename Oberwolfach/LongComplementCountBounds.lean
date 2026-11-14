module

public import Oberwolfach.LongOrdinaryComplementTarget
public import Oberwolfach.FiniteComplementApproximation

@[expose] public section
/-! Convert an ordinary complement error to bounds in terms of long components. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_complement_count_bounds (n:ℕ) (long target θ err count:ℝ)
    (hlo:long≤target) (hhi:target≤long+(101/100:ℝ)*θ)
    (hcount:|count-(n:ℝ)*target|≤err):
    (n:ℝ)*long-err≤count ∧ count≤(n:ℝ)*(long+(101/100:ℝ)*θ)+err :=by
  have hn:0≤(n:ℝ):=by positivity
  have hl:=mul_le_mul_of_nonneg_left hlo hn
  have hu:=mul_le_mul_of_nonneg_left hhi hn
  have hb:=abs_le.mp hcount
  constructor <;> linarith

theorem long_ordinary_complement_final_bound {n K:ℕ} {U:Type} [Fintype U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ) (hθ:0≤θ)
    (hlong:∀u,(1/2:ℝ)≤
      ((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n)
    (u:U) (count err:ℝ)
    (hcount:|count-((n:ℝ)-(1-θ)*(n:ℝ)*
      (∑i:Fin K,longAssignedKeptFraction F hF K θ i u))|≤err):
    (n:ℝ)*ordinaryAssignedFraction F hF K u none-err≤count ∧
    count≤(n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ)+err :=by
  have ht:=long_ordinary_complement_target hn F hF K hK θ hθ hlong u
  apply long_complement_count_bounds n (ordinaryAssignedFraction F hF K u none)
    (1-(1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)) θ err count ht.1 ht.2
  convert hcount using 1 <;> congr 1 <;> ring
end Oberwolfach
