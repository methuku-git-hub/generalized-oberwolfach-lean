module

public import Oberwolfach.OrdinaryCommonComponentReservation
public import Oberwolfach.OrdinaryAbundanceReservation

@[expose] public section
/-! The original common abundant cycle length gives one exact common reserved
    fraction and the corresponding component families before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_data_from_abundance
    (β:ℝ) (hβ:0<β) (hβ1:β≤1) (r:ℕ) (hr:3≤r) (K:ℕ) (hrK:r≤K):
    ∃N:ℕ,∀n≥N,∀(U:Type) [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hfreq:∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=r)).card:ℝ)),
    ∃(i₀:Fin K) (s:ℝ) (C:∀w,Finset (F w).ConnectedComponent),
      i₀.val+1=r ∧ β/200≤s ∧ s≤β/100 ∧
      (∀w c,c∈C w→Fintype.card c=r) ∧
      (∀w,(r:ℝ)*(C w).card=s*n) ∧
      (∀w,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):=by
  obtain ⟨N,hN⟩:=ordinary_common_component_reservation β hβ hβ1 r hr
  refine ⟨max N 1,?_⟩
  intro n hn U _ F hF hfreq
  have hn0:0<n:=by omega
  let i₀:Fin K:=⟨r-1,by omega⟩
  have hi:i₀.val+1=r:=by dsimp [i₀];omega
  obtain ⟨hl,hu,C,hcard,hsize⟩:=hN n (by omega) U F hfreq
  let s₀:=β/100
  let k:=⌊s₀*(n:ℝ)/(r:ℝ)⌋₊
  let s:ℝ:=(r:ℝ)*(k:ℝ)/(n:ℝ)
  change s≤β/100 at hu
  change β/100/2≤s at hl
  have hsβ:s≤β:=by linarith
  have hfreq':∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i₀.val+1)).card:ℝ):=by
    simpa only [hi] using hfreq
  have hres:=ordinary_reservation_from_specified_abundance hn0 F hF K i₀ β s hsβ hfreq'
  refine ⟨i₀,s,C,hi,?_,?_,hsize,?_,hres⟩
  · linarith
  · exact hu
  · intro w
    have hnR:(n:ℝ)≠0:=by exact_mod_cast (ne_of_gt hn0)
    have hk:(C w).card=k:=by simpa only [k,s₀] using hcard w
    rw [hk]
    dsimp [s]
    field_simp
end Oberwolfach
