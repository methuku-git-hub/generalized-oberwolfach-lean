module

public import Oberwolfach.OrdinaryAbundanceReservedData

@[expose] public section
/-! Choose the common reserved fraction small enough for the existing
    matching parameter hierarchy while retaining a fixed positive lower bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_small_reserved_data_from_abundance
    (β:ℝ) (hβ:0<β) (hβ1:β≤1) (r:ℕ) (hr:3≤r) (K:ℕ) (hrK:r≤K):
    ∃N:ℕ,∀n≥N,∀(U:Type) [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hfreq:∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=r)).card:ℝ)),
    ∃(i₀:Fin K) (s:ℝ) (C:∀w,Finset (F w).ConnectedComponent),
      i₀.val+1=r ∧ (min β (1/(2*(K:ℝ))))/200≤s ∧ s≤1/100 ∧ s≤1/(2*(K:ℝ)) ∧
      (∀w c,c∈C w→Fintype.card c=r) ∧
      (∀w,(r:ℝ)*(C w).card=s*n) ∧
      (∀w,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):=by
  have hK:0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  let β':=min β (1/(2*(K:ℝ)))
  have hb:0<β':=lt_min hβ (by positivity)
  have hb1:β'≤1:=(min_le_left _ _).trans hβ1
  obtain ⟨N,hN⟩:=ordinary_reserved_data_from_abundance β' hb hb1 r hr K hrK
  refine ⟨N,?_⟩
  intro n hn U _ F hF hfreq
  have hfreq':∀w,β'*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=r)).card:ℝ):=by
    intro w
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans (hfreq w)
  obtain ⟨i,s,C,hi,hl,hu,hC,heq,hres⟩:=hN n hn U F hF hfreq'
  refine ⟨i,s,C,hi,hl,?_,?_,hC,heq,hres⟩
  · nlinarith [hu,hb1]
  · have hsmall:β'≤1/(2*(K:ℝ)):=min_le_right _ _
    nlinarith [hu,hsmall]
end Oberwolfach
