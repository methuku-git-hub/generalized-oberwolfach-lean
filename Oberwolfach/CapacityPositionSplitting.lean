module

public import Oberwolfach.CapacityPositionCorrections
public import Oberwolfach.SignedDegreeCorrection

@[expose] public section

/-! Actual ordinary-edge capacities can be split into the prescribed cyclic
positions. Both endpoint demands are imposed, and the final share is proved
positive using its explicit accumulated error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

set_option maxHeartbeats 1200000 in
theorem capacity_position_splitting
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (k : ℕ) (hk : 0<k) (w : E → ℝ)
    (p q O I : V → ℝ) (M z err : ℝ) (herr : 0≤err)
    (hrow : ∀ v,(∑ e,if tail e=v then w e else 0)=O v)
    (hcol : ∀ v,(∑ e,if head e=v then w e else 0)=I v)
    (hbalance : ∀ v,O v-I v=p v-q v)
    (hp : ∑ v,p v=M) (hq : ∑ v,q v=M) (hO : ∑ v,O v=(k+1)*M)
    (hpclose : ∀ v,|p v-z|≤err) (hqclose : ∀ v,|q v-z|≤err)
    (hOclose : ∀ v,|O v-(k+1)*z|≤err) (hIclose : ∀ v,|I v-(k+1)*z|≤err)
    (κ s B δ ε h : ℝ) (hw : ∀ e,|w e-1|≤κ) (hs : 0<s) (hB : 1≤B)
    (hn : 0<Fintype.card V) (hδ : 0≤δ) (hδsmall : δ<1/4)
    (hdegp : ∀ v,|occurrenceDegree tail v-(Fintype.card E : ℝ)/Fintype.card V|≤ε)
    (hdegm : ∀ v,|occurrenceDegree head v-(Fintype.card E : ℝ)/Fintype.card V|≤ε)
    (hsmall : s*ε+3*err ≤ δ*s*((Fintype.card E : ℝ)/Fintype.card V))
    (hMC : (Fintype.card E : ℝ)/B ≤ h*Fintype.card V*Fintype.card V/2)
    (hlarge : ∀ (S T : Finset V),
      1-2*δ < (S.card : ℝ)/Fintype.card V+(T.card : ℝ)/Fintype.card V →
      h*Fintype.card V*Fintype.card V*
        min ((S.card : ℝ)/Fintype.card V) ((T.card : ℝ)/Fintype.card V) ≤
        ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card : ℝ))
    (hbudget : κ/(k+1:ℝ)+k*(B*s) ≤ 1/(2*(k+1:ℝ))) :
    ∃ f : Fin (k+1) → E → ℝ,
      (∀ e,(∑ j,f j e)=w e) ∧
      (∀ j v,(∑ e,if tail e=v then f j e else 0)=capacityPositionDemands k (p v) (q v) (O v) j.castSucc) ∧
      (∀ j v,(∑ e,if head e=v then f j e else 0)=capacityPositionDemands k (p v) (q v) (O v) j.succ) ∧
      (∀ j e,1/(2*(k+1:ℝ)) ≤ f j e ∧ f j e ≤ 2/(k+1:ℝ)) := by
  classical
  let d (j : Fin (k+2)) (v : V) := capacityPositionDemands k (p v) (q v) (O v) j
  have hdtotal (j : Fin (k+2)) : (∑ v,d j v)=M := capacityPositionDemands_total k hk p q O M hp hq hO j
  have hI : (∑ v,I v)=(k+1)*M := by
    have he (v : V) : I v=O v-p v+q v := by linarith [hbalance v]
    simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,hO,hp,hq]
    ring
  have hderror (j : Fin (k+2)) (v : V) : |d j v-z|≤2*err :=
    capacityPositionDemands_error k hk (p v) (q v) (O v) z err herr (hpclose v) (hqclose v) (hOclose v) j
  let Δp (j : Fin k) (v : V) := d j.castSucc.castSucc v-O v/(k+1:ℝ)
  let Δm (j : Fin k) (v : V) := d j.castSucc.succ v-I v/(k+1:ℝ)
  have hΔp (j : Fin k) : (∑ v,Δp j v)=0 := equal_share_correction_total k _ O M (hdtotal _) hO
  have hΔm (j : Fin k) : (∑ v,Δm j v)=0 := equal_share_correction_total k _ I M (hdtotal _) hI
  have hΔpb (j : Fin k) (v : V) : |Δp j v|≤3*err := equal_share_correction_bound k _ (O v) z err herr (hderror _ v) (hOclose v)
  have hΔmb (j : Fin k) (v : V) : |Δm j v|≤3*err := equal_share_correction_bound k _ (I v) z err herr (hderror _ v) (hIclose v)
  have hex (j : Fin k) := bounded_signed_degree_correction tail head (Δp j) (Δm j)
    (hΔp j) (hΔm j) s B δ ε (3*err) h hs hB hn hδ hδsmall hdegp hdegm (hΔpb j) (hΔmb j) hsmall hMC hlarge
  choose u hu hut huh using hex
  let f := capacityPositionWeights k w u
  have hfrow : ∀ j v,(∑ e,if tail e=v then f j e else 0)=d j.castSucc v := by
    apply capacityPositionWeights_occurrence_marginals tail k w u (fun j => d j.castSucc)
    · intro v
      rw [hrow]
      exact capacityPositionDemands_outgoing k hk (p v) (q v) (O v)
    · intro j v
      simpa only [hrow] using hut j v
  have hfcol : ∀ j v,(∑ e,if head e=v then f j e else 0)=d j.succ v := by
    apply capacityPositionWeights_occurrence_marginals head k w u (fun j => d j.succ)
    · intro v
      rw [hcol]
      exact capacityPositionDemands_incoming k hk (p v) (q v) (O v) (I v) (hbalance v)
    · intro j v
      simpa only [hcol] using huh j v
  refine ⟨f,?_,hfrow,hfcol,?_⟩
  · intro e
    simpa only [Finset.sum_apply] using congrFun (capacityPositionWeights_total k w u) e
  · intro j e
    have hBs : 0≤B*s := mul_nonneg (by linarith) hs.le
    have hh := (capacityPositionWeights_bounds k hk w u κ (B*s) hBs hw hu j e).trans hbudget
    obtain ⟨hlo,hup⟩ := abs_le.mp hh
    have hid : 1/(k+1:ℝ)=2*(1/(2*(k+1:ℝ))) := by field_simp
    have hpos : 0≤1/(k+1:ℝ) := by positivity
    have hi2 : 2/(k+1:ℝ)=2*(1/(k+1:ℝ)) := by ring
    dsimp only [f]
    constructor <;> linarith

end Oberwolfach
