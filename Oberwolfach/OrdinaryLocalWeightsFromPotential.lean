module

public import Oberwolfach.OrdinaryLocalFactorFromWeights

@[expose] public section
/-! Extract the fixed local wheel-factor weights from the parent cycle
weights and root-omitted potential estimates, before any fresh sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_local_weights_from_potential (m:ℕ) (hm:2≤m)
    (P Q F:SimpleGraph V) (T:Finset V) (j:ℕ) (p q s D δ ξ L cLo cHi:ℝ)
    (hn:0<Fintype.card V) (hQP:Q≤P) (hj:j≤2) (hp:0<p) (hp1:p≤1)
    (hq:p≤q) (hq1:q≤1) (hs:p≤s) (hs1:s≤1)
    (hδ:0≤δ) (hL:0≤L) (hcLo:0<cLo) (hcHi:0≤cHi)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hreg:∀v∈T,|(P.degree v:ℝ)-D|≤δ*Fintype.card V)
    (hF:∀v,(F.degree v:ℝ)≤L) (weight:OrdinaryCycle P (m+1)→ℝ)
    (hweight:∀C,cLo/(Fintype.card V:ℝ)^(m-1)≤weight C ∧ weight C≤cHi/(Fintype.card V:ℝ)^(m-1))
    (hedge:∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (hpotential:∀v∈T,|ordinaryLocalPotential P Q F T (fun C=>2*weight C/(D*q^(m+1)*s^(j*m))) v-
      ordinaryLocalTarget P F weight D v|≤ξ):
    ∃wt:LocalOrdinaryCycle Q F T (m+1)→ℝ,
      (∀C,cLo/(Fintype.card V:ℝ)^m≤wt C ∧ wt C≤(4*cHi/p^(3*m+1))/(Fintype.card V:ℝ)^m) ∧
      (∀v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤
        ξ+2*δ+12*(m+1:ℝ)^4*cHi*L/Fintype.card V):=by
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn
  let B:=4*cHi/p^(3*m+1)
  let φ:OrdinaryCycle P (m+1)→ℝ:=fun C=>2*weight C/(D*q^(m+1)*s^(j*m))
  let wt:LocalOrdinaryCycle Q F T (m+1)→ℝ:=fun C=>φ (localOrdinaryParent hQP C)
  have hw (C:LocalOrdinaryCycle Q F T (m+1)):
      cLo/(Fintype.card V:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card V:ℝ)^m:=
    ordinary_local_coefficient_bounds m j (by omega) _ D p q s cLo cHi _ hnR hp hp1 hq hq1 hs hs1 hj
      hDlo hDhi hcLo hcHi (hweight _)
  refine ⟨wt,hw,?_⟩
  intro v hv
  have ht:=ordinaryLocalTarget_error P F (show 2≤m+1 by omega) hn weight
    (fun C=>(div_nonneg hcLo.le (by positivity)).trans (hweight C).1) cHi L D δ hcHi hL hδ
    (by simpa only [show m+1-2=m-1 by omega] using fun C=>(hweight C).2) hF hedge hDlo v (hreg v hv)
  have hid:=ordinaryLocalPotential_present P Q F T hQP φ v hv
  have hpot:=hpotential v hv
  change |ordinaryLocalPotential P Q F T φ v-ordinaryLocalTarget P F weight D v|≤ξ at hpot
  have htriangle:=abs_sub_le (ordinaryLocalPotential P Q F T φ v) (ordinaryLocalTarget P F weight D v) 1
  rw [hid] at hpot htriangle
  rw [abs_sub_comm]
  have hfinal:=htriangle.trans (add_le_add hpot ht)
  have heq:ξ+(2*δ+12*((m+1:ℕ):ℝ)^4*cHi*L/Fintype.card V)=
      ξ+2*δ+12*(m+1:ℝ)^4*cHi*L/Fintype.card V:=by push_cast;ring
  rw [heq] at hfinal
  convert hfinal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
