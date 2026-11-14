module

public import Oberwolfach.EndpointFactorFromFixedWeights
public import Oberwolfach.EndpointPotentialDeletionBounds
public import Oberwolfach.MixedGraphDeletionCounts

@[expose] public section

/-! Exact endpoint factors after arbitrary bounded-degree rim and spoke
removal. The original parent weights and both potential targets stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_factor_after_bounded_deletion (p κ c C : ℝ)
    (hp : 0<p) (hp1 : p≤1) (hκ : 0<κ) (hc : 0<c) (hC : 0<C) :
    ∃ ε₀ τ η K : ℝ,0<ε₀ ∧ 0<τ ∧ 0<η ∧ 0<K ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (P R H F D E : SimpleGraph V) (A B : Finset V) (x : V),N≤A.card →
      Disjoint A B → R≤P\F →
      (∀ u∈B,∀ w,¬F.Adj u w) →
      ∀ q s ε L Ldel δ ξ : ℝ,p≤q → q≤1 → p≤s → s≤1 → ε+4*Ldel/A.card+3*Ldel/B.card≤ε₀ → 0≤L → 0≤Ldel → 0≤δ →
      L≤τ*A.card → κ*A.card≤(B.card:ℝ) → B.card≤A.card →
      (∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ v,(D.degree v:ℝ)≤Ldel) → (∀ v,(E.degree v:ℝ)≤Ldel) →
      (∀ X J : Finset V,x∈X → X⊆insert x A → J⊆B →
        X.card≤3 → J.card≤2 → X.card+J.card≤4 →
        q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-ε*A.card≤
          ((common (common A X (fun v=>R.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ)) →
      (∀ X : Finset V,x∈X → X⊆insert x A → (X.card=1 ∨ X.card=3) →
        (∀ v∈X,∀ w∈X,¬F.Adj v w) →
        (s^X.card-ε)*B.card≤((common B X (fun v=>H.neighborFinset v)).card:ℝ)) →
      ∀ weight : Sym2 V→ℝ,
      (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        0≤weight s(v,w) ∧ weight s(v,w)≤C/A.card) →
      (∀ v∈A∩P.neighborFinset x,∑ w∈A∩P.neighborFinset x,weight s(v,w)=1) →
      (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        ¬P.Adj v w → weight s(v,w)=0) →
      (∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
        c/A.card≤weight e ∧ weight e≤C/A.card) →
      |q*(A∩P.neighborFinset x).card/(2*B.card*s)-1|≤δ →
      (∀ v∈common A {x} (fun y=>(P\F).neighborFinset y),
        |endpointRowPotential P R H F A B x v weight (B.card*q^2*s^3)-
          endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w))|≤ξ) →
      (∀ u∈B,
        |endpointIndexPotential P R H F A x u weight (B.card*q^2*s^3)-
          q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e)|≤ξ) →
      δ+K*L/A.card+ξ+5*(C/(κ*p^5))*Ldel/A.card≤η →
      let S:=common A {x} (fun v=>(R\D).neighborFinset v)
      let T:=common B {x} (fun v=>(H\E).neighborFinset v)
      S.card=2*T.card →
      HasResourceDecomposition (endpointTriangleVertices
        (Q:=endpointHostGraph (R\D) (H\E) A B) (F:=F) (S:=S) (T:=T)) (S∪T) := by
  obtain ⟨ε₀,τ,η,K,hε,hτ,hη,hK,N,hfactor⟩:=endpoint_factor_from_fixed_weights p κ c C hp hp1 hκ hc hC
  refine ⟨ε₀,τ,η,K,hε,hτ,hη,hK,max N 1,?_⟩
  intro V _ _ P R H F D E A B x hn hAB hR hFB q s ε L Ldel δ ξ
    hq hq1 hs hs1 hε' hL hLdel hδ hLτ hB hBA hdeg hF hD hE hrows hindices
    weight hw hsum hzero hpos hbalance hrow hindex herr
  dsimp only
  intro hratio
  have haN:0<A.card:=by omega
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr haN
  have hb:(0:ℝ)<B.card:=(mul_pos hκ ha).trans_le hB
  let t:=4*Ldel/A.card+3*Ldel/B.card
  have hta:4*Ldel≤t*A.card:=by
    calc
      _ = (4*Ldel/A.card)*A.card:=(div_mul_cancel₀ _ (ne_of_gt ha)).symm
      _ ≤ _:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) ha.le
  have htb:3*Ldel≤t*B.card:=by
    calc
      _ = (3*Ldel/B.card)*B.card:=(div_mul_cancel₀ _ (ne_of_gt hb)).symm
      _ ≤ _:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hb.le
  let Cnorm:=C/(κ*p^5)
  have hCnorm:0≤Cnorm:=by dsimp [Cnorm];positivity
  have hcoef:∀ e,e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet →
      0≤weight e/(B.card*q^2*s^3)∧weight e/(B.card*q^2*s^3)≤Cnorm/(A.card:ℝ)^2:=by
    intro e he
    have hh:=endpoint_triangle_coefficient_bounds A.card B.card κ p q s c C (weight e)
      ha hκ hp hc.le hC.le hB (Nat.cast_le.mpr hBA) hq hq1 hs hs1 (hpos e he)
    exact ⟨(by positivity : 0≤c/(A.card:ℝ)^2).trans hh.1,hh.2⟩
  have hpot:=endpoint_potential_errors_after_deletion P R H F D E A B
    (common A {x} (fun y=>(P\F).neighborFinset y)) x weight
    (fun v=>endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w)))
    (fun _=>q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e))
    (B.card*q^2*s^3) Cnorm Ldel ξ haN hBA hCnorm hLdel hcoef hD hE hrow hindex
  have hrows' : ∀ X J:Finset V,x∈X → X⊆insert x A → J⊆B →
      X.card≤3 → J.card≤2 → X.card+J.card≤4 →
      q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-(ε+t)*A.card≤
        ((common (common A X (fun v=>(R\D).neighborFinset v)) J (fun v=>(H\E).neighborFinset v)).card:ℝ):=by
    intro X J hx hX hJ hXc hJc hXJ
    have hraw:=hrows X J hx hX hJ hXc hJc hXJ
    have hchange:=mixed_common_sdiff_bound R H D E A X J Ldel hD hE
    have hloss:((X.card+J.card:ℕ):ℝ)*Ldel≤4*Ldel:=mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hXJ) hLdel
    have hh:=(abs_le.mp hchange).1
    nlinarith only [hraw,hh,hloss,hta]
  have hindices' : ∀ X:Finset V,x∈X → X⊆insert x A → (X.card=1∨X.card=3) →
      (∀ v∈X,∀ w∈X,¬F.Adj v w) →
      (s^X.card-(ε+t))*B.card≤((common B X (fun v=>(H\E).neighborFinset v)).card:ℝ):=by
    intro X hx hX hXc hXF
    have hraw:=hindices X hx hX hXc hXF
    have hchange:=ordinary_common_sdiff_bound H E B X Ldel hE
    have hcard:X.card≤3:=by rcases hXc with h|h <;> omega
    have hloss:(X.card:ℝ)*Ldel≤3*Ldel:=mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hLdel
    have hh:=(abs_le.mp hchange).1
    nlinarith only [hraw,hh,hloss,htb]
  have hresult:=hfactor V P (R\D) (H\E) F A B x ((le_max_left N 1).trans hn) hAB
    (sdiff_le.trans hR) hFB q s (ε+t) L δ (ξ+5*Cnorm*Ldel/A.card)
    hq hq1 hs hs1 (by dsimp [t];linarith only [hε']) hL hδ hLτ hB hBA hdeg hF
    (by convert hrows' using 1 <;> congr!) (by convert hindices' using 1 <;> congr!) weight hw hsum hzero hpos hbalance hpot.1
    (by
      intro u hu
      apply (hpot.2 u hu).trans
      have hnonneg:0≤Cnorm*Ldel/A.card:=by positivity
      have he:ξ+3*Cnorm*Ldel/A.card+2*(Cnorm*Ldel/A.card)=ξ+5*Cnorm*Ldel/A.card:=by ring
      rw [←he]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hnonneg))
    (by dsimp [Cnorm];linarith only [herr])
    (by convert hratio using 1 <;> congr!)
  convert hresult using 1 <;> congr!

end Oberwolfach
