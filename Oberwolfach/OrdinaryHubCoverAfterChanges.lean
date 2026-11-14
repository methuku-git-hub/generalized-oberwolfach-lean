module

public import Oberwolfach.OrdinaryHubCoverFromSpokePotentials
public import Oberwolfach.OrdinaryHubCountChanges
public import Oberwolfach.OrdinaryPotentialDegreeStability

@[expose] public section

/-! One set of original counts and root-omitted loads supports every later
bounded host modification and every permissible list of hubs. The fixed
cycle coefficients and the original order are retained throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_hub_cover_after_changes (m:ℕ) (hm:2≤m) (α p b B:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hb:0<b) (hB:0≤B):
    ∃ ε ρ:ℝ,0<ε ∧ 0<ρ ∧ ∃ N:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P R F:SimpleGraph V) (H:V→U→Prop) (q s:ℝ),p≤q → p≤s →
      (∀ v,(ordinaryLocalBaseDegree m+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ u,∀ S:Finset V,S.card≤3→
        |((common (common Finset.univ S (fun v=>R.neighborFinset v)) {u}
          (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
          q^S.card*s*(common Finset.univ S (fun v=>P.neighborFinset v)).card|≤ε*Fintype.card V) →
    ∀ φ:OrdinaryCycle P (m+1)→ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^m≤φ C ∧ φ C≤B/(Fintype.card V:ℝ)^m) →
      (∀ v u,|ordinaryPotentialLoad (ordinaryCycleWheelWeight P F (m+1) φ 1) (Sum.inr (v,u)) R H-1|≤ε) →
    ∀ (Q:SimpleGraph V) (H':V→U→Prop) (L:ℝ),Q≤P → 0≤L → L≤ρ*Fintype.card V →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
      (∀ v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (H' v))).card:ℝ)≤L) →
      (∀ u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H' v u))).card:ℝ)≤L) →
    ∀ (n:ℕ) (u:Fin n→U),Function.Injective u →
      (∀ v,(2*(Finset.univ.filter (fun i=>H' v (u i))).card:ℝ)≤ρ*Fintype.card V) →
      (∀ i,(m+1)∣(Finset.univ.filter (fun v=>H' v (u i))).card) →
      ∃ M:Finset (OrdinaryWheel Q F H' (m+1)),
        (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)) ∧
        M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
          Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H' v (u i))).image (fun v=>Sum.inr (v,u i))) ∧
        (∀ v,(ordinaryWheelRimGraph M).degree v≤2*(Finset.univ.filter (fun i=>H' v (u i))).card) ∧
        (∀ i,∀ v,H' v (u i)→∃! W:M,Sum.inr (v,u i)∈ordinaryWheelResources W.val):=by
  obtain ⟨θ,hθ,N,hcover⟩:=ordinary_hub_cover_from_spoke_potentials m hm α p b B hα hp hp1 hb hB
  let C:ℝ:=4*(m+1:ℝ)^4*B
  have hC:0≤C:=by dsimp [C];positivity
  let ρ:=min (θ/8) (θ/(2*(C+1)))
  have hρ:0<ρ:=lt_min (by positivity) (by positivity)
  have hρ8:8*ρ≤θ:=by have h:=min_le_left (θ/8) (θ/(2*(C+1)));dsimp [ρ];linarith only [h]
  have hρθ:ρ≤θ:=by linarith only [hρ8,hρ]
  have hCρ:C*ρ≤θ/2:=by
    have h:=min_le_right (θ/8) (θ/(2*(C+1)))
    have hh:ρ*(2*(C+1))≤θ:=(le_div_iff₀ (by positivity)).mp h
    nlinarith only [hh,hρ]
  refine ⟨θ/2,ρ,by positivity,hρ,max N 1,?_⟩
  intro V U _ _ _ _ hn hU P R F H q s hq hs hP hcounts φ hφ hpot Q H' L hQP hL hLρ hF hQR hHr hHc n u hu hinc hdiv
  have hnN:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hnN
  have hρn:ρ*Fintype.card V≤θ*Fintype.card V:=mul_le_mul_of_nonneg_right hρθ hnR.le
  have hc:=ordinary_hub_counts_under_changes P R Q F H H' q s (θ/2) θ L
    (hp.le.trans hq) (hp.le.trans hs) hL (by
      have h:=mul_le_mul_of_nonneg_right hρ8 hnR.le
      nlinarith only [h,hLρ]) hQR hHc hcounts
  have hpotential (v:V) (u:U):
      |ordinaryPotentialLoad (ordinaryCycleWheelWeight P F (m+1) φ 1) (Sum.inr (v,u)) Q H'-1|≤θ:=by
    have hh:=ordinaryPotentialLoad_spoke_degree_stability P F (fun _ : V=>fun _ : U=>True)
      (m+1) (by omega) hnN hU (ordinaryCycleWheelWeight P F (m+1) φ 1) B hB
      (fun W=>by
        dsimp [ordinaryCycleWheelWeight]
        simpa only [div_one,Nat.add_sub_cancel] using
          And.intro ((div_pos hb (pow_pos hnR _)).le.trans (hφ W.val.1).1) (hφ W.val.1).2)
      R Q H H' L hL
      (fun v=>by rw [←graph_changed_neighbour_card];exact hQR v)
      (fun v=>by
        have hh:=hHr v
        rw [changed_predicate_card] at hh
        convert hh using 1 <;> simp only [bipAdj] <;> congr!)
      (fun u=>by
        have hh:=hHc u
        rw [changed_predicate_card] at hh
        convert hh using 1 <;> simp only [bipAdj] <;> congr!) v u
    have hcst:C*L/Fintype.card V≤θ/2:=by
      have hratio:L/(Fintype.card V:ℝ)≤ρ:=(div_le_iff₀ hnR).mpr hLρ
      calc
        _=C*(L/Fintype.card V):=by ring
        _≤C*ρ:=mul_le_mul_of_nonneg_left hratio hC
        _≤θ/2:=hCρ
    have hcast:((m+1:ℕ):ℝ)=(m+1:ℝ):=by norm_cast
    rw [hcast] at hh
    have hst:=target_stability hh (hpot v u)
    exact hst.trans (by change θ/2+C*L/Fintype.card V≤θ;linarith only [hcst])
  exact hcover V U P Q F H' q s (by omega) hQP hq hs hP
    (fun v=>(hF v).trans (hLρ.trans hρn))
    (fun u S hS=>hc u S (hS.trans (by unfold ordinaryLocalRootBound;split_ifs <;> omega)))
    φ hφ hpotential n u hu (fun v=>(hinc v).trans hρn) hdiv

end Oberwolfach
