module

public import Oberwolfach.TransferCandidates
public import Oberwolfach.TransferRetentionCommon
public import Oberwolfach.RawIntervalNeighbourGraphs
public import Oberwolfach.OrdinaryRawIntervalSampling
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.SampledNeighbourDensity

@[expose] public section

/-! The original interval/physical sampling law has many potential
transfers simultaneously. Root spokes are omitted, the original ambient
root domain is retained, and all candidate lower counts are derived. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_ordinary_transfer_potential_event
    (r : ℕ) (hr : 3 ≤ r) (α pH : ℝ) (hα : 0<α) (hpH : 0<pH)
    (hδ : (if r=3 then (3/4:ℝ) else 1/2)+α/2≤1) :
    ∃ c : ℝ,0<c ∧ ∀ L : ℝ,0≤L → ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V → 0<Fintype.card V →
    ∀ (P F : SimpleGraph V) (π : Equiv.Perm V),
    (∀ v,((if r=3 then (3/4:ℝ) else 1/2)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) →
    ∀ (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
      (d : ℕ) (hd : 2≤d)
      (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) → (∀ u,s u j=pH) →
    ∀ p t₀ t : ℝ,0≤p → p≤1 → 0<t₀ → 0<t →
      t₀≤pH^2*Fintype.card V/2 → t₀≤α*pH^2*Fintype.card V/4 →
      (∀ e∈P.edgeFinset,p≤ρ e) →
    1-((Fintype.card {a : U×U // a.1≠a.2}:ℝ)*(Fintype.card V+1))*
        (2*Real.exp (-2*t₀^2/((4*(d:ℝ)+3)^2*(2*Fintype.card V))))-
      (Fintype.card (V×{a : U×U // a.1≠a.2}):ℝ)*
        (2*Real.exp (-2*t^2/((r:ℝ)^2*((1+2*r)*r)/Fintype.card V)))≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ v : V,∀ u u' : U,u≠u' →
          p^((1+2*r)*r)*c-t<transferSurvivalSum r hr P F
            (transferRootCompletedSpokes (rawWheelSpokes π d σ j) v) v u u' (fun e=>σ (Sum.inl e))) := by
  let θ : ℝ := if r=3 then 3/4 else 1/2
  have hθ : 0≤θ := by dsimp [θ];split_ifs <;> norm_num
  have hmargin : 0<1-((if r=3 then 3 else 2:ℕ):ℝ)*(1-(θ+α/2)) := by
    dsimp [θ]
    split_ifs <;> push_cast <;> linarith
  obtain ⟨c,hc,hcN⟩ := ordinary_transfer_candidates_many r hr (θ+α/2) (pH^2/2) hδ (by positivity) hmargin
  refine ⟨c,hc,?_⟩
  intro L hL
  obtain ⟨N,hN⟩ := hcN L hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hn P F π hP hF ρ hρ hρ1 d hd q hq hQ s hs hS j hnoshort hj
    p t₀ t hp hp1 ht₀ ht hts htm hprob
  let I := {a : U×U // a.1≠a.2}
  let J := V×I
  let H (ω : RawIntervalFamilyOutcome V U Γ Color) (z : V) (u : U) :=
    rawIntervalFamilyState π d ω (z,u)=some (Sum.inr j)
  let A (ω : RawIntervalFamilyOutcome V U Γ Color) (a : I) :=
    rawIntervalHubNeighbourhood π d ω j {a.val.1,a.val.2}
  let Good (ω : RawIntervalFamilyOutcome V U Γ Color) := ∀ a : I,
    (|((A ω a).card:ℝ)-pH^2*Fintype.card V|<t₀) ∧
    (∀ v,|((P.neighborFinset v∩A ω a).card:ℝ)-pH^2*P.degree v|<t₀)
  let b := ((Fintype.card I:ℝ)*(Fintype.card V+1))*
    (2*Real.exp (-2*t₀^2/((4*(d:ℝ)+3)^2*(2*Fintype.card V))))
  have hpaircard (a : I) : ({a.val.1,a.val.2}:Finset U).card=2 := by simp [a.property]
  have hgood : 1-b≤(FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability Good := by
    have hh := rawIntervalHubNeighbourhood_common_event π d hd q hq hQ s hs hS hnoshort hn P j pH hj
      (fun a : I=>({a.val.1,a.val.2}:Finset U)) (fun _=>Finset.insert_nonempty _ _) 2 (by omega)
      (fun a=>(hpaircard a).le) t₀ ht₀
    simpa only [hpaircard,Nat.cast_ofNat,Good,A,b] using hh
  have hmany (ω : RawIntervalFamilyOutcome V U Γ Color) (hω : Good ω) (a : J) :
      c*(Fintype.card V:ℝ)^(r^2)≤Fintype.card
        (OrdinaryTransferConfiguration hr P F (transferRootCompletedSpokes (H ω) a.1)
          a.1 a.2.val.1 a.2.val.2) := by
    have hcounts (z : V) := sampled_neighbour_density (Fintype.card V:ℝ) (pH^2) θ α t₀
      ((A ω a.2).card:ℝ) (P.degree z:ℝ) ((P.neighborFinset z∩A ω a.2).card:ℝ)
      (Nat.cast_nonneg _) (sq_nonneg _) hα (by positivity) hδ ht₀.le hts htm
      (hω a.2).1.le (hP z) ((hω a.2).2 z).le
    have hA : (pH^2/2)*Fintype.card V≤((A ω a.2).card:ℝ) := by
      have hh := (hcounts a.1).1
      linarith only [hh]
    have hH : ∀ z∈A ω a.2,H ω z a.2.val.1 ∧ H ω z a.2.val.2 := by
      intro z hz
      simpa only [A,rawIntervalHubNeighbourhood,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,H] using hz
    have hh := hN V U hnN P F (A ω a.2) a.1 (H ω) a.2.val.1 a.2.val.2 hA
      (fun z _=>by simpa only [Finset.inter_comm] using (hcounts z).2) hF hH
    convert hh using 1 <;> congr!
  let μ := rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS
  have hh := transferSurvivalSum_two_exposures r hr P F
    (fun ω (a : J)=>transferRootCompletedSpokes (H ω) a.1)
    Prod.fst (fun a : J=>a.2.val.1) (fun a : J=>a.2.val.2) hn
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)) Good b hgood
    (fun e=>FiniteLaw.retentionCoin (ρ e) (hρ e) (hρ1 e)) p t (fun _=>c) hp hp1 ht
    (fun e he=>hprob e he) hmany
  have he := finiteLaw_pi_sum_probability μ
    (fun ω τ=>Good ω ∧ ∀ a : J,p^((1+2*r)*r)*c-t<transferSurvivalSum r hr P F
      (transferRootCompletedSpokes (H ω) a.1) a.1 a.2.val.1 a.2.val.2 τ)
  erw [← he] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ v u u' huu
  convert hσ.2 (v,⟨(u,u'),huu⟩) using 1 <;> congr!

end Oberwolfach
