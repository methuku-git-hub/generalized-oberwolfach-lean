module

public import Oberwolfach.OrdinaryIsolatorCandidateCounts
public import Oberwolfach.RawWheelRootedSurvival
public import Oberwolfach.RawIntervalNeighbourGraphs
public import Oberwolfach.SampledNeighbourDensity

@[expose] public section

/-! Uniform potential ordinary isolator counts in the original two-exposure
law. Dense candidate families are proved from ambient degree estimates;
the endpoint spokes and physical root edge are still omitted. The bounded
set size and candidate constant precede the actual spoke marginal pH. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_ordinary_isolator_uniform_potential_event
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1) (hpstar : 0<pstar) :
    ∃ K : ℕ,2≤K ∧ ∀ k : ℕ,K≤k → ∃ c : ℝ,0<c ∧
    ∀ L : ℝ,0≤L → ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V → 0<Fintype.card V →
    ∀ (P F : SimpleGraph V) (π : Equiv.Perm V) (θ : ℝ),0≤θ → θ+α/2≤1 →
    (∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) →
    ∀ (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
      (d : ℕ) (hd : 2≤d)
      (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color), (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
      ∀ pH : ℝ,pstar≤pH → (∀ u,s u j=pH) →
    ∀ p t₀ t : ℝ,0≤p → p≤1 → 0<t₀ → 0<t →
      t₀≤pH*Fintype.card V/2 → t₀≤α*pH*Fintype.card V/4 →
      (∀ e∈P.edgeFinset,p≤ρ e) →
    1-((Fintype.card U:ℝ)*(Fintype.card V+1))*
        (2*Real.exp (-2*t₀^2/((4*(d:ℝ)+3)^2*Fintype.card V)))-
      (Fintype.card ({a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}×U):ℝ)*
        (2*Real.exp (-2*t^2/(((2+k:ℕ):ℝ)^2/Fintype.card V)))≤
      (FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ x y : V,x≠y → ¬F.Adj x y → ∀ u : U,
          p^((2+k)^2)*c-t<rootedInducedSurvivalSum P
            (fun S : OrdinaryIsolatorCandidate P F (rawWheelSpokes π d σ j)
              (2+k) θ (α/4) x y u=>S.val)
            s(x,y) (fun e=>σ (Sum.inl e))) := by
  obtain ⟨K,hK⟩ := ordinary_isolator_candidate_many α (pstar/2) hα hα1 (by positivity)
  refine ⟨max K 2,le_max_right _ _,?_⟩
  intro k hk
  obtain ⟨c,hc,hcN⟩ := hK k ((le_max_left _ _).trans hk)
  refine ⟨c,hc,?_⟩
  intro L hL
  obtain ⟨N,hN⟩ := hcN L hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hn P F π θ hθ hθ1 hP hF
    ρ hρ hρ1 d hd q hq hQ s hs hS j hnoshort pH hpHlo hj p t₀ t hp hp1 ht₀ ht hts htm hprob
  have hpH : 0<pH := hpstar.trans_le hpHlo
  let J := {a : V×V // a.1≠a.2 ∧ ¬F.Adj a.1 a.2}×U
  let H (ω : RawIntervalFamilyOutcome V U Γ Color) (z : V) (u : U) :=
    rawIntervalFamilyState π d ω (z,u)=some (Sum.inr j)
  let A (ω : RawIntervalFamilyOutcome V U Γ Color) (u : U) :=
    rawIntervalHubNeighbourhood π d ω j {u}
  let Good (ω : RawIntervalFamilyOutcome V U Γ Color) := ∀ u : U,
    (|((A ω u).card:ℝ)-pH*Fintype.card V|<t₀) ∧
    (∀ v,|((P.neighborFinset v∩A ω u).card:ℝ)-pH*P.degree v|<t₀)
  let b := ((Fintype.card U:ℝ)*(Fintype.card V+1))*
    (2*Real.exp (-2*t₀^2/((4*(d:ℝ)+3)^2*Fintype.card V)))
  have hgood : 1-b≤(FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability Good := by
    have hh := rawIntervalHubNeighbourhood_common_event π d hd q hq hQ s hs hS hnoshort hn P j pH hj
      (fun u : U=>({u}:Finset U)) (fun u=>Finset.singleton_nonempty u) 1 (by omega)
      (by intro u; simp) t₀ ht₀
    simpa only [Finset.card_singleton,pow_one,Nat.cast_one,one_mul,Good,A,b] using hh
  let I (ω : RawIntervalFamilyOutcome V U Γ Color) (a : J) :=
    OrdinaryIsolatorCandidate P F (H ω) (2+k) θ (α/4) a.1.val.1 a.1.val.2 a.2
  have hmany (ω : RawIntervalFamilyOutcome V U Γ Color) (hω : Good ω) (a : J) :
      c*(Fintype.card V:ℝ)^((2+k)-2)≤Fintype.card (I ω a) := by
    have hcounts (v : V) := sampled_neighbour_density
      (Fintype.card V:ℝ) pH θ α t₀ ((A ω a.2).card:ℝ) (P.degree v:ℝ)
      ((P.neighborFinset v∩A ω a.2).card:ℝ) (Nat.cast_nonneg _) hpH.le hα
      (by positivity) hθ1 ht₀.le hts htm (hω a.2).1.le (hP v) ((hω a.2).2 v).le
    have hA : (pstar/2)*Fintype.card V≤((A ω a.2).card:ℝ) := by
      have hh := (hcounts a.1.val.1).1
      have hscale := mul_le_mul_of_nonneg_right hpHlo (Nat.cast_nonneg (Fintype.card V) : (0:ℝ)≤Fintype.card V)
      linarith only [hh,hscale]
    have hH : ∀ z∈A ω a.2,H ω z a.2 := by
      intro z hz
      simpa only [A,rawIntervalHubNeighbourhood,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.mem_singleton,forall_eq,H] using hz
    have hh := hN V U hnN P F (H ω) (A ω a.2) a.1.val.1 a.1.val.2 a.2
      a.1.property.1 a.1.property.2 hA hH θ hθ (by linarith) (fun v _=>(hcounts v).2) hF
    simp only [Nat.add_sub_cancel_left]
    convert hh using 1 <;> congr!
  have hh := rawWheelRootedSurvival_common_event (J:=J) P ρ hρ hρ1 d hd q hq hQ s hs hS
    (I:=I) (fun _ _ S=>S.val) (fun _ _=>Subtype.val_injective)
    (fun a=>a.1.val.1) (fun a=>a.1.val.2) (fun a=>a.1.property.1)
    (by omega : 4≤2+k) hn (fun _ _ S=>S.property.1)
    Good b hgood p t (fun _=>c) hp hp1 ht hprob hmany
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ x y hxy hfxy u
  convert hσ.2 (⟨(x,y),hxy,hfxy⟩,u) using 1 <;> congr!

end Oberwolfach
