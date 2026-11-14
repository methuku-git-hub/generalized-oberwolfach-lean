module

public import Oberwolfach.ProfileEligibleRoots

@[expose] public section

/-! One outcome satisfying all vertex tests, all eligible profile-root
tests, and a further event. The candidate labels are fixed before the
sample; the bound uses their number present in one outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem finiteLaw_vertices_bad_probability {Ω W : Type*} [Fintype Ω] [Fintype W] [DecidableEq W]
    (μ : FiniteLaw Ω) (Y : Ω → Finset W) (M : ℕ) (hM : ∀ ω,(Y ω).card ≤ M)
    (Bad : W → Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ v,μ.probability (fun ω => v∈Y ω ∧ Bad v ω) ≤
      ε*μ.probability (fun ω => v∈Y ω)) :
    μ.probability (fun ω => ∃ v∈Y ω,Bad v ω) ≤ ε*M := by
  have hcard (ω) : ((Finset.univ.filter (fun v : W => v∈Y ω)).card:ℝ) ≤ M := by
    have he : Finset.univ.filter (fun v : W => v∈Y ω)=Y ω := by ext v;simp
    rw [he]
    exact_mod_cast hM ω
  have hh := finiteLaw_eligible_bad_probability μ Finset.univ (fun v ω => v∈Y ω) Bad M ε hε
    (fun ω => by convert hcard ω using 1 <;> congr!) (fun v _ => h v)
  simpa only [Finset.mem_univ,exists_const,true_and] using hh

theorem profile_roots_bad_probability {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (a : I → ℕ) (c : ℕ) (ha : ∑ i,a i=c)
    (Y : Ω → Finset (Σ i,V i)) (M : ℕ) (hM : ∀ ω,(Y ω).card ≤ M)
    (Bad : (∀ i,FixedSubset (V i) (a i)) → Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ ρ,μ.probability (fun ω => profileRootSet ρ⊆Y ω ∧ Bad ρ ω) ≤
      ε*μ.probability (fun ω => profileRootSet ρ⊆Y ω)) :
    μ.probability (fun ω => ∃ ρ,profileRootSet ρ⊆Y ω ∧ Bad ρ ω) ≤ ε*(M:ℝ)^c := by
  have hg := profile_roots_common_event μ a c ha Y M hM Bad ε hε h
  have hc := finiteLaw_probability_compl μ (fun ω => ∃ ρ,profileRootSet ρ⊆Y ω ∧ Bad ρ ω)
  simp only [not_exists,not_and] at hc
  linarith

theorem profile_all_sampling_tests_exists {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (a : I → ℕ) (c : ℕ) (ha : ∑ i,a i=c)
    (Y : Ω → Finset (Σ i,V i)) (M : ℕ) (hM : ∀ ω,(Y ω).card ≤ M)
    (BadV : (Σ i,V i) → Ω → Prop)
    (BadR : (∀ i,FixedSubset (V i) (a i)) → Ω → Prop) (BadOther : Ω → Prop)
    (εv εr δ : ℝ) (hεv : 0 ≤ εv) (hεr : 0 ≤ εr)
    (hV : ∀ v,μ.probability (fun ω => v∈Y ω ∧ BadV v ω) ≤
      εv*μ.probability (fun ω => v∈Y ω))
    (hR : ∀ ρ,μ.probability (fun ω => profileRootSet ρ⊆Y ω ∧ BadR ρ ω) ≤
      εr*μ.probability (fun ω => profileRootSet ρ⊆Y ω))
    (hOther : μ.probability BadOther ≤ δ)
    (hsmall : εv*M+εr*(M:ℝ)^c+δ < 1) :
    ∃ ω,0 < μ.mass ω ∧
      (∀ v∈Y ω,¬BadV v ω) ∧
      (∀ ρ,profileRootSet ρ⊆Y ω → ¬BadR ρ ω) ∧ ¬BadOther ω := by
  let A := fun j : Fin 3 => if j=0 then (fun ω => ∃ v∈Y ω,BadV v ω)
    else if j=1 then (fun ω => ∃ ρ,profileRootSet ρ⊆Y ω ∧ BadR ρ ω) else BadOther
  let p := fun j : Fin 3 => if j=0 then εv*M else if j=1 then εr*(M:ℝ)^c else δ
  have htests : ∀ j∈Finset.univ,μ.probability (A j) ≤ p j := by
    intro j _
    fin_cases j <;> norm_num [A,p]
    · simpa only [Sigma.exists] using finiteLaw_vertices_bad_probability μ Y M hM BadV εv hεv hV
    · exact profile_roots_bad_probability μ a c ha Y M hM BadR εr hεr hR
    · exact hOther
  have hp : ∑ j∈(Finset.univ : Finset (Fin 3)),p j < 1 := by
    simpa [p,Fin.sum_univ_succ,add_assoc] using hsmall
  obtain ⟨ω,hω,hgood⟩ := finiteLaw_common_event_exists μ Finset.univ A p htests hp
  have hv := hgood 0 (Finset.mem_univ _)
  have hr := hgood 1 (Finset.mem_univ _)
  have ho := hgood 2 (Finset.mem_univ _)
  simp only [A,ite_true,not_exists,not_and] at hv
  simp only [A,show (1 : Fin 3)≠0 by decide,ite_false,ite_true,not_exists,not_and] at hr
  simp only [A,show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,ite_false] at ho
  exact ⟨ω,hω,hv,hr,ho⟩

end Oberwolfach
