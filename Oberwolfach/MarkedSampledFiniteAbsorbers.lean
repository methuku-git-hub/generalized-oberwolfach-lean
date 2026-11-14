module

public import Oberwolfach.MarkedCompletionAbsorberInputs
public import Oberwolfach.MarkedFiniteAbsorberProperty
public import Oberwolfach.RetainedMarkedSpokeGeometry

@[expose] public section

/-! Construct marked absorbers for all later bounded divisible remainders
on one retained sample. The absorber size precedes the bounded forbidden
allowance and separation radius. No transformer or profile is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sampled_finite_absorbers
    (k₀ l Q:ℕ) (hl:2≤l) (hlen:l+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω:ℝ) (hα₀:0<α₀) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α₀/2≤1/2+α₀):
    ∃ ε δ:ℝ,0<ε∧0<δ∧∀ size:ℕ,∃ a₀ b₀:ℕ,∀ f d:ℕ,∀ hd:2≤d,∃ N:ℕ,1≤N∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),(∀ x r, 0 < r → r < 2*d+1 → (π^r) x ≠ x)→
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V)→
      (∀ v,(1/2+α₀)*Fintype.card V≤(P.degree v:ℝ))→
    ∀ (ρ s₀:ℝ) (hρlo:ρstar≤ρ) (hρhi:ρ≤1) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let densities:=marked_seed_density_bounds (l+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
    let p:=ρ*s₀/2
    let k:=p/((l+4:ℕ):ℝ)
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (g:Γ) (j:Color),
    (∀ u,q u g=s₀/((l+4:ℕ):ℝ))→(∀ u,s u j=s₀)→
    1-2/(Fintype.card V:ℝ)^Q≤
      (rawMarkedRetentionLaw π d hd g p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
        (fun z=>let H:Bool→V→U→Prop := retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
          MarkedFiniteAbsorberProperty
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
            (H false) (H true) π (3*d) l ε size a₀ b₀ f):=by
  let pstar:=min (ρstar*sstar/(2*((l+4:ℕ):ℝ))) (sstar*sstar/((l+4:ℕ):ℝ))
  let pmin:=min pstar (1/2)
  let γ:=min α₀ (1/2)
  have hpstar:0<pstar:=by dsimp[pstar];positivity
  have hpmin:0<pmin:=lt_min hpstar (by norm_num)
  have hγ:0<γ:=lt_min hα₀ (by norm_num)
  obtain ⟨bc,bp,hbc,hbp,hsample⟩:=marked_completion_absorber_input_realization k₀ l (by omega) hlen α₀ ρstar sstar ω Q hα₀ hρstar hsstar hω hmargin
  obtain ⟨hlo,hhi⟩:=successorWeightConstants_pos k₀ (α₀/2) (by positivity)
  obtain ⟨ε,hε,habs⟩:=marked_finite_remainder_absorber l hl (pmin^4*γ/4) (pmin^(l+11)*ω/2)
    ((sstar/((l+4:ℕ):ℝ))^2) (min bc bp) (successorWeightLower k₀ (α₀/2)/2)
    (2*successorWeightUpper k₀ (α₀/2)/pstar^(2*(l+4)+1))
    (by positivity) (by positivity) (by positivity) (lt_min hbc hbp) (by positivity) (by positivity)
  obtain ⟨δ,hδ,hsample⟩:=hsample ε hε
  refine ⟨ε,δ,hε,hδ,?_⟩
  intro size
  obtain ⟨a₀,b₀,habs⟩:=habs size
  refine ⟨a₀,b₀,?_⟩
  intro f d hd
  obtain ⟨Na,habs⟩:=habs f (3*d)
  obtain ⟨Ns,hNs,hsample⟩:=hsample d hd
  refine ⟨max Na Ns,hNs.trans (le_max_right _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hUlo hUhi P π hπ D hDlo hDhi hnear hdeg
  obtain ⟨weight,hw,hweight⟩:=hsample V U Γ Color (by omega) hUlo hUhi P π hπ D hDlo hDhi hnear hdeg
  intro ρ s₀ hρlo hρhi hslo hshi densities p k q hq hQ s hs hS g j hq₀ hs₀
  have hevent:=(hweight ρ s₀ hρlo hρhi hslo hshi q hq hQ s hs hS g j hq₀ hs₀).2
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro z hz
  let H:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
  obtain ⟨Counts,⟨Profiles⟩⟩:=hz
  change MarkedFiniteAbsorberProperty _ _ _ _ (H false) (H true) π (3*d) l ε size a₀ b₀ f
  intro A S hdiv hsize hspokes W B F₀ hf₀ hpairs hHB hB hW
  apply habs V U _ _ (by omega) _ _ _ _ (H false) (H true) π (by omega) A S hdiv hsize hspokes ?_
    W B F₀ hf₀ hpairs hHB Counts (markedSampleArc_physical_injective P π (3*d) (fun e=>z.1 (Sum.inl e))) hB hW ?_ Profiles
  · intro a ha
    cases a with
    | inl a=>exact marked_sample_host_arc_separated P π (3*d) (fun e=>z.1 (Sum.inl e)) false a
    | inr a=>exact marked_sample_host_arc_separated P π (3*d) (fun e=>z.1 (Sum.inl e)) true a
  · intro v u hK h0
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) g
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j v u ⟨h0,hK⟩

end Oberwolfach
