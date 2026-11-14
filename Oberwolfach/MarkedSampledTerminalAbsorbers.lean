module

public import Oberwolfach.MarkedSampledFiniteAbsorbers
public import Oberwolfach.MarkedTerminalAbsorberProperty

@[expose] public section

/-! The original marked retention event supplies a fixed terminal absorber
for every later permitted terminal host and bounded forbidden set. The
finite family of possible remainders is counted before any of its absorbers
are chosen. No additional random sample or independence claim is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sampled_terminal_absorbers
    (k₀ l Q:ℕ) (hl:2≤l) (hlen:l+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω:ℝ) (hα₀:0<α₀) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α₀/2≤1/2+α₀):
    ∃ δ:ℝ,0<δ∧∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f d:ℕ,∀ hd:2≤d,∃ N:ℕ,1≤N∧
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
          MarkedTerminalAbsorberProperty
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
            (H false) (H true) π (3*d) l size a₀ b₀ e₀ f) :=by
  obtain ⟨ε,δ,hε,hδ,hbase⟩:=marked_sampled_finite_absorbers k₀ l Q hl hlen
    α₀ ρstar sstar ω hα₀ hρstar hsstar hω hmargin
  refine ⟨δ,hδ,?_⟩
  intro size
  obtain ⟨a₀,b₀,hbase⟩:=hbase size
  refine ⟨2^(2*size^2)*a₀,2^(2*size^2)*b₀,2^(2*size^2)*(2*a₀^2+a₀*b₀),?_⟩
  intro f d hd
  obtain ⟨N,hN,hbase⟩:=hbase (f+2^(2*size^2)*(2*a₀^2+a₀*b₀)) d hd
  refine ⟨max N (Nat.ceil ((size:ℝ)/ε)),hN.trans (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hUlo hUhi P π hπ D hDlo hDhi hnear hdeg
    ρ s₀ hρlo hρhi hslo hshi densities p k q hq hQ s hs hS g j hq₀ hs₀
  have hevent:=hbase V U Γ Color (by omega) hUlo hUhi P π hπ D hDlo hDhi hnear hdeg
    ρ s₀ hρlo hρhi hslo hshi q hq hQ s hs hS g j hq₀ hs₀
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro z hz
  have hsize:(size:ℝ)≤ε*Fintype.card V:=by
    have hh:(size:ℝ)/ε≤Fintype.card V:=(Nat.le_ceil _).trans
      (Nat.cast_le.mpr (show Nat.ceil ((size:ℝ)/ε)≤Fintype.card V by omega))
    nlinarith only [(div_le_iff₀ hε).mp hh]
  exact marked_finite_to_terminal_absorber _ _ _ _ _ _ _
    (markedSampleArc_physical_injective P π (3*d) (fun e=>z.1 (Sum.inl e)))
    (3*d) l size a₀ b₀ f ε hsize hz

end Oberwolfach
