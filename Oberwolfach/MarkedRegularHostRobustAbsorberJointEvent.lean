module

public import Oberwolfach.MarkedSampledReservedAbsorbersAfterPhysicalDeletion
public import Oberwolfach.MarkedVortexDensityMass
public import Oberwolfach.TwoCommonEvents

@[expose] public section
/-! Specialize the sampled deletion-robust absorber event to the original
regular host and intersect it with an existing event on the same retained
law. The absorber guarantee is uniform over later bounded deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_regular_host_robust_absorber_with_existing_event
    (k₀ l Qpow:ℕ) (hl:2≤l) (hlen:l+4+1=(k₀+2)*2)
    (α ρstar sstar:ℝ) (hα:0<α) (hρstar:0<ρstar) (hsstar:0<sstar)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧ ∀ size:ℕ,
    ∃ a₀ b₀ e₀:ℕ,∀ f d:ℕ,∀ hd:2≤d,∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V→0<Fintype.card V→∀ (G:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D→
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hrlo:ρstar ≤ initialIndexDensity U D) (hrhi:initialIndexDensity U D ≤ 1),
    ∀ (π:Equiv.Perm V),(∀ x j,0 < j → j < 2*d+1 → (π^j) x≠x)→
    ∀ (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let ρ:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds (l+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hrlo hrhi hslo hshi
    let p:=ρ*s₀/2
    let k:=p/((l+4:ℕ):ℝ)
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (g:Γ) (j:Color),
    (∀ u,q u g=s₀/((l+4:ℕ):ℝ))→(∀ u,s u j=s₀)→
    ∀ (E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g→Prop) (err:ℝ),
    1-err≤(rawMarkedRetentionLaw π d hd g p k (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability E→
    1-err-2/(Fintype.card V:ℝ)^Qpow≤
      (rawMarkedRetentionLaw π d hd g p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
        (fun z=>let H:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
          E z ∧ ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
            (∀ x,(DR.degree x:ℝ)≤ζAbs*Fintype.card V)→
            (∀ x,(DS.degree x:ℝ)≤ζAbs*Fintype.card V)→
          let σ':=rawMarkedDeleteRims z.1 DR.edgeFinset
          let H':=markedDeletePhysicalSpokes H DS
          MarkedReservedTerminalAbsorberProperty
            (fun e:MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
            (H' false) (H' true) π (3*d) l size a₀ b₀ e₀ f εAbs):=by
  obtain ⟨εAbs,ζAbs,δAbs,hε,hζ,hδ,hbase⟩:=marked_sampled_reserved_absorbers_after_physical_deletion
    k₀ l Qpow hl hlen α ρstar sstar (ρstar/4) hα hρstar hsstar (by positivity) hmargin
  refine ⟨εAbs,ζAbs,δAbs,hε,hζ,hδ,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hbase⟩:=hbase size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f d hd
  obtain ⟨N,hN,hbase⟩:=hbase f d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hnpos G D hreg hD hrlo hrhi π hπ s₀ hslo hshi ρ densities p k
  have hhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith [mul_nonneg hα.le hn0]
  have hDhi:(D:ℝ)≤2*Fintype.card V:=by
    have hh:D≤Fintype.card V:=regular_degree_le_card hreg hnpos
    have hh':(D:ℝ)≤Fintype.card V:=by exact_mod_cast hh
    have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    linarith
  have hUlo:(ρstar/4)*(Fintype.card V:ℝ)≤Fintype.card U:=by
    have hh:=marked_vortex_hub_mass_lower hreg hnpos hhalf ρstar hρstar hrlo
    nlinarith
  have hUhi:Fintype.card U≤Fintype.card V:=by
    have hDpos:(0:ℝ)<D:=by
      have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hnpos
      linarith
    have hu2:(2:ℝ)*Fintype.card U≤D:=by
      have hh:=(div_le_iff₀ hDpos).mp hrhi
      simpa [initialIndexDensity] using hh
    have hh:D≤Fintype.card V:=regular_degree_le_card hreg hnpos
    have hh':(D:ℝ)≤Fintype.card V:=by exact_mod_cast hh
    have hU0:(0:ℝ)≤Fintype.card U:=Nat.cast_nonneg _
    exact_mod_cast (show (Fintype.card U:ℝ)≤Fintype.card V by linarith)
  have hnear:∀ v,|((G.degree v:ℝ)-(D:ℝ))|≤δAbs*Fintype.card V:=by
    intro v
    rw [hreg v]
    simp only [sub_self,abs_zero]
    positivity
  have hmin:∀ v,(1/2+α)*Fintype.card V≤(G.degree v:ℝ):=by intro v;simpa only [hreg v] using hD
  intro q hq hQ s hs hS g j hq₀ hs₀ E err hE
  have hrob:=hbase V U Γ Color hn hUlo hUhi G π hπ D hhalf hDhi hnear hmin ρ s₀ hrlo hrhi hslo hshi
    q hq hQ s hs hS g j hq₀ hs₀
  let μ:=rawMarkedRetentionLaw π d hd g p k (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hnorm:=hrob
  have hb:=finiteLaw_two_events_lower μ E _ err (2/(Fintype.card V:ℝ)^Qpow) hE hnorm
  convert hb using 1 <;> congr!
end Oberwolfach
