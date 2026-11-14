module

public import Oberwolfach.MarkedReferenceActiveAbsorberProperty
public import Oberwolfach.MarkedReferenceActiveAbsorberSeparateThresholds
public import Oberwolfach.MarkedReferencePriorFailureUniform

@[expose] public section
/-! The existing reference and robust-absorber event with its event predicate
named explicitly, for intersection on the same retained law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_reference_active_absorber_probability_separate_thresholds
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2) (α ρ₀ sstar tstar kstar tol χActive Qexp pstar ζActive:ℝ)
    (hQpow:0<Qpow) (hQexp:0<Qexp) (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀)
    (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α)
    (htol:0<tol) (hχActive:0<χActive) (hpstar:0<pstar) (hpstarBound:pstar≤ρ₀*tstar/4) (hζActive:0<ζActive):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig:ℝ,0<βconfig ∧ ∀ εref δref χ β ε:ℝ,
    0<εref→0<δref→0<χ→0≤β→β≤α/8→β≤1/4→β≤εref/4→0<ε→ε<1/4→
    ∀ ε₀:ℝ,χ+2*χActive<ε₀→∀ d:ℕ,∀ hd:2≤d,∃ m₀:ℕ,1≤m₀ ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,∃ n₀:ℕ,1≤n₀ ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hrlo:ρ₀ ≤ initialIndexDensity U D) (hrhi:initialIndexDensity U D ≤ 1),
      m₀≤m→n₀≤Fintype.card V→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D
    let I:=markedVortexInnerVertices Q
    let T:=markedVortexDeeperVertices Q
    let J:=markedVortexInnerHubs Q
    let Wrem:=markedVortexDeeperHubs Q;
    ∀ (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds (r+4) (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hrlo hrhi hslo hshi
    let p:=dens*s₀/2
    let k:=p/((r+4:ℕ):ℝ)
    kstar≤p→kstar≤k→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (a:Γ) (j:Color),(∀ u,q u a=s₀/((r+4:ℕ):ℝ))→(∀ u,s u j=s₀)→tstar≤s₀/((r+4:ℕ):ℝ)→
    1-ε₀≤
      (rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
        size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z) :=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,hcore⟩:=
    marked_fixed_vortex_reference_active_absorber_event_separate_thresholds r h k₀ Qpow hr hlen α ρ₀ sstar tstar kstar tol χActive Qexp pstar ζActive
      hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin htol hχActive hpstar hpstarBound hζActive
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,?_⟩
  intro εref δref χ β ε hεref hδref hχ hβ hβα hβ1 hβε hε hε1 ε₀ hgap d hd
  obtain ⟨m₀,hm₀,hcore⟩:=hcore εref δref χ β ε hεref hδref hχ hβ hβα hβ1 hβε hε hε1 d hd
  obtain ⟨N,hN⟩:=eventually_marked_reference_absorber_failure_below χ χActive Qexp ε₀ Qpow hQexp hQpow hgap
  refine ⟨m₀,hm₀,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hcore⟩:=hcore size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨n₀,hn₀,hcore⟩:=hcore f₀
  refine ⟨max n₀ N,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ G D m hreg hn hmind hrlo hrhi hm hnBig hmV Q π hpres hπ L hL
  intro W Z f g ρ Dload I T J Wrem s₀ hslo hshi dens densities p k hp hk q hq hQ s hs hS a j hqa hsj htstar
  have hbig:N≤Fintype.card V:=by omega
  have hsmall:=hN (Fintype.card V) hbig
  have hh:=hcore V U Γ Color G D m hreg hn hmind hrlo hrhi hm (by omega) hmV Q π hpres hπ L hL s₀ hslo hshi hp hk q hq hQ s hs hS a j hqa hsj htstar
  have hh':1-χ-2*χActive-2*(Fintype.card V:ℝ)^(-Qexp)-2/(Fintype.card V:ℝ)^Qpow≤
      (rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
        size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z):=by
    simpa only [MarkedReferenceActiveAbsorberProperty] using hh
  apply (show 1-ε₀≤1-χ-2*χActive-2*(Fintype.card V:ℝ)^(-Qexp)-2/(Fintype.card V:ℝ)^Qpow by linarith).trans
  exact hh'
end Oberwolfach
