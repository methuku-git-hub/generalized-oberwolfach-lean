module

public import Oberwolfach.LongAssignedReferenceSeedHubWitness
public import Oberwolfach.MarkedReferencePriorProbabilitySeparate
public import Oberwolfach.LongActualRawLawParameters

@[expose] public section
/-! The existing reference and robust-absorber event with its event predicate
named explicitly, for intersection on the same retained law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_assigned_fixed_vortex_reference_probability_separate
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hm:7≤r+4) (hlen:r+4+1=(k₀+2)*2) (α ρ₀ sstar tstar kstar tol χActive Qexp pstar ζActive:ℝ)
    (hQpow:0<Qpow) (hQexp:0<Qexp) (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀)
    (hsstar:0<sstar) (hsstar1:sstar≤1/100) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/2≤1/2+α)
    (htol:0<tol) (hχActive:0<χActive) (hpstar:0<pstar) (hpstarBound:pstar≤ρ₀*tstar/4) (hζActive:0<ζActive):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig:ℝ,0<βconfig ∧ ∀ εref δref χ β ε:ℝ,
    0<εref→0<δref→0<χ→0≤β→β≤α/8→β≤1/4→β≤εref/4→0<ε→ε<1/4→
    ∀ ε₀:ℝ,χ+2*χActive<ε₀→∀ d:ℕ,∀ hd:2≤d,∃ m₀:ℕ,1≤m₀ ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,∃ n₀:ℕ,1≤n₀ ∧
    ∀ (n:ℕ) (hn:0<n) (U:Type) [Fintype U] [DecidableEq U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (K:ℕ) (hK:0<K) (θ:ℝ) (hθ0:0≤θ) (hθ:θ≤1/100)
      (G:SimpleGraph (Fin n)) (D vsize:ℕ) (hreg:G.IsRegularOfDegree D) (hD:0<D)
      (hmind:(1/2+α)*n≤(D:ℝ)) (hrlo:ρ₀≤ initialIndexDensity U D) (hrhi:initialIndexDensity U D≤1)
      (hcut:(1/((r+4:ℝ)+1))/(d:ℝ)≤θ) (hclass:∀u,factorPreparationClass (F u) K=none),
      m₀≤vsize→n₀≤n→vsize≤n→∀ (Q:Vortex U G D β ε vsize) (π:Equiv.Perm (Fin n))
      (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    let dens:=initialIndexDensity U D
    let p:=dens*(1/100:ℝ)/2
    let k:=dens*((1/100:ℝ)/((r+4:ℕ):ℝ))/2
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let s:=longAssignedSpokeProbability F hF K (r+4) θ
    let hsize:dens*(D:ℝ)=2*Fintype.card U:=by dsimp [dens,initialIndexDensity];field_simp
    let hLaw:=long_assigned_actual_raw_law_parameters hn F hF Allowed hAllowed K hK (r+4) d hm hd θ ρ₀ dens D
      hθ0 hθ hρ₀ hrlo hrhi (by exact_mod_cast hD) hsize (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcut) hclass
    kstar≤p→kstar≤k→tstar≤(1/100:ℝ)/((r+4:ℕ):ℝ)→
    letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
    1-ε₀≤(rawMarkedRetentionLaw π d hd false p k hLaw.1 hLaw.2.1
      (by dsimp only [p,k];have hp:=hLaw.2.2.1;have hk:=hLaw.2.2.2.1;have hu:=hLaw.2.2.2.2.1;have hh:=hLaw.2.2.2.2.2.1;linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2).probability
      (fun z=>MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
        size a₀ b₀ e₀ f₀ G D vsize β ε Q π hpres L (1/100) p k q s false false z) :=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,hcore⟩:=
    marked_fixed_vortex_reference_active_absorber_probability_separate_thresholds r h k₀ Qpow hr hlen α ρ₀ sstar tstar kstar tol χActive Qexp pstar ζActive
      hQpow hQexp hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin htol hχActive hpstar hpstarBound hζActive
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,?_⟩
  intro εref δref χ β ε hεref hδref hχ hβ hβα hβ1 hβε hε hε1 ε₀ hgap d hd
  obtain ⟨m₀,hm₀,hcore⟩:=hcore εref δref χ β ε hεref hδref hχ hβ hβα hβ1 hβε hε hε1 ε₀ hgap d hd
  refine ⟨m₀,hm₀,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hcore⟩:=hcore size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨n₀,hn₀,hcore⟩:=hcore f₀
  refine ⟨n₀,hn₀,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed K hK θ hθ0 hθ G D vsize hreg hD hmind hrlo hrhi hcut hclass hmV hnBig hvn Q π hpres hπ L hL
  intro dens p k q s hsize hLaw hp hk ht
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hqref:∀u,q u false=(1/100:ℝ)/((r+4:ℕ):ℝ):=by intro u; rfl
  have hsref:∀u,s u false=(1/100:ℝ):=by intro u; rfl
  have hkEq:k=p/((r+4:ℕ):ℝ):=by dsimp [p,k];ring
  have hh:=hcore (Fin n) U Bool Bool G D vsize hreg (by simpa using hn) (by simpa using hmind) hrlo hrhi hmV (by simpa using hnBig) (by simpa using hvn) Q π hpres hπ L hL (1/100) hsstar1 (by norm_num)
      (by simpa [p,dens] using hp) (by simpa [p,k,dens,hkEq] using hk)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2 false false hqref hsref ht
  convert hh using 1 <;> congr 4 <;> first
    | rfl
    | exact Subsingleton.elim _ _
    | exact hkEq
    | exact hkEq.symm
    | (funext z; congr 1 <;> first | rfl | exact hkEq | exact hkEq.symm)
end Oberwolfach
