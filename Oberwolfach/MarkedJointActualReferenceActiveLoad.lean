module

public import Oberwolfach.MarkedReferenceActiveAbsorberEventNamed
public import Oberwolfach.MarkedActualActiveLoadEventManuscriptSeeds

@[expose] public section
/-! The actual active local-load estimates and the reference, active-row and
robust-absorber event on one retained outcome, for the manuscript seeds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_joint_actual_reference_active_load
    (r h k₀ Qpow:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρ₀ sstar tstar kstar tolRef χActive Qref pstarRef ζActive τ tolLocal χLocal Qlocal ζLocal:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2)
    (htolRef:0<tolRef) (hχActive:0<χActive) (hpstarRef:0<pstarRef)
    (hpstarRefBound:pstarRef≤ρ₀*tstar/4) (hζActive:0<ζActive)
    (hτ:0<τ) (htolLocal:0<tolLocal) (hχLocal:0<χLocal) (hζLocal:0<ζLocal):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig βmax:ℝ,0<βconfig ∧ 0<βmax ∧ ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,
    ∀ εref δref χRef β ε:ℝ,
    0<εref→0<δref→0<χRef→0≤β→β≤βmax→β≤εref/4→0<ε→ε<1/4→
    ∀ (f₀ d:ℕ) (hd:2≤d),∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    m₀≤m→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let X:=fun i=>↥(A i)
    let f:=fun i=>markedVortexActiveVertexEmbedding Q i
    let g:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρ:=fun i=>markedVortexActivePermutation Q π hpres i
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ));
    ∃ weight:∀ i,(Fin (r+4+1)→X i)→ℝ,
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds (r+4) (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/((r+4:ℕ):ℝ);
    kstar≤p→kstar≤kval→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/((r+4:ℕ):ℝ))→(∀ u,s u j=s₀)→tstar≤s₀/((r+4:ℕ):ℝ)→
    let Eref:=MarkedReferenceActiveAbsorberProperty r h d (α/2) βconfig εref δref tolRef ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j
    let err:=χRef+2*χActive+2*(Fintype.card V:ℝ)^(-Qref)+2/(Fintype.card V:ℝ)^Qpow;
    1-χLocal-(Fintype.card V:ℝ)^(-Qlocal)-err≤
      (rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>(∀ i≤L+1,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d (r+4) (Dactive i) p kval s₀ (weight i)
        (τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζLocal)
        (rawMarkedRestrictPair (f i) (g i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Eref z):=by
  have hαref:0<α/2:=by positivity
  have hαref1:α/2≤1:=by linarith
  have hmarginref:successorCycleRatio k₀+(α/2)/2≤1/2+α/2:=by linarith
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,href⟩:=
    marked_fixed_vortex_reference_active_absorber_event_named r h k₀ Qpow hr hlen (α/2) ρ₀ sstar tstar kstar
      tolRef χActive Qref pstarRef ζActive hαref hαref1 hρ₀ hsstar htstar htstar1 horder hkstar hmarginref
      htolRef hχActive hpstarRef hpstarRefBound hζActive
  obtain ⟨βlocal,hβlocal,hlocal⟩:=
    marked_actual_active_local_load_event_manuscript_seeds k₀ (r+4) hlen (by omega)
      α τ ρ₀ sstar tolLocal χLocal Qlocal tstar ζLocal
      hα hτ hρ₀ hsstar htolLocal hχLocal htstar hζLocal hmargin
  let βmax:=min βlocal (min (α/16) (1/4))
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βmax,hβconfig,hβmax,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,href⟩:=href size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro εref δref χRef β ε hεref hδref hχRef hb hbmax hbε he he1 f₀ d hd
  have hblocal:β≤βlocal:=hbmax.trans (min_le_left _ _)
  have hbα:β≤(α/2)/8:=by
    have hh:=hbmax.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hb1:β≤1/4:=hbmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨mRef,hmRef,href⟩:=href εref δref χRef β ε hεref hδref hχRef hb hbα hb1 hbε he he1 f₀ d hd
  obtain ⟨NLocal,hNLocal,hlocal⟩:=hlocal d hd
  obtain ⟨mLocal,hmLocal,hlocal⟩:=hlocal ε he he1.le
  let m₀:=max mRef (max mLocal NLocal)
  have hm₀:1≤m₀:=hmRef.trans (le_max_left _ _)
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm hmn Q π hpres hshort L hL W Z A B X f g ρ Dactive pstarLocal
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hnLocal:NLocal≤Fintype.card V:=by
    have hmN:NLocal≤m:=(le_max_right mLocal NLocal).trans ((le_max_right mRef _).trans hm)
    exact hmN.trans hmn
  have hmref:mRef≤m:=(le_max_left _ _).trans hm
  have hmlocal:mLocal≤m:=(le_max_left mLocal NLocal).trans ((le_max_right mRef _).trans hm)
  obtain ⟨weight,hweight⟩:=hlocal V U G D m β Q hreg hn hnLocal hD hρlo hρhi hb hblocal hmlocal π hpres hshort (L+1) (by omega)
  refine ⟨weight,?_⟩
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo Eref err
  have hDref:(1/2+α/2)*Fintype.card V≤(D:ℝ):=by
    have hn':(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith
  have hRef:=href V U Γ Color G D m hreg hn hDref hρlo hρhi hmref hmn Q π hpres hshort L hL
    s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
  have hExtra:1-err≤(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability Eref:=by
    dsimp [err]
    linarith
  exact hweight Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo Eref err hExtra
end Oberwolfach
