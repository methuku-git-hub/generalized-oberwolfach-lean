module

public import Oberwolfach.CycleSamplingAlmostRegularParameters
public import Oberwolfach.OrdinarySamplingPackingFromMeans

@[expose] public section
/-! Almost-spanning vertex-disjoint cycle packing from a bounded perfect
fractional cycle decomposition of an almost-regular dense graph. -/
set_option autoImplicit false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_almost_regular_fractional_cycle_packing
    (r:ℕ) (hr:3≤r) (B θ γ:ℝ) (hB:1≤B) (hθ:0<θ) (hθsmall:θ≤1/20)
    (hγ:0<γ) (hγ1:γ≤1):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V)
      [DecidableEq (OrdinaryCycle G r)],N≤Fintype.card V→
      ∀ d:ℝ,(Fintype.card V:ℝ)/2≤d→d≤Fintype.card V→
      (∀ v,(Fintype.card V:ℝ)/2≤(G.degree v:ℝ))→
      (∀ v,|(G.degree v:ℝ)-d|≤θ*(Fintype.card V:ℝ)/4)→
      ∀ w:OrdinaryCycle G r→ℝ,
      (∀ e:G.edgeSet,∑ C,w C*ordinaryCycleIncidence G r C e=1)→
      (∀ C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-2))→
      ∃ M:Finset (OrdinaryCycle G r),
        (∀ C∈M,∀ C'∈M,C≠C'→Disjoint C.val.val.support.toFinset C'.val.val.support.toFinset) ∧
        (1-γ)*(1-10*θ)*Fintype.card V≤(r:ℝ)*M.card := by
  have hBpos:0<B := by linarith
  have hrpos:0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  let a:ℝ:=(1-10*θ)/(2*r)
  let av:ℝ:=1/(8*B)
  let q:ℝ:=(r:ℝ)^2/2
  let c:ℝ:=Real.exp 1*(r:ℝ)^2
  let K:ℝ:=8*B*c
  have hslack:0<1-10*θ := by linarith
  have ha:0<a := by dsimp [a];positivity
  have hav:0<av := by dsimp [av];positivity
  have hq:0≤q := by dsimp [q];positivity
  have hc:0<c := by dsimp [c];positivity
  have hK:0<K := by dsimp [K];positivity
  have hε:0≤10*θ := by positivity
  have hmargin:a*r≤1-10*θ := by
    have hnon:0≤1-10*θ := by linarith
    dsimp [a]
    field_simp
    linarith
  have hscale:2*Real.exp 1*q≤c := by dsimp [q,c];ring_nf;rfl
  obtain ⟨Npack,hpack⟩:=ordinary_sampling_packing_from_means r 2 hr K a γ (10*θ) θ av q c
    hK ha hγ hγ1 hε hmargin hθ (by linarith) hav hq hc hscale
  obtain ⟨Nparam,hparam⟩:=cycle_sampling_almost_regular_parameters B θ c hB hθ hθsmall hc.le
  refine ⟨max 1 (max Npack Nparam),?_⟩
  intro V _ _ G _ hn d hdlo hdhi hmin hreg w hw hwb
  have hnpos:0<Fintype.card V:=by omega
  let scale:ℝ:=(Fintype.card V:ℝ)/(2*B)
  obtain ⟨D,hDlo,hDhi,hcode,hrows⟩:=hparam (Fintype.card V)
    ((le_max_right Npack Nparam).trans ((le_max_right 1 _).trans hn)) d hdlo hdhi
  have hp:=ordinary_cycle_sampling_scaled_probability G r hr hnpos B hBpos w hwb
  have hlo (v:V):av*(Fintype.card V:ℝ)^2≤scale*(G.degree v:ℝ)/2 := by
    have hh:=ordinary_cycle_sampling_vertex_mean_lower (Fintype.card V) (G.degree v) B (Nat.cast_nonneg _) hBpos (hmin v)
    dsimp [av,scale]
    convert hh using 1 <;> ring
  have hrows' (v:V):(1-10*θ)*D≤(1-θ)*(scale*(G.degree v:ℝ)/2) ∧
      (1+θ)*(scale*(G.degree v:ℝ)/2)≤D := hrows (G.degree v) (hreg v)
  have hpair:scale*((r:ℝ)^2*B)≤q*Fintype.card V := by
    have hh:=ordinary_cycle_sampling_pair_mean_scale (Fintype.card V) B r hBpos
    dsimp [scale,q]
    linarith
  have hcode':c*Fintype.card V≤K*D/Fintype.card V := by
    dsimp [K];exact hcode
  obtain ⟨σ,_,M,hdisj,hcover⟩:=hpack V G
    ((le_max_left Npack Nparam).trans ((le_max_right 1 _).trans hn)) D hDlo hDhi w hw B scale hBpos.le
    (by dsimp [scale];positivity) (fun C=>(hwb C).2) (fun C=>(hp C).1)
    (fun C=>le_trans (hp C).2 (by norm_num)) hlo hrows' hpair hcode'
  let f:RetainedOrdinaryCycle G r σ→OrdinaryCycle G r:=Subtype.val
  refine ⟨M.image f,?_,?_⟩
  · intro C hC C' hC' hne
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hC'
    have hxy:x≠y := fun hh=>hne (congrArg Subtype.val hh)
    simpa [retainedOrdinaryCycleVertices,f] using hdisj x hx y hy hxy
  · have hcard:(M.image f).card=M.card := Finset.card_image_of_injective _ Subtype.val_injective
    rw [hcard]
    exact hcover
end Oberwolfach
