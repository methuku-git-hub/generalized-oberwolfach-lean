module

public import Oberwolfach.MarkedVortexTerminalDecompositionGeometry

@[expose] public section
/-! The first and terminal vortex sets meet the constructed reservoir's
protection and size requirements under the original regular-host bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_reservoir_geometry
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β ε ρ₀ εabs εv:ℝ)
    (Q:Vortex U P D β ε vsize)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hρ₀:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hε:0≤ε) (hεabs:ε≤εabs) (hεv:ε≤εv)
    (tK fK:ℕ) (htK:2*vsize≤tK) (hfK:2*vsize≤fK):
    let A:=Finset.univ\Q.extendedVertices 1
    let Z:=Q.extendedVertices 1
    let Wterm:=Q.extendedVertices Q.length
    let W:=Wterm
    let Bterm:=Q.extendedIndices Q.length
    let B:=Q.extendedIndices 1;
    (ρ₀/4)*Fintype.card V≤(Fintype.card U:ℝ) ∧ Fintype.card U≤Fintype.card V ∧
    A=Finset.univ\Z ∧ (Z.card:ℝ)≤εabs*Fintype.card V ∧
    Wterm.card+Bterm.card≤tK ∧ Wterm⊆W ∧ Bterm⊆B ∧ W.card≤fK ∧
    (B.card:ℝ)≤εabs*Fintype.card V+fK ∧
    (Z.card:ℝ)≤εv*Fintype.card V ∧ (B.card:ℝ)≤εv*Fintype.card V+fK :=by
  intro A Z Wterm W Bterm B
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hL:Q.length-1+1=Q.length:=by have h:=Q.length_pos;omega
  obtain ⟨hterm,hV,hU⟩:=marked_vortex_terminal_decomposition_geometry P D vsize β ε εabs Q (Q.length-1) (2*vsize) 0
    hL hreg hn hD hρhi hε hεabs (le_refl _)
  obtain ⟨_,hVv,hUv⟩:=marked_vortex_terminal_decomposition_geometry P D vsize β ε εv Q (Q.length-1) (2*vsize) 0
    hL hreg hn hD hρhi hε hεv (le_refl _)
  have hterm':Wterm.card+Bterm.card≤2*vsize:=by simpa only [Wterm,Bterm,hL] using hterm
  have hV':(Z.card:ℝ)≤εabs*Fintype.card V:=by simpa only [Z,hL,Nat.cast_zero,add_zero] using hV
  have hU':(B.card:ℝ)≤εabs*Fintype.card V:=by simpa only [B,hL,Nat.cast_zero,add_zero] using hU
  have hVv':(Z.card:ℝ)≤εv*Fintype.card V:=by simpa only [Z,hL,Nat.cast_zero,add_zero] using hVv
  have hUv':(B.card:ℝ)≤εv*Fintype.card V:=by simpa only [B,hL,Nat.cast_zero,add_zero] using hUv
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*Fintype.card U:=by dsimp [initialIndexDensity];field_simp
  obtain ⟨v⟩:=Fintype.card_pos_iff.mp hn
  have hDhi:(D:ℝ)≤Fintype.card V:=by
    have hh:=P.degree_lt_card_verts v
    rw [hreg v] at hh
    exact_mod_cast hh.le
  have hUn:Fintype.card U≤Fintype.card V:=by
    have hh:=mul_le_mul_of_nonneg_right hρhi hDreal.le
    have hUreal:(Fintype.card U:ℝ)≤Fintype.card V:=by nlinarith
    exact_mod_cast hUreal
  have hUlo:(ρ₀/4)*Fintype.card V≤(Fintype.card U:ℝ):=by
    have ha:=mul_le_mul hρlo hDlo (by positivity : (0:ℝ)≤(Fintype.card V:ℝ)/2) (hρ₀.le.trans hρlo)
    nlinarith only [ha,hsize]
  refine ⟨hUlo,hUn,rfl,hV',hterm'.trans htK,Finset.Subset.rfl,?_,?_,?_,hVv',?_⟩
  · exact Q.extendedIndices_subset (by have h:=Q.length_pos;omega)
  · have hh:Wterm.card≤2*vsize:=by omega
    exact hh.trans hfK
  · have hf:(0:ℝ)≤fK:=by positivity
    linarith
  · have hf:(0:ℝ)≤fK:=by positivity
    linarith
end Oberwolfach
