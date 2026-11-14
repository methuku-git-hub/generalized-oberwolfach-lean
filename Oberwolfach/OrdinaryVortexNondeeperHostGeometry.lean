module

public import Oberwolfach.VortexApplications
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! The deterministic nondeeper host used after a root cover inherits the
regular host's degree margin and the exact rim/spoke mean relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_nondeeper_host_geometry
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β ε ρ₀ θ α:ℝ) (Q:Vortex U P D β ε vsize)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hDlo:(Fintype.card V:ℝ)/2≤D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤3*α/20) (hε:0<ε) (hε1:ε≤1/4)
    (hv:0<vsize) (hθ:1/2≤θ) (hα:0<α) (hdegree:(θ+α)*Fintype.card V≤D)
    (i:ℕ) (hi:i+2≤Q.length):
    let A:=Q.vertices i\Q.vertices (i+2)
    let B:=Q.indices i\Q.indices (i+2)
    let ρ:=initialIndexDensity U D
    let Dlocal:=2*(B.card:ℝ)/ρ;
    (∀x:A,(θ+α/2)*Fintype.card A≤((P.induce (A:Set V)).degree x:ℝ)) ∧
    (∀x:A,|((P.induce (A:Set V)).degree x:ℝ)-Dlocal|≤(5/3:ℝ)*β*Fintype.card A) ∧
    (Fintype.card A:ℝ)/2≤Dlocal ∧ (ρ₀/4)*Fintype.card A≤(Fintype.card B:ℝ) ∧
    Fintype.card B≤Fintype.card A ∧
    ∀pR pH:ℝ,pR=ρ*pH→pR*Dlocal=2*Fintype.card B*pH :=by
  intro A B ρ Dlocal
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hnreal:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hvreal:0<(vsize:ℝ):=by exact_mod_cast hv
  have hterminal:0<(Q.vertices Q.length).card:=by
    have hh:0<ε*(vsize:ℝ)/2:=by positivity
    exact_mod_cast (hh.trans_le Q.terminal_lower)
  have hparentSub:Q.vertices Q.length⊆Q.vertices i:=
    finset_chain_subset Q.vertices Q.length Q.nested (by omega) (le_refl _)
  obtain ⟨x₀,hx₀⟩:=Finset.card_pos.mp hterminal
  have hx₀':x₀∈Q.vertices i:=hparentSub hx₀
  have hdiff:=Q.difference_degree_estimates hreg hn hρ hβ hε.le hε1 (show i < i+2 by omega) hi x₀ (by simpa using hx₀')
  have hcentre:|Dlocal-((D:ℝ)/Fintype.card V)*A.card|≤(5/3:ℝ)*β*A.card:=by
    dsimp only [A,B,ρ,Dlocal]
    convert hdiff.1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hDrel:θ+α≤(D:ℝ)/Fintype.card V:=(le_div_iff₀ hnreal).2 (by simpa [mul_comm] using hdegree)
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  obtain ⟨v₀⟩:=(inferInstance : Nonempty V)
  have hDhi:(D:ℝ)≤Fintype.card V:=by
    have hh:=P.degree_lt_card_verts v₀
    rw [hreg v₀] at hh
    exact_mod_cast hh.le
  have hDrelhi:(D:ℝ)/Fintype.card V≤1:=(div_le_one hnreal).2 hDhi
  have hAnon:(0:ℝ)≤A.card:=by positivity
  have hlow:Dlocal≥(1/2:ℝ)*A.card:=by
    have hh:=mul_le_mul_of_nonneg_right hDrel hAnon
    have hc:=(abs_le.mp hcentre).1
    have hb:=mul_le_mul_of_nonneg_right hβα hAnon
    nlinarith only [hh,hc,hb,hθ,hα]
  have hupper:Dlocal≤(1+(5/3:ℝ)*β)*A.card:=by
    have hh:=mul_le_mul_of_nonneg_right hDrelhi hAnon
    have hc:=(abs_le.mp hcentre).2
    nlinarith only [hh,hc]
  have hratio:ρ*Dlocal=2*(B.card:ℝ):=by dsimp [Dlocal];field_simp [hρ.ne']
  have hUlo:(ρ₀/4)*(A.card:ℝ)≤B.card:=by
    have h1:=mul_le_mul hρlo hlow (by positivity : (0:ℝ)≤(1/2:ℝ)*A.card) hρ.le
    nlinarith only [h1,hratio]
  have hUhi:B.card≤A.card:=by
    have h1:=mul_le_mul_of_nonneg_right hρhi (show 0≤Dlocal by positivity)
    have hbA:=mul_le_mul_of_nonneg_right hβ1 hAnon
    have hc:(B.card:ℝ)≤A.card:=by nlinarith only [h1,hratio,hupper,hbA,hAnon]
    exact_mod_cast hc
  have hdeg (x:A):((P.induce (A:Set V)).degree x)=(P.neighborFinset x.val∩A).card:=by
    have hmap:((P.induce (A:Set V)).neighborFinset x).map
        (Function.Embedding.subtype (· ∈ (A:Set V))) = P.neighborFinset x.val ∩ A := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
      change (∃ a, ∃ b:a∈A, P.Adj x.val a ∧ a=y) ↔ P.Adj x.val y ∧ y∈A
      constructor
      · rintro ⟨a,ha,hxy,rfl⟩
        exact ⟨hxy,ha⟩
      · rintro ⟨hxy,hy⟩
        exact ⟨y,hy,hxy,rfl⟩
    have hh:=congrArg Finset.card hmap
    simp only [Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x
    have hx:x.val∈Q.vertices i:=(Finset.mem_sdiff.mp x.property).1
    have hd:=Q.difference_degree_estimates hreg hn hρ hβ hε.le hε1 (show i < i+2 by omega) hi x.val (by simpa using hx)
    have hlocal:|((P.induce (A:Set V)).degree x:ℝ)-Dlocal|≤(5/3:ℝ)*β*A.card:=by
      rw [hdeg x]
      dsimp only [A,B,ρ,Dlocal]
      convert hd.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    have hc:=(abs_le.mp hcentre).1
    have hlocal':=(abs_le.mp hlocal).1
    have hh:=mul_le_mul_of_nonneg_right hDrel hAnon
    have hb:=mul_le_mul_of_nonneg_right hβα hAnon
    simp only [Fintype.card_coe]
    nlinarith only [hc,hlocal',hh,hb]
  · intro x
    have hx:x.val∈Q.vertices i:=(Finset.mem_sdiff.mp x.property).1
    have hd:=Q.difference_degree_estimates hreg hn hρ hβ hε.le hε1 (show i < i+2 by omega) hi x.val (by simpa using hx)
    have hlocal:|((P.induce (A:Set V)).degree x:ℝ)-Dlocal|≤(5/3:ℝ)*β*A.card:=by
      rw [hdeg x]
      dsimp only [A,B,ρ,Dlocal]
      convert hd.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    simpa only [Fintype.card_coe] using hlocal
  · simp only [Fintype.card_coe]
    nlinarith only [hlow]
  · simpa only [Fintype.card_coe] using hUlo
  · simpa only [Fintype.card_coe] using hUhi
  · intro pR pH hp
    rw [hp]
    simp only [Fintype.card_coe]
    calc
      ρ*pH*Dlocal=(ρ*Dlocal)*pH:=by ring
      _=2*(B.card:ℝ)*pH:=by rw [hratio]
end Oberwolfach
