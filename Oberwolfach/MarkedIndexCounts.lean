module

public import Oberwolfach.RawMarkedPatternSampling

@[expose] public section

/-! Index counts for separated typed vertex labels on a fixed hub set.
The count includes each hub only once, and all labels are ambient vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedIndexResources (J : Finset (Bool×V)) (u : U) : Finset (MarkedResource V U) :=
  J.image (fun a=>Sum.inr (a.1,a.2,u))

def rawMarkedIndexCount (π : Equiv.Perm V) (d : ℕ) (B : Finset U)
    (J : Finset (Bool×V)) (g : Γ) (j : Color) (σ : RawMarkedOutcome V U Γ Color) : ℝ :=
  ∑ u∈B,if ∀ a∈J,rawMarkedPairSpokes π d σ g j a.1 a.2 u then 1 else 0

theorem markedIndexResources_mem (J : Finset (Bool×V)) (u : U) (a : Bool×V×U) :
    Sum.inr a∈markedIndexResources J u ↔ a.2.2=u ∧ (a.1,a.2.1)∈J := by
  constructor
  · intro ha
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp ha
    have he' := Sum.inr.inj he
    exact ⟨(congrArg (fun x : Bool×V×U=>x.2.2) he').symm,
      (congrArg (fun x : Bool×V×U=>(x.1,x.2.1)) he') ▸ hb⟩
  · intro ha
    refine Finset.mem_image.mpr ⟨(a.1,a.2.1),ha.2,?_⟩
    apply congrArg Sum.inr
    exact Prod.ext rfl (Prod.ext rfl ha.1.symm)

theorem markedIndexResources_load (J : Finset (Bool×V)) (B : Finset U) (e : MarkedResource V U) :
    (∑ u : B,if e∈markedIndexResources J u.val then (1:ℝ) else 0)≤1 := by
  rw [Finset.sum_coe_sort B (fun u : U=>if e∈markedIndexResources J u then (1:ℝ) else 0),← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  have hc : (B.filter (fun u=>e∈markedIndexResources J u)).card≤1 := by
    cases e with
    | inl e=>simp [markedIndexResources]
    | inr a=>
      have hsub : B.filter (fun u=>Sum.inr a∈markedIndexResources J u)⊆{a.2.2} := by
        intro u hu
        exact Finset.mem_singleton.mpr ((markedIndexResources_mem J u a).mp (Finset.mem_filter.mp hu).2).1.symm
      simpa using Finset.card_le_card hsub
  exact_mod_cast hc

theorem markedIndexResources_disjoint (π : Equiv.Perm V) (d : ℕ) (J : Finset (Bool×V))
    (hsep : ∀ a∈J,∀ b∈J,a≠b → ¬PermutationClose π (3*d) a.2 b.2)
    (u : U) (a b : MarkedResource V U)
    (ha : a∈markedIndexResources J u) (hb : b∈markedIndexResources J u) (hne : a≠b) :
    Disjoint (rawMarkedResourceCoordinates π d a) (rawMarkedResourceCoordinates π d b) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  apply rawMarkedResourceCoordinates_disjoint π d
  right
  exact hsep x hx y hy (by intro he;subst y;exact hne rfl)

theorem rawMarkedIndexCount_patterns (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (B : Finset U) (J : Finset (Bool×V)) (g : Γ) (j : Color) (σ : RawMarkedOutcome V U Γ Color) :
    rawMarkedIndexCount π d B J g j σ=
      rawMarkedPatternSum P π d (fun u : B=>markedIndexResources J u.val) (fun _=>1) g j σ := by
  unfold rawMarkedIndexCount rawMarkedPatternSum supportedPatternSum
  rw [Finset.sum_coe_sort B (fun u : U=>(1:ℝ)*patternValue (markedIndexResources J u)
    (fun _=>true) (typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [one_mul,patternValue_indicator]
  congr 1
  simp only [markedIndexResources,Finset.forall_mem_image,typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq]

theorem markedIndexResources_target (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color)
    (J : Finset (Bool×V)) (u : U) :
    (∏ e∈markedIndexResources J u,rawMarkedWheelMarginal P π d p k q s g j e)=
      ∏ a∈J,if a.1 then q u g else s u j := by
  unfold markedIndexResources
  rw [Finset.prod_image (by
    intro a ha b hb he
    have he' := Sum.inr.inj he
    exact Prod.ext (congrArg (fun e : Bool×V×U=>e.1) he')
      (congrArg (fun e : Bool×V×U=>e.2.1) he'))]
  rfl

theorem rawMarkedIndexCount_tail
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (B : Finset U) (hB : B.Nonempty) (J : Finset (Bool×V))
    (hsep : ∀ a∈J,∀ b∈J,a≠b → ¬PermutationClose π (3*d) a.2 b.2)
    (h : ℕ) (hsize : J.card≤h) (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|rawMarkedIndexCount π d B J g j σ-
        ∑ u∈B,∏ a∈J,if a.1 then q u g else s u j|)≤
      2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((h:ℝ)+1)*B.card))) := by
  have hh := rawMarkedPatternSum_tail P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    (fun u : B=>markedIndexResources J u.val) (fun _=>1) (by intro _;norm_num)
    (fun u a ha b hb hab=>markedIndexResources_disjoint π d J hsep u.val a b ha hb hab) g j
    1 ((h:ℝ)+1) B.card (by norm_num) (by positivity) (by exact_mod_cast hB.card_pos)
    (by
      intro u
      have hc := (Finset.card_image_le (s:=J) (f:=fun a=>Sum.inr (α:=(V×V)⊕(V×V)) (a.1,a.2,u.val))).trans hsize
      have hc' : ((markedIndexResources J u.val).card:ℝ)≤h := by exact_mod_cast hc
      linarith)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe];exact le_refl _)
    (fun e=>markedIndexResources_load J B e) t ht
  simp only [one_mul,markedIndexResources_target] at hh
  rw [Finset.sum_coe_sort B (fun u : U=>∏ a∈J,if a.1 then q u g else s u j)] at hh
  simpa only [rawMarkedIndexCount_patterns P] using hh

end Oberwolfach
