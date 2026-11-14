module

public import Oberwolfach.MarkedProtectedInnerCorrection
public import Oberwolfach.MarkedInducedCorrectionRemainder
public import Oberwolfach.MarkedFiniteInnerAvoidance
public import Oberwolfach.FiniteImageIncidenceBound

@[expose] public section

/-! Actual sparse correction in the ambient host's induced inner pair.
The four near-balance and cut hypotheses are imposed on that fixed pair;
the correction is constructed there and lifted with exact occurrence,
spoke-type, degree and protected-pair identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_induced_inner_correction (q : ℕ) (hq : 1≤q) (ω h δ ξ : ℝ)
    (hω : 0<ω) (hh : 0<h) (hδ : 0<δ) (hδsmall : δ<1/4) (hξ : 0<ξ)
    (hξh : ((q:ℝ)+1)*ξ≤h/100) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ η : ℝ,0≤η → η≤η₀ →
    ∀ (V U E K:Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],
    ∀ (tail head:E→V) (ktail khead:K→V),
      Function.Injective (fun e=>(tail e,head e))→Function.Injective (fun e=>(ktail e,khead e))→
    ∀ (H₀ HK:V→U→Prop),(∀ v u,¬(H₀ v u∧HK v u))→
    ∀ (π:Equiv.Perm V) (I T:Finset V) (J W:Finset U),T⊆I→W⊆J→
      (∀ v,π v∈I↔v∈I)→(∀ v,π v∈T↔v∈T)→
      n₀≤I.card→ω*I.card≤J.card→J.card≤I.card→
      (T.card:ℝ)≤h*I.card→(W.card:ℝ)≤h*J.card→
    let EI:={e:E // tail e∈I∧head e∈I}
    let KI:={e:K // ktail e∈I∧khead e∈I}
    let tI:=fun e:EI=>(⟨tail e.val,e.property.1⟩:I)
    let hI':=fun e:EI=>(⟨head e.val,e.property.2⟩:I)
    let ktI:=fun e:KI=>(⟨ktail e.val,e.property.1⟩:I)
    let khI:=fun e:KI=>(⟨khead e.val,e.property.2⟩:I)
    let H0I:=fun v:I=>fun u:J=>H₀ v.val u.val
    let HKI:=fun v:I=>fun u:J=>HK v.val u.val;
      (∀ v,|occurrenceDegree (Sum.elim tI ktI) v-
        (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤η*I.card)→
      (∀ v,|occurrenceDegree (Sum.elim hI' khI) v-
        (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤η*I.card)→
      (∀ v,|occurrenceDegree khI v-(∑ u,if HKI v u then (1:ℝ) else 0)|≤η*I.card)→
      (∀ u,|(∑ v,if H0I v u then (1:ℝ) else 0)-(q:ℝ)*(∑ v,if HKI v u then (1:ℝ) else 0)|≤η*I.card)→
      BipartiteLargeCut (occurrenceMultiplicity tI hI') δ (2*h)→
      BipartiteLargeCut (occurrenceMultiplicity ktI khI) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity H0I) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity HKI) δ (2*h)→
    let S:=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)
    ∃ (DA:Finset (E⊕K)) (DS:Finset (V×U)),
      (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I) ∧
      (∀ z∈DS,z.1∈I∧z.2∈J∧z∈S) ∧
      (∀ v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤
        8*((q:ℝ)+1)*ξ*I.card) ∧
      (∀ v,((DS.filter (fun z=>v=z.1)).card:ℝ)≤4*((q:ℝ)+1)*ξ*I.card) ∧
      (∀ u,((DS.filter (fun z=>z.2=u)).card:ℝ)≤4*((q:ℝ)+1)*ξ*I.card) ∧
      (DA.card:ℝ)≤8*((q:ℝ)+1)*ξ*(I.card:ℝ)^2 ∧
      (DS.card:ℝ)≤4*((q:ℝ)+1)*ξ*(I.card:ℝ)^2 ∧
      MarkedRemainderDivisible tail head ktail khead HK
        ((Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA)
        ((S.filter (fun z=>z.1∈I∧z.2∈J))\DS) q ∧
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedInnerResource T W)=∅ :=by
  obtain ⟨η₀,hη₀,N,hN⟩:=marked_protected_inner_correction q hq ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,N,?_⟩
  intro η hη hηsmall V U E K _ _ _ _ _ _ tail head ktail khead hinj hkinj H₀ HK hH
    π I T J W hTI hWJ hI hT hn hωn hJI hTsize hWsize EI KI tI hI' ktI khI H0I HKI
    hbp hbm hbk hbw hc0 hcK hcs0 hcsK S
  let ρ:Equiv.Perm I:=π.subtypePerm hI
  let TI:=Finset.univ.filter (fun v:I=>v.val∈T)
  let WJ:=Finset.univ.filter (fun u:J=>u.val∈W)
  have hTIcard:TI.card=T.card:=by
    have himg:TI.image Subtype.val=T:=by
      ext x
      simp only [TI,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨y,hy,rfl⟩;exact hy
      · intro hx;exact ⟨⟨x,hTI hx⟩,hx,rfl⟩
    rw [←himg,Finset.card_image_of_injective _ Subtype.val_injective]
  have hWJcard:WJ.card=W.card:=by
    have himg:WJ.image Subtype.val=W:=by
      ext x
      simp only [WJ,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨y,hy,rfl⟩;exact hy
      · intro hx;exact ⟨⟨x,hWJ hx⟩,hx,rfl⟩
    rw [←himg,Finset.card_image_of_injective _ Subtype.val_injective]
  have hρ:∀ x:I,ρ x∈TI↔x∈TI:=by
    intro x
    simp only [TI,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hT x.val
  have hi:Function.Injective (fun e:EI=>(tI e,hI' e)):=by
    intro a b hab
    exact Subtype.ext (hinj (Prod.ext (congrArg Subtype.val (congrArg Prod.fst hab))
      (congrArg Subtype.val (congrArg Prod.snd hab))))
  have hki:Function.Injective (fun e:KI=>(ktI e,khI e)):=by
    intro a b hab
    exact Subtype.ext (hkinj (Prod.ext (congrArg Subtype.val (congrArg Prod.fst hab))
      (congrArg Subtype.val (congrArg Prod.snd hab))))
  obtain ⟨DA,DS,hsub,hdeg,hrow,hcol,hcardA,hcardS,hdiv,havoid⟩:=hN η hη hηsmall I J EI KI
    (by simpa only [Fintype.card_coe] using hn) (by simpa only [Fintype.card_coe] using hωn)
    (by simpa only [Fintype.card_coe] using hJI) tI hI' ktI khI hi hki H0I HKI
    (fun v u=>hH v.val u.val) ρ TI WJ hρ
    (by simpa only [hTIcard,Fintype.card_coe] using hTsize)
    (by simpa only [hWJcard,Fintype.card_coe] using hWsize)
    (by simpa only [Fintype.card_coe] using hbp) (by simpa only [Fintype.card_coe] using hbm)
    (by simpa only [Fintype.card_coe] using hbk) (by simpa only [Fintype.card_coe] using hbw)
    hc0 hcK hcs0 hcsK
  simp only [Fintype.card_coe] at hdeg hrow hcol hcardA hcardS
  let f:EI⊕KI↪E⊕K:=⟨Sum.map Subtype.val Subtype.val,Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩⟩
  let g:I×J↪V×U:=⟨Prod.map Subtype.val Subtype.val,by
    intro a b hab
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hab)) (Subtype.ext (congrArg Prod.snd hab))⟩
  let i:I↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let j:J↪U:=⟨Subtype.val,Subtype.val_injective⟩
  have ht:∀ a∈DA,Sum.elim tail ktail (f a)=i (Sum.elim tI ktI a):=by intro a _;cases a <;> rfl
  have hd:∀ a∈DA,Sum.elim head khead (f a)=i (Sum.elim hI' khI a):=by intro a _;cases a <;> rfl
  refine ⟨DA.image f,DS.image g,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a ha
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp ha
    cases a with
    | inl a=>exact a.property
    | inr a=>exact a.property
  · intro z hz
    obtain ⟨pair,hpair,heq⟩:=Finset.mem_image.mp hz
    subst z
    refine ⟨pair.1.property,pair.2.property,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hsub hpair)).2⟩
  · exact finite_image_incidence_bound DA f i (Sum.elim tI ktI) (Sum.elim hI' khI)
      (Sum.elim tail ktail) (Sum.elim head khead) ht hd _ (by positivity) hdeg
  · exact finite_image_fibre_bound DS g i Prod.fst Prod.fst (fun _ _=>rfl) _ (by positivity) hrow
  · have hh':=finite_image_fibre_bound DS g j Prod.snd Prod.snd (fun _ _=>rfl) (4*((q:ℝ)+1)*ξ*I.card) (by positivity)
      (fun u=>by simpa only [eq_comm] using hcol u)
    simpa only [eq_comm] using hh'
  · rw [Finset.card_image_of_injective _ f.injective];exact hcardA
  · rw [Finset.card_image_of_injective _ g.injective];exact hcardS
  · exact marked_induced_correction_remainder tail head ktail khead H₀ HK I J q DA DS (by convert hdiv using 1 <;> congr!)
  · obtain ⟨ha,hs⟩:=(marked_finite_inner_empty_iff tI hI' ktI khI ρ DA DS TI WJ hρ).mp havoid
    apply (marked_finite_inner_empty_iff tail head ktail khead π (DA.image f) (DS.image g) T W hT).mpr
    constructor
    · intro a ha' hab
      obtain ⟨a0,ha0,heq⟩:=Finset.mem_image.mp ha'
      subst a
      apply ha a0 ha0
      have hab':i (Sum.elim tI ktI a0)∈T∧i (Sum.elim hI' khI a0)∈T:=by
        rw [←ht a0 ha0,←hd a0 ha0];exact hab
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab'.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab'.2⟩⟩
    · intro z hz hab
      obtain ⟨pair,hpair,heq⟩:=Finset.mem_image.mp hz
      subst z
      exact hs pair hpair ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab.2⟩⟩

end Oberwolfach
