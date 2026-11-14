module

public import Oberwolfach.MarkedRestrictedNearBalancePacking
public import Oberwolfach.MarkedDeletedTermDegrees
public import Oberwolfach.MarkedReservedHostBalances
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! The earlier approximate packing is constructed in the actual complement
of the inner pair and sampled boundary. The sampling law is unchanged.
The deletion allowance precedes the reservation probability, while the
balance accuracy follows it and precedes separation and graph order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sampled_complement_approximation (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ β L bminus bplus ω h δ : ℝ,
    0<β → 1≤L → 0<bminus → 0<bplus → 0<ω → 0<h → 0<δ → δ<1/4 →
    ∃ ε η₀ δ₀ ξ τ₀:ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧ 0<ξ ∧ 0<τ₀ ∧ τ₀≤1/2 ∧
    ∀ (τ:ℝ),0<τ → τ≤τ₀ → ∃ θ:ℝ,0<θ ∧ ∀ (b q:ℕ),∃ n₀:ℕ,
    ∀ (V E K U : Type)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → 4*α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      4*(α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      4*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (k+2),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → 4*β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      4*β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η₀) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η₀) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    BipartiteLargeCut (occurrenceMultiplicity tail head) δ (2*h) →
    BipartiteLargeCut (occurrenceMultiplicity ktail khead) δ (2*h) →
    BipartiteLargeCut (relationMultiplicity H₀) δ (2*h) →
    BipartiteLargeCut (relationMultiplicity Hₖ) δ (2*h) →
    ∀ (X:Finset V) (Z:Finset U),( (ordinaryInnerVertices X Z).card:ℝ)≤ξ*Fintype.card V →
    let a:=fun r j=>((markedBalanceTermSet tail head ktail khead H₀ Hₖ r j).card:ℝ)
    let c:=fun r j=>(((markedBalanceTermSet tail head ktail khead H₀ Hₖ r j).filter (fun e=>
      (if markedActiveAuxTail tail ktail H₀ Hₖ e=r then markedActiveAuxHead head khead H₀ Hₖ e
        else markedActiveAuxTail tail ktail H₀ Hₖ e)∈ordinaryInnerVertices X Z)).card:ℝ);
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (k+1) (a (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) →
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (k+1) (c (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) →
    (∀ u,|markedSixDegreeBalance (k+1) (a (Sum.inr u)) 3|≤θ*Fintype.card V) →
    (∀ u,|markedSixDegreeBalance (k+1) (c (Sum.inr u)) 3|≤θ*Fintype.card V) →
    ∀ (hτ:0≤τ) (hτ1:τ≤1),
    1-2/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
      (fun σ=>
        let PE:=fun e:E=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e)
        let PK:=fun e:K=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e)
        let t':=fun e:{e//PE e}=>tail e.val
        let h':=fun e:{e//PE e}=>head e.val
        let kt':=fun e:{e//PK e}=>ktail e.val
        let kh':=fun e:{e//PK e}=>khead e.val
        let H₀':=fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u
        let Hₖ':=fun x u=>Hₖ x u∧¬markedBoundarySpokeAllowed X Z σ x u;
        ∃ M:Finset (MarkedWheel t' h' kt' kh' (k+1) π b H₀' Hₖ'),
          (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
          (∀ x:V⊕U,((markedIncidentEdges t' h' kt' kh' π H₀' Hₖ' false x \
            M.biUnion markedActiveResources).card:ℝ)≤τ^9*Fintype.card V) ∧
          (∀ x:V⊕U,((markedPhysicalIncidentEdges t' h' kt' kh' π H₀' Hₖ' x \
            M.biUnion markedWheelPhysicalResources).card:ℝ)≤τ^9*Fintype.card V)) := by
  obtain ⟨c₀,hc₀⟩:=marked_restricted_near_balance_packing α p₀ hα hαmax hp₀ hp₀max
  refine ⟨c₀,?_⟩
  intro k hk β L bminus bplus ω h δ hβ hL hbm hbp hω hh hδ hδsmall
  obtain ⟨ε,η₀,δ₀,s,hε,hη₀,hδ₀,hs,hpack⟩:=hc₀ k hk β L bminus bplus ω h δ hβ hL hbm hbp hω hh hδ hδsmall
  refine ⟨ε,η₀,δ₀,s/100,min (s/100) (1/2),hε,hη₀,hδ₀,by positivity,by positivity,min_le_right _ _,?_⟩
  intro τ hτpos hτsmall
  have hτs:τ≤s/100:=hτsmall.trans (min_le_left _ _)
  obtain ⟨ηbal,hηbal,hpack'⟩:=hpack (τ^9) (by positivity)
  let e:=min (s/100) (ηbal/(16*((k:ℝ)+5)))
  have he:0<e:=by dsimp only [e];positivity
  have hes:e≤s/100:=min_le_left _ _
  have hebal:((k:ℝ)+5)*e≤ηbal/16:=by
    have ht:=(le_div_iff₀ (by positivity:0<16*((k:ℝ)+5))).mp (min_le_right (s/100) (ηbal/(16*((k:ℝ)+5))))
    dsimp only [e]
    nlinarith only [ht]
  refine ⟨ηbal/8,by positivity,?_⟩
  intro b q
  obtain ⟨Np,hNp⟩:=hpack' b
  obtain ⟨Nd,hNd⟩:=marked_reservation_deleted_count_event e he q
  obtain ⟨Nb,hNb⟩:=marked_reserved_host_balance_event e he q
  refine ⟨max 1 (max Np (max Nd Nb)),?_⟩
  intro V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV ps qs δsp Dexc hdata hsmall i hipos
    hcommon hpaths ψ hRerr hSerr hψ hcut0 hcutK hcutH0 hcutHK X Z hsize a c ha hc hau hcu hτ hτ1
  let n:ℝ:=Fintype.card V
  let nn:ℝ:=Fintype.card (V⊕U)
  have hnpos:0<Fintype.card V:=by omega
  have hnreal:0<n:=by change 0<(Fintype.card V:ℝ);exact_mod_cast hnpos
  have hNN:nn≤2*n:=by
    dsimp only [nn,n]
    simp only [Fintype.card_sum,Nat.cast_add]
    have huR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast huV
    linarith
  have hNds:Nd≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  have hNbs:Nb≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  have hdEvent:=hNd V U E K hNds tail head ktail khead H₀ Hₖ π hphys X Z τ hτ hτ1
  have hbEvent:=hNb V U E K hNbs tail head ktail khead H₀ Hₖ π hphys X Z (k+1)
    ((ηbal/8)*Fintype.card V) ((ηbal/8)*Fintype.card V) (by positivity) (by positivity)
    (by convert ha using 1 <;> congr!) (by convert hc using 1 <;> congr!)
    (by convert hau using 1 <;> congr!) (by convert hcu using 1 <;> congr!) τ hτ hτ1
  let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin τ hτ hτ1)
  have hjoint {A B:(Sym2 (V⊕U)→Bool)→Prop}
      (hA:1-1/nn^q≤μ.probability A) (hB:1-1/nn^q≤μ.probability B):
      1-2/nn^q≤μ.probability (fun σ=>A σ∧B σ):=by
    have hj:=finiteLaw_good_intersection μ A B (1/nn^q) hB
    calc
      _ = 1-1/nn^q-1/nn^q:=by ring
      _ ≤ μ.probability A-1/nn^q:=sub_le_sub_right hA _
      _ ≤ _:=hj
  apply (hjoint hdEvent hbEvent).trans
  apply finiteLaw_probability_mono
  intro σ hσ PE PK t' h' kt' kh' H₀' Hₖ'
  obtain ⟨hrows,hcols⟩:=marked_deleted_term_degree_bounds tail head ktail khead H₀ Hₖ PE PK
    (fun x u=>¬markedBoundarySpokeAllowed X Z σ x u)
    ((e+4*τ)*nn+6*(ordinaryInnerVertices X Z).card) (by convert hσ.1 using 1 <;> congr!)
  have hloss:(e+4*τ)*nn+6*(ordinaryInnerVertices X Z).card≤s*n:=by
    have hcoef:e+4*τ≤s/100+4*(s/100):=by linarith
    have ht:=mul_le_mul hcoef hNN (by dsimp only [nn];positivity) (by positivity)
    change ((ordinaryInnerVertices X Z).card:ℝ)≤(s/100)*n at hsize
    nlinarith only [ht,hsize,mul_nonneg hs.le hnreal.le]
  have hbal:((ηbal/8)*n)+((ηbal/8)*n)+((k+1:ℕ)+4)*e*nn≤ηbal*n:=by
    have hcoef:(0:ℝ)≤((k:ℝ)+5)*e:=by positivity
    have ht:=mul_le_mul hebal hNN (by dsimp only [nn];positivity) (by positivity)
    push_cast
    nlinarith only [ht,mul_nonneg hηbal.le hnreal.le]
  have hresult:=hNp ηbal hηbal.le le_rfl V E K U tail head ktail khead π hphys p D hp hpmax
    (by omega) hDlo hDhi hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV
    ps qs δsp Dexc hdata hsmall i hipos hcommon hpaths ψ hRerr hSerr hψ
    hcut0 hcutK hcutH0 hcutHK PE PK H₀' Hₖ' (fun _ _ h=>h.1) (fun _ _ h=>h.1)
    (fun v=>⟨(hrows v).1.trans hloss,(hrows v).2.1.trans hloss,(hrows v).2.2.1.trans hloss,
      (hrows v).2.2.2.1.trans hloss,by convert (hrows v).2.2.2.2.1.trans hloss using 1 <;> congr!,by convert (hrows v).2.2.2.2.2.trans hloss using 1 <;> congr!⟩)
    (fun u=>⟨by convert (hcols u).1.trans hloss using 1 <;> congr!,by convert (hcols u).2.trans hloss using 1 <;> congr!⟩)
    (by intro v;convert (hσ.2.1 v).trans (by convert hbal using 1 <;> push_cast <;> ring) using 1 <;> congr!)
    (by intro v;convert (hσ.2.2.1 v).trans (by convert hbal using 1 <;> push_cast <;> ring) using 1 <;> congr!)
    (by intro v;convert (hσ.2.2.2.1 v).trans (by convert hbal using 1 <;> push_cast <;> ring) using 1 <;> congr!)
    (by intro u;convert (hσ.2.2.2.2 u).trans (by convert hbal using 1 <;> push_cast <;> ring) using 1 <;> push_cast <;> congr!)
  convert hresult using 1 <;> congr!
end Oberwolfach
