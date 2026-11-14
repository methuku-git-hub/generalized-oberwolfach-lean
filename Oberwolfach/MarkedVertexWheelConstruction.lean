module

public import Oberwolfach.MarkedAttachmentArcTypes
public import Oberwolfach.MarkedAttachmentHubConstruction
public import Oberwolfach.MarkedFixedAttachmentFamilies
public import Oberwolfach.MarkedRimIncidenceSpokes

@[expose] public section

/-! Construct the vertex wheels from actual rim/spoke cycles and the Hall
assignment. Their fixed endpoint arcs and root spokes are deduced from
those cycles; only their internal vertices require new host choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
  [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

theorem directed_incidence_total_card (src dst:A→V):
    Fintype.card (Σ v,DirectedIncidence src dst v)=2*Fintype.card A:=by
  rw [Fintype.card_congr (Equiv.sigmaSumDistrib (fun v=>{e:A // dst e=v}) (fun v=>{e:A // src e=v})),
    Fintype.card_sum,Fintype.card_congr (Equiv.sigmaFiberEquiv dst),Fintype.card_congr (Equiv.sigmaFiberEquiv src)]
  omega

theorem marked_vertex_wheel_construction
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l)
    (src dst:A→V) (row:S→V) (f:V→V) (jr:A→Bool) (js:S→Bool)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (hjin:∀ v e,js (a v e).val=markedIncidenceSpokeType jr (τ v (Sum.inl e)))
    (hjout:∀ v e,markedIncidenceSpokeType jr (τ v (Sum.inr e))=false)
    (pr:A→(Fin (l+2)↪V)) (ps:S→(Fin (l+3)↪V)) (hub:A→U)
    (RC RD:A→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (SC SD:S→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (hRC:∀ e i,(RC e).1.val i=Fin.cons (α:=fun _=>V) (src e) (Fin.cons (dst e) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hRD:∀ e i,(RD e).1.val i=Fin.cons (α:=fun _=>V) (f (src e)) (Fin.cons (f (dst e)) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hRCu:∀ e,(RC e).2.val=hub e) (hRDu:∀ e,(RD e).2.val=hub e)
    (hSC:∀ e i,(SC e).1.val i=rootedCycleOrder (markedRootOrder (l+3) (js e)) (row e) (ps e) i)
    (hSD:∀ e i,(SD e).1.val i=rootedCycleOrder (markedRootOrder (l+3) (js e)) (f (row e)) (ps e) i)
    (W Z P:Finset V) (hPZ:Disjoint P Z) (hPW:P⊆W)
    (hroots:∀ e,src e∈Z∧dst e∈Z∧f (src e)∈Z∧f (dst e)∈Z)
    (hrP:∀ e k,pr e k∈P) (hsP:∀ s k,ps s k∈P)
    (hPP:∀ x∈P,∀ y∈P,x≠y→¬PermutationClose π b x y)
    (hPZsep:∀ x∈P,∀ y∈Z,¬PermutationClose π b x y)
    (hpr:∀ e g,e≠g→Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (pr g)))
    (hps:∀ s t,s≠t→Disjoint (Finset.univ.image (ps s)) (Finset.univ.image (ps t)))
    (hrs:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s)))
    (hsp:∀ z:Σ v,DirectedIncidence src dst v,
      H₀ (markedAttachmentFirst (l+1) a d (fun e=>pr e) (fun s=>ps s) z) (hub (directedIncidenceEdge (τ z.1 z.2)))∧
      H₀ (markedAttachmentLast (l+1) a d (fun e=>pr e) (fun s=>ps s) z) (hub (directedIncidenceEdge (τ z.1 z.2))))
    (c:ℝ)
    (hstep:∀ u:U,∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun y=>
      (if t then ∃ e,ktail e=x∧khead e=y else ∃ e,tail e=x∧head e=y)∧
      (if t then HK y u else H₀ y u))).card:ℝ))
    (hjoin:∀ u:U,∀ x y,x≠y→c≤((Finset.univ.filter (fun q=>(∃ e,tail e=x∧head e=q)∧
      (∃ e,tail e=q∧head e=y)∧H₀ q u)).card:ℝ))
    (hbudget:W.card+(2*(Fintype.card A:ℝ)*(l+3)+Z.card+P.card+l+4)*(2*b+1)<c):
    let first:=markedAttachmentFirst (l+1) a d (fun e=>pr e) (fun s=>ps s)
    let last:=markedAttachmentLast (l+1) a d (fun e=>pr e) (fun s=>ps s)
    let jv:=fun z:Σ v,DirectedIncidence src dst v=>markedIncidenceSpokeType jr (τ z.1 z.2)
    ∃ pv:(Σ v,DirectedIncidence src dst v)→(Fin (l+3)↪V),
    ∃ VC VD:(Σ v,DirectedIncidence src dst v)→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ z,pv z 0=first z∧pv z (Fin.last (l+2))=last z∧
        (VC z).2.val=hub (directedIncidenceEdge (τ z.1 z.2))∧(VD z).2.val=hub (directedIncidenceEdge (τ z.1 z.2)))∧
      (∀ z k,(VC z).1.val k=rootedCycleOrder (markedRootOrder (l+3) (jv z)) z.1 (pv z) k)∧
      (∀ z k,(VD z).1.val k=rootedCycleOrder (markedRootOrder (l+3) (jv z)) (f z.1) (pv z) k)∧
      (∀ z k,pv z k∉Z∧∀ y∈Z,¬PermutationClose π b (pv z k) y)∧
      (∀ z k,pv z k∈W→pv z k∈({first z,last z}:Finset V))∧
      (∀ z k,pv z k∈P→pv z k∈({first z,last z}:Finset V))∧
      (∀ z,PermutationSeparated π b (pv z))∧
      (∀ z z',z≠z'→Disjoint (Finset.univ.image (pv z)) (Finset.univ.image (pv z')))∧
      (∀ z z' k k',pv z k≠pv z' k'→¬PermutationClose π b (pv z k) (pv z' k'))∧
      ∀ z k,∀ y∈P,pv z k≠y→¬PermutationClose π b (pv z k) y:=by
  dsimp only
  let first:=markedAttachmentFirst (l+1) a d (fun e=>pr e) (fun s=>ps s)
  let last:=markedAttachmentLast (l+1) a d (fun e=>pr e) (fun s=>ps s)
  let jv:=fun z:Σ v,DirectedIncidence src dst v=>markedIncidenceSpokeType jr (τ z.1 z.2)
  have hend:=marked_attachment_endpoints_injective (l+1) (by omega) a d pr ps hpr hps hrs
  have hP:=marked_actual_attachment_rows (l+1) src dst row a d pr ps P hrP hsP
  have hc:=marked_actual_attachment_arcs (l+1) (by omega) src dst row a d id jr js
    (fun e=>pr e) (fun s=>ps s) (fun e=>(RC e).1) (fun s=>(SC s).1)
    hRC hSC jv (fun v e=>(hjin v e).symm) hjout
  have hd:=marked_actual_attachment_arcs (l+1) (by omega) src dst row a d f jr js
    (fun e=>pr e) (fun s=>ps s) (fun e=>(RD e).1) (fun s=>(SD s).1)
    hRD hSD jv (fun v e=>(hjin v e).symm) hjout
  have hrc:=marked_assigned_incidence_spoke_types (l+1) (by omega) id jr
    (fun e=>pr e) hub RC hRC hRCu τ jv (fun _=>rfl)
  have hrd:=marked_assigned_incidence_spoke_types (l+1) (by omega) f jr
    (fun e=>pr e) hub RD hRD hRDu τ jv (fun _=>rfl)
  have hroot:∀ z:Σ v,DirectedIncidence src dst v,z.1∈Z∧f z.1∈Z:=by
    rintro ⟨v,z⟩
    cases z with
    | inl e=>simpa only [e.property] using And.intro (hroots e.val).2.1 (hroots e.val).2.2.2
    | inr e=>simpa only [e.property] using And.intro (hroots e.val).1 (hroots e.val).2.2.1
  have hrootsp:∀ z:Σ v,DirectedIncidence src dst v,
      if jv z then HK z.1 (hub (directedIncidenceEdge (τ z.1 z.2)))∧HK (f z.1) (hub (directedIncidenceEdge (τ z.1 z.2)))
      else H₀ z.1 (hub (directedIncidenceEdge (τ z.1 z.2)))∧H₀ (f z.1) (hub (directedIncidenceEdge (τ z.1 z.2))):=by
    intro z
    have h₁:=hrc z
    have h₂:=hrd z
    cases hj:jv z <;> simp only [hj,id_eq,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂ ⊢
    all_goals exact ⟨h₁,h₂⟩
  have hcl:∀ z:Σ v,DirectedIncidence src dst v,
      if jv z then (∃ e,ktail e=last z∧khead e=z.1)∧(∃ e,ktail e=last z∧khead e=f z.1)
      else (∃ e,tail e=last z∧head e=z.1)∧(∃ e,tail e=last z∧head e=f z.1):=by
    intro z
    have h₁:=(hc z).2
    have h₂:=(hd z).2
    cases hj:jv z <;> simp only [hj,id_eq,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂ ⊢
    all_goals exact ⟨h₁,h₂⟩
  have hbd:W.card+((Fintype.card (Σ v,DirectedIncidence src dst v):ℝ)*(l+3)+Z.card+P.card+l+4)*(2*b+1)<c:=by
    rw [directed_incidence_total_card]
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hbudget
  obtain ⟨pv,VC,VD,hends,hVC,hVD,hZ,hW,hsep,hdis,hcross,hPcross⟩:=marked_fixed_attachment_families
    tail head ktail khead H₀ HK π b l hl (fun z:Σ v,DirectedIncidence src dst v=>z.1)
    (fun z=>f z.1) first last (fun z=>hub (directedIncidenceEdge (τ z.1 z.2))) jv W Z P hPZ
    hroot (fun z=>(hP z).1) (fun z=>(hP z).2) (fun z=>hend.2.2 z z)
    (two_endpoint_sets_disjoint first last hend.1 hend.2.1 hend.2.2) hPP hPZsep hsp hrootsp
    (fun z=>⟨(hc z).1,(hd z).1⟩) hcl c (fun z=>hstep _) (fun z=>hjoin _) hbd
  exact ⟨pv,VC,VD,hends,hVC,hVD,hZ,hW,fun z k hk=>hW z k (hPW hk),hsep,hdis,hcross,hPcross⟩

end Oberwolfach
