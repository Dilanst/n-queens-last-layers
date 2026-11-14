import EnvolventeTemporalDelProcesoGuiado
namespace ArticuloA.Historias
open scoped BigOperators
noncomputable section
open Classical

private theorem producto_temporal {α : Type} (s : Finset α) (u : α→ℝ)
    (pos : ∀ i∈s,0≤u i) (top : ∀ i∈s,u i≤1) :
    1-∑ i∈s,u i≤∏ i∈s,(1-u i) ∧
    (1+∑ i∈s,u i)*(∏ i∈s,(1-u i))≤1 := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert a s na ih=>
    have p:=pos a (Finset.mem_insert_self _ _)
    have h:=top a (Finset.mem_insert_self _ _)
    have ps (i) (hi : i∈s):=pos i (Finset.mem_insert_of_mem hi)
    have ts (i) (hi : i∈s):=top i (Finset.mem_insert_of_mem hi)
    obtain ⟨lo,up⟩:=ih ps ts
    have sn : 0≤∑ i∈s,u i:=Finset.sum_nonneg ps
    have pn : 0≤∏ i∈s,(1-u i):=Finset.prod_nonneg (fun i hi=>sub_nonneg.mpr (ts i hi))
    have step:=mul_le_mul_of_nonneg_left lo (sub_nonneg.mpr h)
    have shrink : (1+(u a+∑ i∈s,u i))*(1-u a)≤1+∑ i∈s,u i:=by
      nlinarith [sq_nonneg (u a),mul_nonneg p sn]
    rw [Finset.sum_insert na,Finset.prod_insert na]
    constructor
    · nlinarith [mul_nonneg p sn]
    · rw [←mul_assoc]
      exact (mul_le_mul_of_nonneg_right shrink pn).trans up

theorem multiplicador_temporal_hasta_cuatro {α : Type} (s : Finset α) (u : α→ℝ)
    {κ : ℝ} (kn : 0≤κ) (ks : κ≤1/16) (sz : s.card≤4)
    (lo : ∀ i∈s,0≤u i) (hi : ∀ i∈s,u i≤κ) :
    let U:=∑ i∈s,u i
    let Γ:=(∏ i∈s,(1-u i))⁻¹
    1+U≤Γ ∧ Γ≤2 ∧ Γ-(1+U)≤32*κ^2 := by
  dsimp only
  let U:=∑ i∈s,u i
  let P:=∏ i∈s,(1-u i)
  have un : 0≤U:=Finset.sum_nonneg lo
  have u4 : U≤4*κ:=by
    calc U≤∑ _i∈s,κ:=Finset.sum_le_sum hi
         _ = (s.card:ℝ)*κ:=by simp
         _ ≤ 4*κ:=mul_le_mul_of_nonneg_right (by exact_mod_cast sz) kn
  obtain ⟨lb,ub⟩:=producto_temporal s u lo (fun i m=>(hi i m).trans (by linarith))
  change 1-U≤P at lb
  change (1+U)*P≤1 at ub
  have pp : 0<P:=by linarith
  have i1 : 1+U≤1/P:=(le_div_iff₀ pp).mpr ub
  have i2 : 1/P≤1/(1-U):=one_div_le_one_div_of_le (by linarith) lb
  have p2 : 1/(1-U)≤2:=(div_le_iff₀ (by linarith : 0<1-U)).mpr (by linarith)
  have u2 : U^2≤16*κ^2:=by nlinarith [mul_nonneg (sub_nonneg.mpr u4) (show 0≤4*κ+U by linarith)]
  have k2 : 0≤32*κ^2:=by positivity
  have tail : 1/(1-U)≤1+U+32*κ^2:=by
    apply (div_le_iff₀ (by linarith : 0<1-U)).mpr
    nlinarith [mul_nonneg k2 (show 0≤1/2-U by linarith)]
  change 1+U≤P⁻¹ ∧ P⁻¹≤2 ∧ P⁻¹-(1+U)≤32*κ^2
  rw [←one_div]
  exact ⟨i1,i2.trans p2,by linarith⟩

theorem resto_de_deriva_de_una_casilla {Γ U T p κ : ℝ}
    (kn : 0≤κ) (ks : κ≤1/16) (un : 0≤U) (u4 : U≤4*κ)
    (tn : 0≤T) (t4 : T≤4*κ) (pn : 0≤p)
    (g0 : 1+U≤Γ) (g2 : Γ≤2) (gr : Γ-(1+U)≤32*κ^2) :
    |Γ*(1-T+3*p)-1-(U-T)|≤100*κ^2+6*p := by
  have ku : 32*κ^2≤2*κ:=by nlinarith [mul_nonneg kn (show 0≤1/16-κ by linarith)]
  have pr : 0≤T*(Γ-1):=mul_nonneg tn (by linarith)
  have top : T*(Γ-1)≤(4*κ)*(6*κ):=
    mul_le_mul t4 (by linarith) (by linarith) (by positivity)
  have qp : 0≤p*Γ:=mul_nonneg pn (by linarith)
  have qt:=mul_le_mul_of_nonneg_left g2 pn
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg κ]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.multiplicador_temporal_hasta_cuatro
#print axioms ArticuloA.Historias.resto_de_deriva_de_una_casilla
