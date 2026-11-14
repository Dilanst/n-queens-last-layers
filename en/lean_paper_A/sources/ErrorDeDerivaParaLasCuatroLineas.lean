import MediaDelCambioDeMasaEnElPasoReal
import PesoTemporalDeTresOCuatroFamilias
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped BigOperators NNReal
noncomputable section
open Classical

theorem resto_multiplicativo_de_G {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (e : Cell n)
    (s : Finset (Fin 4)) (p : Cell n→ℝ) {κ : ℝ} (kn : 0≤κ) (ks : κ≤1/16)
    (pos : ∀ i,0<fraccionVivaG v q t e i)
    (uref : ∀ i,riesgoPrevisto v q t e i≤κ) (load : ∀ i,riesgoDeLinea p e i≤κ)
    (prob : ∀ c,0≤p c) :
    let U:=∑ i∈s,riesgoPrevisto v q t e i
    let T:=∑ i,riesgoDeLinea p e i
    let a:=pesoDeFamiliasG v q t e s
    |pesoDeFamiliasG v q (t+1) e s*(1-T+3*p e)-a-a*(U-T)|≤a*(100*κ^2+6*p e) := by
  let u:=riesgoPrevisto v q t e
  let a:=pesoDeFamiliasG v q t e s
  let Γ:=(∏ i∈s,(1-u i))⁻¹
  let U:=∑ i∈s,u i
  let T:=∑ i,riesgoDeLinea p e i
  have un (i) : 0≤u i:=div_nonneg (NNReal.coe_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pos i).le)
  have sz : s.card≤4:=by simpa using Finset.card_le_univ s
  obtain ⟨g0,g2,gr⟩:=multiplicador_temporal_hasta_cuatro s u kn ks sz (fun i _=>un i) (fun i _=>uref i)
  have u4 : U≤4*κ:=by
    calc U≤∑ _i∈s,κ:=Finset.sum_le_sum (fun i _=>uref i)
         _ = (s.card:ℝ)*κ:=by simp
         _ ≤ 4*κ:=mul_le_mul_of_nonneg_right (by exact_mod_cast sz) kn
  have rn (i) : 0≤riesgoDeLinea p e i:=Finset.sum_nonneg (fun b _=>by split <;> simp [prob])
  have t4 : T≤4*κ:=by
    calc T≤∑ _i : Fin 4,κ:=Finset.sum_le_sum (fun i _=>load i)
         _ = 4*κ:=by simp
  have r:=resto_de_deriva_de_una_casilla kn ks (Finset.sum_nonneg (fun i _=>un i)) u4
    (Finset.sum_nonneg (fun i _=>rn i)) t4 (prob e) g0 g2 gr
  have non : 0≤a:=div_nonneg (NNReal.coe_nonneg _) (Finset.prod_nonneg (fun i _=>(pos i).le))
  rw [actualizacion_del_peso v qp t e s (fun i _=>pos i)]
  change |a*Γ*(1-T+3*p e)-a-a*(U-T)|≤_
  calc _ = |a*(Γ*(1-T+3*p e)-1-(U-T))|:=by congr 1; ring
       _ = a*|Γ*(1-T+3*p e)-1-(U-T)|:=by rw [abs_mul,abs_of_nonneg non]
       _ ≤ _:=mul_le_mul_of_nonneg_left r non

theorem deriva_y_error_del_observable {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (f : Cell n→ℝ) (fn : ∀ e,0≤f e)
    {κ pmax : ℝ} (kn : 0≤κ) (ks : κ≤1/16)
    (pos : ∀ e i,0<fraccionVivaG v q t e i)
    (uref : ∀ e i,riesgoPrevisto v q t e i≤κ)
    (load : ∀ e i,riesgoDeLinea (leyDePieza v q t l) e i≤κ)
    (top : ∀ e,leyDePieza v q t l e≤pmax) :
    let p:=leyDePieza v q t l
    let a:=fun s e=>pesoDeFamiliasG v q s e Finset.univ*f e
    let V:=pesoObservable (a t) (some l)
    |media (pasoDeG v q t (some l)) (fun y=>pesoObservable (a (t+1)) y-V)-
      ∑ e,masaVivaEn l (a t) e*((∑ i,riesgoPrevisto v q t e i)-(∑ i,riesgoDeLinea p e i))|
      ≤V*(100*κ^2+6*pmax) := by
  let p:=leyDePieza v q t l
  let a:=fun s e=>pesoDeFamiliasG v q s e Finset.univ*f e
  dsimp only
  rw [deriva_fisica_de_masa_disponible v q t l reg,←Finset.sum_sub_distrib]
  change |∑ e,(_-_ - _)|≤(∑ e,masaVivaEn l (a t) e)*_
  rw [Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  by_cases live : ∀ d∈l,compatible e d
  · simp only [masaVivaEn,if_pos live]
    have bound:=resto_multiplicativo_de_G v qp e Finset.univ p kn ks (pos e) (uref e) (load e)
      (ley_de_pieza_no_negativa v q t l)
    let w:=pesoDeFamiliasG v q t e Finset.univ
    have wn : 0≤w:=div_nonneg (NNReal.coe_nonneg _) (Finset.prod_nonneg (fun i _=>(pos e i).le))
    have rel:=mul_le_mul_of_nonneg_right bound (fn e)
    change |(_*f e)*_-(w*f e)-(w*f e)*_|≤(w*f e)*_
    rw [show (pesoDeFamiliasG v q (t+1) e Finset.univ*f e)*(1-(∑ i,riesgoDeLinea p e i)+3*p e)-
         w*f e-w*f e*((∑ i,riesgoPrevisto v q t e i)-(∑ i,riesgoDeLinea p e i))=
       (pesoDeFamiliasG v q (t+1) e Finset.univ*(1-(∑ i,riesgoDeLinea p e i)+3*p e)-w-
         w*((∑ i,riesgoPrevisto v q t e i)-(∑ i,riesgoDeLinea p e i)))*f e by ring,
       abs_mul,abs_of_nonneg (fn e)]
    apply rel.trans
    have h:=mul_le_mul_of_nonneg_left (show 100*κ^2+6*p e≤100*κ^2+6*pmax by linarith [top e]) (mul_nonneg wn (fn e))
    change w*_ *f e≤_
    linarith only [h] 
  · simp only [masaVivaEn,if_neg live,zero_mul,sub_self,abs_zero,le_refl]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_y_error_del_observable
