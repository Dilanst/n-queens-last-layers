import RangoDelIncrementoYDeLaInnovacionDeG
import PesoTemporalDeTresOCuatroFamilias
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem peso_acotado_por_las_holguras {n q t} (v : Cell n→ℝ≥0) (s : Finset (Fin 4)) (e : Cell n)
    {η U : ℝ} (hp : 0<η) (hs : ∀ i∈s,η≤fraccionVivaG v q t e i)
    (cap : (v e:ℝ)≤U) :
    0≤pesoDeFamiliasG v q t e s ∧ pesoDeFamiliasG v q t e s≤U/η^s.card := by
  have low : η^s.card≤∏ i∈s,fraccionVivaG v q t e i:=by
    calc η^s.card=∏ _i∈s,η:=by simp
         _ ≤ _:=Finset.prod_le_prod (fun _ _=>hp.le) hs
  exact ⟨div_nonneg (NNReal.coe_nonneg _) ((pow_pos hp _).le.trans low),
    div_le_div₀ ((NNReal.coe_nonneg _).trans cap) cap (pow_pos hp _) low⟩

theorem ganancia_de_la_linea_con_holguras {n q t} (v : Cell n→ℝ≥0) (qp : 0<q)
    (l : List (Cell n)) (i : Fin 4) (z : Cell n) {κ : ℝ} (kn : 0≤κ) (ks : κ≤1/16)
    (pos : ∀ e j,0<fraccionVivaG v q t e j) (rates : ∀ e j,riesgoPrevisto v q t e j≤κ) :
    let s:=(Finset.univ : Finset (Fin 4)).erase i
    let a:=fun t' e=>pesoDeFamiliasG v q t' e s
    let d:=gananciaPorTiempo l (fibraFisicaG i z) (a t) (a (t+1))
    0≤d ∧ d≤(∑ e∈fibraFisicaG i z,masaVivaEn l (a t) e)*(6*κ) := by
  let s:=(Finset.univ : Finset (Fin 4)).erase i
  let a:=fun t' e=>pesoDeFamiliasG v q t' e s
  have cell (e : Cell n) : 0≤masaVivaEn l (a (t+1)) e-masaVivaEn l (a t) e ∧
      masaVivaEn l (a (t+1)) e-masaVivaEn l (a t) e≤masaVivaEn l (a t) e*(6*κ):=by
    by_cases live : ∀ d∈l,compatible e d
    · simp only [masaVivaEn,if_pos live,a]
      let u:=riesgoPrevisto v q t e
      have un (j) : 0≤u j:=div_nonneg (NNReal.coe_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pos e j).le)
      have size : s.card=3:=by simp [s,Finset.card_erase_of_mem]
      obtain ⟨lb,_,err⟩:=multiplicador_temporal_hasta_cuatro s u kn ks (by omega)
        (fun j _=>un j) (fun j _=>rates e j)
      have su:=Finset.sum_nonneg (s:=s) (fun j _=>un j)
      have upper : (∑ j∈s,u j)≤3*κ:=by
        calc _ ≤ ∑ _j∈s,κ:=Finset.sum_le_sum (fun j _=>rates e j)
             _ = _:=by simp [size]
      have kk : 32*κ^2≤2*κ:=by nlinarith [mul_nonneg kn (show 0≤1/16-κ by linarith)]
      have wn : 0≤pesoDeFamiliasG v q t e s:=div_nonneg (NNReal.coe_nonneg _) (Finset.prod_nonneg (fun j _=>(pos e j).le))
      rw [actualizacion_del_peso v qp t e s (fun j _=>pos e j)]
      let Γ:=(∏ j∈s,(1-u j))⁻¹
      change 0≤_*Γ-_ ∧ _*Γ-_≤_
      have gl : 1≤Γ:=by dsimp only [Γ]; linarith only [lb,su]
      have gh : Γ≤1+6*κ:=by dsimp only [Γ]; linarith only [err,upper,kk,kn]
      have p1:=mul_le_mul_of_nonneg_left gl wn
      have p2:=mul_le_mul_of_nonneg_left gh wn
      constructor <;> nlinarith only [p1,p2]
    · simp only [masaVivaEn,if_neg live,zero_mul,sub_self,le_refl,and_self]
  change 0≤(∑ e∈fibraFisicaG i z,_) ∧ (∑ e∈fibraFisicaG i z,_)≤(∑ e∈fibraFisicaG i z,_)*_
  rw [Finset.sum_mul]
  exact ⟨Finset.sum_nonneg (fun e _=>(cell e).1),Finset.sum_le_sum (fun e _=>(cell e).2)⟩

theorem salto_de_W_con_holgura {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) {η U : ℝ} (hp : 0<η) (up : 0≤U)
    (cap : ∀ e,(v e:ℝ)≤U) (hs : ∀ e i,η≤fraccionVivaG v q (t+1) e i)
    (f : Cell n→ℝ) {F : ℝ} (fn : ∀ e,0≤f e) (ft : ∀ e,f e≤F) (fp : 0≤F) (b : Cell n) :
    let a:=fun m e=>pesoDeFamiliasG v q m e Finset.univ*f e
    let Y:=deltaDeMasaEn l Finset.univ (a t) (a (t+1))
    |Y (some (b::l))-media (pasoDeG v q t (some l)) Y|≤4*n*(U/η^4*F) := by
  have bound (e) :=peso_acotado_por_las_holguras v Finset.univ e hp (fun j _=>hs e j) (cap e)
  apply salto_centrado_del_tablero v q t l reg
  · exact fun e=>mul_nonneg (bound e).1 (fn e)
  · intro e
    have h : pesoDeFamiliasG v q (t+1) e Finset.univ≤U/η^4:=by simpa using (bound e).2
    exact mul_le_mul h (ft e) (fn e) (by positivity)
  · positivity
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.salto_de_W_con_holgura
#print axioms ArticuloA.Historias.ganancia_de_la_linea_con_holguras
