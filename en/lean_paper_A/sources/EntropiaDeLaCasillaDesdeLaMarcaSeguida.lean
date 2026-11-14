import CostoDelTruncamientoEnElTableroFisico
import SeguimientoDeLasMarcasEnLaMismaHistoria
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem media_de_la_marca_con_el_normalizador_real {I : Type} {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (f : I→Cell n→ℝ) (i : I) (reg : total masas (opcionesGuiadas v q t l)≠0)
    (pos : ∀ e j,0≤fraccionVivaG v q t e j) :
    (∑ e,leyDePieza v q t l e*f i e)=observacionFisica v q f (.inl i) t l/tableroG v q t l := by
  simp only [observacionFisica,pesoObservable,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  rw [probabilidad_de_pieza_como_cociente v q t l reg]
  by_cases live : ∀ b∈l,compatible e b
  · simp only [masaVivaEn,if_pos live,tableroG,cuatro_familias_dan_el_peso_de_G v q t e (pos e)]; ring
  · simp only [masaVivaEn,if_neg live,zero_div,zero_mul]

theorem transporte_superior_de_una_marca {W V s q E b : ℝ} (qp : 0<q)
    (half : q/2≤W) (sn : 0≤s) (sq : s≤q) (bw : |W-q|/q≤E) (bv : |V-s|/q≤b) :
    V/W≤s/q+2*(E+b) := by
  have wp : 0<W:=by linarith
  have er:=(abs_le.mp ((div_le_iff₀ qp).mp bw)).1
  have vb:=(abs_le.mp ((div_le_iff₀ qp).mp bv)).2
  have en : 0≤E:=(div_nonneg (abs_nonneg _) qp.le).trans bw
  have bn : 0≤b:=(div_nonneg (abs_nonneg _) qp.le).trans bv
  have wq : q-W≤E*q:=by linarith only [er]
  have avg : s/q≤1:=(div_le_one qp).mpr sq
  have diff : s/q*(q-W)≤E*q:=
    (mul_le_mul_of_nonneg_left wq (div_nonneg sn qp.le)).trans (mul_le_of_le_one_left (mul_nonneg en qp.le) avg)
  have corr:=mul_le_mul_of_nonneg_right half (add_nonneg en bn)
  apply (div_le_iff₀ wp).mpr
  have eq : s/q*q=s:=div_mul_cancel₀ _ qp.ne'
  rw [mul_sub,eq] at diff
  nlinarith only [diff,vb,corr]

theorem entropia_de_la_casilla_en_un_padre_seguido {I : Type} {n q t : ℕ} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (f : I→Cell n→ℝ) (i : I) {a L E b : ℝ} (ap : 0<a) (lp : 0≤L) (qp : 0<q)
    (mass : ∑ e,(v e:ℝ)=q) (sz : ∀ e,0≤f i e ∧ f i e≤1)
    (repr : ∀ e,marcaLogaritmica a (v e)=L*f i e)
    (reg : total masas (opcionesGuiadas v q t l)≠0) (pos : ∀ e j,0≤fraccionVivaG v q t e j)
    (half : (q:ℝ)/2≤tableroG v q t l) (bw : |tableroG v q t l-q|/q≤E)
    (bv : |observacionFisica v q f (.inl i) t l-(∑ e,(v e:ℝ)*f i e)|/q≤b) :
    log a-(∑ e,(v e:ℝ)*marcaLogaritmica a (v e))/q-2*L*(E+b)≤
        -(∑ e,leyDePieza v q t l e*log (v e:ℝ)) := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  let s:=∑ e,(v e:ℝ)*f i e
  have sn : 0≤s:=Finset.sum_nonneg (fun e _=>mul_nonneg (NNReal.coe_nonneg _) (sz e).1)
  have sq : s≤q:= (Finset.sum_le_sum (s:=Finset.univ) (fun e _=>mul_le_of_le_one_right (NNReal.coe_nonneg (v e)) (sz e).2)).trans_eq mass
  have bound:=transporte_superior_de_una_marca qr half sn sq bw bv
  rw [←media_de_la_marca_con_el_normalizador_real v l f i reg pos] at bound
  have norm:=ley_de_pieza_normalizada v q t l reg
  have support (e : Cell n) (zero : v e=0) : leyDePieza v q t l e=0:=by
    rw [probabilidad_de_pieza_como_cociente v q t l reg]
    by_cases live : ∀ b∈l,compatible e b <;> simp [masaVivaEn,live,pesoGuiado,zero]
  have clip:=entropia_de_celda_y_marca_truncada (leyDePieza v q t l) (fun e=>(v e:ℝ)) ap
    (ley_de_pieza_no_negativa v q t l) norm (fun e=>NNReal.coe_nonneg _) (fun e h=>support e (NNReal.coe_eq_zero.mp h))
  have scale (w : Cell n→ℝ) : (∑ e,w e*marcaLogaritmica a (v e))=L*∑ e,w e*f i e:=by
    simp_rw [repr]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
  rw [scale] at clip
  rw [scale]
  apply le_trans _ clip
  have scaled:=mul_le_mul_of_nonneg_left bound lp
  change L*(∑ e,leyDePieza v q t l e*f i e)≤L*(s/(q:ℝ)+2*(E+b)) at scaled
  change log a-L*s/(q:ℝ)-2*L*(E+b)≤_
  linarith only [scaled,mul_add L (s/(q:ℝ)) (2*(E+b)),mul_div_assoc L s (q:ℝ),mul_assoc 2 L (E+b),mul_left_comm L 2 (E+b)]
end
end ArticuloA.Historias

#print axioms ArticuloA.Historias.entropia_de_la_casilla_en_un_padre_seguido
