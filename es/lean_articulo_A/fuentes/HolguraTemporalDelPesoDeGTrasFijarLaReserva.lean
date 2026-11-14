import SumaDeDosEtiquetadosDeLasMismasFibras
import UnaMismaReservaEnB1YEnElProcesoG
import NormalizacionFisicaDeLaReserva
namespace ArticuloA.Historias
open Repair Perfil Trayectoria Trayectoria.E2 Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem llave_de_la_fibra_en_G {n} (i : Fin 4) (z e : Cell n) :
    (llaveDeLinea i e=llaveDeLinea i z) ↔ enLaFibra (etiquetaDeCasilla z i) e := by
  have ec:=e.2.isLt
  have zc:=z.2.isLt
  fin_cases i <;> simp [llaveDeLinea,enLaFibra,etiquetaDeCasilla,etiquetaD,etiquetaA,Fin.ext_iff] <;> omega

theorem masa_de_linea_en_G_es_la_de_B1 {n} (v : Cell n→ℝ≥0) (i : Fin 4) (z : Cell n) :
    (masaDeLineaG v i z:ℝ)=masaBajo (fun e=>(v e:ℝ)) (enLaFibra (etiquetaDeCasilla z i)) := by
  unfold masaDeLineaG masaBajo
  rw [NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : llaveDeLinea i e=llaveDeLinea i z
  · simp [h,pesoCuando,(llave_de_la_fibra_en_G i z e).mp h]
  · simp [h,pesoCuando,mt (llave_de_la_fibra_en_G i z e).mpr h]

theorem el_peso_retenido_evita_ambas_marcas {n} (w : Cell n→ℝ) (b : ℝ)
    (u : LineaReservable n→Bool) (e : Cell n) (nz : b*pesoRetenido w u e≠0) :
    ¬oblicuaMarcada u etiquetaD 2 (llaveDeLinea 2 e) ∧ ¬oblicuaMarcada u etiquetaA 3 (llaveDeLinea 3 e) := by
  have keep : quedaTrasReserva u e:=by
    by_contra off; exact nz (by simp [pesoRetenido,off])
  obtain ⟨d,a⟩:=keep
  rw [(eval_de_las_dos_marcas u e).1,(eval_de_las_dos_marcas u e).2,d,a]
  decide

theorem margen_temporal_de_cada_denominador {n q t : ℕ} (qp : 0<q) (tq : t≤q)
    (v : Cell n→ℝ≥0) {η : ℝ} (hp : 0<η) (h1 : η≤1)
    (slack : ∀ j : FibraDeB1 n,masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)≤1-η)
    (i : Fin 4) (z : Cell n) :
    η≤1-(1-η)*((t:ℝ)/q) ∧
    1-(1-η)*((t:ℝ)/q)≤((1-(t:ℝ≥0)/q*masaDeLineaG v i z:ℝ≥0):ℝ) := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have rate : 0≤(t:ℝ)/q:=by positivity
  have endp : (t:ℝ)/q≤1:=(div_le_one qr).mpr (by exact_mod_cast tq)
  have load:=slack (etiquetaDeCasilla z i)
  rw [←masa_de_linea_en_G_es_la_de_B1] at load
  have incl:=mul_le_mul_of_nonneg_left load rate
  have bound:=mul_le_mul_of_nonneg_left endp (sub_nonneg.mpr h1)
  have one : (t:ℝ≥0)/q*masaDeLineaG v i z≤1:=by
    apply NNReal.coe_le_coe.mp
    push_cast
    linarith only [incl,bound,hp]
  rw [NNReal.coe_sub one]
  push_cast
  constructor <;> linarith only [incl,bound]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.margen_temporal_de_cada_denominador
#print axioms ArticuloA.Historias.el_peso_retenido_evita_ambas_marcas
