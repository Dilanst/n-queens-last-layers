import CambioDeUnaLineaEnLaReserva
import CotaDelFalloGeometricoEnElProcesoG
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators

def oblicuaMarcada {n} (ω : LineaReservable n→Bool) (tag : Cell n→LineaReservable n)
    (i : Fin 4) (j : ℤ) : Prop:=∃ e,llaveDeLinea i e=j ∧ ω (tag e)=true

theorem eval_de_las_dos_marcas {n} (ω : LineaReservable n→Bool) (e : Cell n) :
    (oblicuaMarcada ω etiquetaD 2 (llaveDeLinea 2 e) ↔ ω (etiquetaD e)=true) ∧
    (oblicuaMarcada ω etiquetaA 3 (llaveDeLinea 3 e) ↔ ω (etiquetaA e)=true) := by
  constructor <;> constructor
  · rintro ⟨f,h,a⟩
    have eq : etiquetaD f=etiquetaD e:=by
      have u:=f.2.isLt; have v:=e.2.isLt
      simp [llaveDeLinea] at h
      simp [etiquetaD,Fin.ext_iff]; omega
    simpa [eq] using a
  · exact fun h=>⟨e,rfl,h⟩
  · rintro ⟨f,h,a⟩
    have eq : etiquetaA f=etiquetaA e:=by
      simp [llaveDeLinea] at h
      simp [etiquetaA,Fin.ext_iff]; omega
    simpa [eq] using a
  · exact fun h=>⟨e,rfl,h⟩

def quedaTrasReserva {n} (ω : LineaReservable n→Bool) (e : Cell n) : Prop :=
  ω (etiquetaD e)=false ∧ ω (etiquetaA e)=false

theorem las_marcas_de_B1_son_las_de_G {n} (ω : LineaReservable n→Bool) (z e : Cell n) :
    acuerdoDeReserva (lineasSolicitadas z e) (lineasPropias e) ω ↔
    marcasDeG (oblicuaMarcada ω etiquetaD 2) (oblicuaMarcada ω etiquetaA 3) z e ∧ quedaTrasReserva ω e := by
  simp [acuerdoDeReserva,lineasSolicitadas,lineasPropias,marcasDeG,quedaTrasReserva,
    Finset.forall_mem_union,(eval_de_las_dos_marcas ω _).1,(eval_de_las_dos_marcas ω _).2]
  tauto

theorem masa_tras_normalizar_la_reserva {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e)
    (factor : ℝ) (crece : 1≤factor) (ω : LineaReservable n→Bool) (z : Cell n) :
    masaMarcadaB1 w z ω ≤ masaBajo
      (fun e=>if quedaTrasReserva ω e then factor*w e else 0)
      (marcasDeG (oblicuaMarcada ω etiquetaD 2) (oblicuaMarcada ω etiquetaA 3) z) := by
  apply Finset.sum_le_sum
  intro e _
  rw [las_marcas_de_B1_son_las_de_G]
  unfold pesoCuando
  by_cases h : marcasDeG (oblicuaMarcada ω etiquetaD 2) (oblicuaMarcada ω etiquetaA 3) z e <;>
    by_cases s : quedaTrasReserva ω e <;> simp [h,s]
  exact (one_mul (w e)).symm.le.trans (mul_le_mul_of_nonneg_right crece (pos e))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.las_marcas_de_B1_son_las_de_G
#print axioms ArticuloA.Historias.masa_tras_normalizar_la_reserva
