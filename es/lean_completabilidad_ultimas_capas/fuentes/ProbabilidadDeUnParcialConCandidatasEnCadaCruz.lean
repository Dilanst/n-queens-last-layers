import ProbabilidadDeLosPrefijosRegularesDeB2
import CotaDelFalloGeometricoEnElProcesoG
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem fallo_descompuesto_en_dos_eventos {X : Type} (xs : Atoms ℝ≥0 X) (V O : X→Prop) :
    (avg masas xs (mark masas (fun x=>¬(V x ∧ O x)))).val=
    (avg masas xs (mark masas (fun x=>¬V x))).val+(avg masas xs (mark masas (fun x=>V x ∧ ¬O x))).val := by
  rw [←media_coe,←media_coe,←media_coe]
  induction xs with
  | nil=>simp [media]
  | cons i xs ih=>
    by_cases v : V i.2 <;> by_cases o : O i.2 <;> simp [media,v,o,mark,masas] at ih ⊢ <;> linarith only [ih]

def falloDelParcialReservado {n} (v : Cell n→ℝ≥0) (q m : ℕ) (D A : ℤ→Prop) (d : ℝ≥0) : ℝ :=
  (avg masas (rutas (pasoDeG v q) 0 q (some [])) (mark masas (fun l=>
      ¬(prefijoRegular (condicionDeSeguimientoG v q (marcasDeG D A) d) 0 (some []) l ∧ salidaFisicaDeG m D A l)))).val

theorem fallo_total_del_parcial {n m q} (v : Cell n→ℝ≥0) (D A : ℤ→Prop) (d : ℝ≥0) (a : ℝ)
    (sum : q+m=n) (evita : ∀ e,v e≠0→¬D (llaveDeLinea 2 e) ∧ ¬A (llaveDeLinea 3 e))
    (prob : (3/4:ℝ≥0)*d≤1) (markSize : ((9*m+2:ℕ):ℝ)≤(((3/4:ℝ≥0)*d):ℝ)*q/3)
    (b2 : cotaDeSalidaDeB2 v q (marcasDeG D A) d a) :
    falloDelParcialReservado v q m D A d≤
      (Fintype.card (IndiceDeSeguimiento n (Option (Cell n))):ℝ)*(q+1)*(2*exp (-(a^2)))+
      (n:ℝ)^2*exp (-(((3/4:ℝ≥0)*d):ℝ)*q/6) := by
  unfold falloDelParcialReservado
  rw [fallo_descompuesto_en_dos_eventos]
  exact add_le_add b2 (fallo_geometrico_en_origenes_regulares v D A d sum evita prob markSize)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.fallo_total_del_parcial
