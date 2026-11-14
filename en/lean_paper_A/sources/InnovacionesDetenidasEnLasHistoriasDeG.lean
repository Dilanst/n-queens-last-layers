import ColaDeInnovacionesConDependenciaDelPaso
import LeyCondicionalDeLaPiezaEnElTablero
namespace ArticuloA.Historias
open RealFinita Trayectoria Trayectoria.ProfileKernel Trayectoria.E2
open scoped BigOperators NNReal
noncomputable section
open Classical

def innovacionActiva {X : Type} (P : ℕ→X→Atoms ℝ≥0 X) (ok : ℕ→X→Prop) (Y : ℕ→X→X→ℝ)
    (t : ℕ) (x y : X) : ℝ := if ok t x then Y t x y-media (P t x) (Y t x) else 0

theorem innovacion_activa_centrada {X : Type} (P : ℕ→X→Atoms ℝ≥0 X) (ok : ℕ→X→Prop)
    (Y : ℕ→X→X→ℝ) (law : ∀ t x,total masas (P t x)=1) (t : ℕ) (x : X) :
    media (P t x) (innovacionActiva P ok Y t x)=0 := by
  change media (P t x) (fun y=>if ok t x then Y t x y-media (P t x) (Y t x) else 0)=0
  by_cases h : ok t x
  · simp only [innovacionActiva,if_pos h]
    have l:=media_affine (P t x) (Y t x) (-media (P t x) (Y t x)) 1
    rw [law] at l
    change media _ (fun y=> -media (P t x) (Y t x)+1*Y t x y)=1*(-media (P t x) (Y t x))+1*media (P t x) (Y t x) at l
    simp only [one_mul,neg_add_cancel] at l
    simpa only [sub_eq_add_neg,add_comm] using l
  · simp only [innovacionActiva,if_neg h]
    have l:=media_affine (P t x) (fun _=>0) 0 0
    simpa only [zero_mul,zero_add,mul_zero,add_zero] using l

theorem cola_bilateral_de_innovaciones_G {n} (v : Cell n→ℝ≥0) (q : ℕ)
    (ok : ℕ→EstadoGuiado n→Prop) (Y : ℕ→EstadoGuiado n→EstadoGuiado n→ℝ)
    {B θ : ℝ} (bp : 0≤B) (tp : 0≤θ) (small : θ*B≤1)
    (jump : ∀ t x,ok t x→∀ b∈pasoDeG v q t x,
        |Y t x b.2-media (pasoDeG v q t x) (Y t x)|≤B)
    (t m k : ℕ) (mk : m≤k) (x : EstadoGuiado n) (a : ℝ) :
    let D:=innovacionActiva (pasoDeG v q) ok Y
    (avg masas (rutas (pasoDeG v q) t k x) (mark masas (fun l=>a≤|sumarPasos D t x 0 (l.take m)|))).val≤
       2*Real.exp ((m:ℝ)*(θ*B)^2-θ*a) := by
  let P:=pasoDeG v q
  let D:=innovacionActiva P ok Y
  have law:=G_es_ley v q
  have zero : ∀ u y,media (P u y) (D u y)=0:=innovacion_activa_centrada P ok Y law
  have bound (u y) (j) (mem : j∈P u y) : |D u y j.2|≤B:=by
    by_cases yes : ok u y
    · simpa only [D,innovacionActiva,if_pos yes] using jump u y yes j mem
    · simpa only [D,innovacionActiva,if_neg yes,abs_zero] using bp
  have neg (u y) : media (P u y) (fun s=> -(D u y s))=0:=by
    have e:=media_affine (P u y) (D u y) 0 (-1)
    simpa only [zero_add,neg_one_mul,mul_zero,zero u y,neg_zero] using e
  have hi:=cola_superior_de_pasos P law D zero bound tp small t m k mk x a
  have lo:=cola_superior_de_pasos P law (fun u y b=> -(D u y b)) neg
    (fun u y j h=>by simpa only [abs_neg] using bound u y j h) tp small t m k mk x a
  let H:=rutas P t k x
  let val:=fun l : List (EstadoGuiado n)=>sumarPasos D t x 0 (l.take m)
  have reverse (l : List (EstadoGuiado n)) : sumarPasos (fun u y b=> -(D u y b)) t x 0 (l.take m)= -val l:=by
    simpa only [neg_zero,val] using cambiar_signo_de_la_suma D (l.take m) t x 0
  simp_rw [reverse] at lo
  have both : avg masas H (mark masas (fun l=>a≤|val l|)) ≤
      avg masas H (mark masas (fun l=>a≤val l))+avg masas H (mark masas (fun l=>a≤ -val l)):=by
    change _≤masas.add _ _
    rw [←avg_plus]
    apply avg_mono masas H
    intro j _
    by_cases positive : 0≤val j.2
    · rw [show (mark masas (fun l=>a≤|val l|)) j.2=(mark masas (fun l=>a≤val l)) j.2 by simp [mark,abs_of_nonneg positive]]
      exact le_add_of_nonneg_right (zero_le _)
    · rw [show (mark masas (fun l=>a≤|val l|)) j.2=(mark masas (fun l=>a≤ -val l)) j.2 by simp [mark,abs_of_neg (lt_of_not_ge positive)]]
      exact le_add_of_nonneg_left (zero_le _)
  have bR:=NNReal.coe_le_coe.mpr both
  change (avg masas H _).val≤(avg masas H _).val+(avg masas H _).val at bR
  exact bR.trans ((add_le_add hi lo).trans (le_of_eq (by ring)))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_bilateral_de_innovaciones_G
