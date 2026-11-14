import ComparacionFinitaDelPerfil
import CorteSublinealYSimplificacion
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel
noncomputable section
open Classical

theorem del_coste_a_la_entropia (n q : ℕ) (hn : 2≤n) (qn : q≤2*n-1)
    (u : E2.ColorWeights ℝ≥0) (base : Fin 4→Indice n→ℝ) (A l J s Er Ev Es : ℝ)
    (real : (q:ℝ)*(Real.log (Wreal n u)-(Real.log n+Real.log q+l))≤Er)
    (virtual : (↑(2*n-1-q):ℝ)*(Real.log (Wvirtual n u)-4*Real.log (2*n-1-q:ℕ))≤Ev)
    (pesos : (n:ℝ)*J-(∑ i,∑ j,Real.log (base i j))≤Es)
    (euler : (n:ℝ)*s=(q:ℝ)*(l-3)-(n:ℝ)*J) :
    cotaKL n q hn u A base ≤ q*Real.log n+n*s-Real.log (count n q)+restoRango n hn A+Er+Ev+Es := by
  let H := 2*n-1-q
  have N : (↑(2*n-1):ℝ) = (q:ℝ)+(H:ℝ) := by
    exact_mod_cast (by dsimp only [H]; omega : 2*n-1=q+H)
  have hr := log_factorial_inferior q
  have hv := log_factorial_inferior H
  change (H:ℝ)*(Real.log (Wvirtual n u)-4*Real.log H)≤Ev at virtual
  change (q:ℝ)*Real.log (Wreal n u)+(H:ℝ)*Real.log (Wvirtual n u)-4*(↑(2*n-1):ℝ)+restoRango n hn A-
    (∑ i,∑ j,Real.log (base i j))-Real.log (count n q)-Real.log q.factorial-4*Real.log H.factorial ≤ _
  rw [N,euler]
  linarith only [real,virtual,pesos,hr,hv]

theorem coste_frente_al_tablero_lleno (n h : ℕ) (hn : 2≤n) (lim : 2*h≤n) (nQ : 0<count n n)
    (u : E2.ColorWeights ℝ≥0) (base : Fin 4→Indice n→ℝ) (A l J s s₁ Er Ev Es Eb : ℝ)
    (real : (↑(n-h):ℝ)*(Real.log (Wreal n u)-(Real.log n+Real.log (n-h:ℕ)+l))≤Er)
    (virtual : (↑(2*n-1-(n-h)):ℝ)*(Real.log (Wvirtual n u)-4*Real.log (2*n-1-(n-h):ℕ))≤Ev)
    (pesos : (n:ℝ)*J-(∑ i,∑ j,Real.log (base i j))≤Es)
    (euler : (n:ℝ)*s=(↑(n-h):ℝ)*(l-3)-(n:ℝ)*J)
    (borde : (n:ℝ)*(s-s₁)≤2*h*Real.log n+Eb) :
    cotaKL n (n-h) hn u A base ≤ n*Real.log n+n*s₁-Real.log (count n n)+
      restoRango n hn A+Er+Ev+Es+Eb+h*Real.log 2+2*Real.log h.factorial := by
  have first := del_coste_a_la_entropia n (n-h) hn (by omega) u base A l J s Er Ev Es real virtual pesos euler
  have second := Capas.cancelacion_de_borde n h (by omega) lim nQ s s₁ Eb borde
  linarith only [first,second]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.coste_frente_al_tablero_lleno
