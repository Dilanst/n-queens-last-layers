import MasaAgregadaEnElSoporteDeLasHistorias
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped BigOperators NNReal
noncomputable section
open Classical

private theorem expandir_una_media {X I : Type} [Fintype I] (xs : Atoms ℝ≥0 X)
    (tab : I→X) (inj : Function.Injective tab) (all : ∀ v∈xs,∃ i,tab i=v.2) (f : X→ℝ) :
    media xs f=∑ i,masaAgregada xs (tab i)*f (tab i) := by
  induction xs with
  | nil=>change (0:ℝ)=∑ i,(0:ℝ)*f (tab i); simp
  | cons v rest ih=>
    obtain ⟨i,hi⟩:=all v List.mem_cons_self
    have step (j : I) : masaAgregada (v::rest) (tab j)=
        (if i=j then (v.1:ℝ) else 0)+masaAgregada rest (tab j) := by
      change ((v.1*mark masas (fun y=>y=tab j) v.2+avg masas rest _:ℝ≥0):ℝ)=_
      rw [←hi]
      by_cases eq : i=j
      · simp [eq,mark,masas,masaAgregada]
      · have different : tab i ≠ tab j:=fun h=>eq (inj h)
        simp [eq,different,mark,masas,masaAgregada]
    have sumrest:=ih (fun a ha=>all a (List.mem_cons_of_mem v ha))
    simp_rw [step,add_mul]
    rw [Finset.sum_add_distrib,←sumrest,media]
    simp [←hi,ite_mul]

def leyDePieza {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n)) (b : Cell n) : ℝ :=
  masaAgregada (pasoDeG v q t (some l)) (some (b::l))

theorem media_del_paso_fisico {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (pos : total masas (opcionesGuiadas v q t l)≠0) (f : EstadoGuiado n→ℝ) :
    media (pasoDeG v q t (some l)) f=∑ b,leyDePieza v q t l b*f (some (b::l)) := by
  apply expandir_una_media _ (fun b=>some (b::l))
  · intro i j eq; simpa using eq
  · intro a ha
    obtain ⟨e,eq,_,_⟩:=origen_regular_agrega_casilla v q t l pos a.1 a.2 ha
    exact ⟨e,eq.symm⟩

theorem ley_de_pieza_normalizada {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (pos : total masas (opcionesGuiadas v q t l)≠0) : ∑ b,leyDePieza v q t l b=1 := by
  have eq:=media_del_paso_fisico v q t l pos (fun _=>1)
  simp only [mul_one] at eq
  rw [←eq]
  change media _ (fun _=>(↑(1:ℝ≥0):ℝ))=1
  rw [media_coe]
  change (total masas (pasoDeG v q t (some l))).val=1
  rw [G_es_ley]; rfl

theorem ley_de_pieza_no_negativa {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n)) (b : Cell n) :
    0≤leyDePieza v q t l b := NNReal.coe_nonneg _
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_del_paso_fisico
#print axioms ArticuloA.Historias.ley_de_pieza_normalizada
