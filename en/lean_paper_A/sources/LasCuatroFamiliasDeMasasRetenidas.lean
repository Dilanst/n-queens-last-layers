import OscilacionDelPesoDeUnaFibra
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators

abbrev FibraDeB1 (n : ℕ) := (Bool × Fin n) ⊕ LineaReservable n

def enLaFibra {n} (i : FibraDeB1 n) (e : Cell n) : Prop :=
  match i with
  | .inl (false,r) => e.1=r
  | .inl (true,c) => e.2=c
  | .inr (false,j) => etiquetaD e=(false,j)
  | .inr (true,j) => etiquetaA e=(true,j)

def bitsDeLaFibra {n} (i : FibraDeB1 n) (e : Cell n) : Finset (LineaReservable n) :=
  match i with
  | .inl _ => lineasPropias e
  | .inr (false,_) => {etiquetaA e}
  | .inr (true,_) => {etiquetaD e}

def pesoEnLaFibra {n} (w : Cell n→ℝ) (i : FibraDeB1 n) (e : Cell n) := pesoCuando (enLaFibra i e) (w e)
def masaAuxiliar {n} (w : Cell n→ℝ) (i : FibraDeB1 n) := retenidaPor (pesoEnLaFibra w i) (bitsDeLaFibra i)
def centroDeLaFibra {n} (τ : ℝ) (w : Cell n→ℝ) (i : FibraDeB1 n) :=
  (1-τ)^(match i with | .inl _=>2 | .inr _=>1) * masaBajo w (enLaFibra i)

theorem media_de_cada_fibra {n} (τ : ℝ) (w : Cell n→ℝ) (i : FibraDeB1 n) :
    mediaCubo τ (masaAuxiliar w i)=centroDeLaFibra τ w i := by
  unfold centroDeLaFibra masaAuxiliar masaBajo
  apply media_de_masa_retenida
  intro e
  rcases i with ⟨b,r⟩|⟨b,j⟩
  · exact son_dos_lineas_propias e
  · cases b <;> simp [bitsDeLaFibra]

theorem oscilacion_de_cada_fibra {n} (w : Cell n→ℝ) (B : ℝ) (bn : 0≤B)
    (cap : ∀ e,|w e|≤B) (i : FibraDeB1 n) : oscilacionPorBit (masaAuxiliar w i) B := by
  have cap' (e : Cell n) : |pesoEnLaFibra w i e|≤B := by
    unfold pesoEnLaFibra pesoCuando
    split <;> simp [cap,bn]
  have inside (e : Cell n) (p : pesoEnLaFibra w i e≠0) : enLaFibra i e := by
    by_contra h
    exact p (by simp [pesoEnLaFibra,pesoCuando,h])
  rcases i with ⟨b,r⟩|⟨b,j⟩
  · apply oscila_una_fila_o_columna _ B bn cap'
    intro e f he hf
    have a:=inside e he
    have b':=inside f hf
    cases b
    · exact Or.inl (a.trans b'.symm)
    · exact Or.inr (a.trans b'.symm)
  · cases b
    · apply oscila_una_oblicua_sin_su_bit _ B bn cap' true
      intro e f he hf
      exact (inside e he).trans (inside f hf).symm
    · apply oscila_una_oblicua_sin_su_bit _ B bn cap' false
      intro e f he hf
      exact (inside e he).trans (inside f hf).symm

theorem masa_efectiva_de_la_oblicua {n} (w : Cell n→ℝ) (j : LineaReservable n)
    (ω : LineaReservable n→Bool) :
    masaBajo (fun e=>if quedaTrasReserva ω e then w e else 0) (enLaFibra (.inr j)) =
    if ω j=false then masaAuxiliar w (.inr j) ω else 0 := by
  rcases j with ⟨b,j⟩
  cases b <;> cases keep : ω (_,j) <;>
    simp only [keep,Bool.false_eq_true,Bool.true_eq_false,if_true,if_false] <;>
    unfold masaBajo
  all_goals first | unfold masaAuxiliar retenidaPor | skip
  all_goals first | apply Finset.sum_congr rfl; intro e _ | apply Finset.sum_eq_zero; intro e _
  all_goals
    simp only [pesoEnLaFibra,pesoCuando,enLaFibra,bitsDeLaFibra,acuerdoDeReserva,
      Finset.not_mem_empty,IsEmpty.forall_iff,Finset.mem_singleton,quedaTrasReserva]
    split_ifs <;> simp_all

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_de_cada_fibra
#print axioms ArticuloA.Historias.oscilacion_de_cada_fibra
#print axioms ArticuloA.Historias.masa_efectiva_de_la_oblicua
