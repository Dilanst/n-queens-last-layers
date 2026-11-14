import ColaBilateralEnElMismoCamino
import PrimeraSalidaPorInnovaciones
open scoped NNReal BigOperators
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto Corte Trayectoria.E2 E2.Regular
noncomputable section
open Classical
abbrev Activa (n : ℕ) := (Fin 2 ⊕ Fin 4) ⊕ (Fin 4 × Fin (2*n-1))
def coordenada {n : ℕ} : Activa n→Coord
  | .inl (.inl i) => if i=0 then .realCount else .boardWeight
  | .inl (.inr f) => .family f
  | .inr (f,j) => .degree (f,j.val)
def pasoParado {n : ℕ} (w : ColorWeights ℝ≥0) (halt : ℕ→State n→Bool) :=
  stopped masas (kernel masas w (·⁻¹)) halt

private theorem cuota_pos (i j : ℕ) (ne : i+j≠0) : masas.add (ns masas i) (ns masas j)≠masas.zero := by
  change ns masas i+ns masas j≠0; rw [ns_real,ns_real,←Nat.cast_add]; exact_mod_cast ne

theorem parada_normalizada {n : ℕ} (w : ColorWeights ℝ≥0) (halt : ℕ→State n→Bool) (t : ℕ) (x : ℕ×State n) :
    total masas (pasoParado w halt t x)=1 :=
  stopped_total masas _ _ (kernel_total masas w _ (fun _ ne => inv_mul_cancel₀ ne) cuota_pos) _ _

def medidaCoord {n : ℕ} (v : Cell n→ℝ≥0) (w : ColorWeights ℝ≥0) (c : Coord) (_ : ℕ) (x : ℕ×State n) :=
  observed masas (·⁻¹) v w x.2 c

def ruidoE2 {n : ℕ} (v : Cell n→ℝ≥0) (w : ColorWeights ℝ≥0) (halt : ℕ→State n→Bool)
    (x : ℕ×State n) (c : Coord) (t : ℕ) (l : List (ℕ×State n)) :=
  saldo (leerLibro (pasoParado w halt) (medidaCoord v w c) (fun _ _ => 0) 0 (libroCero x) (l.take t))

theorem cola_fisica_en_prefijo {n : ℕ} (hn : n≠0) (v : Cell n→ℝ≥0) (w : ColorWeights ℝ≥0)
    (halt : ℕ→State n→Bool) (c : Coord) (M H : ℝ≥0) (cap : ∀ e,v e≤M)
    (line : ∀ t (x : State n),halt t x=false → ∀ f j,j<2*n-1 → x.active f j → w f j≤H)
    (x : ℕ×State n) (m T : ℕ) (time : m≤T) (θ g : ℝ) (np : 0≤θ)
    (small : θ*(2*(coordCap masas M H c).val)≤1) :
    (avg masas (rutas (pasoParado w halt) 0 T x)
      (mark masas (fun l => g≤|ruidoE2 v w halt x c m l|))).val ≤
      2*Real.exp (m*(θ*(2*(coordCap masas M H c).val))^2-θ*g) := by
  let S:=pasoParado w halt
  let K:=coordCap masas M H c
  have sn : ns masas n≠masas.zero := by rw [ns_real]; change (n:ℝ≥0)≠0; exact_mod_cast hn
  have jump (t : ℕ) (y : ℕ×State n) (i) (mem : i∈S t y) :=
    coord_stopped masas (·⁻¹) (fun _ ne => inv_mul_cancel₀ ne) cuota_pos sn v w halt t y.1 y.2
      M H cap (line y.1 y.2) c i mem
  have same : ((K+K:ℝ≥0):ℝ)=2*K.val := by simp [two_mul]
  have b := cola_de_prefijo S (medidaCoord v w c) (fun _ _ => 0) (parada_normalizada w halt)
    (K+K) (fun _ => True) (by simp) (fun t y _ i mem => by
      have z : avg masas (S t y) (fun _ => (0:ℝ≥0))=0 := by rw [avg_constant]; exact mul_zero _
      simpa only [medidaCoord,z,add_zero,zero_add] using jump t y i mem)
    0 m T time x trivial θ g np (by simpa only [same] using small)
  simpa only [same,K,ruidoE2,S] using b
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.cola_fisica_en_prefijo
