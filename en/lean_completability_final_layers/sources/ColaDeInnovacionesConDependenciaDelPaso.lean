import PrefijosDeUnaMismaTrayectoria
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel Trayectoria.Adjunto
open scoped NNReal
noncomputable section
open Classical
variable {X : Type}

def sumarPasos (D : ℕ→X→X→ℝ) (t : ℕ) (x : X) (z : ℝ) : List X→ℝ
  | []=>z
  | y::l=>sumarPasos D (t+1) y (z+D t x y) l

def pasoConSuma (P : ℕ→X→Atoms ℝ≥0 X) (D : ℕ→X→X→ℝ) (t : ℕ) (x : X×ℝ) : Atoms ℝ≥0 (X×ℝ) :=
  (P t x.1).map (fun a=>(a.1,(a.2,x.2+D t x.1 a.2)))

theorem proyectar_suma_del_prefijo (P : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ t x,total masas (P t x)=1)
    (D : ℕ→X→X→ℝ) (t m k : ℕ) (mk : m≤k) (x : X) (z : ℝ) (f : ℝ→ℝ≥0) :
    avg masas (rutas P t k x) (fun l=>f (sumarPasos D t x z (l.take m)))=
      avg masas (leaves masas (pasoConSuma P D) t m (x,z)) (fun y=>f y.2) := by
  induction m generalizing t k x z with
  | zero=>
    simp only [List.take_zero,sumarPasos,leaves,avg_point]
    rw [avg_constant,masa_de_rutas P norm]; exact one_mul _
  | succ m ih=>
    cases k with
    | zero=>omega
    | succ k=>
      rw [rutas,leaves,avg_bind,avg_bind,pasoConSuma,avg_push masas (P t x) (fun y=>(y,z+D t x y))]
      apply congrArg (avg masas (P t x))
      funext y
      rw [avg_push]
      exact ih (t+1) k (by omega) y (z+D t x y)

theorem cola_superior_de_pasos (P : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ t x,total masas (P t x)=1)
    (D : ℕ→X→X→ℝ) (cent : ∀ t x,media (P t x) (D t x)=0)
    {B θ : ℝ} (jump : ∀ t x a,a∈P t x→|D t x a.2|≤B)
    (tp : 0≤θ) (small : θ*B≤1) (t m k : ℕ) (mk : m≤k) (x : X) (a : ℝ) :
    (avg masas (rutas P t k x) (mark masas (fun l=>a≤sumarPasos D t x 0 (l.take m)))).val≤
      Real.exp ((m:ℝ)*(θ*B)^2-θ*a) := by
  let row:=pasoConSuma P D
  have law (u) (s : X×ℝ) : total masas (row u s)=1:=by
    change avg masas ((P u s.1).map (fun b=>(b.1,(b.2,s.2+D u s.1 b.2)))) _=1
    rw [avg_push masas (P u s.1) (fun y=>(y,s.2+D u s.1 y))]; exact norm _ _
  have zero (u) (s : X×ℝ) : media (row u s) (fun y=>y.2-s.2)=0:=by
    change media ((P u s.1).map (fun b=>(b.1,(b.2,s.2+D u s.1 b.2)))) (fun y=>y.2-s.2)=0
    rw [media_map (P u s.1) (fun y=>(y,s.2+D u s.1 y))]
    simpa only [add_sub_cancel_left] using cent u s.1
  have cap (u) (s : X×ℝ) (b) (hb : b∈row u s) : |b.2.2-s.2|≤B:=by
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hb
    simpa using jump u s.1 c hc
  have tail:=Momento.cola realExp row (fun _ y=>y.2) law zero θ B tp small cap t m (x,0) a
  change (avg masas (rutas P t k x) (fun l=>mark masas (fun z : ℝ=>a≤z) (sumarPasos D t x 0 (l.take m)))).val≤_
  rw [proyectar_suma_del_prefijo P norm D t m k mk]
  simpa only [realExp,mul_zero,add_zero] using tail

theorem cambiar_signo_de_la_suma (D : ℕ→X→X→ℝ) (l : List X) (t : ℕ) (x : X) (z : ℝ) :
    sumarPasos (fun u b y=> -(D u b y)) t x (-z) l= -(sumarPasos D t x z l) := by
  induction l generalizing t x z with
  | nil=>rfl
  | cons y l ih=>simp only [sumarPasos,←neg_add]; exact ih (t+1) y _
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.cola_superior_de_pasos
