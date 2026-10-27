import EthCor.ConnFormula
import EthCor.HamIsoTM

/-! # Connected solutions with the checks of a seed

The seeds of `EthCor.Iso` act on the n vertex bits. To the formula `connF n E ψ` on 3n variables we
add a variable z = 3n set to false, the checks of ω as the chains of `EthCor.HamI.isoF` (variables
3n + 1 + i), and for every chain bit its complement (`compF`). A chain bit and its complement hold
one true bit, so the satisfying assignments with n + ℓ + mm·k true variables are those of `connF`
with n + ℓ true variables whose vertex set passes the checks (`cnt_ciF`). By
`EthCor.Conn.conn_parity_P` half their number has the parity of the number of connected solutions
of size ℓ that pass the checks (`ci_parity`). With the isolation lemma: no connected solution gives
parity 0 for every seed; one gives parity 1 for at least a 2^{−δn} fraction of the seeds
(`ci_decide`). -/

namespace EthCor.ConnI

open Groundwork.Prog CountKSat GraphProblems Finset EthCor.Ham EthCor.HamS EthCor.HamI EthCor.HamITM EthCor.Iso
  EthCor.Conn

/-! ### The formula -/

/-- The bits B + A + i are the complements of the bits B + i, i < A. -/
def compF (B A : ℕ) : Fml := (List.range A).flatMap fun i =>
  [[(B + i, true), (B + A + i, true)], [(B + i, false), (B + A + i, false)]]

/-- The formula of the vertex sets that satisfy ψ, induce a connected subgraph and pass the checks
of ω: on 3n + 1 + 2·mm·k variables. -/
def ciF {k t mm : ℕ} (n : ℕ) (E : List (ℕ × ℕ)) (ψ : Fml) (ω : Seed n k t mm) : Fml :=
  connF n E ψ ++ [[(n + n + n, false)]] ++ isoF (n + n + n) (n + n + n + 1) k ω.1.val (rowsOf ω) (fixesOf ω) ++
    compF (n + n + n + 1) (mm * k)

theorem sat_compF (f : ℕ → Bool) (B A : ℕ) :
    (∀ C ∈ compF B A, ∃ l ∈ C, f l.1 = l.2) ↔ ∀ i < A, f (B + A + i) = !f (B + i) := by
  rw [compF, forall_flatMap_range]
  refine forall₂_congr fun i _ => ?_
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, sat2]
  generalize f (B + i) = a, f (B + A + i) = b
  cases a <;> cases b <;> decide

theorem connF_vars {n : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) : ∀ C ∈ connF n E ψ, C.length ≤ max (C.length) 4 ∧ ∀ l ∈ C, l.1 < n + n + n := by
  intro D hD
  refine ⟨le_max_left _ _, ?_⟩
  simp only [connF, List.mem_append] at hD
  rcases hD with (hD | hD) | hD
  · exact fun l hl => by have := hψ D hD l hl; omega
  · rw [sideF] at hD
    obtain ⟨v, hv, hD⟩ := List.mem_flatMap.1 hD
    rw [List.mem_range] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl <;> intro l hl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;> simp <;> omega
  · rw [edgeCC] at hD
    obtain ⟨p, hp, hD⟩ := List.mem_flatMap.1 hD
    have := hE p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> intro l hl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl | rfl | rfl <;>
      simp <;> omega

/-! ### The count -/

theorem ext_natAdd' {N A : ℕ} (w : Fin (N + A) → Bool) {i : ℕ} (hi : i < A) :
    ext w (N + i) = w (Fin.natAdd N ⟨i, hi⟩) := by
  simp only [CountKSat.ext, dif_pos (show N + i < N + A by omega)]; rfl

theorem comp_iff {N A : ℕ} (w : Fin (N + A) → Bool) (h : Fin A → Bool) :
    (∀ i < A, ext h i = !ext w (N + i)) ↔ h = fun i => !w (Fin.natAdd N i) := by
  constructor
  · intro H
    funext i
    have := H i.val i.2
    rwa [ext_fin, ext_natAdd' w i.2] at this
  · rintro rfl i hi
    rw [ext_natAdd' w hi]
    simp only [CountKSat.ext, dif_pos hi]

theorem count_comp {N A : ℕ} (y : Fin N → Bool) (g : Fin A → Bool) :
    (univ.filter fun i => Fin.append (Fin.append y g) (fun i => !(Fin.append y g) (Fin.natAdd N i)) i = true).card =
      (univ.filter fun i => y i = true).card + A := by
  simp only [Fin.append_right]
  rw [card_true_append, card_true_append]
  have := card_true_not g
  omega

section Count

variable {n k t mm : ℕ}

/-- Step C: the complements are determined. -/
theorem stepC {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n)
    (hk : 1 ≤ k) (ω : Seed n k t mm) (s : ℕ) :
    cntS (n + n + n + 1 + mm * k + mm * k) s (ciF n E ψ ω) =
      (univ.filter fun w : Fin (n + n + n + 1 + mm * k) → Bool =>
        (∀ C ∈ connF n E ψ ++ [[(n + n + n, false)]] ++
          isoF (n + n + n) (n + n + n + 1) k ω.1.val (rowsOf ω) (fixesOf ω), ∃ l ∈ C, ext w l.1 = l.2) ∧
        (univ.filter fun i => Fin.append w (fun i => !w (Fin.natAdd (n + n + n + 1) i)) i = true).card = s).card := by
  unfold cntS
  refine card_append _ _ (fun w i => !w (Fin.natAdd (n + n + n + 1) i)) fun w h => ?_
  have hlt : ∀ a < n + n + n + 1 + mm * k, ext (Fin.append w h) a = ext w a := fun a ha => ext_append_lt w h ha
  have hvars : ∀ C ∈ connF n E ψ ++ [[(n + n + n, false)]] ++
      isoF (n + n + n) (n + n + n + 1) k ω.1.val (rowsOf ω) (fixesOf ω), ∀ l ∈ C, l.1 < n + n + n + 1 + mm * k := by
    intro C hC l hl
    rcases List.mem_append.1 hC with hC | hC
    · rcases List.mem_append.1 hC with hC | hC
      · have := (connF_vars hE hψ C hC).2 l hl; omega
      · rw [List.mem_singleton] at hC; subst hC; rw [List.mem_singleton] at hl; subst hl; simp only; omega
    · exact (isoF_clause (by omega) (by omega) hk ω hC).2 l hl
  rw [ciF, List.forall_mem_append, sat_congr (f' := ext w) (fun C hC l hl => hlt _ (hvars C hC l hl)), sat_compF]
  have hc : (∀ i < mm * k, ext (Fin.append w h) (n + n + n + 1 + mm * k + i) =
      !ext (Fin.append w h) (n + n + n + 1 + i)) ↔ h = fun i => !w (Fin.natAdd (n + n + n + 1) i) := by
    rw [← comp_iff w h]
    exact forall₂_congr fun i hi => by rw [ext_append_ge, hlt _ (by omega)]
  rw [hc]
  constructor
  · rintro ⟨⟨h1, rfl⟩, h3⟩; exact ⟨⟨h1, h3⟩, rfl⟩
  · rintro ⟨⟨h1, h3⟩, rfl⟩; exact ⟨⟨h1, rfl⟩, h3⟩

/-- Step D: the chain bits are determined. -/
theorem stepD {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n)
    (hk : 1 ≤ k) (ω : Seed n k t mm) (s : ℕ) :
    (univ.filter fun w : Fin (n + n + n + 1 + mm * k) → Bool =>
        (∀ C ∈ connF n E ψ ++ [[(n + n + n, false)]] ++
          isoF (n + n + n) (n + n + n + 1) k ω.1.val (rowsOf ω) (fixesOf ω), ∃ l ∈ C, ext w l.1 = l.2) ∧
        (univ.filter fun i => Fin.append w (fun i => !w (Fin.natAdd (n + n + n + 1) i)) i = true).card = s + mm * k).card =
      (univ.filter fun y : Fin (n + n + n + 1) → Bool =>
        (∀ C ∈ connF n E ψ ++ [[(n + n + n, false)]], ∃ l ∈ C, ext y l.1 = l.2) ∧ H ω (fun j => ext y j.val) ∧
        (univ.filter fun i => y i = true).card = s).card := by
  refine card_append _ _ (auxT ω) fun y g => ?_
  have hlt : ∀ a < n + n + n + 1, ext (Fin.append y g) a = ext y a := fun a ha => ext_append_lt y g ha
  have hvars : ∀ C ∈ connF n E ψ ++ [[(n + n + n, false)]], ∀ l ∈ C, l.1 < n + n + n + 1 := by
    intro C hC l hl
    rcases List.mem_append.1 hC with hC | hC
    · have := (connF_vars hE hψ C hC).2 l hl; omega
    · rw [List.mem_singleton] at hC; subst hC; rw [List.mem_singleton] at hl; subst hl; simp only; omega
  rw [List.forall_mem_append, sat_congr (f' := ext y) (fun C hC l hl => hlt _ (hvars C hC l hl)), count_comp]
  have hzf : (∀ C ∈ connF n E ψ ++ [[(n + n + n, false)]], ∃ l ∈ C, ext y l.1 = l.2) → ext y (n + n + n) = false :=
    fun h => by
      have := h _ (List.mem_append_right _ (List.mem_singleton_self _))
      simpa using this
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have := (sat_isoF_iff (by omega) hk ω (by omega) y g (hzf h1)).1 h2
    exact ⟨⟨h1, this.1, by omega⟩, this.2⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨⟨h1, (sat_isoF_iff (by omega) hk ω (by omega) y g (hzf h1)).2 ⟨h2, h4⟩⟩, by omega⟩

/-- Step E: the variable z is false. -/
theorem stepE {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < p.2 ∧ p.2 < n) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n)
    (ω : Seed n k t mm) (s : ℕ) :
    (univ.filter fun y : Fin (n + n + n + 1) → Bool =>
        (∀ C ∈ connF n E ψ ++ [[(n + n + n, false)]], ∃ l ∈ C, ext y l.1 = l.2) ∧ H ω (fun j => ext y j.val) ∧
        (univ.filter fun i => y i = true).card = s).card =
      (univ.filter fun w : Fin (n + n + n) → Bool => ((∀ C ∈ connF n E ψ, ∃ l ∈ C, ext w l.1 = l.2) ∧
        H ω (fun j => ext w j.val)) ∧ (univ.filter fun i => w i = true).card = s).card := by
  refine card_append _ _ (fun _ _ => false) fun w b => ?_
  have hlt : ∀ a < n + n + n, ext (Fin.append w b) a = ext w a := fun a ha => ext_append_lt w b ha
  have hH : (fun j : Fin n => ext (Fin.append w b) j.val) = fun j => ext w j.val := funext fun j => hlt _ (by omega)
  have hz : ext (Fin.append w b) (n + n + n) = b 0 := by
    have h1 := ext_append_ge w b 0
    simp only [Nat.add_zero] at h1
    rw [h1]
    simp only [CountKSat.ext, dif_pos Nat.zero_lt_one]
    rfl
  have hb : b 0 = false ↔ b = fun _ => false := ⟨fun h => funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h,
    fun h => by rw [h]⟩
  rw [List.forall_mem_append, sat_congr (f' := ext w) (fun C hC l hl => hlt _ ((connF_vars hE hψ C hC).2 l hl)), hH,
    card_true_append]
  simp only [List.mem_singleton, forall_eq, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, hz]
  rw [hb]
  constructor
  · rintro ⟨⟨h1, rfl⟩, h2, h3⟩
    exact ⟨⟨⟨h1, h2⟩, by simpa using h3⟩, rfl⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨⟨h1, rfl⟩, h2, by simpa using h3⟩

end Count

open Classical in
/-- **Connected solutions with the checks of a seed**: half the number of satisfying assignments of
`ciF` with n + ℓ + mm·k true variables has the parity of the number of vertex sets X of size ℓ ≥ 1
with X ⊨ ψ, G[X] connected, that pass the checks and the fixings of ω. -/
theorem ci_parity {n : ℕ} (G : SimpleGraph (Fin n)) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) {ℓ k t mm : ℕ}
    (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (ω : Seed n k t mm) :
    cntS (n + n + n + 1 + mm * k + mm * k) (n + ℓ + mm * k) (ciF n (edges n (matrix G)) ψ ω) / 2 % 2 =
      ((univ.filter fun x : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧
        (univ.filter fun v => x v = true).card = ℓ ∧ (G.induce {v | x v = true}).Connected).filter (H ω)).card % 2 := by
  have hE := edges_bound n (matrix G)
  rw [stepC hE hψ hk ω, stepD hE hψ hk ω, stepE hE hψ ω, conn_parity_P G hψ hℓ (H ω), filter_filter]
  congr 2
  ext x
  simp only [mem_filter, mem_univ, true_and]
  tauto

open Classical in
/-- **Connected solutions with one-sided error.** For every δ > 0 there are k and t such that for
all graphs G on n ≥ n₀ vertices, ψ on the vertex bits, ℓ ≥ 1 and the seeds ω of `Seed n k t (3n+3)`:
if there is no connected solution of size ℓ, the parity is 0 for every seed; if there is one, it is
1 for at least a 2^{−δn} fraction of the seeds. -/
theorem ci_decide (δ : ℝ) (hδ : 0 < δ) : ∃ k t : ℕ, 1 ≤ k ∧ 1 ≤ t ∧ ∃ n₀ : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ψ : Fml) (ℓ : ℕ), n₀ ≤ n → (∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) → 1 ≤ ℓ →
      (numConnF G ψ ℓ = 0 → ∀ ω : Seed n k t (3 * n + 3),
        cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
          (ciF n (edges n (matrix G)) ψ ω) / 2 % 2 = 0) ∧
      (0 < numConnF G ψ ℓ →
        (Fintype.card (Seed n k t (3 * n + 3)) : ℝ) ≤ 2 ^ (δ * n) *
          (univ.filter fun ω : Seed n k t (3 * n + 3) =>
            cntS (n + n + n + 1 + (3 * n + 3) * k + (3 * n + 3) * k) (n + ℓ + (3 * n + 3) * k)
              (ciF n (edges n (matrix G)) ψ ω) / 2 % 2 = 1).card) := by
  obtain ⟨k, t, hk, ht, M₀, hM₀⟩ := isolation δ hδ
  refine ⟨k, t, hk, ht, M₀, fun n G ψ ℓ hn hψ hℓ => ⟨fun h0 ω => ?_, fun hpos => ?_⟩⟩
  · rw [ci_parity G hψ hℓ hk ω]
    have : (univ.filter fun x : Fin n → Bool => (∀ C ∈ ψ, ∃ l ∈ C, ext x l.1 = l.2) ∧
        (univ.filter fun v => x v = true).card = ℓ ∧ (G.induce {v | x v = true}).Connected) = ∅ :=
      card_eq_zero.1 h0
    rw [this]; simp
  · have h := hM₀ n hn _ (card_pos.1 hpos)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast card_le_card fun ω hω => by
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      rw [ci_parity G hψ hℓ hk ω, hω]

end EthCor.ConnI
