import EthCor.Potts
import EthCor.HamIsoTM
import EthCor.HamSparseTM
import EthCor.ConnFormula
import FromPrinted.Sets
import GraphProblems.Host
import GraphProblems.SetTM

/-! # The Potts spectrum of a sparse graph in time C·2^{δn}

For q colors, the formula `pottsF n q E` has a variable x_{vq+c} for every vertex v and color c and
a variable y_i = x_{nq+i} for the i-th edge of the list E. Its clauses say that every vertex has
exactly one color (`vtxF`, width q and 2) and that y_i holds exactly when the two ends of edge i
have the same color (`edgeM`, width 3). Its satisfying assignments are the colorings σ, and such an
assignment has n + (number of monochromatic edges) true variables (`cnt_pottsF`). Anthropic's
machine `FromPrinted.Consequences.SIZED` counts the satisfying assignments with a given number of
true variables. On a graph with at most D·n edges the formula has at most (q + D)·n variables, so
`potts_spectrum` follows: for every q ≥ 1, D and δ > 0 one Turing machine computes the Potts density of
states `pottsSpec G q j` from the code of G and j in unary, within C·2^{δn} steps. With
`EthCor.Potts.tutte_hyperbola` this gives the Tutte polynomial on the hyperbola (x−1)(y−1) = q. -/

namespace EthCor.PottsTM

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat GraphProblems Turing Finset EthCor.Ham EthCor.HamTM
  EthCor.HamITM EthCor.Potts

/-! ### The formula -/

/-- The pairs (c, c') with c' < c < q. -/
def amo (q : ℕ) : List (ℕ × ℕ) := (List.range q ×ˢ List.range q).filter fun p => decide (p.2 < p.1)

/-- The vertex v gets exactly one color: x_{vq+c} for some c < q, and never two. -/
def vtxF (q v : ℕ) : Fml :=
  ((List.range q).map fun c => (v * q + c, true)) ::
    (amo q).map fun p => [(v * q + p.1, false), (v * q + p.2, false)]

def colF (n q : ℕ) : Fml := (List.range n).flatMap fun v => vtxF q v

/-- y = x_{nq+i} says that the edge (a, b) is monochromatic: for every color c,
x_{aq+c} ∧ x_{bq+c} → y and y ∧ x_{aq+c} → x_{bq+c}. -/
def edgeM (n q i : ℕ) (p : ℕ × ℕ) : Fml := (List.range q).flatMap fun c =>
  [[(p.1 * q + c, false), (p.2 * q + c, false), (n * q + i, true)],
   [(n * q + i, false), (p.1 * q + c, false), (p.2 * q + c, true)]]

def monoF (n q : ℕ) (E : List (ℕ × ℕ)) : Fml :=
  (List.range E.length).flatMap fun i => edgeM n q i (E.getD i (0, 0))

/-- The colorings with q colors, and y_i ↔ the i-th edge is monochromatic. -/
def pottsF (n q : ℕ) (E : List (ℕ × ℕ)) : Fml := colF n q ++ monoF n q E

/-! ### Its satisfying assignments -/

theorem mem_amo {q : ℕ} {p : ℕ × ℕ} : p ∈ amo q ↔ p.1 < q ∧ p.2 < p.1 := by
  obtain ⟨a, b⟩ := p
  simp only [amo, List.mem_filter, List.mem_product, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

theorem getD_mem {E : List (ℕ × ℕ)} {i : ℕ} (hi : i < E.length) : E.getD i (0, 0) ∈ E := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem idx_lt {n q v c : ℕ} (hv : v < n) (hc : c < q) : v * q + c < n * q := by
  have := Nat.mul_le_mul_right q (show v + 1 ≤ n by omega)
  rw [Nat.succ_mul] at this
  omega

theorem div_idx {q v c : ℕ} (hc : c < q) : (v * q + c) / q = v := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem mod_idx {q v c : ℕ} (hc : c < q) : (v * q + c) % q = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem sat_vtxF (f : ℕ → Bool) (q v : ℕ) :
    (∀ C ∈ vtxF q v, ∃ l ∈ C, f l.1 = l.2) ↔ (∃ c < q, f (v * q + c) = true) ∧
      ∀ c < q, ∀ c' < q, f (v * q + c) = true → f (v * q + c') = true → c = c' := by
  rw [vtxF, List.forall_mem_cons, List.forall_mem_map]
  have h1 : (∃ l ∈ (List.range q).map fun c => (v * q + c, true), f l.1 = l.2) ↔ ∃ c < q, f (v * q + c) = true := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, e⟩; exact ⟨c, hc, e⟩
    · rintro ⟨c, hc, e⟩; exact ⟨_, ⟨c, hc, rfl⟩, e⟩
  rw [h1]
  refine and_congr_right fun _ => ?_
  constructor
  · intro H c hc c' hc' e1 e2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := (EthCor.HamS.sat2 f _ _).1 (H (c', c) (mem_amo.2 ⟨hc', h⟩))
      simp only at this
      rcases this with e | e <;> simp_all
    · have := (EthCor.HamS.sat2 f _ _).1 (H (c, c') (mem_amo.2 ⟨hc, h⟩))
      simp only at this
      rcases this with e | e <;> simp_all
  · intro H p hp
    obtain ⟨h1, h2⟩ := mem_amo.1 hp
    rw [EthCor.HamS.sat2]
    by_cases e1 : f (v * q + p.1) = true
    · by_cases e2 : f (v * q + p.2) = true
      · exact absurd (H _ h1 _ (by omega) e1 e2) (by omega)
      · right; simpa using e2
    · left; simpa using e1

theorem sat_edgeM (f : ℕ → Bool) (n q i : ℕ) (p : ℕ × ℕ) :
    (∀ C ∈ edgeM n q i p, ∃ l ∈ C, f l.1 = l.2) ↔ ∀ c < q,
      (f (p.1 * q + c) = true → f (p.2 * q + c) = true → f (n * q + i) = true) ∧
      (f (n * q + i) = true → f (p.1 * q + c) = true → f (p.2 * q + c) = true) := by
  constructor
  · intro H c hc
    have h1 := H [(p.1 * q + c, false), (p.2 * q + c, false), (n * q + i, true)]
      (List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, by simp⟩)
    have h2 := H [(n * q + i, false), (p.1 * q + c, false), (p.2 * q + c, true)]
      (List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, by simp⟩)
    rw [sat3] at h1 h2
    dsimp only at h1 h2
    refine ⟨fun e1 e2 => ?_, fun e1 e2 => ?_⟩
    · rcases h1 with h | h | h <;> simp_all
    · rcases h2 with h | h | h <;> simp_all
  · intro H C hC
    obtain ⟨c, hc, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨H1, H2⟩ := H c (List.mem_range.1 hc)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> rw [sat3] <;> dsimp only
    · by_cases e1 : f (p.1 * q + c) = true <;> by_cases e2 : f (p.2 * q + c) = true <;> simp_all
    · by_cases e1 : f (p.1 * q + c) = true <;> by_cases e2 : f (n * q + i) = true <;> simp_all

theorem sat_pottsF (f : ℕ → Bool) (n q : ℕ) (E : List (ℕ × ℕ)) :
    (∀ C ∈ pottsF n q E, ∃ l ∈ C, f l.1 = l.2) ↔ (∀ v < n, ∀ C ∈ vtxF q v, ∃ l ∈ C, f l.1 = l.2) ∧
      ∀ i < E.length, ∀ C ∈ edgeM n q i (E.getD i (0, 0)), ∃ l ∈ C, f l.1 = l.2 := by
  rw [pottsF, colF, monoF, List.forall_mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun v hv C hC => h1 C (List.mem_flatMap.2 ⟨v, List.mem_range.2 hv, hC⟩),
      fun i hi C hC => h2 C (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hC⟩)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun C hC => ?_, fun C hC => ?_⟩
    · obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC; exact h1 v (List.mem_range.1 hv) C hC
    · obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC; exact h2 i (List.mem_range.1 hi) C hC

/-- The color of the vertex a, as a number (q if a is not a vertex). -/
def cl {n q : ℕ} (σ : Fin n → Fin q) (a : ℕ) : ℕ := if h : a < n then (σ ⟨a, h⟩).val else q

theorem cl_lt {n q : ℕ} (σ : Fin n → Fin q) {a : ℕ} (h : a < n) : cl σ a < q := by
  rw [cl, dif_pos h]; exact (σ _).2

/-- Given the colors ca, cb of the ends, the clauses of an edge say y = [ca = cb]. -/
theorem edge_iff {q a b : ℕ} (f : ℕ → Bool) (y : Bool) {ca cb : ℕ} (ha : ca < q) (hb : cb < q)
    (hfa : ∀ c < q, f (a * q + c) = decide (ca = c)) (hfb : ∀ c < q, f (b * q + c) = decide (cb = c)) :
    (∀ c < q, (f (a * q + c) = true → f (b * q + c) = true → y = true) ∧
      (y = true → f (a * q + c) = true → f (b * q + c) = true)) ↔ y = decide (ca = cb) := by
  constructor
  · intro H
    obtain ⟨H1, H2⟩ := H ca ha
    rw [hfa ca ha, hfb ca ha] at H1 H2
    by_cases e : ca = cb
    · subst e; simp only [decide_true, forall_const] at H1; simp [H1]
    · have : y = false := by
        cases y
        · rfl
        · simp only [decide_true, forall_const, decide_eq_true_eq] at H2; exact absurd H2.symm e
      simp [this, e]
  · intro hy c hc
    rw [hfa c hc, hfb c hc, hy]
    simp only [decide_eq_true_eq]
    exact ⟨fun h1 h2 => h1.trans h2.symm, fun h h1 => h.symm.trans h1⟩

/-- The assignment of the coloring σ: x_{vq+c} = [σ v = c]. -/
def colA {n q : ℕ} (σ : Fin n → Fin q) (k : Fin (n * q)) : Bool := decide (cl σ (k.val / q) = k.val % q)

/-- y_i = [the i-th edge is monochromatic]. -/
def edgeA {n q : ℕ} (E : List (ℕ × ℕ)) (σ : Fin n → Fin q) (i : Fin E.length) : Bool :=
  decide (cl σ (E.getD i (0, 0)).1 = cl σ (E.getD i (0, 0)).2)

def enc {n q : ℕ} (E : List (ℕ × ℕ)) (σ : Fin n → Fin q) : Fin (n * q + E.length) → Bool :=
  Fin.append (colA σ) (edgeA E σ)

/-- The number of monochromatic edges of the list. -/
def mE {n q : ℕ} (E : List (ℕ × ℕ)) (σ : Fin n → Fin q) : ℕ := (univ.filter fun i => edgeA E σ i = true).card

theorem ext_colA {n q : ℕ} {E : List (ℕ × ℕ)} (σ : Fin n → Fin q) {v c : ℕ} (hv : v < n) (hc : c < q) :
    ext (enc E σ) (v * q + c) = decide (cl σ v = c) := by
  rw [enc, ext_append_lt _ _ (idx_lt hv hc)]
  simp only [CountKSat.ext, dif_pos (idx_lt hv hc), colA, div_idx hc, mod_idx hc]

theorem ext_edgeA {n q : ℕ} {E : List (ℕ × ℕ)} (σ : Fin n → Fin q) {i : ℕ} (hi : i < E.length) :
    ext (enc E σ) (n * q + i) = decide (cl σ (E.getD i (0, 0)).1 = cl σ (E.getD i (0, 0)).2) := by
  rw [enc, ext_append_ge]
  simp only [CountKSat.ext, dif_pos hi, edgeA]

theorem card_colA {n q : ℕ} (σ : Fin n → Fin q) : (univ.filter fun k : Fin (n * q) => colA σ k = true).card = n := by
  refine Eq.trans ?_ (Finset.card_fin n)
  symm
  refine Finset.card_bij (fun v _ => (⟨v.val * q + (σ v).val, idx_lt v.2 (σ v).2⟩ : Fin (n * q)))
    (fun v _ => ?_) (fun v _ v' _ h => ?_) (fun k hk => ?_)
  · simp only [mem_filter, mem_univ, true_and, colA, decide_eq_true_eq]
    rw [div_idx (σ v).2, mod_idx (σ v).2, cl, dif_pos v.2]
  · have h' := congrArg (fun k : Fin (n * q) => k.val / q) h
    simp only [div_idx (σ v).2, div_idx (σ v').2] at h'
    exact Fin.ext h'
  · have hk' := (mem_filter.1 hk).2
    simp only [colA, decide_eq_true_eq] at hk'
    have hv : k.val / q < n := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq k.2 (Nat.mul_comm n q))
    refine ⟨⟨k.val / q, hv⟩, mem_univ _, Fin.ext ?_⟩
    rw [cl, dif_pos hv] at hk'
    simp only
    rw [hk']
    exact Nat.div_add_mod' k.val q

theorem count_enc {n q : ℕ} (E : List (ℕ × ℕ)) (σ : Fin n → Fin q) :
    (univ.filter fun k => enc E σ k = true).card = n + mE E σ := by
  rw [enc, EthCor.Conn.card_true_append, card_colA, mE]

theorem sat_enc {n q : ℕ} (E : List (ℕ × ℕ)) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n) (σ : Fin n → Fin q) :
    ∀ C ∈ pottsF n q E, ∃ l ∈ C, ext (enc E σ) l.1 = l.2 := by
  rw [sat_pottsF]
  refine ⟨fun v hv => (sat_vtxF _ q v).2 ⟨⟨cl σ v, cl_lt σ hv, by rw [ext_colA σ hv (cl_lt σ hv)]; simp⟩,
    fun c hc c' hc' h1 h2 => ?_⟩, fun i hi => ?_⟩
  · rw [ext_colA σ hv hc] at h1
    rw [ext_colA σ hv hc'] at h2
    simp only [decide_eq_true_eq] at h1 h2
    omega
  · have hp := hE _ (getD_mem hi)
    rw [sat_edgeM]
    exact (edge_iff _ _ (cl_lt σ hp.1) (cl_lt σ hp.2) (fun c hc => ext_colA σ hp.1 hc)
      (fun c hc => ext_colA σ hp.2 hc)).2 (ext_edgeA σ hi)

/-- **The count.** The satisfying assignments of `pottsF` with n + j true variables are the
colorings with j monochromatic edges of the list. -/
theorem cnt_pottsF {n q : ℕ} (E : List (ℕ × ℕ)) (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n) (j : ℕ) :
    cntS (n * q + E.length) (n + j) (pottsF n q E) = (univ.filter fun σ : Fin n → Fin q => mE E σ = j).card := by
  rw [cntS]
  symm
  refine Finset.card_bij (fun σ _ => enc E σ) (fun σ hσ => ?_) (fun σ _ σ' _ h => ?_) (fun a ha => ?_)
  · rw [mem_filter] at hσ ⊢
    exact ⟨mem_univ _, sat_enc E hE σ, by rw [count_enc, hσ.2]⟩
  · funext v
    have := congrArg (fun a => ext a (v.val * q + (σ v).val)) h
    simp only [ext_colA _ v.2 (σ v).2, cl, dif_pos v.2, decide_true] at this
    exact (Fin.ext (of_decide_eq_true this.symm)).symm
  · obtain ⟨-, hsat, hcnt⟩ := mem_filter.1 ha
    obtain ⟨hV, hEd⟩ := (sat_pottsF _ _ _ _).1 hsat
    have hV' := fun v hv => (sat_vtxF _ q v).1 (hV v hv)
    choose! col hcol hcolT using fun v hv => (hV' v hv).1
    let σ : Fin n → Fin q := fun v => ⟨col v.val, hcol v.val v.2⟩
    have hf : ∀ v < n, ∀ c < q, ext a (v * q + c) = decide (cl σ v = c) := by
      intro v hv c hc
      rw [cl, dif_pos hv]
      show ext a (v * q + c) = decide (col v = c)
      by_cases e : col v = c
      · rw [decide_eq_true e, ← e]; exact hcolT v hv
      · rw [decide_eq_false e]
        cases h : ext a (v * q + c)
        · rfl
        · exact absurd ((hV' v hv).2 _ (hcol v hv) _ hc (hcolT v hv) h) e
    have henc : enc E σ = a := by
      funext k
      rw [← ext_fin (enc E σ) k, ← ext_fin a k]
      by_cases hk : k.val < n * q
      · have hv : k.val / q < n := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hk (Nat.mul_comm n q))
        have hq : 0 < q := Nat.pos_of_ne_zero fun h => by subst h; simp at hk
        have hc : k.val % q < q := Nat.mod_lt _ hq
        rw [← Nat.div_add_mod' k.val q, ext_colA σ hv hc, hf _ hv _ hc]
      · obtain ⟨i, hi⟩ : ∃ i, k.val = n * q + i := ⟨k.val - n * q, by omega⟩
        have hi' : i < E.length := by have := k.2; omega
        rw [hi, ext_edgeA σ hi']
        have hp := hE _ (getD_mem hi')
        exact ((edge_iff (ext a) _ (cl_lt σ hp.1) (cl_lt σ hp.2) (hf _ hp.1) (hf _ hp.2)).1
          ((sat_edgeM _ _ _ _ _).1 (hEd i hi'))).symm
    refine ⟨σ, mem_filter.2 ⟨mem_univ _, ?_⟩, henc⟩
    have := count_enc E σ
    rw [henc, hcnt] at this
    omega

/-! ### The edge list and the edges of G -/

open Classical in
/-- The monochromatic entries of the edge list of G are the monochromatic edges of G. -/
theorem mE_eq {n q : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Fin q) :
    mE (edges n (matrix G)) σ = mono G σ := by
  have hb := edges_bound n (matrix G)
  have key : ∀ i : Fin (edges n (matrix G)).length, ((edges n (matrix G)).getD i (0, 0)).1 <
      ((edges n (matrix G)).getD i (0, 0)).2 ∧ ((edges n (matrix G)).getD i (0, 0)).2 < n := fun i =>
    hb _ (getD_mem i.2)
  let a : Fin (edges n (matrix G)).length → Fin n := fun i => ⟨_, (key i).1.trans (key i).2⟩
  let b : Fin (edges n (matrix G)).length → Fin n := fun i => ⟨_, (key i).2⟩
  have hab : ∀ i, (a i).val < (b i).val := fun i => (key i).1
  rw [mE, mono]
  refine Finset.card_bij (fun i _ => s(a i, b i)) (fun i hi => ?_) (fun i _ i' _ h => ?_) (fun e he => ?_)
  · have hi' := (mem_filter.1 hi).2
    rw [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.map_mk, Sym2.mk_isDiag_iff]
    have hm : ((a i).val, (b i).val) ∈ edges n (matrix G) := getD_mem i.2
    refine ⟨((mem_edges stAdj G (a i) (b i)).1 hm).2, ?_⟩
    have h1 : cl σ (a i).val = cl σ (b i).val := of_decide_eq_true hi'
    rw [cl, cl, dif_pos (a i).2, dif_pos (b i).2] at h1
    exact Fin.ext h1
  · rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e : (edges n (matrix G)).getD i (0, 0) = (edges n (matrix G)).getD i' (0, 0) :=
        Prod.ext (congrArg Fin.val h1) (congrArg Fin.val h2)
      rw [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ i'.2] at e
      exact Fin.ext ((edges_nodup n (matrix G)).getElem_inj_iff.1 e)
    · have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      have k1 := hab i
      have k2 := hab i'
      omega
  · obtain ⟨he1, he2⟩ := mem_filter.1 he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he1
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff] at he2
      have hfind : ∀ u v : Fin n, u < v → G.Adj u v → σ u = σ v → ∃ i, ∃ _ : i ∈ univ.filter
          (fun i => edgeA (edges n (matrix G)) σ i = true), s(a i, b i) = s(u, v) := by
        intro u v huv hadj hσ
        obtain ⟨i, hi, hE⟩ := List.mem_iff_getElem.1 ((mem_edges stAdj G u v).2 ⟨huv, hadj⟩)
        have hg : (edges n (matrix G)).getD i (0, 0) = (u.val, v.val) := by rw [List.getD_eq_getElem _ _ hi, hE]
        have h1 : a ⟨i, hi⟩ = u := Fin.ext (show ((edges n (matrix G)).getD i (0, 0)).1 = u.val by rw [hg])
        have h2 : b ⟨i, hi⟩ = v := Fin.ext (show ((edges n (matrix G)).getD i (0, 0)).2 = v.val by rw [hg])
        refine ⟨⟨i, hi⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, by rw [h1, h2]⟩
        show decide (cl σ (a ⟨i, hi⟩).val = cl σ (b ⟨i, hi⟩).val) = true
        rw [h1, h2, cl, cl, dif_pos u.2, dif_pos v.2]
        exact decide_eq_true (congrArg Fin.val hσ)
      rcases lt_trichotomy u v with huv | rfl | huv
      · exact hfind u v huv he1 he2
      · exact absurd he1 (G.loopless.irrefl _)
      · obtain ⟨i, hi, e⟩ := hfind v u huv he1.symm he2.symm
        exact ⟨i, hi, e.trans Sym2.eq_swap⟩

open Classical in
theorem card_le_length {n : ℕ} (G : SimpleGraph (Fin n)) : G.edgeFinset.card ≤ (edges n (matrix G)).length := by
  have h := mE_eq (q := 1) G (fun _ => 0)
  have h1 : mono G (fun _ : Fin n => (0 : Fin 1)) = G.edgeFinset.card := by
    rw [mono, filter_true_of_mem]
    intro e _
    induction e using Sym2.ind with
    | h u v => rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
  rw [← h1, ← h, mE]
  exact (card_filter_le _ _).trans (by rw [card_univ, Fintype.card_fin])

/-! ### Sizes -/

theorem shaped_pottsF {n q : ℕ} {E : List (ℕ × ℕ)} (hE : ∀ p ∈ E, p.1 < n ∧ p.2 < n) :
    Shaped (q + 3) (n * q + E.length) (pottsF n q E) := by
  intro C hC
  rw [pottsF, colF, monoF, List.mem_append] at hC
  rcases hC with hC | hC
  · obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC
    have hv := List.mem_range.1 hv
    rw [vtxF, List.mem_cons] at hC
    rcases hC with rfl | hC
    · refine ⟨by simp, fun l hl => ?_⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
      have := idx_lt hv (List.mem_range.1 hc)
      simp only
      omega
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hC
      obtain ⟨h1, h2⟩ := mem_amo.1 hp
      have e1 := idx_lt hv h1
      have e2 := idx_lt hv (show p.2 < q by omega)
      refine ⟨by simp, fun l hl => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only <;> omega
  · obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
    have hi := List.mem_range.1 hi
    have hp := hE _ (getD_mem hi)
    obtain ⟨c, hc, hC⟩ := List.mem_flatMap.1 hC
    have hc := List.mem_range.1 hc
    have e1 := idx_lt hp.1 hc
    have e2 := idx_lt hp.2 hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl | rfl <;>
      simp only <;> omega

theorem length_amo (q : ℕ) : (amo q).length ≤ q * q := by
  unfold amo
  exact (List.length_filter_le _ _).trans (by rw [List.length_product, List.length_range])

theorem length_pottsF_le {n q : ℕ} (E : List (ℕ × ℕ)) :
    (pottsF n q E).length ≤ n * (q * q + 1) + E.length * (q * 2) := by
  rw [pottsF, List.length_append]
  have h1 : (colF n q).length ≤ n * (q * q + 1) := by
    have := length_flatMap_le (List.range n) (fun v => vtxF q v) (q * q + 1) fun v _ => by
      simp only [vtxF, List.length_cons, List.length_map]; have := length_amo q; omega
    rwa [List.length_range] at this
  have h2 : (monoF n q E).length ≤ E.length * (q * 2) := by
    have := length_flatMap_le (List.range E.length) (fun i => edgeM n q i (E.getD i (0, 0))) (q * 2) fun i _ => by
      have := length_flatMap_le (List.range q) (fun c => [[(((E.getD i (0, 0)).1 * q + c, false)),
        ((E.getD i (0, 0)).2 * q + c, false), (n * q + i, true)], [(n * q + i, false),
        ((E.getD i (0, 0)).1 * q + c, false), ((E.getD i (0, 0)).2 * q + c, true)]]) 2 fun c _ => by simp
      rwa [List.length_range] at this
    rwa [List.length_range] at this
  omega

theorem length_input_potts {n D j : ℕ} (G : SimpleGraph (Fin n)) (hj : j ≤ D * n) :
    (code G ++ unary j).length + 1 ≤ (D + 6) * (n + 2) ^ 2 := by
  rw [List.length_append, length_code_eq]
  simp only [unary, List.length_append, List.length_replicate, List.length_singleton]
  nlinarith

/-! ### The machine -/

section Poly

variable {α : Type} [Enc α]

theorem pottsF_polyT (q : ℕ) {n : α → ℕ} {E : α → List (ℕ × ℕ)} (hn : Unary n) (hE : PolyT E) :
    PolyT fun a => pottsF (n a) q (E a) := by
  have hn' := hn.poly
  have hr : PolyT fun a => List.range (n a) := PolyT.range hn
  have hrE : PolyT fun a => List.range (E a).length := PolyT.range (Unary.of_length hE)
  have hv : PolyT fun p : α × ℕ => vtxF q p.2 := by unfold vtxF; fun_prop
  have hm : PolyT fun p : α × ℕ => edgeM (n p.1) q p.2 ((E p.1).getD p.2 (0, 0)) := by unfold edgeM; fun_prop
  unfold pottsF colF monoF
  exact PolyT.append (PolyT.flatMap hv hr) (PolyT.flatMap hm hrE)

end Poly

/-- Read the code of G and j; write (nq + m in unary, n + j, `pottsF`). -/
def preP (q : ℕ) (x : List Bool) : List Unit × ℕ × Fml :=
  (List.replicate (nH x * q + (EH x).length) (), nH x + ones (sI x), pottsF (nH x) q (EH x))

theorem preP_polyT (q : ℕ) : PolyT (preP q) := by
  have hg : PolyT gH := by unfold gH; have := stCertRead.1; fun_prop
  have hn : Unary nH := Unary.of_length hg.fst
  have hE : PolyT EH := edges_polyT hn hg.snd
  have hs : PolyT sI := by unfold sI; have := hn.poly; fun_prop
  have hl : PolyT fun x => ones (sI x) := by unfold ones; fun_prop
  have h1 : PolyT fun x => List.replicate (nH x * q + (EH x).length) () :=
    (hn.mul (Unary.const q)).add (Unary.of_length hE)
  have h2 : PolyT fun x => nH x + ones (sI x) := PolyT.add hn.poly hl
  have h3 : PolyT fun x => pottsF (nH x) q (EH x) := pottsF_polyT q hn hE
  exact PolyT.prodMk h1 (PolyT.prodMk h2 h3)

/-- Prepare, count with `SIZED`, write the number in binary. -/
def pottsM (q w ℓ τ : ℕ) : Stepped (List Bool) (List Bool) :=
  Stepped.mapOut (Stepped.mapIn (preP q) (FromPrinted.Consequences.SIZED w ℓ τ)) Nat.bits

@[instance_reducible] def isPolyT_pottsM (q w ℓ τ : ℕ) [IsPolyT (FromPrinted.Consequences.SIZED w ℓ τ)] :
    IsPolyT (pottsM q w ℓ τ) :=
  haveI := IsPolyT.mapIn (M := FromPrinted.Consequences.SIZED w ℓ τ) (preP_polyT q)
  IsPolyT.mapOut (M := Stepped.mapIn (preP q) (FromPrinted.Consequences.SIZED w ℓ τ)) bits_polyT

theorem read_potts {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) (j : ℕ) :
    preP q (code G ++ unary j) = (List.replicate (n * q + (edges n (matrix G)).length) (), n + j,
      pottsF n q (edges n (matrix G))) := by
  obtain ⟨hn, hE, hs⟩ := read_code G (unary j)
  have h1 : ones (unary j) = j := by simpa using Read.ones_unary_append j []
  rw [preP, hn, hE, hs, h1]

/-! ### The theorem -/

open Classical in
/-- **The Potts density of states of sparse graphs in time C·2^{δn}.** For every number of colors
q ≥ 1, density D and δ > 0, one Turing machine with finite alphabets: given a graph G on n vertices
with at most D·n edges and j ≤ |E(G)| in unary, it outputs in binary the number of colorings
σ : Fin n → Fin q with exactly j monochromatic edges, within ⌊C·2^{δn}⌋ steps. -/
theorem potts_spectrum (q D : ℕ) (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n j : ℕ) (G : SimpleGraph (Fin n)), G.edgeFinset.card ≤ D * n → j ≤ G.edgeFinset.card →
      Wrap.Outputs M (code G ++ unary j) (Nat.bits (pottsSpec G q j)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.Consequences.SIZED_counts (q + 3)
    (show 0 < δ / (2 * ((q : ℝ) + D + 1)) by positivity)
  have := isPolyT_pottsM q (q + 3) ℓ τ
  obtain ⟨A, hA⟩ : ∃ A, A = q * q + q + 2 + D * (2 * q + 1) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = c * A ^ c + c + 1 := ⟨_, rfl⟩
  let ι := Σ n : ℕ, {p : ℕ × SimpleGraph (Fin n) // p.2.edgeFinset.card ≤ D * n ∧ p.1 ≤ p.2.edgeFinset.card}
  suffices hrun : ∀ x : ι, ∃ T : ℕ, (pottsM q (q + 3) ℓ τ).Runs (code x.2.1.2 ++ unary x.2.1.1) T (K * (x.1 + 2) ^ K)
      (Nat.bits (pottsSpec x.2.1.2 q x.2.1.1)) ∧ (T : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ (δ / 2 * (x.1 : ℝ)) by
    obtain ⟨N, C', hfin, hN⟩ := tm_of_stepped (pottsM q (q + 3) ℓ τ) (ι := ι) (fun x => code x.2.1.2 ++ unary x.2.1.1)
      (fun x => Nat.bits (pottsSpec x.2.1.2 q x.2.1.1)) (fun x => x.1) hδ K (D + 6) 2
      (fun x => length_input_potts x.2.1.2 (x.2.2.2.trans x.2.2.1)) hrun
    exact ⟨N, C', hfin, fun n j G hm hj => hN ⟨n, (j, G), hm, hj⟩⟩
  rintro ⟨n, ⟨j, G⟩, hm, hj⟩
  dsimp only at hm hj ⊢
  have hE : ∀ p ∈ edges n (matrix G), p.1 < n ∧ p.2 < n := fun p hp => by
    have := edges_bound n (matrix G) p hp; omega
  have hEl : (edges n (matrix G)).length = G.edgeFinset.card := le_antisymm (EthCor.HamSTM.length_edges_le_card G) (card_le_length G)
  have hnq : n ≤ n * q := Nat.le_mul_of_pos_right n hq
  obtain ⟨T, hT, hTle⟩ := hc (n * q + (edges n (matrix G)).length) (n + j) (pottsF n q (edges n (matrix G)))
    (by omega) (shaped_pottsF hE)
  rw [← read_potts q G j, cnt_pottsF _ hE j] at hT
  have hcount : (univ.filter fun σ : Fin n → Fin q => mE (edges n (matrix G)) σ = j).card = pottsSpec G q j := by
    rw [pottsSpec]
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and, mE_eq]
  rw [hcount] at hT
  refine ⟨T, (Stepped.mapOut_runs (Stepped.mapIn_runs hT)).mono le_rfl ?_, ?_⟩
  · have hl := length_pottsF_le (n := n) (q := q) (edges n (matrix G))
    have e1 : (edges n (matrix G)).length ≤ D * n := hEl ▸ hm
    have e2 : (edges n (matrix G)).length * (q * 2) ≤ D * n * (q * 2) := Nat.mul_le_mul_right _ e1
    have hNA : n * q + (edges n (matrix G)).length + (pottsF n q (edges n (matrix G))).length + 2 ≤ A * (n + 2) := by
      have s1 : n * q + (edges n (matrix G)).length + (pottsF n q (edges n (matrix G))).length + 2 ≤
          n * q + D * n + (n * (q * q + 1) + D * n * (q * 2)) + 2 := by omega
      refine s1.trans ?_
      rw [hA]
      nlinarith [Nat.zero_le (q * q), Nat.zero_le (q * D), Nat.zero_le n, Nat.zero_le D, Nat.zero_le q]
    calc c * (n * q + (edges n (matrix G)).length + (pottsF n q (edges n (matrix G))).length + 2) ^ c
        ≤ c * (A * (n + 2)) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNA _)
      _ = c * A ^ c * (n + 2) ^ c := by rw [mul_pow, mul_assoc]
      _ ≤ K * (n + 2) ^ K := Nat.mul_le_mul (by rw [hK]; omega) (Nat.pow_le_pow_right (by omega) (by rw [hK]; omega))
  · have hN : ((n * q + (edges n (matrix G)).length : ℕ) : ℝ) ≤ ((q : ℝ) + D + 1) * n := by
      have h1 : (edges n (matrix G)).length ≤ D * n := hEl ▸ hm
      have : n * q + (edges n (matrix G)).length ≤ (q + D + 1) * n := by nlinarith
      exact_mod_cast this
    have e : δ / (2 * ((q : ℝ) + D + 1)) * ((n * q + (edges n (matrix G)).length : ℕ) : ℝ) ≤ δ / 2 * n := by
      calc δ / (2 * ((q : ℝ) + D + 1)) * ((n * q + (edges n (matrix G)).length : ℕ) : ℝ)
          ≤ δ / (2 * ((q : ℝ) + D + 1)) * (((q : ℝ) + D + 1) * n) := mul_le_mul_of_nonneg_left hN (by positivity)
        _ = δ / 2 * n := by field_simp
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / (2 * ((q : ℝ) + D + 1)) * ((n * q + (edges n (matrix G)).length : ℕ) : ℝ)) := hTle
      _ ≤ c * (2 : ℝ) ^ (δ / 2 * n) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two e) (Nat.cast_nonneg _)
      _ ≤ K * (2 : ℝ) ^ (δ / 2 * n) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show c ≤ K by omega)) (by positivity)

open Classical in
/-- **The Tutte polynomial on the hyperbola (x−1)(y−1) = q, from the machine.** For every q ≥ 1, D
and δ > 0, one Turing machine: on every graph G with at most D·n edges, its outputs N_j on
`code G ++ unary j`, j = 0, …, |E(G)|, each within ⌊C·2^{δn}⌋ steps, satisfy
(x−1)^{k(E)}·(y−1)^n·T(G; x, y) = Σ_j N_j·y^j for all x, y ≠ 1 in any field with (x−1)(y−1) = q. -/
theorem tutte_tm (q D : ℕ) (hq : 1 ≤ q) {δ : ℝ} (hδ : 0 < δ) : ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.edgeFinset.card ≤ D * n → ∃ N : ℕ → ℕ,
      (∀ j ≤ G.edgeFinset.card,
        Wrap.Outputs M (code G ++ unary j) (Nat.bits (N j)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊) ∧
      ∀ (K : Type) [Field K] (x y : K), x ≠ 1 → y ≠ 1 → (x - 1) * (y - 1) = q →
        (x - 1) ^ comps G.edgeFinset * (y - 1) ^ n * tutte G x y =
          ∑ j ∈ range (G.edgeFinset.card + 1), (N j : K) * y ^ j := by
  obtain ⟨M, C, hfin, hM⟩ := potts_spectrum q D hq hδ
  exact ⟨M, C, hfin, fun n G hm => ⟨pottsSpec G q, fun j hj => hM n j G hm hj,
    fun K _ x y hx hy hxy => tutte_hyperbola G q hx hy hxy⟩⟩

end EthCor.PottsTM
