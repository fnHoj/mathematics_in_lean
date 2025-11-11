import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image

-- 1. b 是实数集合A的上界的定义
def IsUpperBound(A : Set ℝ )(b : ℝ ): Prop :=
  ∀ a ∈ A, a ≤ b

-- 2. s 是实数集合A的上确界的定义
def IsSup (A : Set ℝ )(s : ℝ ):
  Prop :=
  (IsUpperBound A s) ∧
  (∀ b, IsUpperBound A b → s ≤ b)

-- 3. (完备性公理): 每一个非空的、有上界的实数集合都有一个最小上界。
-- A.Nonempty
axiom completeness (A : Set ℝ) (h : A.Nonempty) (h₁ : ∃ x, IsUpperBound A x) :
  ∃ s, IsSup A s


-- 4. 设 s ∈ R 是集合 A ⊆ R 的一个上界。那么，s = sup A 当且仅当 ∀ε > 0 ，∃a ∈ A 满足 s− ε < a 。
theorem sup_iff (A : Set ℝ) (s : ℝ) (hub : IsUpperBound A s) :
    IsSup A s ↔ ∀ ε > 0, ∃ a ∈ A, s - ε < a := by
  constructor
  · rintro ⟨-, hs⟩ ε εpos
    by_contra!
    linarith [hs _ this]
  · intro h
    use hub
    intro b hubb
    by_contra!
    rcases h (s - b) (by linarith) with ⟨a, aA, h'⟩
    simp at h'
    linarith [hubb a aA]


#check Set.mem_range_self

-- 5. 数列x收敛于L的定义
-- 序列：x : ℕ → ℝ
def converges_to (x : ℕ → ℝ) (L : ℝ ):=
  ∀ ε > 0, ∃ N, ∀ n ≥  N, |x n - L| < ε


-- 6. 定理 : 如果单调上升的实数序列 {xn} 是有界的，那么 {xn} 收敛并且 limn→∞ xn = sup(xn)
-- Set.range x 是函数 x 所有输出值组成的集合
-- Monotone x 单调
-- Set.mem_range_self : f i ∈ Set.range f
theorem monotone_inc_bounded_converge(x:ℕ → ℝ )(hm: Monotone x)(hb: ∃ b,IsUpperBound (Set.range x) b):
  ∃ s, IsSup (Set.range x) s ∧ converges_to x s:= by
  have hnm: (Set.range x).Nonempty:= by
    use x 0
    simp
  have hsup: ∃ s, IsSup (Set.range x) s:= by
    apply completeness
    apply hnm
    exact hb
  rcases hsup with ⟨s, hs⟩
  use s, hs
  intro ε hε
  let hup:= hs.left
  rw[sup_iff] at hs
  rcases hs ε hε with ⟨a, ha⟩
  rcases ha with ⟨⟨ N, hN ⟩, h1⟩
  use N
  intro n hn
  have h2: x n - s ≤ 0:=by
    simp
    apply hup
    simp
  rw[abs_of_nonpos]
  rw[neg_sub]
  have h3: x n ≥ x N := by apply hm hn
  linarith
  apply h2
  apply hup

theorem monotone_inc_bounded_converge1 (x: ℕ → ℝ )(hm: Monotone x)(hb: ∃ b,IsUpperBound (Set.range x) b):
    ∃ s, IsSup (Set.range x) s ∧ converges_to x s:= by
  obtain ⟨s, hs⟩ := completeness (Set.range x) ⟨x 0, 0, rfl⟩ hb
  use s, hs; intro ε εpos
  obtain ⟨_, ⟨N, rfl⟩, h'⟩ := (sup_iff _ _ hs.1).mp hs ε εpos
  use N; intro n nge
  rw [abs_of_nonpos] <;> linarith [hm nge, hs.left (x n) ⟨n, rfl⟩]

-- 定义紧集
-- 定义 3.3.1. 称集合 K ⊆ R 是紧的，若其中的每个序列都有一个收敛于 K 中极限的子序列。

def SeqCompact (K : Set ℝ) : Prop :=
  ∀ (u : ℕ → ℝ), (∀ n, u n ∈ K) →
      ∃ (l : ℝ), (l ∈ K) ∧
        ( ∃ (φ : ℕ → ℕ), (StrictMono φ) ∧ (converges_to (u ∘ φ) l))

-- 定义集合有界
--定义 3.3.3. 称一个集合 A ⊆ R 是有界的，若存在 M > 0 使得 ∀a ∈ A 都有 |a| ≤ M

def IsBound(A : Set ℝ )(b : ℝ ): Prop :=
  ∀ a ∈ A, |a| ≤ b

-- 定义闭集
-- 定义极限点

-- ε邻域
-- 给定 a ∈ R 和 ε > 0 ，a 的 ε 邻域是集合
-- Vε (a) = {x ∈ R : |x− a| < ε}
-- 换句话说，Vε (a) 是以 a 为中心、半径为 ε 的开区间 (a− ε, a + ε)

def V_ε  (a : ℝ) (ε : ℝ) : Set ℝ:=
  {x : ℝ | |x-a| < ε }

-- 定义 3.2.1. 称一个集合 O ⊆ R 是开的，若 ∀a ∈ O ，存在一个 ε-邻域 Vε (a) ⊆ O。
-- ε > 0
def IsOpenSet (O : Set ℝ) : Prop :=
  ∀ a ∈ O, ∃ ε, V_ε a ε ⊆ O

-- 定义闭集之前要先定义极限点
--极限点定义 3.2.4. 称点 x 是集合 A 的极限点，若 x 的每个 ε-邻域 Vε (x) 与集合 A 的交都不为空。
def IsLimitPoint1 (x : ℝ) (A : Set ℝ) : Prop :=
  ∀ ε > 0 , V_ε x ε ∩ A ≠ ∅

--极限点定义 3.2.4. 换一种写法，不想展开集合
--书中关于极限点的定义不够严谨，必须加上x的每个邻域都在 A 中与x以外的某点相交
--即y ≠ x

def IsLimitPoint (x : ℝ) (A : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ y, (y ∈ V_ε x ε) ∧ (y ∈ A) ∧ (y ≠ x)

--定理 3.2.5. 点 x 是集合 A 的极限点，当且仅当存在 A 中的序列 an 满足
-- ∀n ∈ N, an ≠  x
-- x = lim an

-- "存在 A 中的序列 a_n 满足: 1. (∀n, a_n ≠ x) ∧ 2. (a_n → x)"
def HasConvergentSeqNeq (x : ℝ) (A : Set ℝ) : Prop :=
  ∃ (u : ℕ → ℝ), -- 存在一个序列 u
    (∀ n, u n ∈ A) ∧
    (∀ n, u n ≠ x) ∧
    (converges_to u x)

theorem limit_point_iff_seq (x : ℝ) (A : Set ℝ) :
    IsLimitPoint x A ↔ HasConvergentSeqNeq x A := by
  sorry

-- 定义 3.2.7. 称集合 F ⊆ R 为闭集，若其包含其所有极限点。
def IsClosedSet (F : Set ℝ) : Prop :=
  ∀ (x : ℝ), IsLimitPoint x F → x ∈ F

-- 柯西序列的定义
-- "一个序列 {x_n} 是柯西序列，若 ∀ε > 0, ∃N, ∀m, n ≥ N, |x_m - x_n| < ε"

def IsCauchy (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |x m - x n| < ε

--定理 3.2.8. 一个集合 F ⊆ R 是闭的，当且仅当包含在 F 中的每个 Cauchy 序列都有一个极限，
--且该极限也是 F 的一个元素。

-- "包含在 F 中的每个 Cauchy 序列都有一个极限，且该极限也是 F 的一个元素。"
def IsSequentiallyComplete (F : Set ℝ) : Prop :=
  ∀ (u : ℕ → ℝ), -- "对于 F 中的每个..."
    (∀ n, u n ∈ F) → -- "...序列 u..."
    (IsCauchy u) → -- "...如果 u 是 Cauchy 序列..."
      ∃ (l : ℝ), -- "...那么存在一个极限 l..."
        (converges_to u l) ∧ (l ∈ F) -- "...u 收敛到 l，并且 l 在 F 中。"

-- "一个集合 F ⊆ R 是闭的，当且仅当 [上面定义的 IsSequentiallyComplete]"
theorem closed_iff_sequentially_complete (F : Set ℝ) :
    IsClosedSet F ↔ IsSequentiallyComplete F := by
  sorry

-- 定理 3.3.4 (Heine-Borel 定理). 一个集合 K ⊆ R 是紧的，当且仅当它是闭的且有界的。
theorem Heine_Borel (K : Set ℝ) : (SeqCompact K)
↔ (∃ b, IsBound K b) ∧ (IsClosedSet K) := by
  sorry

-- 定义 4.3.1.

-- 在c点连续
--称一个函数 f : A → R 在点 c ∈ A 处连续，若 ∀ε > 0 ， ∃δ > 0 ，使得每当 |x− c| < δ
--(且 x ∈ A ) 时，就有 |f (x)− f (c)| < ε 。
def IsContinuousAt (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (x : ℝ),(x ∈ A ∧ |x - c| < δ) → |f x - f c| < ε

--连续函数的定义
--如果 f 在定义域 A 中的每一点都连续，那么我们说 f 在 A 上连续。
def IsContinuousOn (f : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ (c : ℝ), (c ∈ A) → (IsContinuousAt f A c)

-- 连续性的 "序列" 定义
-- "f 在 c 点（在 A 集合内）是序列连续的"
def IsSeqContinuousAt (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) : Prop :=
  -- "对于任意序列 u..."
  ∀ (u : ℕ → ℝ),
    -- "...如果 u 在 A 中..."
    (∀ n, u n ∈ A) →
    -- "...并且 u 收敛到 c..."
    (converges_to u c) →
    -- "...那么 f(u) 就收敛到 f(c)"
    (converges_to (f ∘ u) (f c))

theorem continuous_at_iff_seq_continuous_at
(f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) :
    IsContinuousAt f A c ↔ IsSeqContinuousAt f A c := by
  sorry -- 这是一个非常经典且重要的证明，我们暂时"sorry"

-- 定理 4.4.2 (紧集的保持性)
-- 设 f : A → R 在 A 上连续。如果 K ⊆ A 是紧集，那么 f(K) 也是紧集。
-- ------------------------------------------------
theorem preservation_of_compactness
    -- 假设 f 是一个函数
    (f : ℝ → ℝ) (A K : Set ℝ)
    -- 假设 f 在 A 上连续
    (h_cont : IsContinuousOn f A)
    -- 假设 K 是 A 的子集
    (h_sub : K ⊆ A)
    -- 假设 K 是紧集
    (h_compact : SeqCompact K) :
    -- 结论：f(K) (在 Lean 中写作 f '' K) 也是紧集
    SeqCompact (f '' K) := by
  -- 证明开始：
  -- 根据紧集 (SeqCompact) 的定义，我们必须...
  -- "...(y_n) 为包含在值域 f(K) 中的任意序列。"
  intro y h_y_in_fK
  -- h_y_in_fK : ∀ n, y n ∈ f '' K
  -- 目标：∃ (l ∈ f '' K) (φ...), converges_to (y ∘ φ) l

  -- ---------------------------------
  -- 证明步骤 2: 构造 (x_n) 序列
  -- "断言 (y_n) ⊆ f(K) 意味着，∀n ∈ N，我们可以找到 (至少一个) x_n ∈ K 满足 f(x_n) = y_n。"
  -- ---------------------------------
  -- (f '' K) 的定义是 {z | ∃ x ∈ K, f x = z}
  -- h_y_in_fK n 告诉我们 ∃ x ∈ K, f x = y n
  -- 我们使用"选择公理" (Classical.choose) 来为每个 n *挑选* 一个 x
  let x (n : ℕ) : ℝ := Classical.choose (h_y_in_fK n)

  -- "Classical.choose_spec" 告诉我们 x n 满足它被"挑选"时的性质
  let hx_spec (n : ℕ) := Classical.choose_spec (h_y_in_fK n)
  -- hx_spec n : (x n ∈ K) ∧ (f (x n) = y n)

  -- 我们可以把这个性质拆分开来
  have h_x_in_K : ∀ n, x n ∈ K := fun n  => (hx_spec n).left
  have h_f_eq_y : ∀ n, f (x n) = y n := fun n => (hx_spec n).right

  -- "这便产生了一个序列 (x_n) ⊆ K。" (我们已经构造了 x 和 h_x_in_K)

  -- ---------------------------------
  -- 证明步骤 3: 利用 K 的紧性
  -- "由于 K 是紧的，存在一个收敛的子序列 (x_n_k)，其极限 x = lim x_n_k 也也在 K 中。"
  -- ---------------------------------
  -- 我们将 h_compact (K是紧集) 应用到序列 x (它在 K 中)
  let ⟨x_lim, h_x_lim_in_K, φ, hφ_mono, h_x_conv⟩ := h_compact x h_x_in_K
  -- h_x_lim_in_K : x_lim ∈ K
  -- hφ_mono      : StrictMono φ
  -- h_x_conv     : converges_to (x ∘ φ) x_lim

  -- ---------------------------------
  -- 证明步骤 4: 利用 f 的连续性
  -- "最后，我们利用 f 在 A 上连续的事实，..."
  -- ---------------------------------
  -- 我们需要证明 (y ∘ φ) 收敛
  -- (y ∘ φ) n = y (φ n)
  --           = f (x (φ n))   (根据 h_f_eq_y)
  --           = f ((x ∘ φ) n) (根据函数复合)
  -- 所以我们的目标是证明 converges_to (f ∘ (x ∘ φ)) (f x_lim)

  -- 1. 获取 "f 在 x_lim 处连续" 的证明
  have h_x_lim_in_A : x_lim ∈ A := h_sub h_x_lim_in_K -- 因为 x_lim ∈ K 且 K ⊆ A
  have h_cont_at_lim : IsContinuousAt f A x_lim := h_cont x_lim h_x_lim_in_A -- 根据 h_cont 的定义

  -- 2. 将 "ε-δ 连续" 转换为 "序列连续"
  rw [continuous_at_iff_seq_continuous_at] at h_cont_at_lim
  -- h_cont_at_lim : IsSeqContinuousAt f A x_lim

  -- 3. h_cont_at_lim 的定义是:
  -- ∀ (u : ℕ → ℝ), (∀ n, u n ∈ A) → (converges_to u x_lim) → (converges_to (f ∘ u) (f x_lim))
  -- 我们的序列 u 就是 (x ∘ φ)

  -- 4. 证明 (x ∘ φ) 满足序列连续性的前提
  have h_subseq_in_A : ∀ n, (x ∘ φ) n ∈ A := by
    intro n
    apply h_sub -- K ⊆ A
    apply h_x_in_K -- x n ∈ K 对所有 n 成立，所以对 φ n 也成立

  -- 5. 应用序列连续性
  have h_y_conv : converges_to (f ∘ (x ∘ φ)) (f x_lim) := by
    apply h_cont_at_lim (x ∘ φ) h_subseq_in_A h_x_conv

  -- 6. 将 (f ∘ (x ∘ φ)) 换回 (y ∘ φ)
  have h_f_comp_eq_y_comp : f ∘ (x ∘ φ) = y ∘ φ := by
    ext n
    simp [h_f_eq_y] -- simp 会自动展开 (f ∘ (x ∘ φ)) n = f (x (φ n))

  rw [h_f_comp_eq_y_comp] at h_y_conv
  -- h_y_conv : converges_to (y ∘ φ) (f x_lim)

  -- ---------------------------------
  -- 证明步骤 5: 结论
  -- "由于 x ∈ K, 我们有 f(x) ∈ f(K), 因此 f(K) 是紧的。"
  -- ---------------------------------
  -- 我们的目标是：∃ (l : ℝ), (l ∈ f '' K) ∧ (∃ (φ : ℕ → ℕ), ...)
  -- 我们选择的极限 l 就是 f(x_lim)
  use f x_lim
  constructor
  · -- 证明 f(x_lim) ∈ f '' K
    -- (f '' K) 的定义是 {y | ∃ x_orig ∈ K, f x_orig = y}
    use x_lim
  use φ


--下面开始形式化极值定理，但缺少下确界的定义和对应的确界原理，这里补充：

-- b 是实数集合 A 的下界的定义
def IsLowerBound (A : Set ℝ) (b : ℝ) : Prop :=
  ∀ a ∈ A, b ≤ a

-- i 是实数集合 A 的下确界的定义
def IsInf (A : Set ℝ) (i : ℝ) : Prop :=
  (IsLowerBound A i) ∧
  (∀ b, IsLowerBound A b → b ≤ i)

-- (完备性公理，下界版本)
axiom completeness_inf (A : Set ℝ) (h : A.Nonempty) (h₁ : ∃ x, IsLowerBound A x) :
  ∃ i, IsInf A i

-- 2. 新增：证明的关键引理 (暂时 sorry)
-- "一个闭合且有界的非空集合，其确界在集合内"
-- ------------------------------------------------

theorem closed_bounded_contains_sup (A : Set ℝ)
    (h_nonempty : A.Nonempty)
    (h_closed : IsClosedSet A)
    (h_bdd : ∃ b, IsUpperBound A b) :
  ∃ s, IsSup A s ∧ s ∈ A := by
  sorry -- 这个证明本身依赖 IsLimitPoint 和 IsClosedSet 的定义，我们先 "sorry"

theorem closed_bounded_contains_inf (A : Set ℝ)
    (h_nonempty : A.Nonempty)
    (h_closed : IsClosedSet A)
    (h_bdd : ∃ b, IsLowerBound A b) :
  ∃ i, IsInf A i ∧ i ∈ A := by
  sorry -- 同上

-- 定理 4.4.3 (极值定理). 如果 f : K → R 在紧集 K ⊆ R 上连续，则 f 达到最大值和最小值。换
-- 句话说，存在 x0, x1 ∈ K 使得对于所有 x ∈ K 有 f (x0) ≤ f (x) ≤ f (x1)。

theorem extreme_value_theorem
    -- "如果 f : K → R"
    (f : ℝ → ℝ) (K : Set ℝ)
    -- "在紧集 K ⊆ R 上连续"
    (h_cont : IsContinuousOn f K)
    (h_compact : SeqCompact K)
    -- (教科书悄悄省略了 K 不能为空，但这是必需的)
    (h_nonempty : K.Nonempty) :
    -- "则 f 达到最大值和最小值"
    -- "换句话说，存在 x₀, x₁ ∈ K"
    ∃ (x₀ : ℝ) (hx₀ : x₀ ∈ K) (x₁ : ℝ) (hx₁ : x₁ ∈ K),
      -- "使得对于所有 x ∈ K"
      ∀ (x : ℝ), (hx : x ∈ K) →
        -- "f(x₀) ≤ f(x) ≤ f(x₁)"
        (f x₀ ≤ f x) ∧ (f x ≤ f x₁) := by

  -- 证明 1. "由于 K 是紧集且 f 连续，故 f(K) 也是紧集。"
  -- (在 Lean 中 f(K) 写作 f '' K)
  -- (我们使用 `preservation_of_compactness` 定理)
  -- (K ⊆ K 是 (Set.Subset.refl K))
  have h_fK_compact : SeqCompact (f '' K) :=
    preservation_of_compactness f K K h_cont (Set.Subset.refl K) h_compact

  -- 证明 2. "在 R 中，紧集等价于闭且有界。因此, f(K) 是闭且有界的。"
  -- (我们使用 `Heine_Borel` 定理)
  have h_fK_closed_bounded := (Heine_Borel (f '' K)).mp h_fK_compact
  -- h_fK_closed_bounded : (∃ b, IsBound (f '' K) b) ∧ (IsClosedSet (f '' K))
  -- 我们把它拆开
  let ⟨⟨b_bound, h_fK_isBound⟩, h_fK_isClosed⟩ := h_fK_closed_bounded

  -- 证明 3. "f(K) 是非空的" (因为 K 非空)
  have h_fK_nonempty : (f '' K).Nonempty := by
    -- `h_nonempty` 告诉我们 ∃ x, x ∈ K
    rcases h_nonempty with ⟨x_init, hx_init⟩
    -- 那么 f(x_init) 就在 f '' K 中
    use f x_init
    -- `f x_init ∈ f '' K` 的定义是 `∃ x' ∈ K, f x' = f x_init`
    use x_init, hx_init

  -- 证明 4. "由有界性, f(K) 存在上确界 M 和下确界 m。"
  -- (我们需要从 IsBound |a| ≤ b 推出上/下界)
  have h_fK_bdd_upper : ∃ b, IsUpperBound (f '' K) b := by
    use b_bound
    intro y hy_in_fK
    have h_abs := h_fK_isBound y hy_in_fK -- |y| ≤ b_bound
    linarith [abs_le.mp h_abs] -- 从 |y| ≤ b 得到 y ≤ b

  have h_fK_bdd_lower : ∃ b, IsLowerBound (f '' K) b := by
    use -b_bound
    intro y hy_in_fK
    have h_abs := h_fK_isBound y hy_in_fK -- |y| ≤ b_bound
    linarith [abs_le.mp h_abs] -- 从 |y| ≤ b 得到 -b ≤ y

  -- 证明 5. "因 f(K) 是闭集，故 M, m ∈ f(K)。"
  -- (我们使用步骤 2 中新增的 `closed_bounded_contains_sup/inf` 引理)
  have h_sup_in_set :=
    closed_bounded_contains_sup (f '' K) h_fK_nonempty h_fK_isClosed h_fK_bdd_upper
  have h_inf_in_set :=
    closed_bounded_contains_inf (f '' K) h_fK_nonempty h_fK_isClosed h_fK_bdd_lower

  -- "解包" 结果
  rcases h_sup_in_set with ⟨M, hM_is_sup, hM_in_fK⟩
  rcases h_inf_in_set with ⟨m, hm_is_inf, hm_in_fK⟩

  -- 证明 6. "存在 x₀, x₁ ∈ K 使得 f(x₀) = m 和 f(x₁) = M。"
  -- `hM_in_fK` 的意思是 `M ∈ f '' K`
  -- `f '' K` 的定义是 `{ y | ∃ x ∈ K, f x = y }`
  -- 所以，`M ∈ f '' K` 意味着 `∃ x₁, x₁ ∈ K ∧ f x₁ = M`
  rcases hM_in_fK with ⟨x₁, hx₁_in_K, hfx₁_eq_M⟩
  rcases hm_in_fK with ⟨x₀, hx₀_in_K, hfx₀_eq_m⟩

  -- 证明 7. "从...即 f 在 K 上达到最大值和最小值。"
  -- 我们的目标是：∃ (x₀ : ℝ) (hx₀ : x₀ ∈ K) (x₁ : ℝ) (hx₁ : x₁ ∈ K), ...
  -- 我们已经找到了 x₀, hx₀_in_K, x₁, hx₁_in_K，现在 `use` 它们
  use x₀, hx₀_in_K, x₁, hx₁_in_K

  -- 剩下的目标：∀ (x : ℝ), (hx : x ∈ K) → (f x₀ ≤ f x) ∧ (f x ≤ f x₁)
  intro x hx_in_K

  -- 把 f x₀ 换成 m, f x₁ 换成 M
  rw [hfx₀_eq_m, hfx₁_eq_M]

  -- 目标变为：(m ≤ f x) ∧ (f x ≤ M)
  -- 这正是 m 和 M 作为下确界/上确界的定义！

  -- 证明 `m ≤ f x`
  have h_fx_in_fK : f x ∈ f '' K := by use x, hx_in_K
  have h_m_le_fx : m ≤ f x := by
    exact hm_is_inf.left (f x) h_fx_in_fK -- m 是 f '' K 的下界

  -- 证明 `f x ≤ M`
  have h_fx_le_M : f x ≤ M := by
    exact hM_is_sup.left (f x) h_fx_in_fK -- M 是 f '' K 的上界

  -- 把两个证明合在一起
  exact ⟨h_m_le_fx, h_fx_le_M⟩
