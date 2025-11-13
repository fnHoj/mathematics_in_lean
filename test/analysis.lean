import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image

-- 由于需要大量选择公理所以索性摆烂吧 😇
noncomputable section

-- 1. b 是实数集合 A 的上界的定义
def IsUpperBound(A : Set ℝ )(b : ℝ ): Prop :=
  ∀ a ∈ A, a ≤ b

-- b 是实数集合 A 的下界的定义
-- 切记：下界 (lower bound) 与下界 (the Nether) 毫无关联。
def IsLowerBound (A : Set ℝ) (b : ℝ) : Prop :=
  ∀ a ∈ A, b ≤ a

-- 2. s 是实数集合 A 的上确界的定义
def IsSup (A : Set ℝ )(s : ℝ ):
  Prop :=
  (IsUpperBound A s) ∧
  (∀ b, IsUpperBound A b → s ≤ b)

-- i 是实数集合 A 的下确界的定义
def IsInf (A : Set ℝ) (i : ℝ) : Prop :=
  (IsLowerBound A i) ∧
  (∀ b, IsLowerBound A b → b ≤ i)

-- 3. (完备性公理): 每一个非空的、有上界的实数集合都有一个最小上界。
axiom completeness (A : Set ℝ) (h : A.Nonempty) (h₁ : ∃ x, IsUpperBound A x) :
  ∃ s, IsSup A s

-- (完备性公理，下界版本)
axiom completeness_inf (A : Set ℝ) (h : A.Nonempty) (h₁ : ∃ x, IsLowerBound A x) :
  ∃ i, IsInf A i

-- 4. 设 s ∈ R 是集合 A ⊆ R 的一个上界。
-- 那么，s = sup A 当且仅当 ∀ ε > 0, ∃ a ∈ A 满足 s − ε < a 。
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

-- 同上但下界
theorem inf_iff (A : Set ℝ) (i : ℝ) (hlb : IsLowerBound A i) :
    IsInf A i ↔ ∀ ε > 0, ∃ a ∈ A, a < i + ε := by
  constructor
  · rintro ⟨-, hi⟩ ε εpos
    by_contra!
    linarith [hi _ this]
  · intro h
    use hlb
    intro b hlbb
    by_contra!
    rcases h (b - i) (by linarith) with ⟨a, aA, h'⟩
    simp at h'
    linarith [hlbb a aA]

-- 5. 数列x收敛于L的定义
def converges_to (x : ℕ → ℝ) (L : ℝ ):=
  ∀ ε > 0, ∃ N, ∀ n ≥  N, |x n - L| < ε

-- 6. 定理 : 如果单调上升的实数序列 {xn} 是有界的，那么 {xn} 收敛并且 limn→∞ xn = sup(xn)
-- Set.range x 是函数 x 所有输出值组成的集合
-- Monotone x 单调
-- Set.mem_range_self : f i ∈ Set.range f
theorem monotone_inc_bounded_converge (x : ℕ → ℝ) (hm : Monotone x) (hb : ∃ b, IsUpperBound (Set.range x) b) :
    ∃ s, IsSup (Set.range x) s ∧ converges_to x s := by
  obtain ⟨s, hs⟩ := completeness (Set.range x) ⟨x 0, 0, rfl⟩ hb
  use s, hs; intro ε εpos
  obtain ⟨_, ⟨N, rfl⟩, _⟩ := (sup_iff _ _ hs.left).mp hs ε εpos
  use N; intro n nge
  rw [abs_of_nonpos] <;> linarith [hm nge, hs.left (x n) ⟨n, rfl⟩]

-- 若极限存在则唯一
theorem limit_unique (h₀ : converges_to x l₀) (h₁ : converges_to x l₁) : l₀ = l₁ := by
  by_contra! h
  rw [← lt_or_lt_iff_ne] at h
  wlog h' : l₀ < l₁ generalizing l₀ l₁
  · exact this h₁ h₀ h.symm (h.resolve_left h')
  let ε := (l₁ - l₀) / 2
  have εpos : 0 < ε := half_pos (sub_pos.mpr h')
  rcases h₀ ε εpos with ⟨N₀, h₀⟩
  rcases h₁ ε εpos with ⟨N₁, h₁⟩
  specialize h₀ (max N₀ N₁) (le_max_left ..)
  specialize h₁ (max N₀ N₁) (le_max_right ..)
  simp_all [abs_lt, ε]; linarith

/--
某种夹逼：

对于序列 {lₙ}, {rₙ}，若：

- l 单调增，r 单调减
- ∀ n, lₙ < rₙ
- lim(n → ∞) (rₙ - lₙ) = 0

则 {lₙ}, {rₙ} 收敛于同一实数
-/
theorem converges_of_squeezes (l r : ℕ → ℝ)
      (monol : Monotone l) (monor : Monotone (-r ·))
      (ller : ∀ n, l n ≤ r n)
      (h : converges_to (fun n ↦ r n - l n) 0) :
    ∃ w, converges_to l w ∧ converges_to r w := by
  -- l 有上界
  have lub : ∃ b, IsUpperBound (Set.range l) b := by
    use r 0; rintro _ ⟨n, rfl⟩
    exact le_trans (ller n) (neg_le_neg_iff.mp (monor (Nat.zero_le n)))
  -- 由于 l 单调增，它收敛于其上确界 s
  rcases monotone_inc_bounded_converge l monol lub with ⟨s, hs, hs'⟩
  use s, hs'
  -- 证明 r 收敛于 s：
  -- 一方面，r 必须接近 l
  -- 另一方面，l 又死盯着 s 不放
  -- 这两者整合即可
  intro ε εpos
  rcases hs' ε εpos with ⟨N₀, h₀⟩
  rcases h ε εpos with ⟨N₁, h₁⟩
  use max N₀ N₁; intro n hn
  rw [abs_of_nonneg]
  · rcases max_le_iff.mp hn with ⟨nge₀, nge₁⟩
    specialize h₁ n nge₁
    simp [abs_lt] at h₁
    linarith [monol nge₀, ller n, hs.left (l n) ⟨n, rfl⟩]
  -- 支线任务：r n ≥ s
  -- 反证，若 s < r n 则必有某 l 会冲到 r 之上，与 lltr 矛盾
  by_contra! rlts
  rcases hs' (s - r n) (by linarith) with ⟨N₂, h₂⟩
  apply not_lt_of_le (ller (max n N₂))
  calc r (max n N₂)
    _ ≤ r n := by have := monor (le_max_left n N₂); simp at this; linarith
    _ < l N₂ := by linarith [abs_lt.mp (h₂ N₂ (le_refl N₂))]
    _ ≤ l (max n N₂) := monol (le_max_right n N₂)

-- 定义集合有界
-- 定义 3.3.3. 称一个集合 A ⊆ R 是有界的，若存在 M > 0 使得 ∀a ∈ A 都有 |a| ≤ M
-- 尽管是第三章的东西，但 2.5.1 一章居然要用！！☹️
def IsBound (A : Set ℝ) (b : ℝ) : Prop :=
  ∀ a ∈ A, |a| ≤ b

-- 包含于有界集合 K 的序列 {xₙ} 必有界
lemma IsBound.range_bounded (h : IsBound K b) {x : ℕ → ℝ} (hx : ∀ n, x n ∈ K) :
    IsBound (Set.range x) b := by
  rintro _ ⟨n, rfl⟩; exact h (x n) (hx n)

-- 这**一整个** namespace 都是定理 2.5.5 的预备定理。
-- 书上可以只写半页纸。但我不行。😖
-- 想跳过可以直接把这个 namespace 折叠起来。。。
namespace bolzano_weierstrass

-- 闭区间 [l, r] 是否包含序列 {xₙ} 中无限多元素？
def InfiniteBetween (x : ℕ → ℝ) (l r : ℝ) : Prop :=
  ∀ N, ∃ n ≥ N, l ≤ x n ∧ x n ≤ r

-- 包含了 {xₙ} 中无限多元素的闭区间，附带其中任取的一个元素
structure sub_interval (x : ℕ → ℝ) where
  l : ℝ
  r : ℝ
  infinite : InfiniteBetween x l r
  idx : ℕ
  idx_within : l ≤ x idx ∧ x idx ≤ r

abbrev sub_interval.len (I : sub_interval x) := I.r - I.l

-- 区间长度必须非负 (l ≤ r)
@[simp]
theorem sub_interval.ller (I : sub_interval x) : I.l ≤ I.r := by rcases I.infinite 0; linarith
@[simp]
theorem sub_interval.len_nonneg (I : sub_interval x) : 0 ≤ I.len := by simp

-- 区间中任取一个索引大于 n 的元素
def after (l r : ℝ) (infinite : InfiniteBetween x l r) (n : ℕ) : sub_interval x where
  l := l
  r := r
  infinite := infinite
  idx := (infinite (n + 1)).choose
  idx_within := (infinite (n + 1)).choose_spec.right

theorem idx_increases_of_after (l r : ℝ)
      (infinite : InfiniteBetween x l r) (n : ℕ) :
    n < (after l r infinite n).idx := by
  simp [after]
  exact infinite (n + 1) |>.choose_spec |>.left

-- 如果一个区间包含无数元素，
-- 把它对半分，两段当中必有至少一段也有无数元素
def sub_interval.halve (I₀ : sub_interval x) : sub_interval x := by
  let mid := (I₀.l + I₀.r) / 2
  have : ∃ (choice : Bool), if choice
      then InfiniteBetween x mid I₀.r
      else InfiniteBetween x I₀.l mid := by
    by_contra!
    simp [InfiniteBetween, and_comm (a := mid ≤ _)] at this
    rcases this with ⟨⟨N₀, h₀⟩, ⟨N₁, h₁⟩⟩
    rcases I₀.infinite (max N₀ N₁) with ⟨N, hN, xNge, xNle⟩
    rcases max_le_iff.mp hN with ⟨Nge₀, Nge₁⟩
    linarith [h₀ N Nge₀ xNge, h₁ N Nge₁ xNle]
  have h := this.choose_spec
  by_cases choice : this.choose <;> simp [choice] at h
  · exact after mid I₀.r h I₀.idx
  · exact after I₀.l mid h I₀.idx

@[simp]
theorem sub_interval.idx_increases_of_halve (I₀ : sub_interval x) :
    I₀.idx < I₀.halve.idx := by
  simp [halve]
  split_ifs with choice <;>
  · apply Nat.lt_of_add_one_le
    apply idx_increases_of_after

@[simp]
theorem sub_interval.l_increases_of_halve (I₀ : sub_interval x) :
    I₀.l ≤ I₀.halve.l := by
  simp [halve]
  split_ifs with choice <;> simp [after]
  linarith [I₀.ller]

@[simp]
theorem sub_interval.r_decreases_of_halve (I₀ : sub_interval x) :
    I₀.halve.r ≤ I₀.r := by
  simp [halve]
  split_ifs with choice <;> simp [after]
  linarith [I₀.ller]

@[simp]
theorem sub_interval.len_halves_of_halve (I₀ : sub_interval x) :
    I₀.halve.len = I₀.len / 2 := by
  simp [halve]
  split_ifs with choice <;>
    (simp [after, len]; linarith)

-- 按之前的方法重复折半 n 遍，得到闭区间套
@[simp]
def sub_interval.narrow (I₀ : sub_interval x) : ℕ → sub_interval x
  | 0 => I₀
  | n + 1 => I₀.narrow n |>.halve

def sub_interval.seq (I₀ : sub_interval x) : ℕ → ℕ := (I₀.narrow · |>.idx)
def sub_interval.ls (I₀ : sub_interval x) : ℕ → ℝ := (I₀.narrow · |>.l)
def sub_interval.rs (I₀ : sub_interval x) : ℕ → ℝ := (I₀.narrow · |>.r)
def sub_interval.lens (I₀ : sub_interval x) : ℕ → ℝ := (I₀.narrow · |>.len)

-- 闭区间套可以得出子序列，即书中 a_(nₖ)
theorem sub_interval.seq_strict_mono (I₀ : sub_interval x) :
    StrictMono I₀.seq := by
  intro a b altb
  rcases Nat.exists_eq_add_of_lt altb with ⟨d, rfl⟩
  induction d with
  | zero => simp [seq, narrow, idx_increases_of_halve]
  | succ d ih =>
    specialize ih (by omega)
    simp_all [← add_assoc]
    apply lt_trans ih
    simp [seq, narrow, idx_increases_of_halve]

theorem sub_interval.ls_mono (I₀ : sub_interval x) : Monotone I₀.ls := by
  intro a b aleb
  rcases Nat.exists_eq_add_of_le aleb with ⟨d, rfl⟩
  induction d with
  | zero => rfl
  | succ d ih =>
    specialize ih (Nat.le_add_right ..)
    apply le_trans ih
    simp [← add_assoc, ls, narrow]

theorem sub_interval.rs_decreasing (I₀ : sub_interval x) : Monotone (-I₀.rs ·) := by
  intro a b aleb
  rcases Nat.exists_eq_add_of_le aleb with ⟨d, rfl⟩
  induction d with
  | zero => rfl
  | succ d ih =>
    specialize ih (Nat.le_add_right ..)
    simp_all [← add_assoc, rs]
    exact le_trans (r_decreases_of_halve ..) ih

theorem sub_interval.lens_eq (I₀ : sub_interval x) : I₀.lens = (I₀.len / 2 ^ ·) := by
  ext n
  induction n with
  | zero => simp [lens]
  | succ n ih => simp_all [lens, div_div, pow_succ]

-- 从第 4 行开始都是在手搓阿基米德公理
theorem sub_interval.len_converges (I₀ : sub_interval x) : converges_to I₀.lens 0 := by
  rw [lens_eq]
  intro ε εpos
  simp
  rcases exists_nat_gt (I₀.len / ε) with ⟨k, hk⟩
  use k.log2 + 1
  intro n hn
  apply Nat.lt_of_add_one_le at hn
  rw [abs_of_nonneg (div_nonneg I₀.len_nonneg (pow_nonneg zero_le_two _))]
  rw [div_lt_comm₀ (pow_pos zero_lt_two n) εpos]
  have klt : k < 2 ^ n := by
    refine (Nat.log2_lt ?_).mp hn
    rintro rfl
    simp [div_neg_iff, εpos, lt_asymm εpos, not_lt_of_le I₀.len_nonneg] at hk
  calc
    I₀.len / ε < ↑k := hk
    (k : ℝ) < (2 ^ n : ℕ) := Nat.cast_lt.mpr klt
    (2 ^ n : ℕ) = (2 : ℝ) ^ n := Nat.cast_pow ..

-- 证明这个子序列收敛
theorem sub_interval.subseq_converges (I₀ : sub_interval x) :
    ∃ w, converges_to (x ∘ I₀.seq) w := by
  obtain ⟨w, wl, wr⟩ :=
    converges_of_squeezes
      I₀.ls I₀.rs
      I₀.ls_mono I₀.rs_decreasing
      (I₀.narrow · |>.ller)
      I₀.len_converges
  use w; intro ε εpos
  rcases wl ε εpos with ⟨Nl, hl⟩
  rcases wr ε εpos with ⟨Nr, hr⟩
  use max Nl Nr; intro n nge
  rcases max_le_iff.mp nge with ⟨ngeNl, ngeNr⟩
  specialize hl n ngeNl
  specialize hr n ngeNr
  simp_all [abs_lt, ls, rs, seq]
  constructor <;> linarith [(I₀.narrow n).idx_within]

end bolzano_weierstrass

-- 终于！！
theorem bolzano_weierstrass {x : ℕ → ℝ} (hbdd : ∃ b, IsBound (Set.range x) b) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ l, converges_to (x ∘ φ) l := by
  rcases hbdd with ⟨b, hbdd⟩
  let I₀ : bolzano_weierstrass.sub_interval x :=
    ⟨-b, b, fun N ↦ ⟨N, le_refl N, abs_le.mp (hbdd (x N) ⟨N, rfl⟩)⟩, 0, abs_le.mp (hbdd (x 0) ⟨0, rfl⟩)⟩
  use I₀.seq, I₀.seq_strict_mono
  exact I₀.subseq_converges
-- 定理 2.5.5 圆满落幕，前前后后将近 200 行。🥳

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
-- ∀ n ∈ N, an ≠ x
-- x = lim an

-- "存在 A 中的序列 a_n 满足: 1. (∀n, a_n ≠ x) ∧ 2. (a_n → x)"
def HasConvergentSeqNeq (x : ℝ) (A : Set ℝ) : Prop :=
  ∃ (u : ℕ → ℝ), -- 存在一个序列 u
    (∀ n, u n ∈ A) ∧
    (∀ n, u n ≠ x) ∧
    (converges_to u x)

theorem limit_point_iff_seq (x : ℝ) (A : Set ℝ) :
    IsLimitPoint x A ↔ HasConvergentSeqNeq x A := by
  -- 且让我用个 one-liner 解决 mpr
  symm; use fun ⟨u, uA, unx, hu⟩ ↦ (match hu · · with | ⟨N, hN⟩ => ⟨u N, hN N (le_refl N), uA N, unx N⟩)
  intro h_limit_point
  -- 既然说，对任意 ε 都有 y 满足那啥，
  -- 那我让这个 ε 依次取 1/1, 1/2, 1/3, 1/4, ...
  -- 然后把每个 ε 对应的 y 挑出来组个数列 u 就是了
  have h (n : ℕ) := h_limit_point (n + 1)⁻¹ Nat.inv_pos_of_nat
  let u : ℕ → ℝ := (h · |>.choose)
  use u
  -- 前两个相当显然先 one-liner 掉
  refine and_assoc.mp ⟨by constructor <;> (intro n; have := (h n).choose_spec; tauto), ?_⟩
  intro ε εpos
  -- 艰难曲折地求 N = ⌈1 / ε⌉ + 1
  rcases (-ε⁻¹).exists_floor with ⟨(N | N), Nle, hN⟩ <;> simp_all
  · linarith [inv_pos.mpr εpos]
  -- 结束。
  use N; intro n nge
  apply lt_of_lt_of_le (h n).choose_spec.left
  rw [inv_le_comm₀] <;> linarith [Nat.cast_le (α := ℝ).mpr nge]

/--
给定序列 {xₙ} 和子序列 {(x ∘ φ)ₙ}，
在子序列挑第一个元素，满足：
- i ≥ start（它在子序列中至少是第 start 个）
- φ i ≥ n（它在原序列中至少是第 n 个）
-/
def first_since_after {φ : ℕ → ℕ} (h : StrictMono φ) (start n : ℕ) : ℕ :=
  if n ≤ φ start then start else first_since_after h (start + 1) n
termination_by n - φ start
decreasing_by exact Nat.sub_lt_sub_left (by omega) (h (Nat.lt_add_one _))

def start_le_first_since_after (h : StrictMono φ) (start n : ℕ) :
    start ≤ first_since_after h start n := by
  by_cases hn : n ≤ φ start <;> (rw [first_since_after]; simp [hn])
  apply le_of_lt ∘ Nat.lt_of_add_one_le
  apply start_le_first_since_after
termination_by n - φ start
decreasing_by exact Nat.sub_lt_sub_left (by omega) (h (Nat.lt_add_one _))

def n_le_first_since_after (h : StrictMono φ) (start n : ℕ) :
    n ≤ φ (first_since_after h start n) := by
  by_cases hn : n ≤ φ start <;> (rw [first_since_after]; simp [hn])
  apply n_le_first_since_after
termination_by n - φ start
decreasing_by exact Nat.sub_lt_sub_left (by omega) (h (Nat.lt_add_one _))

-- 柯西序列的定义
-- "一个序列 {x_n} 是柯西序列，若 ∀ε > 0, ∃N, ∀m, n ≥ N, |x_m - x_n| < ε"

def IsCauchy (x : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |x m - x n| < ε

-- 柯西序列必有界
lemma bounded_of_cauchy {x : ℕ → ℝ} (h : IsCauchy x) : ∃ b, IsBound (Set.range x) b := by
  rcases h 1 zero_lt_one with ⟨N, hN⟩
  by_cases Nz : N = 0
  · simp [Nz] at *
    use |x 0| + 1
    rintro _ ⟨n, rfl⟩
    linarith [abs_sub_abs_le_abs_sub (x n) (x 0), hN n 0]
  have : Finset.range N |>.Nonempty := ⟨0, Finset.mem_range.mpr <| Nat.pos_of_ne_zero Nz⟩
  use max (Finset.range N |>.sup' this (|x ·|)) (|x N| + 1)
  rintro _ ⟨n, rfl⟩
  by_cases hn : n < N
  · apply le_max_of_le_left
    apply Finset.le_sup' (|x ·|)
    exact Finset.mem_range.mpr hn
  · simp at hn
    apply le_max_of_le_right
    linarith [abs_sub_abs_le_abs_sub (x n) (x N), hN n hn N (le_refl N)]

-- 任一柯西序列 {xₙ}，若它有一个收敛于 l 的子序列 {(x ∘ φ)ₙ}，
-- 则整个 {xₙ} 也收敛于 l。
theorem IsCauchy.converges_of_sub_converges (h_cauchy : IsCauchy x)
      {φ : ℕ → ℕ} (φmono : StrictMono φ)
      (hl : converges_to (x ∘ φ) l) :
    converges_to x l := by
  intro ε εpos
  rcases h_cauchy (ε / 2) (half_pos εpos) with ⟨N₀, h₀⟩
  rcases hl (ε / 2) (half_pos εpos) with ⟨N₁, h₁⟩
  let N := first_since_after φmono N₁ N₀
  use φ N; intro n nge
  specialize h₀ n ?_ (φ N) ?_; repeat
    linarith [n_le_first_since_after φmono N₁ N₀]
  specialize h₁ N ?_
  · linarith [start_le_first_since_after φmono N₁ N₀]
  simp_all [abs_lt]
  constructor <;> linarith

-- 柯西序列完全等价于序列收敛！！（至少实数上如此）
theorem cauchy_iff_converges : IsCauchy x ↔ ∃ l, converges_to x l := by
  constructor
  · intro h_cauchy
    -- 因为柯西序列都有界，根据这个 BW 定理知道它必有收敛的子序列
    rcases bolzano_weierstrass (bounded_of_cauchy h_cauchy) with ⟨φ, φmono, l, hl⟩
    use l, h_cauchy.converges_of_sub_converges φmono hl
  · rintro ⟨l, h_converges⟩ ε εpos
    rcases h_converges (ε / 2) (half_pos εpos) with ⟨N, hN⟩
    use N; intro m mge n nge
    have := hN m mge; have := hN n nge
    simp [abs_lt] at *; constructor <;> linarith

-- 定义 3.2.7. 称集合 F ⊆ R 为闭集，若其包含其所有极限点。
def IsClosedSet (F : Set ℝ) : Prop :=
  ∀ (x : ℝ), IsLimitPoint x F → x ∈ F

-- 对于闭集 F，有 x ∈ F 当且仅当 x 是 F 的“不严谨极限点”
theorem IsClosedSet.mem_iff_limit_point_1 (h : IsClosedSet F) :
    x ∈ F ↔ IsLimitPoint1 x F := by
  constructor
  · intro xF ε εpos h_empty
    rw [Set.eq_empty_iff_forall_notMem] at h_empty
    refine h_empty x ⟨?_, xF⟩
    simpa [V_ε]
  intro hx
  by_contra!
  have : ¬IsLimitPoint x F := this ∘ h x
  simp [IsLimitPoint] at this
  rcases this with ⟨ε, εpos, hε⟩
  specialize hx ε εpos
  apply hx
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x' ⟨xV, xF⟩
  simp_all [hε x' xV xF]

-- 定理 3.2.8. 一个集合 F ⊆ R 是闭的，当且仅当包含在 F 中的每个 Cauchy 序列都有一个极限，
-- 且该极限也是 F 的一个元素。

-- "包含在 F 中的每个 Cauchy 序列都有一个极限，且该极限也是 F 的一个元素。"
def IsSequentiallyComplete (F : Set ℝ) : Prop :=
  ∀ (u : ℕ → ℝ), -- "对于 F 中的每个..."
    (∀ n, u n ∈ F) → -- "...序列 u..."
    (IsCauchy u) → -- "...如果 u 是 Cauchy 序列..."
      ∃ (l : ℝ), -- "...那么存在一个极限 l..."
        (converges_to u l) ∧ (l ∈ F) -- "...u 收敛到 l，并且 l 在 F 中。"

-- 任何 IsSequentiallyComplete 的集合 F，
-- 如果包含于 F 的数列 {uₙ} 它收敛于 l，
-- 则 l ∈ F。
theorem IsSequentiallyComplete.mem_of_limit
      (h_sc : IsSequentiallyComplete F)
      (uF : ∀ n, u n ∈ F)
      (hl : converges_to u l) :
    l ∈ F := by
  rcases h_sc u uF (cauchy_iff_converges.mpr ⟨l, hl⟩) with ⟨l, hl', lF⟩
  simp_all [limit_unique hl hl']

-- "一个集合 F ⊆ R 是闭的，当且仅当 [上面定义的 IsSequentiallyComplete]"
theorem closed_iff_sequentially_complete (F : Set ℝ) :
    IsClosedSet F ↔ IsSequentiallyComplete F := by
  constructor
  · intro h_closed u uF hu
    rw [cauchy_iff_converges] at hu
    rcases hu with ⟨l, hl⟩
    use l, hl
    rw [h_closed.mem_iff_limit_point_1]
    intro ε εpos
    simp [← Set.not_nonempty_iff_eq_empty]
    rcases hl ε εpos with ⟨N, hN⟩
    use u N, hN N (le_refl N), uF N
  · intro h_sc x hx
    rw [limit_point_iff_seq] at hx
    rcases hx with ⟨u, uF, -, u_converges⟩
    exact h_sc.mem_of_limit uF u_converges

-- 定义紧集
-- 定义 3.3.1. 称集合 K ⊆ R 是紧的，若其中的每个序列都有一个收敛于 K 中极限的子序列。
def SeqCompact (K : Set ℝ) : Prop :=
  ∀ (u : ℕ → ℝ), (∀ n, u n ∈ K) →
    ∃ l ∈ K,
      ∃ (φ : ℕ → ℕ), (StrictMono φ) ∧ (converges_to (u ∘ φ) l)

-- 定理 3.3.4 (Heine-Borel 定理). 一个集合 K ⊆ ℝ 是紧的，当且仅当它是闭的且有界的。
theorem Heine_Borel (K : Set ℝ) :
    SeqCompact K ↔ (∃ b, IsBound K b) ∧ (IsClosedSet K) := by
  constructor; swap
  · rintro ⟨⟨b, Kbdd⟩, hK⟩ u uK
    -- 又是 BW 定理！{uₙ} 有个子序列，收敛于 F 中元素
    rcases bolzano_weierstrass ⟨b, Kbdd.range_bounded uK⟩ with ⟨φ, monoφ, l, hφ⟩
    rw [closed_iff_sequentially_complete] at hK
    use l, hK.mem_of_limit (uK <| φ ·) hφ, φ
  intro h
  constructor; swap
  · rw [closed_iff_sequentially_complete]
    intro u uK hu
    rcases h u uK with ⟨l, lK, φ, φmono, hφ⟩
    use l, hu.converges_of_sub_converges φmono hφ
  simp [IsBound]
  -- 反证！假设 K 无界。
  -- 既然 K 是紧的，那么里面所有数列必有收敛的子序列。
  -- 因此，构造一个包含于 K 且不知收敛的 {uₙ} 即可构造矛盾。
  -- 我令 uₙ = (K 中任取一个绝对值大于 n 的数)。
  -- 由于假设了 K 无界，这么做完全合法。
  by_contra! nbdd
  let u (n : ℕ) : ℝ := nbdd n |>.choose
  have uK : ∀ n, u n ∈ K := (nbdd · |>.choose_spec.left)
  have ult : ∀ n, n < |u n| := (nbdd · |>.choose_spec.right)
  -- K 是紧的，故 {uₙ} 有一个收敛的子序列 {(u ∘ φ)ₙ}。
  -- 证明 {(u ∘ φ)ₙ} 不知收敛即可构造矛盾。
  rcases h u uK with ⟨l, -, φ, φmono, hφ⟩
  absurd hφ
  simp [converges_to]
  use 1, zero_lt_one; intro N
  let n' := exists_nat_ge (|l| + 1) |>.choose
  have n'ge : |l| + 1 ≤ n' := exists_nat_ge (|l| + 1) |>.choose_spec
  let n := first_since_after φmono N n'
  have : (n' : ℝ) ≤ φ n := Nat.cast_le.mpr (n_le_first_since_after φmono N n')
  use n, start_le_first_since_after ..
  calc
    1 ≤ |u (φ n)| - |l| := by linarith [ult (φ n)]
    _ ≤ |u (φ n) - l| := abs_sub_abs_le_abs_sub ..

-- 定义 4.3.1.

-- 在 c 点连续
-- 称一个函数 f : A → R 在点 c ∈ A 处连续，若 ∀ ε > 0, ∃ δ > 0，使得：
-- 每当 |x − c| < δ (且 x ∈ A) 时，
-- 就有 |f(x) − f(c)| < ε。
def IsContinuousAt (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, |x - c| < δ → |f x - f c| < ε

--连续函数的定义
--如果 f 在定义域 A 中的每一点都连续，那么我们说 f 在 A 上连续。
def IsContinuousOn (f : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ c ∈ A, (IsContinuousAt f A c)

-- 连续性的 "序列" 定义
-- "f 在 c 点（在 A 集合内）是序列连续的"
def IsSeqContinuousAt (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) : Prop :=
  ∀ (u : ℕ → ℝ), -- "对于任意序列 u..."
    (∀ n, u n ∈ A) → -- "...如果 u 在 A 中..."
    (converges_to u c) → -- "...并且 u 收敛到 c..."
    (converges_to (f ∘ u) (f c)) -- "...那么 f(u) 就收敛到 f(c)"

theorem continuous_at_iff_seq_continuous_at
      (f : ℝ → ℝ) (A : Set ℝ) (c : ℝ) :
    IsContinuousAt f A c ↔ IsSeqContinuousAt f A c := by
  constructor
  · intro h u uA hu ε εpos
    -- 证明 f(u) 收敛于 f(c)
    -- 对任意 ε，必有 δ 使得 ∀ x ∈ c ± δ, f(x) ∈ f(c) ± ε（由于 f 连续）
    -- 又有 N 使得 ∀ n ≥ N, u n ∈ c ± δ（由于 u 收敛）
    -- 把这俩一拼接：∀ n ≥ N, f(uₙ) ∈ f(c) ± ε。得证！
    rcases h ε εpos with ⟨δ, δpos, hδ⟩
    rcases hu δ δpos with ⟨N, hN⟩
    use N; intro n nge
    exact hδ (u n) (uA n) (hN n nge)
  · intro h ε εpos
    -- 证明 f 在 c 上连续
    -- 反证！把 ε-δ 那套反过来说：
    -- 任意小的 (c ± δ) ∩ A 当中，总归有那么个调皮的 x 让 f(x) 落在 f(c) ± ε 之外
    by_contra! h'
    -- 然后，我分别在 c ± 1, c ± 1/2, c ± 1/3, c ± 1/4... 当中
    -- 各自拎出一个调皮的 x 组成数列 {uₙ}
    -- 显然 {uₙ} 收敛，而且每个元素 uₙ 都：
    -- - 属于 A
    -- - 在 c ± 1/(n+1) 之中
    -- - 调皮，即 f(uₙ) 在 f(c) ± ε 之外
    replace h' := fun n : ℕ ↦ h' (n + 1)⁻¹ Nat.inv_pos_of_nat
    let u (n : ℕ) : ℝ := h' n |>.choose
    have uA n : u n ∈ A := h' n |>.choose_spec.left
    have ult n : |u n - c| < _ := h' n |>.choose_spec.right.left
    have fge n : ε ≤ |f (u n) - f c| := h' n |>.choose_spec.right.right
    have hu : converges_to u c := by
      intro ε εpos
      rcases (-ε⁻¹).exists_floor with ⟨(N | N), Nle, hN⟩ <;> simp_all
      · linarith [inv_pos.mpr εpos]
      use N; intro n nge
      apply lt_of_lt_of_le (ult n)
      rw [inv_le_comm₀] <;> linarith [Nat.cast_le (α := ℝ).mpr nge]
    -- 我们假设了 f 在 c 点满足 IsSeqContinuousAt。
    -- 所以说，既然 {uₙ} 收敛于 c，f(uₙ) 也必然收敛于 f(c)。
    -- 可问题是，{uₙ} 是个处处调皮的序列。
    -- 所以，{uₙ} 偏偏使得 f(uₙ) 不收敛于 f(c)。
    -- 这个弯弯绕绕的反证终于产生矛盾了。
    absurd h u uA hu
    simp [converges_to]
    use ε, εpos
    intro N
    use N, le_refl N, fge N

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
  have h_x_in_K : ∀ n, x n ∈ K := fun n => (hx_spec n).left
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


-- 下面开始形式化极值定理

-- 2. 新增：证明的关键引理 (暂时 sorry)
-- "一个闭合且有界的非空集合，其确界在集合内"
-- ------------------------------------------------

theorem closed_bounded_contains_sup (A : Set ℝ)
      (h_nonempty : A.Nonempty)
      (h_closed : IsClosedSet A)
      (h_bdd : ∃ b, IsUpperBound A b) :
    ∃ s, IsSup A s ∧ s ∈ A := by
  -- 首先我们有完备性公理，所以目标只剩 s ∈ A
  rcases completeness A h_nonempty h_bdd with ⟨s, hs⟩
  use s, hs
  -- 元素属于闭集，当且仅当它是“不严谨极限点”
  -- 根据 sup_iff，上确界就是不严谨极限点。
  rw [h_closed.mem_iff_limit_point_1]
  rintro ε εpos
  rw [← Set.nonempty_iff_ne_empty]
  rcases sup_iff A s hs.left |>.mp hs ε εpos with ⟨a, aA, ha⟩
  use a, ?_, aA
  simp [V_ε, abs_lt]
  constructor <;> linarith [hs.left a aA]

theorem closed_bounded_contains_inf (A : Set ℝ)
      (h_nonempty : A.Nonempty)
      (h_closed : IsClosedSet A)
      (h_bdd : ∃ b, IsLowerBound A b) :
    ∃ i, IsInf A i ∧ i ∈ A := by
  rcases completeness_inf A h_nonempty h_bdd with ⟨i, hi⟩
  use i, hi
  rw [h_closed.mem_iff_limit_point_1]
  rintro ε εpos
  rw [← Set.nonempty_iff_ne_empty]
  rcases inf_iff A i hi.left |>.mp hi ε εpos with ⟨a, aA, ha⟩
  use a, ?_, aA
  simp [V_ε, abs_lt]
  constructor <;> linarith [hi.left a aA]

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
    ∃ x₀ ∈ K, ∃ x₁ ∈ K,
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

end
