theory Layout
  imports Model
begin

definition width :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "width p W i = (if i \<in> branches p then if i \<in> W then 3 else 2 else 1)"

definition address :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "address p W i = (\<Sum>j<i. width p W j)"

definition distance :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "distance p W i = (let t = destination p i in
    if i < t then (\<Sum>j\<in>{Suc i..<t}. width p W j)
    else (\<Sum>j\<in>{t..<Suc i}. width p W j))"

definition fits :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "fits p W i bits \<longleftrightarrow>
    (if i < destination p i then distance p W i < 2 ^ (bits - 1)
     else distance p W i \<le> 2 ^ (bits - 1))"

definition displacement :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> int" where
  "displacement p W i = int (address p W (destination p i)) - int (address p W (Suc i))"

definition valid :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> bool" where
  "valid p W \<longleftrightarrow> W \<subseteq> branches p \<and>
    (\<forall>i\<in>branches p. fits p W i (if i \<in> W then 16 else 8))"

lemma width_positive: "0 < width p W i"
  by (simp add: width_def)

lemma width_code [code]:
  "width p W i = (if i < length p \<and> target (p ! i) \<noteq> None then if i \<in> W then 3 else 2 else 1)"
  by (simp add: width_def branches_def)

definition sizes :: "nat instruction list \<Rightarrow> nat set \<Rightarrow> nat list" where
  "sizes p W = map (\<lambda>(i,op). if target op = None then 1 else if i \<in> W then 3 else 2)
    (zip [0..<length p] p)"

lemma sizes_length [simp]: "length (sizes p W) = length p"
  by (simp add: sizes_def)

lemma sizes_nth:
  "i < length p \<Longrightarrow> sizes p W ! i = width p W i"
  by (simp add: sizes_def width_def branches_def)

lemma width_mono: "W \<subseteq> V \<Longrightarrow> width p W i \<le> width p V i"
  by (auto simp: width_def)

lemma address_zero [simp]: "address p W 0 = 0"
  by (simp add: address_def)

lemma address_suc [simp]: "address p W (Suc i) = address p W i + width p W i"
  by (simp add: address_def)

lemma address_code [code]:
  "address p W i = sum_list (take i (sizes p W)) + (i - length p)"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases "i < length p")
    case True
    with Suc show ?thesis by (simp add: take_Suc_conv_app_nth sizes_nth)
  next
    case False
    with Suc show ?thesis by (simp add: width_def branches_def Suc_diff_le)
  qed
qed

lemma address_mono:
  "W \<subseteq> V \<Longrightarrow> address p W i \<le> address p V i"
  unfolding address_def by (intro sum_mono width_mono) assumption

lemma distance_mono:
  "W \<subseteq> V \<Longrightarrow> distance p W i \<le> distance p V i"
  unfolding distance_def Let_def
  by (auto simp only: if_True if_False intro!: sum_mono width_mono split: if_splits)

lemma fits_downward:
  "W \<subseteq> V \<Longrightarrow> fits p V i bits \<Longrightarrow> fits p W i bits"
  using distance_mono[of W V p i] unfolding fits_def by auto

lemma prefix_interval:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "a \<le> b"
  shows "(\<Sum>j<b. f j) = (\<Sum>j<a. f j) + (\<Sum>j\<in>{a..<b}. f j)"
proof -
  have disjoint: "{..<a} \<inter> {a..<b} = {}" by auto
  have "{..<b} = {..<a} \<union> {a..<b}" using assms by auto
  then show ?thesis by (simp add: sum.union_disjoint disjoint)
qed

lemma displacement_distance:
  "displacement p W i = (if i < destination p i then int (distance p W i) else - int (distance p W i))"
proof (cases "i < destination p i")
  case True
  then have le: "Suc i \<le> destination p i" by simp
  have eq: "int (\<Sum>j<destination p i. width p W j) =
    int (\<Sum>j<Suc i. width p W j) + int (\<Sum>j\<in>{Suc i..<destination p i}. width p W j)"
    using arg_cong[OF prefix_interval[OF le, of "width p W"], where f=int]
    by (simp only: of_nat_add)
  show ?thesis using eq
    by (simp only: displacement_def distance_def address_def Let_def True if_True; linarith)
next
  case False
  then have le: "destination p i \<le> Suc i" by simp
  have eq: "int (\<Sum>j<Suc i. width p W j) =
    int (\<Sum>j<destination p i. width p W j) + int (\<Sum>j\<in>{destination p i..<Suc i}. width p W j)"
    using arg_cong[OF prefix_interval[OF le, of "width p W"], where f=int]
    by (simp only: of_nat_add)
  show ?thesis using eq
    by (simp only: displacement_def distance_def address_def Let_def False if_False; linarith)
qed

lemma distance_code [code]:
  "distance p W i = (if i < destination p i
    then address p W (destination p i) - address p W (Suc i)
    else address p W (Suc i) - address p W (destination p i))"
  using displacement_distance[of p W i]
  unfolding displacement_def by (auto simp: of_nat_diff split: if_splits)

lemma fits_signed:
  "fits p W i bits \<longleftrightarrow>
    - int (2 ^ (bits - 1)) \<le> displacement p W i \<and>
    displacement p W i < int (2 ^ (bits - 1))"
proof -
  have positive: "(0::int) < int (2 ^ (bits - 1) :: nat)" by simp
  have nonnegative: "(0::int) \<le> int (distance p W i)" by simp
  have lower: "- int (2 ^ (bits - 1)) \<le> int (distance p W i)"
    using positive nonnegative by linarith
  have upper: "- int (distance p W i) < int (2 ^ (bits - 1))"
    using positive nonnegative by linarith
  show ?thesis
    by (cases "i < destination p i")
      (simp_all only: fits_def displacement_distance if_True if_False lower upper
        of_nat_less_iff of_nat_le_iff neg_le_iff_le simp_thms)
qed

lemma address_strict:
  assumes "i < j"
  shows "address p W i < address p W j"
proof -
  have pos: "0 < (\<Sum>k\<in>{i..<j}. width p W k)"
    using assms by (intro sum_pos2[where i=i]) (auto simp: width_positive)
  show ?thesis using prefix_interval[OF less_imp_le[OF assms], of "width p W"] pos
    by (simp add: address_def)
qed

end
