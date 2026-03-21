theory Top1_Ch4
  imports Top1_Ch3
begin

section \<open>\<S>30 The Countability Axioms\<close>

(** Basic predicate for countable sets (to avoid extra session dependencies). **)
definition top1_countable :: "'a set \<Rightarrow> bool" where
  "top1_countable S \<longleftrightarrow> (\<exists>f::'a \<Rightarrow> nat. inj_on f S)"

lemma top1_countable_iff_countable:
  "top1_countable S \<longleftrightarrow> countable S"
  by (simp only: top1_countable_def countable_def)

lemma top1_countable_subset:
  assumes hS: "top1_countable S"
  assumes hAS: "A \<subseteq> S"
  shows "top1_countable A"
proof -
  obtain f :: "'a \<Rightarrow> nat" where hf: "inj_on f S"
    using hS unfolding top1_countable_def by blast
  have hA: "inj_on f A"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix x y
    assume hxA: "x \<in> A" and hyA: "y \<in> A"
    assume hfx: "f x = f y"
    have hxS: "x \<in> S" using hAS hxA by blast
    have hyS: "y \<in> S" using hAS hyA by blast
    show "x = y"
      using hf hxS hyS hfx unfolding inj_on_def by blast
  qed
  show ?thesis
    unfolding top1_countable_def
    by (rule exI[where x=f], rule hA)
qed

(** Images of countable sets are countable (in the sense of \<open>top1_countable\<close>). **)
lemma top1_countable_image:
  assumes hS: "top1_countable S"
  shows "top1_countable (f ` S)"
proof -
  obtain g :: "'a \<Rightarrow> nat" where hg: "inj_on g S"
    using hS unfolding top1_countable_def by blast

  define rep where "rep y = (SOME x. x \<in> S \<and> f x = y)" for y

  have rep_spec: "\<forall>y\<in>f ` S. rep y \<in> S \<and> f (rep y) = y"
  proof (intro ballI)
    fix y assume hy: "y \<in> f ` S"
    obtain x where hxS: "x \<in> S" and hyfx: "y = f x"
      using hy by blast
    have ex: "\<exists>x. x \<in> S \<and> f x = y"
      using hxS hyfx by blast
    have hrep: "rep y \<in> S \<and> f (rep y) = y"
      unfolding rep_def
      by (rule someI_ex[OF ex])
    show "rep y \<in> S \<and> f (rep y) = y"
      by (rule hrep)
  qed

  define h where "h y = g (rep y)" for y

  have hinj: "inj_on h (f ` S)"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix y1 y2
    assume hy1: "y1 \<in> f ` S" and hy2: "y2 \<in> f ` S"
    assume hh: "h y1 = h y2"
    have hr1: "rep y1 \<in> S" and hf1: "f (rep y1) = y1"
      using rep_spec hy1 by blast+
    have hr2: "rep y2 \<in> S" and hf2: "f (rep y2) = y2"
      using rep_spec hy2 by blast+
    have hg_eq: "g (rep y1) = g (rep y2)"
      using hh unfolding h_def by simp
    have hrep_eq: "rep y1 = rep y2"
      using hg hr1 hr2 hg_eq unfolding inj_on_def by blast
    have "y1 = f (rep y1)" using hf1 by simp
    also have "... = f (rep y2)" using hrep_eq by simp
    also have "... = y2" using hf2 by simp
    finally show "y1 = y2" .
  qed

  show ?thesis
    unfolding top1_countable_def
    by (rule exI[where x=h], rule hinj)
qed

(** Helper: folding functional updates does not affect an index not updated by the list. **)
lemma fold_fun_update_notin_fst:
  fixes i :: 'i
  fixes l :: "('i \<times> 'a) list"
  fixes f0 :: "'i \<Rightarrow> 'a"
  assumes hi: "i \<notin> set (map fst l)"
  shows "(foldr (\<lambda>p f. f (fst p := snd p)) l f0) i = f0 i"
  using hi
proof (induct l arbitrary: f0)
  case Nil
  show ?case
    by simp
next
  case (Cons p ps)
  have hi_ne: "i \<noteq> fst p"
    using Cons.prems by simp
  have hi_ps: "i \<notin> set (map fst ps)"
    using Cons.prems by simp
  have "(foldr (\<lambda>p f. f (fst p := snd p)) (p # ps) f0) i =
      (fun_upd (foldr (\<lambda>p f. f (fst p := snd p)) ps f0) (fst p) (snd p)) i"
    by simp
  also have "... = (foldr (\<lambda>p f. f (fst p := snd p)) ps f0) i"
    using hi_ne by simp
  also have "... = f0 i"
    by (rule Cons.hyps[OF hi_ps])
  finally show ?case .
qed

(** A concrete injective encoding of pairs of naturals, used to build countability arguments. **)
definition top1_pair_code :: "nat \<times> nat \<Rightarrow> nat" where
  "top1_pair_code p = (2 ^ fst p) * (2 * snd p + 1)"

lemma top1_pair_code_inj: "inj_on top1_pair_code (UNIV::(nat \<times> nat) set)"
  unfolding inj_on_def
proof (intro ballI impI)
  fix p q :: "nat \<times> nat"
  assume hp: "p \<in> (UNIV::(nat \<times> nat) set)" and hq: "q \<in> (UNIV::(nat \<times> nat) set)"
  assume hEq: "top1_pair_code p = top1_pair_code q"
  obtain a b where hpab: "p = (a,b)"
    by (cases p) simp
  obtain c d where hqcd: "q = (c,d)"
    by (cases q) simp

  have hodd_b: "\<not> (2::nat) dvd (2 * b + 1)"
    by simp
  have hodd_d: "\<not> (2::nat) dvd (2 * d + 1)"
    by simp

  have hnot_dvd_a: "\<not> (2 ^ (Suc a)) dvd top1_pair_code (a,b)"
  proof
    assume hdvd: "(2 ^ (Suc a)) dvd top1_pair_code (a,b)"
    have hcomm: "(2::nat) * 2 ^ a = 2 ^ a * 2"
      by (simp add: mult.commute)
    have hdvd': "(2 ^ a * (2::nat)) dvd top1_pair_code (a,b)"
    proof -
      have "(2::nat) * 2 ^ a dvd top1_pair_code (a,b)"
        using hdvd by (simp only: power_Suc)
      thus ?thesis
        by (simp add: hcomm)
    qed
    have hEq': "top1_pair_code (a,b) = (2 ^ a) * (2 * b + 1)"
      unfolding top1_pair_code_def by simp
    have hdvd0: "(2 ^ a * (2::nat)) dvd ((2 ^ a) * (2 * b + 1))"
      apply (subst hEq'[symmetric])
      apply (rule hdvd')
      done
    have "(2::nat) dvd (2 * b + 1)"
      using hdvd0 by (simp add: dvd_mult_cancel_left del: mult_Suc_right)
    thus False
      using hodd_b by blast
  qed

  have hnot_dvd_c: "\<not> (2 ^ (Suc c)) dvd top1_pair_code (c,d)"
  proof
    assume hdvd: "(2 ^ (Suc c)) dvd top1_pair_code (c,d)"
    have hcomm: "(2::nat) * 2 ^ c = 2 ^ c * 2"
      by (simp add: mult.commute)
    have hdvd': "(2 ^ c * (2::nat)) dvd top1_pair_code (c,d)"
    proof -
      have "(2::nat) * 2 ^ c dvd top1_pair_code (c,d)"
        using hdvd by (simp only: power_Suc)
      thus ?thesis
        by (simp add: hcomm)
    qed
    have hEq': "top1_pair_code (c,d) = (2 ^ c) * (2 * d + 1)"
      unfolding top1_pair_code_def by simp
    have hdvd0: "(2 ^ c * (2::nat)) dvd ((2 ^ c) * (2 * d + 1))"
      apply (subst hEq'[symmetric])
      apply (rule hdvd')
      done
    have "(2::nat) dvd (2 * d + 1)"
      using hdvd0 by (simp add: dvd_mult_cancel_left del: mult_Suc_right)
    thus False
      using hodd_d by blast
  qed

  have hac: "a = c"
  proof (cases a c rule: linorder_cases)
    case less
    have hle: "Suc a \<le> c"
      using less by simp
    have hdvd: "((2::nat) ^ (Suc a)) dvd ((2::nat) ^ c)"
    proof -
      have hdecomp: "Suc a + (c - Suc a) = c"
        using hle by simp
      have "(2::nat) ^ c = (2::nat) ^ (Suc a + (c - Suc a))"
        using hdecomp by simp
      also have "\<dots> = (2::nat) ^ (Suc a) * (2::nat) ^ (c - Suc a)"
        by (simp add: power_add)
      finally have "(2::nat) ^ c = (2::nat) ^ (Suc a) * (2::nat) ^ (c - Suc a)" .
      thus ?thesis
        by (rule dvdI)
    qed
    have hEq_cd: "top1_pair_code (c,d) = (2 ^ c) * (2 * d + 1)"
      unfolding top1_pair_code_def by simp
    have hEq_abcd: "top1_pair_code (a,b) = top1_pair_code (c,d)"
      using hEq unfolding hpab hqcd by simp
    have hdiv_cd: "(2 ^ (Suc a)) dvd top1_pair_code (c,d)"
      apply (subst hEq_cd)
      apply (rule dvd_mult2[OF hdvd])
      done
    have hdiv_ab: "(2 ^ (Suc a)) dvd top1_pair_code (a,b)"
      apply (subst hEq_abcd)
      apply (rule hdiv_cd)
      done
    show ?thesis
      using hdiv_ab hnot_dvd_a by blast
  next
    case equal
    show ?thesis
      using equal by simp
  next
    case greater
    have hle: "Suc c \<le> a"
      using greater by simp
    have hdvd: "((2::nat) ^ (Suc c)) dvd ((2::nat) ^ a)"
    proof -
      have hdecomp: "Suc c + (a - Suc c) = a"
        using hle by simp
      have "(2::nat) ^ a = (2::nat) ^ (Suc c + (a - Suc c))"
        using hdecomp by simp
      also have "\<dots> = (2::nat) ^ (Suc c) * (2::nat) ^ (a - Suc c)"
        by (simp add: power_add)
      finally have "(2::nat) ^ a = (2::nat) ^ (Suc c) * (2::nat) ^ (a - Suc c)" .
      thus ?thesis
        by (rule dvdI)
    qed
    have hEq_ab: "top1_pair_code (a,b) = (2 ^ a) * (2 * b + 1)"
      unfolding top1_pair_code_def by simp
    have hEq_abcd: "top1_pair_code (a,b) = top1_pair_code (c,d)"
      using hEq unfolding hpab hqcd by simp
    have hdiv_ab: "(2 ^ (Suc c)) dvd top1_pair_code (a,b)"
      apply (subst hEq_ab)
      apply (rule dvd_mult2[OF hdvd])
      done
    have hdiv_cd: "(2 ^ (Suc c)) dvd top1_pair_code (c,d)"
      apply (subst hEq_abcd[symmetric])
      apply (rule hdiv_ab)
      done
    show ?thesis
      using hdiv_cd hnot_dvd_c by blast
  qed

  have hbd: "b = d"
  proof -
    have hEq_abcd: "top1_pair_code (a,b) = top1_pair_code (c,d)"
      using hEq unfolding hpab hqcd by simp
    have hEq_abd: "top1_pair_code (a,b) = top1_pair_code (a,d)"
      using hEq_abcd hac by simp
    have "2 * b + 1 = 2 * d + 1"
      using hEq_abd unfolding top1_pair_code_def by (simp add: mult_left_cancel)
    hence "2 * b = 2 * d"
      by simp
    thus "b = d"
      by simp
  qed

  show "p = q"
    unfolding hpab hqcd using hac hbd by simp
qed

lemma top1_countable_nat_prod: "top1_countable (UNIV::(nat \<times> nat) set)"
  unfolding top1_countable_def
  by (rule exI[where x=top1_pair_code], rule top1_pair_code_inj)

(** Countability of dependent sums (Sigma types) for the local notion \<open>top1_countable\<close>. **)
lemma top1_countable_SIGMA:
  fixes C :: "'i \<Rightarrow> 'a set"
  assumes hI: "top1_countable I"
  assumes hC: "\<forall>i\<in>I. top1_countable (C i)"
  shows "top1_countable (SIGMA i:I. C i)"
proof -
  obtain eI :: "'i \<Rightarrow> nat" where heI: "inj_on eI I"
    using hI unfolding top1_countable_def by blast

  have hexE: "\<forall>i\<in>I. \<exists>e::'a \<Rightarrow> nat. inj_on e (C i)"
  proof (intro ballI)
    fix i
    assume hi: "i \<in> I"
    have hCi: "top1_countable (C i)"
      using hC hi by blast
    obtain e :: "'a \<Rightarrow> nat" where he: "inj_on e (C i)"
      using hCi unfolding top1_countable_def by blast
    show "\<exists>e::'a \<Rightarrow> nat. inj_on e (C i)"
      by (rule exI[where x=e], rule he)
  qed
  obtain eC :: "'i \<Rightarrow> 'a \<Rightarrow> nat" where heC: "\<forall>i\<in>I. inj_on (eC i) (C i)"
    using bchoice[OF hexE] by blast

  define h where "h p = top1_pair_code (eI (fst p), eC (fst p) (snd p))" for p

  have hinj: "inj_on h (SIGMA i:I. C i)"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix p q :: "'i \<times> 'a"
    assume hp: "p \<in> (SIGMA i:I. C i)" and hq: "q \<in> (SIGMA i:I. C i)"
    assume hEq: "h p = h q"

    obtain i x where hpix: "p = (i,x)"
      by (cases p) simp
    obtain j y where hqjy: "q = (j,y)"
      by (cases q) simp

    have hiI: "i \<in> I" and hx: "x \<in> C i"
      using hp unfolding hpix by blast+
    have hjI: "j \<in> I" and hy: "y \<in> C j"
      using hq unfolding hqjy by blast+

    have hpair: "(eI i, eC i x) = (eI j, eC j y)"
    proof -
      have "top1_pair_code (eI i, eC i x) = top1_pair_code (eI j, eC j y)"
        using hEq unfolding h_def hpix hqjy by simp
      thus ?thesis
        using top1_pair_code_inj unfolding inj_on_def by blast
    qed
    have heIeq: "eI i = eI j"
      using hpair by simp
    have heCeq: "eC i x = eC j y"
      using hpair by simp

    have hij: "i = j"
      using heI hiI hjI heIeq unfolding inj_on_def by blast
    have hxy: "x = y"
      using heC hiI hx hy hij heCeq unfolding inj_on_def by blast

    show "p = q"
      unfolding hpix hqjy using hij hxy by simp
  qed

  show ?thesis
    unfolding top1_countable_def
    by (rule exI[where x=h], rule hinj)
qed

(** Injective encoding of lists of naturals, derived from \<open>top1_pair_code\<close>. **)
fun top1_list_code :: "nat list \<Rightarrow> nat" where
  "top1_list_code [] = 0"
| "top1_list_code (x # xs) = Suc (top1_pair_code (x, top1_list_code xs))"

lemma top1_list_code_inj: "inj_on top1_list_code (UNIV::nat list set)"
  unfolding inj_on_def
  proof (intro ballI impI)
    fix xs ys :: "nat list"
  assume hxs: "xs \<in> (UNIV::nat list set)" and hys: "ys \<in> (UNIV::nat list set)"
  assume hEq: "top1_list_code xs = top1_list_code ys"
  show "xs = ys"
    using hEq
  proof (induction xs arbitrary: ys)
    case Nil
    show ?case
    proof (cases ys)
      case Nil
      show ?thesis
        using Nil by simp
    next
      case (Cons y ys')
      show ?thesis
        using Nil Cons by simp
    qed
  next
    case (Cons x xs)
    show ?case
    proof (cases ys)
      case Nil
      show ?thesis
        using Cons.prems Nil by simp
    next
      case (Cons y ys')
      have hSuc: "top1_pair_code (x, top1_list_code xs) = top1_pair_code (y, top1_list_code ys')"
        using Cons.prems unfolding Cons by simp
      have hp: "(x, top1_list_code xs) = (y, top1_list_code ys')"
        using top1_pair_code_inj hSuc unfolding inj_on_def by blast
      have hxy: "x = y"
        using hp by simp
      have ht: "top1_list_code xs = top1_list_code ys'"
        using hp by simp
      have htail: "xs = ys'"
        by (rule Cons.IH[OF ht])
      show ?thesis
        unfolding Cons using hxy htail by simp
    qed
  qed
qed

lemma top1_countable_lists:
  assumes hS: "top1_countable S"
  shows "top1_countable (lists S)"
proof -
  obtain f :: "'a \<Rightarrow> nat" where hf: "inj_on f S"
    using hS unfolding top1_countable_def by blast

  define enc where "enc xs = top1_list_code (map f xs)" for xs :: "'a list"

  have hmap: "inj_on (map f) (lists S)"
    by (rule inj_on_map_lists[OF hf])
  have henc_nat: "inj_on top1_list_code (UNIV::nat list set)"
    by (rule top1_list_code_inj)

  have henc: "inj_on enc (lists S)"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix xs ys :: "'a list"
    assume hxs: "xs \<in> lists S" and hys: "ys \<in> lists S"
    assume hEq: "enc xs = enc ys"
    have "top1_list_code (map f xs) = top1_list_code (map f ys)"
      using hEq unfolding enc_def by simp
    hence "map f xs = map f ys"
      using henc_nat unfolding inj_on_def by blast
    hence "xs = ys"
      using hmap hxs hys unfolding inj_on_def by blast
    thus "xs = ys" .
  qed

  show ?thesis
    unfolding top1_countable_def
    by (rule exI[where x=enc], rule henc)
qed

(** from \S30 Definition (Countable neighborhood basis at a point) [top1.tex:~3903] **)
definition top1_countable_neighborhood_basis_at ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_countable_neighborhood_basis_at X T x \<longleftrightarrow>
     (\<exists>B. top1_countable B
        \<and> (\<forall>U\<in>B. neighborhood_of x X T U)
        \<and> (\<forall>V. neighborhood_of x X T V \<longrightarrow> (\<exists>U\<in>B. U \<subseteq> V)))"

definition top1_first_countable_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_first_countable_on X T \<longleftrightarrow> (\<forall>x\<in>X. top1_countable_neighborhood_basis_at X T x)"

(** from \S30 Definition (Second countability axiom) [top1.tex:~3903] **)
definition top1_second_countable_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_second_countable_on X T \<longleftrightarrow> (\<exists>B. top1_countable B \<and> basis_for X B T)"

(** from \S30 Theorem 30.2 (Subspaces of first-countable spaces) [top1.tex:~3934] **)
theorem Theorem_30_2_first_countable_subspace:
  assumes h1st: "top1_first_countable_on X T"
  assumes hYX: "Y \<subseteq> X"
  shows "top1_first_countable_on Y (subspace_topology X T Y)"
proof -
  let ?TY = "subspace_topology X T Y"

  show ?thesis
    unfolding top1_first_countable_on_def top1_countable_neighborhood_basis_at_def
  proof (intro ballI)
    fix x
    assume hxY: "x \<in> Y"
    have hxX: "x \<in> X"
      using hYX hxY by blast

    have hx_basis: "top1_countable_neighborhood_basis_at X T x"
      using h1st hxX unfolding top1_first_countable_on_def by blast

    obtain B where hBcnt: "top1_countable B"
      and hBnb: "\<forall>U\<in>B. neighborhood_of x X T U"
      and hBref: "\<forall>V. neighborhood_of x X T V \<longrightarrow> (\<exists>U\<in>B. U \<subseteq> V)"
      using hx_basis unfolding top1_countable_neighborhood_basis_at_def by blast

    define B' where "B' = (\<lambda>U. U \<inter> Y) ` B"

    have hB'cnt: "top1_countable B'"
      unfolding B'_def
      by (rule top1_countable_image[OF hBcnt])

    have hB'nb: "\<forall>U\<in>B'. neighborhood_of x Y ?TY U"
    proof (intro ballI)
      fix U assume hU: "U \<in> B'"
      obtain V where hV: "V \<in> B" and hUeq: "U = V \<inter> Y"
        using hU unfolding B'_def by blast
      have hVnb: "neighborhood_of x X T V"
        using hBnb hV by blast
      have hVT: "V \<in> T"
        using hVnb unfolding neighborhood_of_def by blast
      have hxV: "x \<in> V"
        using hVnb unfolding neighborhood_of_def by blast
      have hUTY: "U \<in> ?TY"
      proof -
        have hUeq': "U = Y \<inter> V"
          using hUeq by (simp add: Int_commute)
        show ?thesis
          unfolding subspace_topology_def hUeq'
          using hVT by blast
      qed
      have hxU: "x \<in> U"
        unfolding hUeq using hxY hxV by blast
      show "neighborhood_of x Y ?TY U"
        unfolding neighborhood_of_def
        by (intro conjI, rule hUTY, rule hxU)
    qed

    have hBref': "\<forall>V. neighborhood_of x Y ?TY V \<longrightarrow> (\<exists>U\<in>B'. U \<subseteq> V)"
    proof (intro allI impI)
      fix V
      assume hVnb: "neighborhood_of x Y ?TY V"
      have hVTY: "V \<in> ?TY"
        using hVnb unfolding neighborhood_of_def by blast
      obtain W where hW: "W \<in> T" and hVeq: "V = Y \<inter> W"
        using hVTY unfolding subspace_topology_def by blast
      have hxV: "x \<in> V"
        using hVnb unfolding neighborhood_of_def by blast
      have hxW: "x \<in> W"
        using hxV hxY unfolding hVeq by blast
      have hWnb: "neighborhood_of x X T W"
        unfolding neighborhood_of_def using hW hxW by blast

      obtain U0 where hU0: "U0 \<in> B" and hU0sub: "U0 \<subseteq> W"
        using hBref hWnb by blast

      have hU0' : "U0 \<inter> Y \<in> B'"
        unfolding B'_def by (rule imageI[OF hU0])
      have hU0'sub: "U0 \<inter> Y \<subseteq> V"
        unfolding hVeq using hU0sub by blast

      show "\<exists>U\<in>B'. U \<subseteq> V"
      proof -
        have "\<exists>U. U \<in> B' \<and> U \<subseteq> V"
          apply (rule exI[where x="U0 \<inter> Y"])
          apply (intro conjI)
           apply (rule hU0')
          apply (rule hU0'sub)
          done
        thus ?thesis
          by blast
      qed
    qed

    show "\<exists>B. top1_countable B \<and> (\<forall>U\<in>B. neighborhood_of x Y ?TY U)
        \<and> (\<forall>V. neighborhood_of x Y ?TY V \<longrightarrow> (\<exists>U\<in>B. U \<subseteq> V))"
      by (rule exI[where x=B'], intro conjI, rule hB'cnt, rule hB'nb, rule hBref')
  qed
qed

(** from \S30 Theorem 30.2 (Subspaces of second-countable spaces) [top1.tex:~3990] **)
theorem Theorem_30_2_second_countable_subspace:
  assumes h2nd: "top1_second_countable_on X T"
  assumes hYX: "Y \<subseteq> X"
  shows "top1_second_countable_on Y (subspace_topology X T Y)"
proof -
  obtain B where hBcnt: "top1_countable B" and hBasis: "basis_for X B T"
    using h2nd unfolding top1_second_countable_on_def by blast

  have hBYcnt: "top1_countable ((\<lambda>b. b \<inter> Y) ` B)"
    by (rule top1_countable_image[OF hBcnt])

  have hBY_eq: "(\<lambda>b. b \<inter> Y) ` B = {b \<inter> Y | b. b \<in> B}"
    by blast

  have hBYbasis:
    "basis_for Y {b \<inter> Y | b. b \<in> B} (subspace_topology X T Y)"
    by (rule Lemma_16_1[OF hBasis hYX])

  show ?thesis
    unfolding top1_second_countable_on_def
    apply (rule exI[where x="{b \<inter> Y | b. b \<in> B}"])
    apply (intro conjI)
     apply (subst hBY_eq[symmetric])
     apply (rule hBYcnt)
    apply (rule hBYbasis)
    done
qed

(** from \S30 Theorem 30.2 (Countable products of first-countable spaces) [top1.tex:~3934] **)
theorem Theorem_30_2_first_countable_product:
  assumes hIcnt: "top1_countable I"
  assumes hfac: "\<forall>i\<in>I. top1_first_countable_on (X i) (T i)"
  shows "top1_first_countable_on (top1_PiE I X) (top1_product_topology_on I X T)"
proof -
  let ?Y = "top1_PiE I X"
  let ?B = "top1_product_basis_on I X T"
  let ?TP = "top1_product_topology_on I X T"

  show ?thesis
    unfolding top1_first_countable_on_def top1_countable_neighborhood_basis_at_def neighborhood_of_def
  proof (intro ballI)
    fix x
    assume hxY: "x \<in> ?Y"
    have hxX: "\<forall>i\<in>I. x i \<in> X i"
      using hxY unfolding top1_PiE_iff by blast

    show "\<exists>B0. top1_countable B0
         \<and> (\<forall>U\<in>B0. U \<in> ?TP \<and> x \<in> U)
         \<and> (\<forall>V. V \<in> ?TP \<and> x \<in> V \<longrightarrow> (\<exists>U\<in>B0. U \<subseteq> V))"
    proof (cases "\<exists>b\<in>?B. x \<in> b")
      case False

      have hnone: "\<forall>V. \<not> (V \<in> ?TP \<and> x \<in> V)"
      proof (intro allI notI)
        fix V
        assume hV: "V \<in> ?TP \<and> x \<in> V"
        have hVgen: "V \<in> topology_generated_by_basis ?Y ?B"
          using hV unfolding top1_product_topology_on_def by simp
        obtain b where hb: "b \<in> ?B" and hxb: "x \<in> b" and hbV: "b \<subseteq> V"
          using hVgen hV unfolding topology_generated_by_basis_def by blast
        show False
          using False hb hxb by blast
      qed

      show ?thesis
        apply (rule exI[where x="{}"])
        apply (intro conjI)
         apply (simp add: top1_countable_def)
        apply simp
        apply (intro allI impI)
        using hnone
        apply blast
        done
    next
      case True
      obtain b0 where hb0: "b0 \<in> ?B" and hxb0: "x \<in> b0"
        using True by blast
      obtain A0 where hb0def: "b0 = top1_PiE I A0"
        and hA0: "(\<forall>i\<in>I. A0 i \<in> T i \<and> A0 i \<subseteq> X i) \<and> finite {i \<in> I. A0 i \<noteq> X i}"
        using hb0 unfolding top1_product_basis_on_def by blast
      have hA0_fin: "finite {i \<in> I. A0 i \<noteq> X i}"
        using hA0 by blast
      have hxA0: "\<forall>i\<in>I. x i \<in> A0 i"
        using hxb0 unfolding hb0def top1_PiE_iff by blast

      have hexB:
        "\<forall>i\<in>I. \<exists>Bi. top1_countable Bi
              \<and> (\<forall>U\<in>Bi. neighborhood_of (x i) (X i) (T i) U)
              \<and> (\<forall>V. neighborhood_of (x i) (X i) (T i) V \<longrightarrow> (\<exists>U\<in>Bi. U \<subseteq> V))"
      proof (intro ballI)
        fix i
        assume hiI: "i \<in> I"
        have h1st: "top1_first_countable_on (X i) (T i)"
          using hfac hiI by blast
        have hB: "top1_countable_neighborhood_basis_at (X i) (T i) (x i)"
          using h1st hxX hiI unfolding top1_first_countable_on_def by blast
        show "\<exists>Bi. top1_countable Bi
              \<and> (\<forall>U\<in>Bi. neighborhood_of (x i) (X i) (T i) U)
              \<and> (\<forall>V. neighborhood_of (x i) (X i) (T i) V \<longrightarrow> (\<exists>U\<in>Bi. U \<subseteq> V))"
          using hB unfolding top1_countable_neighborhood_basis_at_def by blast
      qed
      obtain B0 where hB0:
        "\<forall>i\<in>I. top1_countable (B0 i)
            \<and> (\<forall>U\<in>B0 i. neighborhood_of (x i) (X i) (T i) U)
            \<and> (\<forall>V. neighborhood_of (x i) (X i) (T i) V \<longrightarrow> (\<exists>U\<in>B0 i. U \<subseteq> V))"
        using bchoice[OF hexB] by blast

      define C where "C i = {U \<in> B0 i. U \<subseteq> X i}" for i

      have hCcnt: "\<forall>i\<in>I. top1_countable (C i)"
      proof (intro ballI)
        fix i
        assume hiI: "i \<in> I"
        have hB0cnt: "top1_countable (B0 i)"
          using hB0 hiI by blast
        have hCsub: "C i \<subseteq> B0 i"
          unfolding C_def by blast
        show "top1_countable (C i)"
          by (rule top1_countable_subset[OF hB0cnt hCsub])
      qed

      have hSigma_cnt: "top1_countable (SIGMA i:I. C i)"
        by (rule top1_countable_SIGMA[OF hIcnt hCcnt])
      have hLists_cnt: "top1_countable (lists (SIGMA i:I. C i))"
        by (rule top1_countable_lists[OF hSigma_cnt])

	      define mkF where "mkF l = foldr (\<lambda>p f. f (fst p := snd p)) l A0" for l
      define mkU where "mkU l = top1_PiE I (mkF l)" for l
      define BB where "BB = mkU ` lists (SIGMA i:I. C i)"

      have hBBcnt: "top1_countable BB"
        unfolding BB_def
        by (rule top1_countable_image[OF hLists_cnt])

      have hmkF_props:
        "\<forall>l\<in>lists (SIGMA i:I. C i).
            (\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i)
            \<and> finite {i \<in> I. mkF l i \<noteq> X i}"
      proof (intro ballI)
        fix l
        assume hl: "l \<in> lists (SIGMA i:I. C i)"

        have hP0: "\<forall>i\<in>I. A0 i \<in> T i \<and> A0 i \<subseteq> X i \<and> x i \<in> A0 i"
        proof (intro ballI)
          fix i
          assume hiI: "i \<in> I"
          have "A0 i \<in> T i" and "A0 i \<subseteq> X i"
            using hA0 hiI by blast+
          moreover have "x i \<in> A0 i"
            using hxA0 hiI by blast
          ultimately show "A0 i \<in> T i \<and> A0 i \<subseteq> X i \<and> x i \<in> A0 i"
            by blast
        qed

        have hP: "\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i"
          using hl
        proof (induct l)
          case Nil
          show ?case
            unfolding mkF_def using hP0 by simp
	        next
						          case (Cons p ps)
						          have hpSigma: "p \<in> (SIGMA i:I. C i)"
						            by fact
						          have hps: "ps \<in> lists (SIGMA i:I. C i)"
						            by fact
						          obtain j U where hp: "p = (j, U)"
						            by (cases p) simp
						          have hjI: "j \<in> I" and hU: "U \<in> C j"
						            using hpSigma unfolding hp by blast+

          have hU_T: "U \<in> T j" and hU_subX: "U \<subseteq> X j" and hxjU: "x j \<in> U"
          proof -
            have hUC: "U \<in> B0 j" and hUsub: "U \<subseteq> X j"
              using hU unfolding C_def by blast+
            have hnb: "neighborhood_of (x j) (X j) (T j) U"
              using hB0 hjI hUC by blast
            have hUopen: "U \<in> T j"
              using hnb unfolding neighborhood_of_def by blast
            have hxU: "x j \<in> U"
              using hnb unfolding neighborhood_of_def by blast
            show "U \<in> T j" and "U \<subseteq> X j" and "x j \<in> U"
              using hUopen hUsub hxU by blast+
          qed

	          have hIH: "\<forall>i\<in>I. mkF ps i \<in> T i \<and> mkF ps i \<subseteq> X i \<and> x i \<in> mkF ps i"
	            by fact

	          show ?case
	          proof (intro ballI)
	            fix i
	            assume hiI: "i \<in> I"
	            show "mkF (p # ps) i \<in> T i \<and> mkF (p # ps) i \<subseteq> X i \<and> x i \<in> mkF (p # ps) i"
	            proof (cases "i = j")
	              case True
	              show ?thesis
	                using hU_T hU_subX hxjU
	                by (simp add: mkF_def hp True)
	            next
	              case False
	              have "mkF ps i \<in> T i \<and> mkF ps i \<subseteq> X i \<and> x i \<in> mkF ps i"
	                using hIH hiI by blast
	              thus ?thesis
	                by (simp add: mkF_def hp False)
	            qed
	          qed
	        qed

        have hSub:
          "{i \<in> I. mkF l i \<noteq> X i} \<subseteq> {i \<in> I. A0 i \<noteq> X i} \<union> set (map fst l)"
        proof (rule subsetI)
          fix i
          assume hi: "i \<in> {i \<in> I. mkF l i \<noteq> X i}"
          have hiI: "i \<in> I" and hneq: "mkF l i \<noteq> X i"
            using hi by blast+
          show "i \<in> {i \<in> I. A0 i \<noteq> X i} \<union> set (map fst l)"
          proof (cases "i \<in> set (map fst l)")
            case True
            show ?thesis
              using True by blast
	          next
	            case False
	            have hEq: "mkF l i = A0 i"
	            proof -
			              have "(foldr (\<lambda>p f. f (fst p := snd p)) l A0) i = A0 i"
			                by (rule fold_fun_update_notin_fst[OF False])
		              thus ?thesis
		                unfolding mkF_def .
		            qed
	            have "A0 i \<noteq> X i"
	              using hneq unfolding hEq by blast
	            thus ?thesis
	              using hiI by blast
	          qed
        qed

        have hFin1: "finite (set (map fst l))"
          by simp
        have hFin2: "finite ({i \<in> I. A0 i \<noteq> X i} \<union> set (map fst l))"
          by (rule finite_UnI[OF hA0_fin hFin1])
        have hFin3: "finite {i \<in> I. mkF l i \<noteq> X i}"
          by (rule finite_subset[OF hSub hFin2])

        show "(\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i) \<and> finite {i \<in> I. mkF l i \<noteq> X i}"
          using hP hFin3 by blast
      qed

      have hBBnb: "\<forall>U\<in>BB. U \<in> ?TP \<and> x \<in> U"
      proof (intro ballI)
        fix U
        assume hU: "U \<in> BB"
	        obtain l where hl: "l \<in> lists (SIGMA i:I. C i)" and hUeq: "U = mkU l"
	          using hU unfolding BB_def by blast
	        have hProps:
	          "(\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i) \<and> finite {i \<in> I. mkF l i \<noteq> X i}"
	          using hmkF_props hl by blast
	
	        have hAll: "\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i"
	          using hProps by (rule conjunct1)
	        have hFin: "finite {i \<in> I. mkF l i \<noteq> X i}"
	          using hProps by (rule conjunct2)

	        have hAll2: "\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i"
	        proof (intro ballI)
	          fix i
	          assume hiI: "i \<in> I"
	          have hix: "mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i"
	            by (rule bspec[OF hAll hiI])
	          have hTi: "mkF l i \<in> T i"
	            by (rule conjunct1[OF hix])
	          have hSubXi: "mkF l i \<subseteq> X i"
	            by (rule conjunct1[OF conjunct2[OF hix]])
	          show "mkF l i \<in> T i \<and> mkF l i \<subseteq> X i"
	            by (intro conjI) (rule hTi, rule hSubXi)
	        qed

		        have hBasis: "mkU l \<in> ?B"
		          unfolding top1_product_basis_on_def
		        proof (rule CollectI)
		          show "\<exists>U. mkU l = top1_PiE I U \<and> (\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i) \<and> finite {i \<in> I. U i \<noteq> X i}"
		          proof (rule exI[where x="mkF l"])
		            show "mkU l = top1_PiE I (mkF l) \<and> (\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i) \<and> finite {i \<in> I. mkF l i \<noteq> X i}"
		              using hAll2 hFin by (simp add: mkU_def)
		          qed
		        qed
	
	        have hSubY: "mkU l \<subseteq> ?Y"
	        proof -
	          have hsub: "\<forall>i\<in>I. mkF l i \<subseteq> X i"
	          proof (intro ballI)
	            fix i
	            assume hiI: "i \<in> I"
	            have hix: "mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i"
	              by (rule bspec[OF hAll hiI])
	            show "mkF l i \<subseteq> X i"
	              by (rule conjunct1[OF conjunct2[OF hix]])
	          qed
	          show ?thesis
	            unfolding mkU_def
	            by (rule top1_PiE_mono[OF hsub])
	        qed
	
	        have hOpen: "mkU l \<in> ?TP"
	          unfolding top1_product_topology_on_def topology_generated_by_basis_def
	        proof (rule CollectI)
	          show "mkU l \<subseteq> ?Y \<and> (\<forall>y\<in>mkU l. \<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> mkU l)"
	          proof (intro conjI)
	            show "mkU l \<subseteq> ?Y"
	              by (rule hSubY)
	            show "\<forall>y\<in>mkU l. \<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> mkU l"
	            proof (intro ballI)
	              fix y
	              assume hy: "y \<in> mkU l"
	              show "\<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> mkU l"
	              proof (rule bexI[where x="mkU l"])
	                show "y \<in> mkU l \<and> mkU l \<subseteq> mkU l"
	                  using hy by blast
	                show "mkU l \<in> ?B"
	                  by (rule hBasis)
	              qed
	            qed
	          qed
	        qed

        have hxU': "x \<in> mkU l"
        proof -
          have hx_mkF: "\<forall>i\<in>I. x i \<in> mkF l i"
          proof (intro ballI)
            fix i
            assume hiI: "i \<in> I"
            have "mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i"
              using hProps hiI by blast
            thus "x i \<in> mkF l i"
              by blast
          qed
          have hxundef: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
            using hxY unfolding top1_PiE_iff by blast
          show ?thesis
            unfolding mkU_def top1_PiE_iff
            apply (intro conjI)
             apply (rule hx_mkF)
            apply (rule hxundef)
            done
        qed

        show "U \<in> ?TP \<and> x \<in> U"
          unfolding hUeq using hOpen hxU' by blast
      qed

      have hBBref: "\<forall>V. V \<in> ?TP \<and> x \<in> V \<longrightarrow> (\<exists>U\<in>BB. U \<subseteq> V)"
      proof (intro allI impI)
        fix V
        assume hV: "V \<in> ?TP \<and> x \<in> V"
        have hVgen: "V \<in> topology_generated_by_basis ?Y ?B"
          using hV unfolding top1_product_topology_on_def by simp
        obtain b1 where hb1: "b1 \<in> ?B" and hxb1: "x \<in> b1" and hb1V: "b1 \<subseteq> V"
          using hVgen hV unfolding topology_generated_by_basis_def by blast
        obtain U1 where hb1def: "b1 = top1_PiE I U1"
          and hU1: "(\<forall>i\<in>I. U1 i \<in> T i \<and> U1 i \<subseteq> X i) \<and> finite {i \<in> I. U1 i \<noteq> X i}"
          using hb1 unfolding top1_product_basis_on_def by blast
        define J where "J = {i \<in> I. U1 i \<noteq> X i}"
        have hJfin: "finite J"
          unfolding J_def using hU1 by blast

        have hexSel: "\<forall>i\<in>J. \<exists>U. U \<in> C i \<and> U \<subseteq> U1 i"
        proof (intro ballI)
          fix i
          assume hiJ: "i \<in> J"
          have hiI: "i \<in> I"
            using hiJ unfolding J_def by blast
          have hU1nb: "neighborhood_of (x i) (X i) (T i) (U1 i)"
          proof -
            have hU1open: "U1 i \<in> T i" and hU1sub: "U1 i \<subseteq> X i"
              using hU1 hiI by blast+
            have hxiU1: "x i \<in> U1 i"
              using hxb1 unfolding hb1def top1_PiE_iff using hiI by blast
            show ?thesis
              unfolding neighborhood_of_def using hU1open hxiU1 by blast
          qed
          have hBref: "\<forall>V'. neighborhood_of (x i) (X i) (T i) V' \<longrightarrow> (\<exists>U\<in>B0 i. U \<subseteq> V')"
            using hB0 hiI by blast
          obtain U where hUB0: "U \<in> B0 i" and hUsub: "U \<subseteq> U1 i"
            using hBref hU1nb by blast
          have hUsubX: "U \<subseteq> X i"
            using hU1 hiJ hUsub unfolding J_def by blast
          have hUC: "U \<in> C i"
            unfolding C_def using hUB0 hUsubX by blast
          show "\<exists>U. U \<in> C i \<and> U \<subseteq> U1 i"
            apply (rule exI[where x=U])
            apply (intro conjI)
             apply (rule hUC)
            apply (rule hUsub)
            done
        qed
        obtain sel where hsel: "\<forall>i\<in>J. sel i \<in> C i \<and> sel i \<subseteq> U1 i"
          using bchoice[OF hexSel] by blast

        define S where "S = (\<lambda>i. (i, sel i)) ` J"
        have hSfin: "finite S"
          unfolding S_def by (rule finite_imageI[OF hJfin])
        have hSsub: "S \<subseteq> (SIGMA i:I. C i)"
        proof (rule subsetI)
          fix p
          assume hp: "p \<in> S"
          obtain i where hiJ: "i \<in> J" and hpdef: "p = (i, sel i)"
            using hp unfolding S_def by blast
          have hiI: "i \<in> I"
            using hiJ unfolding J_def by blast
          have "sel i \<in> C i"
            using hsel hiJ by blast
          show "p \<in> (SIGMA i:I. C i)"
            unfolding hpdef using hiI \<open>sel i \<in> C i\<close> by blast
        qed
        obtain l where hl: "set l = S" and hdist: "distinct l"
          using finite_distinct_list[OF hSfin] by blast
        have hlists: "l \<in> lists (SIGMA i:I. C i)"
          using hl hSsub by (simp add: lists_eq_set)

	      have hsubU1: "\<forall>i\<in>I. mkF l i \<subseteq> U1 i"
	        proof (intro ballI)
	          fix i
	          assume hiI: "i \<in> I"
	          show "mkF l i \<subseteq> U1 i"
	          proof (cases "i \<in> J")
	            case True
	            have hpair: "(i, sel i) \<in> set l"
	              using True hl unfolding S_def by blast
	            have hsnd_sel_if_fst: "\<forall>p\<in>set l. fst p = i \<longrightarrow> snd p = sel i"
	            proof (intro ballI impI)
	              fix p
	              assume hp: "p \<in> set l"
	              assume hfst: "fst p = i"
	              have hpS: "p \<in> S"
	                using hp hl by simp
	              obtain k where hkJ: "k \<in> J" and hpdef: "p = (k, sel k)"
	                using hpS unfolding S_def by blast
	              have "k = i"
	                using hfst unfolding hpdef by simp
	              hence "sel k = sel i"
	                by simp
	              show "snd p = sel i"
	                unfolding hpdef using \<open>sel k = sel i\<close> by simp
	            qed

	            have hmkF: "mkF l i = sel i"
	              using hpair hsnd_sel_if_fst
	            proof (induct l)
	              case Nil
	              have False
	                using Nil.prems(1) by simp
	              thus ?case
	                by (rule FalseE)
	            next
	              case (Cons p ps)
	              obtain j U where hp: "p = (j, U)"
	                by (cases p) simp
	              show ?case
	              proof (cases "j = i")
	                case True
	                have "U = sel i"
	                proof -
	                  have "fst p = i"
	                    unfolding hp using True by simp
	                  hence "snd p = sel i"
	                    using Cons.prems(2) by simp
	                  thus ?thesis
	                    unfolding hp by simp
	                qed
	                show ?thesis
	                  unfolding mkF_def hp True \<open>U = sel i\<close> by simp
		              next
		                case False
		                have htail: "(i, sel i) \<in> set ps"
		                  using Cons.prems(1) False hp by auto
		                have hsnd_tail: "\<forall>p\<in>set ps. fst p = i \<longrightarrow> snd p = sel i"
		                  using Cons.prems(2) by simp
		                have "mkF ps i = sel i"
		                  by (rule Cons.hyps[OF htail hsnd_tail])
		                have hij: "i \<noteq> j"
		                  using False by auto
		                have "mkF (p # ps) i = mkF ps i"
		                  unfolding mkF_def hp using hij by simp
		                also have "\<dots> = sel i"
		                  using \<open>mkF ps i = sel i\<close> .
		                finally show ?thesis .
		              qed
		            qed
	            moreover have "sel i \<subseteq> U1 i"
	              using hsel True by blast
	            ultimately show ?thesis
	              by simp
          next
            case False
            have "U1 i = X i"
              using False hiI unfolding J_def by blast
            moreover have hProps:
              "(\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i) \<and> finite {i \<in> I. mkF l i \<noteq> X i}"
              using hmkF_props hlists by blast
            ultimately show ?thesis
              using hProps hiI by blast
          qed
        qed

        have hMk_sub_b1: "mkU l \<subseteq> b1"
          unfolding hb1def mkU_def by (rule top1_PiE_mono[OF hsubU1])
        have hMk_in_BB: "mkU l \<in> BB"
          unfolding BB_def using hlists by blast

        show "\<exists>U\<in>BB. U \<subseteq> V"
          apply (rule bexI[where x="mkU l"])
           apply (rule subset_trans[OF hMk_sub_b1])
           apply (rule subset_trans[OF hb1V])
           apply (rule subset_refl)
          apply (rule hMk_in_BB)
          done
      qed

      show ?thesis
        apply (rule exI[where x=BB])
        apply (intro conjI)
          apply (rule hBBcnt)
         apply (rule hBBnb)
        apply (rule hBBref)
        done
    qed
  qed
qed

(** from \S30 Theorem 30.2 (Countable products of second-countable spaces) [top1.tex:~3990] **)
theorem Theorem_30_2_second_countable_product:
  assumes hIcnt: "top1_countable I"
  assumes hfac: "\<forall>i\<in>I. top1_second_countable_on (X i) (T i)"
  shows "top1_second_countable_on (top1_PiE I X) (top1_product_topology_on I X T)"
proof -
  let ?Y = "top1_PiE I X"
  let ?TP = "top1_product_topology_on I X T"

  have hexB: "\<forall>i\<in>I. \<exists>Bi. top1_countable Bi \<and> basis_for (X i) Bi (T i)"
    using hfac unfolding top1_second_countable_on_def by blast
  obtain B0 where hB0: "\<forall>i\<in>I. top1_countable (B0 i) \<and> basis_for (X i) (B0 i) (T i)"
    using bchoice[OF hexB] by blast

  define Sigma where "Sigma = (SIGMA i:I. B0 i)"

  have hSigma_cnt: "top1_countable Sigma"
  proof -
    have hB0cnt: "\<forall>i\<in>I. top1_countable (B0 i)"
      using hB0 by blast
    show ?thesis
      unfolding Sigma_def
      by (rule top1_countable_SIGMA[OF hIcnt hB0cnt])
  qed

  have hTopI: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  proof (intro ballI)
    fix i
    assume hiI: "i \<in> I"
    have hB0i: "top1_countable (B0 i) \<and> basis_for (X i) (B0 i) (T i)"
      using hB0 hiI by blast
    have "basis_for (X i) (B0 i) (T i)"
      using hB0i by (rule conjunct2)
    thus "is_topology_on (X i) (T i)"
      by (rule basis_for_is_topology_on)
  qed
  have hXiTi: "\<forall>i\<in>I. X i \<in> T i"
    using hTopI unfolding is_topology_on_def by blast

  define mkF where "mkF l = foldr (\<lambda>p f. f (fst p := snd p)) l X" for l
  define mkU where "mkU l = top1_PiE I (mkF l)" for l
  define Cc where "Cc = mkU ` lists Sigma"

  have hCc_cnt: "top1_countable Cc"
  proof -
    have hLists_cnt: "top1_countable (lists Sigma)"
      by (rule top1_countable_lists[OF hSigma_cnt])
    show ?thesis
      unfolding Cc_def
      by (rule top1_countable_image[OF hLists_cnt])
  qed

  have hCc_sub_TP: "Cc \<subseteq> ?TP"
  proof (rule subsetI)
    fix U
    assume hU: "U \<in> Cc"
    obtain l where hl: "l \<in> lists Sigma" and hUeq: "U = mkU l"
      using hU unfolding Cc_def by blast

    have hProps: "\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i"
      using hl
    proof (induct l)
      case Nil
      show ?case
        unfolding mkF_def using hXiTi by simp
	    next
			      case (Cons p ps)
			      have hpSigma: "p \<in> Sigma"
			        by fact
			      have hps: "ps \<in> lists Sigma"
			        by fact
			      obtain j V where hp: "p = (j, V)"
			        by (cases p) simp
		      have hjI: "j \<in> I" and hV: "V \<in> B0 j"
		        using hpSigma unfolding Sigma_def hp by blast+
      have hBasis: "basis_for (X j) (B0 j) (T j)"
        using hB0 hjI by blast
      have hVsub: "V \<subseteq> X j"
        using hBasis hV unfolding basis_for_def is_basis_on_def by blast
      have hVopen: "V \<in> T j"
        by (rule basis_elem_open_if_basis_for[OF hBasis hV])
		      have hIH: "\<forall>i\<in>I. mkF ps i \<in> T i \<and> mkF ps i \<subseteq> X i"
		        by fact
		      show ?case
		      proof (intro ballI)
		        fix i
		        assume hiI: "i \<in> I"
		        show "mkF (p # ps) i \<in> T i \<and> mkF (p # ps) i \<subseteq> X i"
		        proof (cases "i = j")
		          case True
		          show ?thesis
		            using hVopen hVsub
		            by (simp add: mkF_def hp True)
		        next
		          case False
		          show ?thesis
		            using hIH hiI
		            by (simp add: mkF_def hp False)
		        qed
		      qed
	    qed

	    have hSubY: "mkU l \<subseteq> ?Y"
	    proof -
	      have hsub: "\<forall>i\<in>I. mkF l i \<subseteq> X i"
	        using hProps by blast
	      show ?thesis
	        unfolding mkU_def
	        by (rule top1_PiE_mono[OF hsub])
	    qed

	    have hFin_mkF: "finite {i \<in> I. mkF l i \<noteq> X i}"
	    proof -
	      have hEq: "\<And>i. i \<notin> set (map fst l) \<Longrightarrow> mkF l i = X i"
	      proof (induct l)
	        case Nil
	        show ?case
	          by (simp add: mkF_def)
	      next
	        case (Cons p ps)
	        fix i
	        assume hnot: "i \<notin> set (map fst (p # ps))"
	        obtain j V where hp: "p = (j, V)"
	          by (cases p) simp
		        have hij_hnotps: "i \<noteq> j \<and> i \<notin> set (map fst ps)"
		          using hnot unfolding hp by simp
		        have hij: "i \<noteq> j"
		          using hij_hnotps by (elim conjE)
		        have hnotps: "i \<notin> set (map fst ps)"
		          using hij_hnotps by (elim conjE)

		        have "mkF (p # ps) i = mkF ps i"
		          unfolding mkF_def hp using hij by simp
		        also have "\<dots> = X i"
		          using Cons.hyps[OF hnotps] .
		        finally show "mkF (p # ps) i = X i" .
		      qed

	      have hSub: "{i \<in> I. mkF l i \<noteq> X i} \<subseteq> set (map fst l)"
	      proof (rule subsetI)
	        fix i
	        assume hi: "i \<in> {i \<in> I. mkF l i \<noteq> X i}"
	        have hneq: "mkF l i \<noteq> X i"
	          using hi by blast
	        show "i \<in> set (map fst l)"
	        proof (rule ccontr)
	          assume hnot: "i \<notin> set (map fst l)"
	          have "mkF l i = X i"
	            using hEq[OF hnot] .
	          with hneq show False
	            by contradiction
	        qed
	      qed

	      have hFin: "finite (set (map fst l))"
	        by simp
	      show ?thesis
	        by (rule finite_subset[OF hSub hFin])
	    qed
	
		    have hBasisU: "mkU l \<in> top1_product_basis_on I X T"
		      unfolding top1_product_basis_on_def
		      apply (rule CollectI)
		      apply (rule exI[where x="mkF l"])
		      apply (rule conjI)
		       apply (simp add: mkU_def)
		      apply (rule conjI)
		       apply (rule hProps)
		      apply (rule hFin_mkF)
		      done

	    have hOpen: "mkU l \<in> ?TP"
	      unfolding top1_product_topology_on_def topology_generated_by_basis_def
	    proof (rule CollectI)
	      show "mkU l \<subseteq> ?Y \<and> (\<forall>y\<in>mkU l. \<exists>b\<in>top1_product_basis_on I X T. y \<in> b \<and> b \<subseteq> mkU l)"
	      proof (intro conjI)
	        show "mkU l \<subseteq> ?Y"
	          by (rule hSubY)
	        show "\<forall>y\<in>mkU l. \<exists>b\<in>top1_product_basis_on I X T. y \<in> b \<and> b \<subseteq> mkU l"
	        proof (intro ballI)
	          fix y
	          assume hy: "y \<in> mkU l"
	          show "\<exists>b\<in>top1_product_basis_on I X T. y \<in> b \<and> b \<subseteq> mkU l"
	          proof (rule bexI[where x="mkU l"])
	            show "y \<in> mkU l \<and> mkU l \<subseteq> mkU l"
	              using hy by blast
	            show "mkU l \<in> top1_product_basis_on I X T"
	              by (rule hBasisU)
	          qed
	        qed
	      qed
	    qed

    show "U \<in> ?TP"
      unfolding hUeq using hOpen .
  qed

  have hTXsub: "\<forall>U\<in>?TP. U \<subseteq> ?Y"
    unfolding top1_product_topology_on_def topology_generated_by_basis_def by blast

  have hrefine:
    "\<And>U x. U \<in> ?TP \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>C\<in>Cc. C \<in> ?TP \<and> x \<in> C \<and> C \<subseteq> U"
  proof -
    fix U x
    assume hU: "U \<in> ?TP"
    assume hxU: "x \<in> U"
    have hUgen: "U \<in> topology_generated_by_basis ?Y (top1_product_basis_on I X T)"
      using hU unfolding top1_product_topology_on_def by simp
    obtain b where hb: "b \<in> top1_product_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
      using hUgen hxU unfolding topology_generated_by_basis_def by blast
    obtain W where hbdef: "b = top1_PiE I W"
      and hW: "(\<forall>i\<in>I. W i \<in> T i \<and> W i \<subseteq> X i) \<and> finite {i \<in> I. W i \<noteq> X i}"
      using hb unfolding top1_product_basis_on_def by blast
    define J where "J = {i \<in> I. W i \<noteq> X i}"
    have hJfin: "finite J"
      unfolding J_def using hW by blast
    have hxW: "\<forall>i\<in>J. x i \<in> W i"
      using hxb unfolding hbdef J_def top1_PiE_iff by blast

	    have hexSel: "\<forall>i\<in>J. \<exists>V\<in>B0 i. x i \<in> V \<and> V \<subseteq> W i"
	    proof (intro ballI)
      fix i
      assume hiJ: "i \<in> J"
      have hiI: "i \<in> I"
        using hiJ unfolding J_def by blast
      have hBasis: "basis_for (X i) (B0 i) (T i)"
        using hB0 hiI by blast
      have hWi: "W i \<in> T i"
        using hW hiI by blast
      have hxiWi: "x i \<in> W i"
        using hxW hiJ by blast
      show "\<exists>V\<in>B0 i. x i \<in> V \<and> V \<subseteq> W i"
        by (rule basis_for_refine[OF hBasis hWi hxiWi])
	    qed
	    have hexSel': "\<forall>i\<in>J. \<exists>V. V \<in> B0 i \<and> x i \<in> V \<and> V \<subseteq> W i"
	      using hexSel by blast
	    obtain sel where hsel: "\<forall>i\<in>J. sel i \<in> B0 i \<and> x i \<in> sel i \<and> sel i \<subseteq> W i"
	      using bchoice[OF hexSel'] by blast

    define S where "S = (\<lambda>i. (i, sel i)) ` J"
    have hSfin: "finite S"
      unfolding S_def by (rule finite_imageI[OF hJfin])
    have hSsub: "S \<subseteq> Sigma"
    proof
      fix p
      assume hp: "p \<in> S"
      have hp': "p \<in> (\<lambda>i. (i, sel i)) ` J"
        using hp unfolding S_def by simp
      obtain i where hiJ: "i \<in> J" and hp'': "p = (\<lambda>i. (i, sel i)) i"
        using hp' by (rule imageE)
      have hp_pair: "p = (i, sel i)"
        using hp'' by simp
      have hiI: "i \<in> I"
        using hiJ unfolding J_def by simp
      have hseli_all: "sel i \<in> B0 i \<and> x i \<in> sel i \<and> sel i \<subseteq> W i"
        by (rule bspec[OF hsel hiJ])
      have hseli: "sel i \<in> B0 i"
        by (rule conjunct1[OF hseli_all])
      show "p \<in> Sigma"
        unfolding hp_pair Sigma_def using hiI hseli by simp
    qed
    obtain l where hl: "set l = S"
      using finite_list[OF hSfin] by blast
    have hlists: "l \<in> lists Sigma"
      using hl hSsub by (simp add: lists_eq_set)

    have hC: "mkU l \<in> Cc"
      unfolding Cc_def using hlists by blast

    have hfst_in_J: "\<forall>p\<in>set l. fst p \<in> J"
      using hl unfolding S_def by auto

    have hpair_in_l: "\<forall>i\<in>J. (i, sel i) \<in> set l"
      using hl unfolding S_def by auto

		    have hsnd_sel_if_fst: "\<forall>i\<in>J. \<forall>p\<in>set l. fst p = i \<longrightarrow> snd p = sel i"
		    proof (intro ballI ballI impI)
		      fix i p
		      assume hiJ: "i \<in> J"
		      assume hp: "p \<in> set l"
		      assume hfst: "fst p = i"
		      have hpS: "p \<in> S"
		        using hp hl by simp
		      have hpImg: "p \<in> (\<lambda>i. (i, sel i)) ` J"
		        using hpS unfolding S_def by simp
		      from hpImg obtain j where hjJ: "j \<in> J" and hp': "p = (j, sel j)"
		        by (elim imageE) simp
		      have "j = i"
		        using hfst unfolding hp' by simp
		      thus "snd p = sel i"
		        unfolding hp' by simp
		    qed

	    have mkF_eq_sel:
	      "\<And>i. i \<in> J \<Longrightarrow> mkF l i = sel i"
	    proof -
	      fix i
	      assume hiJ: "i \<in> J"
	      have hpair: "(i, sel i) \<in> set l"
	        by (rule bspec[OF hpair_in_l hiJ])
	      have hsame: "\<forall>p\<in>set l. fst p = i \<longrightarrow> snd p = sel i"
	        by (rule bspec[OF hsnd_sel_if_fst hiJ])
	      show "mkF l i = sel i"
	        using hpair hsame
	      proof (induct l)
	        case Nil
	        have False
	          using Nil.prems(1) by simp
	        thus ?case
	          by (rule FalseE)
	      next
	        case (Cons p ps)
	        obtain j V where hp: "p = (j, V)"
	          by (cases p) simp
	        show ?case
	        proof (cases "j = i")
	          case True
	          have hImp: "fst p = i \<longrightarrow> snd p = sel i"
	            using Cons.prems(2) by simp
	          have "fst p = i"
	            unfolding hp using True by simp
	          hence "snd p = sel i"
	            using hImp by simp
	          hence hV: "V = sel i"
	            unfolding hp by simp
	          show ?thesis
	            unfolding mkF_def hp True hV by simp
	        next
	          case False
	          have htail: "(i, sel i) \<in> set ps"
	            using Cons.prems(1) False hp by auto
	          have hsame_ps: "\<forall>p\<in>set ps. fst p = i \<longrightarrow> snd p = sel i"
	            using Cons.prems(2) by simp
	          have "mkF ps i = sel i"
	            by (rule Cons.hyps(1)[OF htail hsame_ps])
	          have hij: "i \<noteq> j"
	            using False by auto
	          from \<open>mkF ps i = sel i\<close> show ?thesis
	            unfolding mkF_def hp using hij by simp
	        qed
	      qed
	    qed

    have mkF_eq_X:
      "\<And>i. i \<in> I \<Longrightarrow> i \<notin> J \<Longrightarrow> mkF l i = X i"
    proof -
      fix i
      assume hiI: "i \<in> I"
      assume hnotJ: "i \<notin> J"
      have hfst_ne: "\<forall>p\<in>set l. fst p \<noteq> i"
        using hfst_in_J hnotJ by blast
      show "mkF l i = X i"
        using hfst_ne
      proof (induct l)
        case Nil
        show ?case
          by (simp add: mkF_def)
      next
	        case (Cons p ps)
	        obtain j V where hp: "p = (j, V)"
	          by (cases p) simp
	        have hij: "i \<noteq> j"
	          using Cons.prems hp by auto
	        have hfst_ne_ps: "\<forall>p\<in>set ps. fst p \<noteq> i"
	          using Cons.prems by simp
	        have "mkF (p # ps) i = mkF ps i"
	          unfolding mkF_def hp using hij by simp
	        also have "\<dots> = X i"
	          using Cons.hyps[OF hfst_ne_ps] .
	        finally show ?case .
	      qed
	    qed

    have hsubW': "\<forall>i\<in>I. mkF l i \<subseteq> W i"
    proof (intro ballI)
      fix i
      assume hiI: "i \<in> I"
      show "mkF l i \<subseteq> W i"
      proof (cases "i \<in> J")
        case True
        have hpair: "(i, sel i) \<in> set l"
          using True hl unfolding S_def by blast
        have hmkF: "mkF l i = sel i"
          by (rule mkF_eq_sel[OF True])
        moreover have "sel i \<subseteq> W i"
          using hsel True by blast
        ultimately show ?thesis
          by simp
      next
        case False
        have hmkF: "mkF l i = X i"
          by (rule mkF_eq_X[OF hiI False])
        have hWi: "W i = X i"
          using False hiI unfolding J_def by blast
        show ?thesis
          unfolding hWi using hmkF by simp
      qed
    qed

    have hmk_sub: "mkU l \<subseteq> b"
      unfolding hbdef mkU_def by (rule top1_PiE_mono[OF hsubW'])

	    have hxC: "x \<in> mkU l"
	    proof -
	      have hxC': "\<forall>i\<in>I. x i \<in> mkF l i"
      proof (intro ballI)
        fix i
        assume hiI: "i \<in> I"
        show "x i \<in> mkF l i"
        proof (cases "i \<in> J")
          case True
          have hpair: "(i, sel i) \<in> set l"
            using True hl unfolding S_def by blast
          have hmkF: "mkF l i = sel i"
            by (rule mkF_eq_sel[OF True])
          show ?thesis
            using hsel True unfolding hmkF by blast
        next
	          case False
	          have hmkF: "mkF l i = X i"
	            by (rule mkF_eq_X[OF hiI False])
	          have hWi: "W i = X i"
	            using False hiI unfolding J_def by blast
	          have hxiWi: "x i \<in> W i"
	            using hxb unfolding hbdef top1_PiE_iff using hiI by simp
	          have "x i \<in> X i"
	            using hxiWi unfolding hWi by simp
	          thus ?thesis
	            unfolding hmkF by simp
	        qed
	      qed
	      have hxY: "x \<in> ?Y"
	        using hTXsub hU hxU by blast
	      have hxundef: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
	        using hxY unfolding top1_PiE_iff by blast
	      show ?thesis
	        unfolding mkU_def top1_PiE_iff using hxC' hxundef by blast
	    qed

	    show "\<exists>C\<in>Cc. C \<in> ?TP \<and> x \<in> C \<and> C \<subseteq> U"
	    proof (rule bexI[where x="mkU l"])
	      show "mkU l \<in> Cc"
	        by (rule hC)
	      show "mkU l \<in> ?TP \<and> x \<in> mkU l \<and> mkU l \<subseteq> U"
	      proof (intro conjI)
	        show "mkU l \<in> ?TP"
	          by (rule subsetD[OF hCc_sub_TP hC])
	        show "x \<in> mkU l"
	          by (rule hxC)
	        show "mkU l \<subseteq> U"
	          by (rule subset_trans[OF hmk_sub hbU])
	      qed
	    qed
	  qed

  have hCc_basis_for: "basis_for ?Y Cc ?TP"
  proof -
    have hTP_top: "is_topology_on ?Y ?TP"
      unfolding top1_product_topology_on_def
      by (rule topology_generated_by_basis_is_topology_on[OF top1_product_basis_is_basis_on[OF hTopI]])
    show ?thesis
      by (rule Lemma_13_2[OF hTP_top hCc_sub_TP hTXsub hrefine])
  qed

  show ?thesis
    unfolding top1_second_countable_on_def
    apply (rule exI[where x=Cc])
    apply (intro conjI)
     apply (rule hCc_cnt)
    apply (rule hCc_basis_for)
    done
qed

(** from \S30 Theorem 30.1 (First countability and sequences) [top1.tex:3911] **)
lemma seq_converges_to_on_in_set_imp_closure:
  assumes hTX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hsA: "\<forall>n. s n \<in> A"
  assumes hsconv: "seq_converges_to_on s x X TX"
  shows "x \<in> closure_on X TX A"
proof -
  have hxX: "x \<in> X"
    using hsconv unfolding seq_converges_to_on_def by blast

  have hchar: "x \<in> closure_on X TX A \<longleftrightarrow> (\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U A)"
    by (rule Theorem_17_5a[OF hTX hxX hAX])

  have hnb: "\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U A"
  proof (intro allI impI)
    fix U
    assume hU: "neighborhood_of x X TX U"
    obtain N where hN: "\<forall>n\<ge>N. s n \<in> U"
      using hsconv hU unfolding seq_converges_to_on_def by blast
    have hsNU: "s N \<in> U"
      using hN by simp
    have hsNA: "s N \<in> A"
      using hsA by simp
    have "s N \<in> U \<inter> A"
      by (rule IntI[OF hsNU hsNA])
    hence "U \<inter> A \<noteq> {}"
      by blast
    thus "intersects U A"
      unfolding intersects_def by simp
  qed

  show ?thesis
    by (rule iffD2[OF hchar hnb])
qed

lemma first_countable_closure_imp_seq:
  assumes hTX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes h1st: "top1_first_countable_on X TX"
  assumes hxcl: "x \<in> closure_on X TX A"
  shows "\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX"
proof -
  have hclsub: "closure_on X TX A \<subseteq> X"
    by (rule closure_on_subset_carrier[OF hTX hAX])
  have hxX: "x \<in> X"
    by (rule subsetD[OF hclsub hxcl])

  have hnbA:
    "\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U A"
  proof -
    have hchar: "x \<in> closure_on X TX A \<longleftrightarrow> (\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U A)"
      by (rule Theorem_17_5a[OF hTX hxX hAX])
    show ?thesis
      by (rule iffD1[OF hchar hxcl])
  qed

  have hx_basis: "top1_countable_neighborhood_basis_at X TX x"
    using h1st hxX unfolding top1_first_countable_on_def by blast

  obtain B where hBcnt: "top1_countable B"
    and hBnb: "\<forall>U\<in>B. neighborhood_of x X TX U"
    and hBref: "\<forall>V. neighborhood_of x X TX V \<longrightarrow> (\<exists>U\<in>B. U \<subseteq> V)"
    using hx_basis unfolding top1_countable_neighborhood_basis_at_def by blast

  obtain f :: "'a set \<Rightarrow> nat" where hf: "inj_on f B"
    using hBcnt unfolding top1_countable_def by blast

  define S where "S n = {b \<in> B. f b \<le> n}" for n

  have inter_TX: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])

  have hXnb: "neighborhood_of x X TX X"
    unfolding neighborhood_of_def by (intro conjI, rule X_TX, rule hxX)

  obtain b0 where hb0B: "b0 \<in> B" and hb0subX: "b0 \<subseteq> X"
    using hBref hXnb by blast

  have hnb0: "neighborhood_of x X TX b0"
    using hBnb hb0B by blast
  have hxb0: "x \<in> b0"
    using hnb0 unfolding neighborhood_of_def by blast
  have hb0TX: "b0 \<in> TX"
    using hnb0 unfolding neighborhood_of_def by blast

  define U where "U n = \<Inter>(insert b0 (S n))" for n

  have hSsubB: "\<And>n. S n \<subseteq> B"
    unfolding S_def by blast

	  have hSinj: "\<And>n. inj_on f (S n)"
	  proof -
	    fix n
	    have "S n \<subseteq> B"
	      by (rule hSsubB)
	    show "inj_on f (S n)"
	      apply (rule inj_on_subset[OF hf])
	      apply (rule hSsubB)
	      done
	  qed

	  have hSfinite: "\<And>n. finite (S n)"
	  proof -
	    fix n
	    have himgsub: "f ` (S n) \<subseteq> {0..n}"
	    proof (rule subsetI)
	      fix k
	      assume hk: "k \<in> f ` (S n)"
	      obtain b where hb: "b \<in> S n" and hkf: "k = f b"
	        using hk by blast
	      have "f b \<le> n"
	        using hb unfolding S_def by blast
	      thus "k \<in> {0..n}"
	        using hkf by simp
	    qed
	    have hfinimg: "finite (f ` (S n))"
	      by (rule finite_subset[OF himgsub], simp)
    have "finite (f ` (S n)) \<longleftrightarrow> finite (S n)"
      by (rule finite_image_iff[OF hSinj])
    show "finite (S n)"
      by (rule iffD1[OF \<open>finite (f ` S n) \<longleftrightarrow> finite (S n)\<close> hfinimg])
  qed

  have hSsubTX: "\<And>n. S n \<subseteq> TX"
  proof (rule subsetI)
    fix n b
    assume hb: "b \<in> S n"
    have hbB: "b \<in> B"
      using hb unfolding S_def by blast
    have hnb: "neighborhood_of x X TX b"
      using hBnb hbB by blast
    show "b \<in> TX"
      using hnb unfolding neighborhood_of_def by blast
  qed

  have hU_open: "\<And>n. U n \<in> TX"
  proof -
    fix n
    have hfin: "finite (insert b0 (S n))"
      by (simp add: hSfinite)
    have hne: "insert b0 (S n) \<noteq> {}"
      by simp
    have hsub: "insert b0 (S n) \<subseteq> TX"
      using hb0TX hSsubTX by blast
    have "\<Inter>(insert b0 (S n)) \<in> TX"
    proof -
      have "finite (insert b0 (S n)) \<and> insert b0 (S n) \<noteq> {} \<and> insert b0 (S n) \<subseteq> TX"
        using hfin hne hsub by blast
      thus ?thesis
        using inter_TX by blast
    qed
    thus "U n \<in> TX"
      unfolding U_def by simp
  qed

  have hU_mem: "\<And>n. x \<in> U n"
  proof -
    fix n
    have hxInAll: "\<forall>b\<in>S n. x \<in> b"
    proof (intro ballI)
      fix b assume hb: "b \<in> S n"
      have hbB: "b \<in> B"
        using hb unfolding S_def by blast
      have hnb: "neighborhood_of x X TX b"
        using hBnb hbB by blast
      show "x \<in> b"
        using hnb unfolding neighborhood_of_def by blast
    qed
    have hxInAll': "\<forall>b\<in>insert b0 (S n). x \<in> b"
    proof (intro ballI)
      fix b
      assume hb: "b \<in> insert b0 (S n)"
      show "x \<in> b"
      proof (cases "b = b0")
        case True
        show ?thesis using True hxb0 by simp
      next
        case False
        have "b \<in> S n"
          using hb False by blast
        thus ?thesis
          using hxInAll by blast
      qed
	    qed
	    have "x \<in> \<Inter>(insert b0 (S n))"
	    proof (rule InterI)
	      fix b
	      assume hb: "b \<in> insert b0 (S n)"
	      show "x \<in> b"
	        using hxInAll' hb by blast
	    qed
	    thus "x \<in> U n"
	      unfolding U_def by simp
	  qed

  have hU_nb: "\<And>n. neighborhood_of x X TX (U n)"
    unfolding neighborhood_of_def
    by (intro conjI, rule hU_open, rule hU_mem)

  have hU_mono: "\<And>m n. n \<le> m \<Longrightarrow> U m \<subseteq> U n"
  proof -
	    fix m n :: nat
	    assume hnm: "n \<le> m"
	    have hSnSm: "S n \<subseteq> S m"
	    proof (rule subsetI)
	      fix b
	      assume hb: "b \<in> S n"
	      have hbB: "b \<in> B" and hfb: "f b \<le> n"
	        using hb unfolding S_def by blast+
	      have "f b \<le> m"
	        using hfb hnm by simp
	      show "b \<in> S m"
	        unfolding S_def using hbB \<open>f b \<le> m\<close> by blast
	    qed
    have hins: "insert b0 (S n) \<subseteq> insert b0 (S m)"
      using hSnSm by blast
    have "\<Inter>(insert b0 (S m)) \<subseteq> \<Inter>(insert b0 (S n))"
      by (rule Inter_anti_mono[OF hins])
    thus "U m \<subseteq> U n"
      unfolding U_def by simp
  qed

  have hU_ref: "\<forall>V. neighborhood_of x X TX V \<longrightarrow> (\<exists>N. U N \<subseteq> V)"
  proof (intro allI impI)
    fix V
    assume hV: "neighborhood_of x X TX V"
    obtain b where hbb: "b \<in> B" and hbV: "b \<subseteq> V"
      using hBref hV by blast
    define N where "N = f b"
    have hbSN: "b \<in> S N"
      unfolding S_def N_def using hbb by simp
    have hbins: "b \<in> insert b0 (S N)"
      using hbSN by blast
	    have hInter_sub: "\<Inter>(insert b0 (S N)) \<subseteq> b"
	      by (rule Inter_lower[OF hbins])
	    have hUNb: "U N \<subseteq> b"
	      unfolding U_def by (rule hInter_sub)
	    have hUNV: "U N \<subseteq> V"
	      by (rule subset_trans[OF hUNb hbV])
	    show "\<exists>N. U N \<subseteq> V"
	      by (rule exI[where x=N], rule hUNV)
	  qed

  have hU_intersects: "\<And>n. intersects (U n) A"
    using hU_nb hnbA by blast

  define s where "s n = (SOME a. a \<in> A \<and> a \<in> U n)" for n

  have hsA: "\<forall>n. s n \<in> A"
  proof (intro allI)
    fix n
    have hnonempty: "\<exists>a. a \<in> A \<and> a \<in> U n"
    proof -
      have "U n \<inter> A \<noteq> {}"
        using hU_intersects[of n] unfolding intersects_def by simp
      then obtain a where ha: "a \<in> U n \<inter> A"
        by blast
      show ?thesis
        using ha by blast
    qed
    have "s n \<in> A \<and> s n \<in> U n"
      unfolding s_def by (rule someI_ex[OF hnonempty])
    thus "s n \<in> A"
      by simp
  qed

  have hsU: "\<forall>n. s n \<in> U n"
  proof (intro allI)
    fix n
    have hnonempty: "\<exists>a. a \<in> A \<and> a \<in> U n"
    proof -
      have "U n \<inter> A \<noteq> {}"
        using hU_intersects[of n] unfolding intersects_def by simp
      then obtain a where ha: "a \<in> U n \<inter> A"
        by blast
      show ?thesis
        using ha by blast
    qed
    have "s n \<in> A \<and> s n \<in> U n"
      unfolding s_def by (rule someI_ex[OF hnonempty])
    thus "s n \<in> U n"
      by simp
  qed

  have hsconv: "seq_converges_to_on s x X TX"
    unfolding seq_converges_to_on_def
  proof (intro conjI allI impI)
    show "x \<in> X"
      by (rule hxX)
    fix V
    assume hV: "neighborhood_of x X TX V"
    obtain N where hUNV: "U N \<subseteq> V"
      using hU_ref hV by blast
    show "\<exists>N. \<forall>n\<ge>N. s n \<in> V"
    proof (rule exI[where x=N])
      show "\<forall>n\<ge>N. s n \<in> V"
      proof (intro allI impI)
        fix n
        assume hn: "n \<ge> N"
        have hUn: "U n \<subseteq> U N"
          by (rule hU_mono[OF hn])
        have hsnUn: "s n \<in> U n"
          using hsU by simp
        have "s n \<in> U N"
          using hsnUn hUn by blast
        thus "s n \<in> V"
          using hUNV by blast
      qed
    qed
  qed

  show ?thesis
    by (rule exI[where x=s], intro conjI, rule hsA, rule hsconv)
qed

theorem Theorem_30_1:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  shows
    "(\<forall>A x. A \<subseteq> X \<longrightarrow>
        ((\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX) \<longrightarrow> x \<in> closure_on X TX A)
      \<and> (top1_first_countable_on X TX \<longrightarrow> x \<in> closure_on X TX A
            \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)))"
    and
    "(\<forall>f. (\<forall>x\<in>X. f x \<in> Y) \<longrightarrow>
        ((top1_continuous_map_on X TX Y TY f
            \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                    \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY))
        \<and> (top1_first_countable_on X TX
            \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                    \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
            \<longrightarrow> top1_continuous_map_on X TX Y TY f)))"
proof -
  show "(\<forall>A x. A \<subseteq> X \<longrightarrow>
        ((\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX) \<longrightarrow> x \<in> closure_on X TX A)
      \<and> (top1_first_countable_on X TX \<longrightarrow> x \<in> closure_on X TX A
            \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)))"
  proof (intro allI)
    fix A x
    show "A \<subseteq> X \<longrightarrow>
        ((\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX) \<longrightarrow> x \<in> closure_on X TX A)
      \<and> (top1_first_countable_on X TX \<longrightarrow> x \<in> closure_on X TX A
            \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX))"
    proof (intro impI)
      assume hAX: "A \<subseteq> X"
      show "((\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)
            \<longrightarrow> x \<in> closure_on X TX A)
        \<and> (top1_first_countable_on X TX \<longrightarrow> x \<in> closure_on X TX A
              \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX))"
      proof (intro conjI)
        show "(\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX) \<longrightarrow>
              x \<in> closure_on X TX A"
        proof
          assume hex: "\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX"
          obtain s where hsA: "\<forall>n. s n \<in> A" and hsconv: "seq_converges_to_on s x X TX"
            using hex by blast
          show "x \<in> closure_on X TX A"
            by (rule seq_converges_to_on_in_set_imp_closure[OF hTX hAX hsA hsconv])
        qed

        show "top1_first_countable_on X TX \<longrightarrow> x \<in> closure_on X TX A
              \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)"
        proof
          assume h1st: "top1_first_countable_on X TX"
          show "x \<in> closure_on X TX A
                \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)"
          proof
            assume hxcl: "x \<in> closure_on X TX A"
            show "\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX"
              by (rule first_countable_closure_imp_seq[OF hTX hAX h1st hxcl])
          qed
        qed
      qed
    qed
  qed

  show "(\<forall>f. (\<forall>x\<in>X. f x \<in> Y) \<longrightarrow>
        ((top1_continuous_map_on X TX Y TY f
            \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                    \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY))
        \<and> (top1_first_countable_on X TX
            \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                    \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
            \<longrightarrow> top1_continuous_map_on X TX Y TY f)))"
  proof (intro allI impI)
    fix f
    assume hmap: "\<forall>x\<in>X. f x \<in> Y"

    show "((top1_continuous_map_on X TX Y TY f
             \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                     \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY))
        \<and> (top1_first_countable_on X TX
             \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                     \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
             \<longrightarrow> top1_continuous_map_on X TX Y TY f))"
    proof (intro conjI)
      show "top1_continuous_map_on X TX Y TY f
        \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
          \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)"
      proof (intro impI allI)
        assume hcont: "top1_continuous_map_on X TX Y TY f"
        fix s x
        assume hs: "seq_converges_to_on s x X TX"
        show "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
          by (rule Theorem_21_3_forward[OF hTX hTY hcont hs])
      qed

      show "top1_first_countable_on X TX
        \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
          \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
        \<longrightarrow> top1_continuous_map_on X TX Y TY f"
      proof (intro impI)
        assume h1st: "top1_first_countable_on X TX"
        assume hseq:
          "\<forall>s x. seq_converges_to_on s x X TX
            \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"

        have hclosure:
          "\<forall>A. A \<subseteq> X \<longrightarrow> f ` (closure_on X TX A) \<subseteq> closure_on Y TY (f ` A)"
        proof (intro allI impI)
          fix A
          assume hAX: "A \<subseteq> X"
          show "f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A)"
          proof (rule subsetI)
            fix y
            assume hy: "y \<in> f ` closure_on X TX A"
            obtain x where hxcl: "x \<in> closure_on X TX A" and hyfx: "y = f x"
              using hy by blast

            obtain s where hsA: "\<forall>n. s n \<in> A" and hsconv: "seq_converges_to_on s x X TX"
              using first_countable_closure_imp_seq[OF hTX hAX h1st hxcl] by blast

            have hconvY: "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
            proof -
              have h1:
                "\<forall>x0. seq_converges_to_on s x0 X TX
                  \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x0) Y TY"
                using hseq by (rule spec[where x=s])
              have hImp:
                "seq_converges_to_on s x X TX
                  \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
                using h1 by (rule spec[where x=x])
              show ?thesis
                by (rule mp[OF hImp hsconv])
            qed

            have himgsub: "f ` A \<subseteq> Y"
            proof (rule subsetI)
              fix z
              assume hz: "z \<in> f ` A"
              obtain a where haA: "a \<in> A" and hzfa: "z = f a"
                using hz by blast
              have haX: "a \<in> X"
                using hAX haA by blast
              have "f a \<in> Y"
                using hmap haX by blast
              show "z \<in> Y"
                using hzfa \<open>f a \<in> Y\<close> by simp
            qed

            have hsimg: "\<forall>n. f (s n) \<in> f ` A"
            proof (intro allI)
              fix n
              have "s n \<in> A"
                using hsA by simp
              thus "f (s n) \<in> f ` A"
                by (rule imageI)
            qed

            have hfxcl: "f x \<in> closure_on Y TY (f ` A)"
              by (rule seq_converges_to_on_in_set_imp_closure[OF hTY himgsub hsimg hconvY])

            show "y \<in> closure_on Y TY (f ` A)"
              using hyfx hfxcl by simp
          qed
        qed

        have hEq:
          "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
            ((\<forall>x\<in>X. f x \<in> Y) \<and>
             (\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A)))"
          by (rule Theorem_18_1(1)[OF hTX hTY, of f])

        show "top1_continuous_map_on X TX Y TY f"
          apply (rule iffD2[OF hEq])
          apply (intro conjI)
           apply (rule hmap)
          apply (rule hclosure)
          done
      qed
    qed
  qed
qed

theorem Theorem_30_2:
  shows "(\<forall>X TX Y. top1_first_countable_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_first_countable_on Y (subspace_topology X TX Y))"
    and "(\<forall>I X T. top1_countable I \<and> (\<forall>i\<in>I. top1_first_countable_on (X i) (T i))
            \<longrightarrow> top1_first_countable_on (top1_PiE I X) (top1_product_topology_on I X T))"
    and "(\<forall>X TX Y. top1_second_countable_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_second_countable_on Y (subspace_topology X TX Y))"
    and "(\<forall>I X T. top1_countable I \<and> (\<forall>i\<in>I. top1_second_countable_on (X i) (T i))
            \<longrightarrow> top1_second_countable_on (top1_PiE I X) (top1_product_topology_on I X T))"
proof -
  show "(\<forall>X TX Y. top1_first_countable_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_first_countable_on Y (subspace_topology X TX Y))"
  proof (intro allI impI)
    fix X TX Y
    assume h: "top1_first_countable_on X TX \<and> Y \<subseteq> X"
    have h1st: "top1_first_countable_on X TX"
      using h by blast
    have hYX: "Y \<subseteq> X"
      using h by blast
    show "top1_first_countable_on Y (subspace_topology X TX Y)"
      by (rule Theorem_30_2_first_countable_subspace[OF h1st hYX])
  qed
  show "(\<forall>I X T. top1_countable I \<and> (\<forall>i\<in>I. top1_first_countable_on (X i) (T i))
            \<longrightarrow> top1_first_countable_on (top1_PiE I X) (top1_product_topology_on I X T))"
  proof (intro allI impI)
    fix I X T
    assume h: "top1_countable I \<and> (\<forall>i\<in>I. top1_first_countable_on (X i) (T i))"
    have hI: "top1_countable I"
      using h by blast
    have hfac: "\<forall>i\<in>I. top1_first_countable_on (X i) (T i)"
      using h by blast
    show "top1_first_countable_on (top1_PiE I X) (top1_product_topology_on I X T)"
      by (rule Theorem_30_2_first_countable_product[OF hI hfac])
  qed
  show "(\<forall>X TX Y. top1_second_countable_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_second_countable_on Y (subspace_topology X TX Y))"
  proof (intro allI impI)
    fix X TX Y
    assume h: "top1_second_countable_on X TX \<and> Y \<subseteq> X"
    have h2nd: "top1_second_countable_on X TX"
      using h by blast
    have hYX: "Y \<subseteq> X"
      using h by blast
    show "top1_second_countable_on Y (subspace_topology X TX Y)"
      by (rule Theorem_30_2_second_countable_subspace[OF h2nd hYX])
  qed
  show "(\<forall>I X T. top1_countable I \<and> (\<forall>i\<in>I. top1_second_countable_on (X i) (T i))
            \<longrightarrow> top1_second_countable_on (top1_PiE I X) (top1_product_topology_on I X T))"
  proof (intro allI impI)
    fix I X T
    assume h: "top1_countable I \<and> (\<forall>i\<in>I. top1_second_countable_on (X i) (T i))"
    have hI: "top1_countable I"
      using h by blast
    have hfac: "\<forall>i\<in>I. top1_second_countable_on (X i) (T i)"
      using h by blast
    show "top1_second_countable_on (top1_PiE I X) (top1_product_topology_on I X T)"
      by (rule Theorem_30_2_second_countable_product[OF hI hfac])
  qed
qed

(** from \S30 Theorem 30.3(a) (Second-countable \<Longrightarrow> Lindelöf) [top1.tex:~4020] **)
theorem Theorem_30_3a:
  assumes h2nd: "top1_second_countable_on X T"
  assumes hUc: "Uc \<subseteq> T"
  assumes hcov: "X \<subseteq> \<Union>Uc"
  shows "\<exists>V. top1_countable V \<and> V \<subseteq> Uc \<and> X \<subseteq> \<Union>V"
proof -
  obtain B where hBcnt: "top1_countable B" and hBasis: "basis_for X B T"
    using h2nd unfolding top1_second_countable_on_def by blast
  have hT_def: "T = topology_generated_by_basis X B"
    using hBasis unfolding basis_for_def by blast
  have hB_basis: "is_basis_on X B"
    using hBasis unfolding basis_for_def by blast
  have hTop: "is_topology_on X T"
    unfolding hT_def by (rule topology_generated_by_basis_is_topology_on[OF hB_basis])

  define J where "J = {b\<in>B. \<exists>U\<in>Uc. b \<subseteq> U}"

  have hJcnt: "top1_countable J"
  proof -
    have "J \<subseteq> B"
      unfolding J_def by blast
    thus ?thesis
      by (rule top1_countable_subset[OF hBcnt])
  qed

  have ex_pick: "\<forall>b\<in>J. \<exists>U. U \<in> Uc \<and> b \<subseteq> U"
    unfolding J_def by blast

  obtain pick where hpick: "\<forall>b\<in>J. pick b \<in> Uc \<and> b \<subseteq> pick b"
    using bchoice[OF ex_pick] by blast

  define V where "V = pick ` J"

  have hVcnt: "top1_countable V"
    unfolding V_def by (rule top1_countable_image[OF hJcnt])

  have hVsub: "V \<subseteq> Uc"
  proof (rule subsetI)
    fix U assume hU: "U \<in> V"
    obtain b where hbJ: "b \<in> J" and hUeq: "U = pick b"
      using hU unfolding V_def by blast
    have "pick b \<in> Uc"
      using hpick hbJ by blast
    thus "U \<in> Uc"
      using hUeq by simp
  qed

  have hVcov: "X \<subseteq> \<Union>V"
  proof (rule subsetI)
    fix x assume hxX: "x \<in> X"
    have hxUc: "x \<in> \<Union>Uc"
      using hcov hxX by blast
    then obtain U0 where hU0Uc: "U0 \<in> Uc" and hxU0: "x \<in> U0"
      by blast
    have hU0T: "U0 \<in> T"
      using hUc hU0Uc by blast
    have hU0_open: "U0 \<in> topology_generated_by_basis X B"
      using hU0T unfolding hT_def by simp
    have exb: "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U0"
      using hU0_open hxU0 unfolding topology_generated_by_basis_def by blast
    obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbU0: "b \<subseteq> U0"
      using exb by blast
    have hbJ: "b \<in> J"
      unfolding J_def using hbB hU0Uc hbU0 by blast
    have hpb: "pick b \<in> Uc \<and> b \<subseteq> pick b"
      using hpick hbJ by blast
    have hxpick: "x \<in> pick b"
      using hxb hpb by blast
    have "pick b \<in> V"
      unfolding V_def by (rule imageI[OF hbJ])
    thus "x \<in> \<Union>V"
      using hxpick by blast
  qed

  show ?thesis
    by (rule exI[where x=V], intro conjI, rule hVcnt, rule hVsub, rule hVcov)
qed

(** A convenient corollary of Theorem 30.3(a): on a second-countable space, every open cover
    of a closed subset has a countable subcover. **)
lemma second_countable_countable_subcover_of_closed:
  assumes h2nd: "top1_second_countable_on X T"
  assumes hA: "closedin_on X T A"
  assumes hUc: "Uc \<subseteq> T"
  assumes hcov: "A \<subseteq> \<Union>Uc"
  shows "\<exists>V. top1_countable V \<and> V \<subseteq> Uc \<and> A \<subseteq> \<Union>V"
proof -
  have hXA_open: "X - A \<in> T"
    by (rule closedin_diff_open[OF hA])

  define UcX where "UcX = insert (X - A) Uc"

  have hUcX_sub: "UcX \<subseteq> T"
    unfolding UcX_def using hUc hXA_open by blast

  have hcovX: "X \<subseteq> \<Union>UcX"
  proof (rule subsetI)
    fix x assume hxX: "x \<in> X"
    show "x \<in> \<Union>UcX"
    proof (cases "x \<in> A")
      case True
      have hxA: "x \<in> A" using True .
      have hxU: "x \<in> \<Union>Uc"
        using hcov hxA by blast
      then obtain U where hUUc: "U \<in> Uc" and hxUin: "x \<in> U"
        by blast
      have "U \<in> UcX"
        unfolding UcX_def using hUUc by blast
      thus ?thesis
        using hxUin by blast
    next
      case False
      have hxXA: "x \<in> X - A"
        using hxX False by blast
      have "X - A \<in> UcX"
        unfolding UcX_def by blast
      thus ?thesis
        using hxXA by blast
    qed
  qed

  obtain V where hVcnt: "top1_countable V" and hVsub: "V \<subseteq> UcX" and hVcov: "X \<subseteq> \<Union>V"
    using Theorem_30_3a[OF h2nd hUcX_sub hcovX] by blast

  define V' where "V' = V - {X - A}"

  have hV'cnt: "top1_countable V'"
  proof -
    have "V' \<subseteq> V"
      unfolding V'_def by blast
    thus ?thesis
      by (rule top1_countable_subset[OF hVcnt])
  qed

  have hV'sub: "V' \<subseteq> Uc"
  proof (rule subsetI)
    fix U assume hU: "U \<in> V'"
    have hUV: "U \<in> V" and hUne: "U \<noteq> X - A"
      using hU unfolding V'_def by blast+
    have hU_UcX: "U \<in> UcX"
      using hVsub hUV by blast
    have hcase: "U = X - A \<or> U \<in> Uc"
      using hU_UcX unfolding UcX_def by blast
    show "U \<in> Uc"
    proof (rule disjE[OF hcase])
      assume hUeq: "U = X - A"
      show "U \<in> Uc"
        using hUne hUeq by contradiction
    next
      assume "U \<in> Uc"
      thus "U \<in> Uc" .
    qed
  qed

  have hV'cov: "A \<subseteq> \<Union>V'"
  proof (rule subsetI)
    fix x assume hxA: "x \<in> A"
    have hxX: "x \<in> X"
      by (rule closedin_sub[OF hA, THEN subsetD, OF hxA])
    have hxUV: "x \<in> \<Union>V"
      using hVcov hxX by blast
    then obtain U where hUV: "U \<in> V" and hxU: "x \<in> U"
      by blast
    have hU_UcX: "U \<in> UcX"
      using hVsub hUV by blast
    have hU_ne: "U \<noteq> X - A"
    proof
      assume hUeq: "U = X - A"
      have "x \<in> X - A"
        using hxU hUeq by simp
      thus False
        using hxA by blast
    qed
    have hUV': "U \<in> V'"
      unfolding V'_def using hUV hU_ne by blast
    show "x \<in> \<Union>V'"
      using hUV' hxU by blast
  qed

  show ?thesis
    by (rule exI[where x=V'], intro conjI, rule hV'cnt, rule hV'sub, rule hV'cov)
qed

(** from \S30 Theorem 30.3(b) (Second-countable \<Longrightarrow> separable) [top1.tex:~4030] **)
theorem Theorem_30_3b:
  assumes h2nd: "top1_second_countable_on X T"
  shows "\<exists>D. top1_countable D \<and> D \<subseteq> X \<and> closure_on X T D = X"
proof -
  obtain B where hBcnt: "top1_countable B" and hBasis: "basis_for X B T"
    using h2nd unfolding top1_second_countable_on_def by blast
  have hT_def: "T = topology_generated_by_basis X B"
    using hBasis unfolding basis_for_def by blast
  have hB_basis: "is_basis_on X B"
    using hBasis unfolding basis_for_def by blast
  have hTop: "is_topology_on X T"
    unfolding hT_def by (rule topology_generated_by_basis_is_topology_on[OF hB_basis])

  define B0 where "B0 = {b\<in>B. b \<noteq> {}}"
  have hB0cnt: "top1_countable B0"
  proof -
    have "B0 \<subseteq> B"
      unfolding B0_def by blast
    thus ?thesis
      by (rule top1_countable_subset[OF hBcnt])
  qed

  define pickpt :: "'a set \<Rightarrow> 'a"
    where "pickpt b = (SOME x. x \<in> b)" for b

  have pickpt_mem:
    "\<And>b. b \<in> B0 \<Longrightarrow> pickpt b \<in> b"
  proof -
    fix b assume hb: "b \<in> B0"
    have hbne: "b \<noteq> {}"
      using hb unfolding B0_def by blast
    have ex: "\<exists>x. x \<in> b"
      using hbne by (simp add: ex_in_conv)
    show "pickpt b \<in> b"
      unfolding pickpt_def by (rule someI_ex[OF ex])
  qed

  define D where "D = pickpt ` B0"

  have hDcnt: "top1_countable D"
    unfolding D_def by (rule top1_countable_image[OF hB0cnt])

  have hDsubX: "D \<subseteq> X"
  proof (rule subsetI)
    fix x assume hx: "x \<in> D"
    obtain b where hb0: "b \<in> B0" and hxeq: "x = pickpt b"
      using hx unfolding D_def by blast
    have hxb: "x \<in> b"
    proof -
      have "pickpt b \<in> b"
        by (rule pickpt_mem[OF hb0])
      thus ?thesis
        using hxeq by simp
    qed
    have hbB: "b \<in> B"
      using hb0 unfolding B0_def by blast
    have hBsub: "\<forall>b\<in>B. b \<subseteq> X"
      using hBasis unfolding basis_for_def is_basis_on_def by blast
    have hbX: "b \<subseteq> X"
      using hBsub hbB by blast
    show "x \<in> X"
      using hxb hbX by blast
  qed

  have hDdense: "closure_on X T D = X"
  proof (rule equalityI)
    show "closure_on X T D \<subseteq> X"
      by (rule closure_on_subset_carrier[OF hTop hDsubX])
    show "X \<subseteq> closure_on X T D"
    proof (rule subsetI)
      fix x assume hxX: "x \<in> X"
      have hxcl:
        "x \<in> closure_on X T D \<longleftrightarrow> (\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects U D)"
        by (rule Theorem_17_5a[OF hTop hxX hDsubX])
      have "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects U D"
      proof (intro allI impI)
        fix U assume hU: "neighborhood_of x X T U"
        have hUT: "U \<in> T" and hxU: "x \<in> U"
          using hU unfolding neighborhood_of_def by blast+
        have hU_open: "U \<in> topology_generated_by_basis X B"
          using hUT unfolding hT_def by simp
        obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
          using hU_open hxU unfolding topology_generated_by_basis_def by blast
        have hbne: "b \<noteq> {}"
          using hxb by blast
        have hb0: "b \<in> B0"
          unfolding B0_def using hbB hbne by blast
        have hxpick: "pickpt b \<in> b"
          by (rule pickpt_mem[OF hb0])
        have "pickpt b \<in> D"
          unfolding D_def by (rule imageI[OF hb0])
        moreover have "pickpt b \<in> U"
          using hxpick hbU by blast
        ultimately have "U \<inter> D \<noteq> {}"
          by blast
        thus "intersects U D"
          unfolding intersects_def by simp
      qed
      hence "x \<in> closure_on X T D"
        using hxcl by blast
      thus "x \<in> closure_on X T D" .
    qed
  qed

  show ?thesis
    by (rule exI[where x=D], intro conjI, rule hDcnt, rule hDsubX, rule hDdense)
qed

(** from \S30 Theorem 30.3 (Second-countable \(\Longrightarrow\) Lindelöf and separable) [top1.tex:~3944] **)
theorem Theorem_30_3:
  assumes h2nd: "top1_second_countable_on X T"
  shows "\<forall>Uc. Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc
           \<longrightarrow> (\<exists>V. top1_countable V \<and> V \<subseteq> Uc \<and> X \<subseteq> \<Union>V)"
    and "\<exists>D. top1_countable D \<and> D \<subseteq> X \<and> closure_on X T D = X"
proof -
  show "\<forall>Uc. Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc
           \<longrightarrow> (\<exists>V. top1_countable V \<and> V \<subseteq> Uc \<and> X \<subseteq> \<Union>V)"
  proof (intro allI impI)
    fix Uc
    assume hUc: "Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc"
    have hUcsub: "Uc \<subseteq> T"
      using hUc by blast
    have hcov: "X \<subseteq> \<Union>Uc"
      using hUc by blast
    show "\<exists>V. top1_countable V \<and> V \<subseteq> Uc \<and> X \<subseteq> \<Union>V"
      by (rule Theorem_30_3a[OF h2nd hUcsub hcov])
  qed
  show "\<exists>D. top1_countable D \<and> D \<subseteq> X \<and> closure_on X T D = X"
    by (rule Theorem_30_3b[OF h2nd])
qed

section \<open>\<S>31 The Separation Axioms\<close>

definition top1_T1_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_T1_on X T \<longleftrightarrow> is_topology_on X T \<and> (\<forall>x\<in>X. closedin_on X T {x})"

(** Every Hausdorff space is T1. **)
lemma hausdorff_imp_T1_on:
  assumes hH: "is_hausdorff_on X T"
  shows "top1_T1_on X T"
proof -
  have hT: "is_topology_on X T"
    using hH unfolding is_hausdorff_on_def by blast
  show ?thesis
    unfolding top1_T1_on_def
  proof (intro conjI)
    show "is_topology_on X T"
      by (rule hT)
    show "\<forall>x\<in>X. closedin_on X T {x}"
      using singleton_closed_in_hausdorff[OF hH] by blast
  qed
qed

(** from \S31 Definition (Regular space) [top1.tex:~4040] **)
definition top1_regular_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_regular_on X T \<longleftrightarrow>
     top1_T1_on X T \<and>
     (\<forall>x\<in>X. \<forall>C. closedin_on X T C \<and> x \<notin> C \<longrightarrow>
        (\<exists>U V. neighborhood_of x X T U \<and> V \<in> T \<and> C \<subseteq> V \<and> U \<inter> V = {}))"

(** Regular spaces are Hausdorff (as in \S31). **)
lemma regular_imp_hausdorff_on:
  assumes hR: "top1_regular_on X T"
  shows "is_hausdorff_on X T"
proof -
  have hT1: "top1_T1_on X T"
    using hR unfolding top1_regular_on_def by (rule conjunct1)
  have hTop: "is_topology_on X T"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)
  have hSep:
    "\<forall>x\<in>X. \<forall>C. closedin_on X T C \<and> x \<notin> C \<longrightarrow>
       (\<exists>U V. neighborhood_of x X T U \<and> V \<in> T \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    using hR unfolding top1_regular_on_def by (rule conjunct2)

  show ?thesis
    unfolding is_hausdorff_on_def
  proof (intro conjI)
    show "is_topology_on X T"
      by (rule hTop)
    show "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
       (\<exists>U V. neighborhood_of x X T U \<and> neighborhood_of y X T V \<and> U \<inter> V = {})"
    proof (intro ballI impI)
      fix x y
      assume hxX: "x \<in> X" and hyX: "y \<in> X"
      assume hne: "x \<noteq> y"
      have hycl: "closedin_on X T {y}"
        using hT1 hyX unfolding top1_T1_on_def by blast
      have hxny: "x \<notin> {y}"
        using hne by blast
      obtain U V where hnbx: "neighborhood_of x X T U" and hV: "V \<in> T"
          and hyV: "{y} \<subseteq> V" and hdisj: "U \<inter> V = {}"
        using hSep[rule_format, OF hxX, of "{y}"] hycl hxny by blast
      have hyVmem: "y \<in> V"
        using hyV by blast
      have hnby: "neighborhood_of y X T V"
        unfolding neighborhood_of_def
        by (intro conjI, rule hV, rule hyVmem)
      show "\<exists>U V. neighborhood_of x X T U \<and> neighborhood_of y X T V \<and> U \<inter> V = {}"
        by (rule exI[where x=U], rule exI[where x=V], intro conjI, rule hnbx, rule hnby, rule hdisj)
    qed
  qed
qed

(** from \S31 Theorem 31.2(b): subspaces of regular spaces are regular. **)
theorem Theorem_31_2_regular_subspace:
  assumes hR: "top1_regular_on X T"
  assumes hYX: "Y \<subseteq> X"
  shows "top1_regular_on Y (subspace_topology X T Y)"
proof -
  let ?TY = "subspace_topology X T Y"

  have hT1: "top1_T1_on X T"
    using hR unfolding top1_regular_on_def by (rule conjunct1)
  have hTop: "is_topology_on X T"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  have hT1Y: "top1_T1_on Y ?TY"
  proof (unfold top1_T1_on_def, intro conjI)
    show "is_topology_on Y ?TY"
      by (rule subspace_topology_is_topology_on[OF hTop hYX])
    show "\<forall>y\<in>Y. closedin_on Y ?TY {y}"
    proof (intro ballI)
      fix y assume hyY: "y \<in> Y"
      have hyX: "y \<in> X"
        using hYX hyY by blast
      have hyclX: "closedin_on X T {y}"
        using hT1 hyX unfolding top1_T1_on_def by blast
      have hEq: "{y} = {y} \<inter> Y"
        using hyY by blast
      have exC: "\<exists>C. closedin_on X T C \<and> {y} = C \<inter> Y"
        apply (rule exI[where x="{y}"])
        apply (intro conjI)
         apply (rule hyclX)
        apply (rule hEq)
        done
      show "closedin_on Y ?TY {y}"
        by (rule iffD2[OF Theorem_17_2[OF hTop hYX, of "{y}"] exC])
    qed
  qed

  have hSep:
    "\<forall>x\<in>X. \<forall>C. closedin_on X T C \<and> x \<notin> C \<longrightarrow>
       (\<exists>U V. neighborhood_of x X T U \<and> V \<in> T \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    using hR unfolding top1_regular_on_def by (rule conjunct2)

  show ?thesis
    unfolding top1_regular_on_def
  proof (intro conjI)
    show "top1_T1_on Y ?TY"
      by (rule hT1Y)
    show "\<forall>x\<in>Y. \<forall>C. closedin_on Y ?TY C \<and> x \<notin> C
      \<longrightarrow> (\<exists>U V. neighborhood_of x Y ?TY U \<and> V \<in> ?TY \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro ballI allI impI)
      fix x C
      assume hxY: "x \<in> Y"
      assume hC: "closedin_on Y ?TY C \<and> x \<notin> C"
      have hxX: "x \<in> X"
        using hYX hxY by blast
      have hCsubY: "C \<subseteq> Y"
        using hC by (blast dest: closedin_sub)

      obtain D where hDcl: "closedin_on X T D" and hDeq: "C = D \<inter> Y"
        using Theorem_17_2[OF hTop hYX, of C] hC
        by blast

      have hxnotD: "x \<notin> D"
      proof
        assume hxD: "x \<in> D"
        have "x \<in> D \<inter> Y"
          using hxD hxY by blast
        thus False
          using hC hDeq by blast
      qed

      obtain U V where hnbx: "neighborhood_of x X T U" and hV: "V \<in> T"
          and hDV: "D \<subseteq> V" and hdisj: "U \<inter> V = {}"
        using hSep[rule_format, OF hxX, of D] hDcl hxnotD by blast

      define U' where "U' = Y \<inter> U"
      define V' where "V' = Y \<inter> V"

      have hU'TY: "U' \<in> ?TY"
        unfolding U'_def subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x=U])
        apply (intro conjI)
         apply (rule refl)
        using hnbx unfolding neighborhood_of_def by blast
      have hV'TY: "V' \<in> ?TY"
        unfolding V'_def subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x=V])
        apply (intro conjI)
         apply (rule refl)
        apply (rule hV)
        done

      have hxU': "x \<in> U'"
      proof -
        have hxU: "x \<in> U"
          using hnbx unfolding neighborhood_of_def by blast
        show ?thesis
          unfolding U'_def using hxY hxU by blast
      qed
      have hnbxY: "neighborhood_of x Y ?TY U'"
        unfolding neighborhood_of_def by (intro conjI, rule hU'TY, rule hxU')

      have hCsubV': "C \<subseteq> V'"
      proof -
        have "D \<inter> Y \<subseteq> V \<inter> Y"
          using hDV by blast
        thus ?thesis
          unfolding hDeq V'_def by simp
      qed

      have hdisj': "U' \<inter> V' = {}"
        unfolding U'_def V'_def using hdisj by blast

      show "\<exists>U V. neighborhood_of x Y ?TY U \<and> V \<in> ?TY \<and> C \<subseteq> V \<and> U \<inter> V = {}"
        by (rule exI[where x=U'], rule exI[where x=V'], intro conjI, rule hnbxY, rule hV'TY, rule hCsubV', rule hdisj')
    qed
  qed
qed

(** Regularity yields the standard "point shrinking" lemma:
    if x lies in an open set U, there exists an open neighborhood V of x whose closure is still inside U. **)
lemma regular_refine_point_into_open:
  assumes hR: "top1_regular_on X T"
  assumes hxX: "x \<in> X"
  assumes hU: "U \<in> T" and hUX: "U \<subseteq> X"
  assumes hxU: "x \<in> U"
  shows "\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U"
proof -
  have hT1: "top1_T1_on X T"
    using hR unfolding top1_regular_on_def by (rule conjunct1)
  have hTop: "is_topology_on X T"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)
  have hXT: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])

  have hSep:
    "\<forall>x\<in>X. \<forall>C. closedin_on X T C \<and> x \<notin> C \<longrightarrow>
       (\<exists>U0 V0. neighborhood_of x X T U0 \<and> V0 \<in> T \<and> C \<subseteq> V0 \<and> U0 \<inter> V0 = {})"
    using hR unfolding top1_regular_on_def by (rule conjunct2)

  let ?C = "X - U"

  have hCcl: "closedin_on X T ?C"
  proof (rule closedin_intro)
    show "?C \<subseteq> X" by (rule Diff_subset)
    show "X - ?C \<in> T"
    proof -
      have eq: "X - (X - U) = X \<inter> U" by blast
      have hXU: "X \<inter> U \<in> T"
        by (rule topology_inter2[OF hTop hXT hU])
      show ?thesis using eq hXU by simp
    qed
  qed

  have hxC: "x \<notin> ?C"
    using hxU by blast

  have hSepx:
    "\<forall>C. closedin_on X T C \<and> x \<notin> C
      \<longrightarrow> (\<exists>U0 V0. neighborhood_of x X T U0 \<and> V0 \<in> T \<and> C \<subseteq> V0 \<and> U0 \<inter> V0 = {})"
    by (rule bspec[OF hSep hxX])
  have hSepC:
    "closedin_on X T ?C \<and> x \<notin> ?C
      \<longrightarrow> (\<exists>U0 V0. neighborhood_of x X T U0 \<and> V0 \<in> T \<and> ?C \<subseteq> V0 \<and> U0 \<inter> V0 = {})"
    by (rule spec[where x="?C", OF hSepx])

  have exUV: "\<exists>U0 V0. neighborhood_of x X T U0 \<and> V0 \<in> T \<and> ?C \<subseteq> V0 \<and> U0 \<inter> V0 = {}"
    apply (rule mp[OF hSepC])
    apply (intro conjI)
     apply (rule hCcl)
    apply (rule hxC)
    done

  obtain U0 V0 where hnb: "neighborhood_of x X T U0" and hV0: "V0 \<in> T"
      and hCV0: "?C \<subseteq> V0" and hdisj: "U0 \<inter> V0 = {}"
    using exUV by blast

  have hU0: "U0 \<in> T" and hxU0: "x \<in> U0"
    using hnb unfolding neighborhood_of_def by blast+

  let ?V = "X \<inter> U0"
  let ?W = "X \<inter> V0"

  have hVopen: "?V \<in> T"
    by (rule topology_inter2[OF hTop hXT hU0])
  have hWopen: "?W \<in> T"
    by (rule topology_inter2[OF hTop hXT hV0])

  have hVsubX: "?V \<subseteq> X" by blast
  have hxV: "x \<in> ?V" using hxX hxU0 by blast

  have hVsubXmW: "?V \<subseteq> X - ?W"
    using hdisj by blast

  have hXmW_closed: "closedin_on X T (X - ?W)"
  proof (rule closedin_intro)
    show "X - ?W \<subseteq> X" by (rule Diff_subset)
    show "X - (X - ?W) \<in> T"
    proof -
      have eq: "X - (X - ?W) = ?W" by blast
      show ?thesis using eq hWopen by simp
    qed
  qed

  have hclV_sub_XmW: "closure_on X T ?V \<subseteq> X - ?W"
    by (rule closure_on_subset_of_closed[OF hXmW_closed hVsubXmW])

  have hXmW_sub_U: "X - ?W \<subseteq> U"
  proof (rule subsetI)
    fix z assume hz: "z \<in> X - ?W"
    have hzX: "z \<in> X" using hz by blast
    have hznotW: "z \<notin> ?W" using hz by blast
    have hznotC: "z \<notin> ?C"
    proof
      assume hzC: "z \<in> ?C"
      have hzV0: "z \<in> V0" using hCV0 hzC by blast
      have "z \<in> ?W" using hzX hzV0 by blast
      thus False using hznotW by blast
    qed
    have hzU: "z \<in> U" using hzX hznotC by blast
    show "z \<in> U" by (rule hzU)
  qed

  have hclV_sub_U: "closure_on X T ?V \<subseteq> U"
    by (rule subset_trans[OF hclV_sub_XmW hXmW_sub_U])

  show ?thesis
    apply (rule exI[where x="?V"])
    apply (intro conjI)
       apply (rule hVopen)
      apply (rule hVsubX)
     apply (rule hxV)
    apply (rule hclV_sub_U)
    done
qed

(** Closure of a rectangle is contained in the product of closures (for the product topology). **)
lemma closure_on_product_rect_subset_prod_closure:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hAX: "A \<subseteq> X"
  assumes hBY: "B \<subseteq> Y"
  shows "closure_on (X \<times> Y) (product_topology_on TX TY) (A \<times> B)
          \<subseteq> (closure_on X TX A) \<times> (closure_on Y TY B)"
proof (rule subsetI)
  let ?TP = "product_topology_on TX TY"
  fix p
  assume hp: "p \<in> closure_on (X \<times> Y) ?TP (A \<times> B)"

  have hTopXY: "is_topology_on (X \<times> Y) ?TP"
    by (rule product_topology_on_is_topology_on[OF hTX hTY])

  have hcont1: "top1_continuous_map_on (X \<times> Y) ?TP X TX pi1"
    by (rule top1_continuous_pi1[OF hTX hTY])
  have hcont2: "top1_continuous_map_on (X \<times> Y) ?TP Y TY pi2"
    by (rule top1_continuous_pi2[OF hTX hTY])

  have hABsubXY: "A \<times> B \<subseteq> X \<times> Y"
    using hAX hBY by blast

  have hpi1_cl: "\<forall>S. S \<subseteq> X \<times> Y \<longrightarrow> pi1 ` closure_on (X \<times> Y) ?TP S \<subseteq> closure_on X TX (pi1 ` S)"
  proof -
    have hEq:
      "top1_continuous_map_on (X \<times> Y) ?TP X TX pi1 \<longleftrightarrow>
        ((\<forall>q\<in>X \<times> Y. pi1 q \<in> X) \<and>
         (\<forall>S. S \<subseteq> X \<times> Y \<longrightarrow> pi1 ` closure_on (X \<times> Y) ?TP S \<subseteq> closure_on X TX (pi1 ` S)))"
      by (rule Theorem_18_1(1)[OF hTopXY hTX, of pi1])
    have hMapCl:
      "(\<forall>q\<in>X \<times> Y. pi1 q \<in> X) \<and>
       (\<forall>S. S \<subseteq> X \<times> Y \<longrightarrow> pi1 ` closure_on (X \<times> Y) ?TP S \<subseteq> closure_on X TX (pi1 ` S))"
      by (rule iffD1[OF hEq hcont1])
    show ?thesis
      by (rule conjunct2[OF hMapCl])
  qed

  have hpi2_cl: "\<forall>S. S \<subseteq> X \<times> Y \<longrightarrow> pi2 ` closure_on (X \<times> Y) ?TP S \<subseteq> closure_on Y TY (pi2 ` S)"
  proof -
    have hEq:
      "top1_continuous_map_on (X \<times> Y) ?TP Y TY pi2 \<longleftrightarrow>
        ((\<forall>q\<in>X \<times> Y. pi2 q \<in> Y) \<and>
         (\<forall>S. S \<subseteq> X \<times> Y \<longrightarrow> pi2 ` closure_on (X \<times> Y) ?TP S \<subseteq> closure_on Y TY (pi2 ` S)))"
      by (rule Theorem_18_1(1)[OF hTopXY hTY, of pi2])
    have hMapCl:
      "(\<forall>q\<in>X \<times> Y. pi2 q \<in> Y) \<and>
       (\<forall>S. S \<subseteq> X \<times> Y \<longrightarrow> pi2 ` closure_on (X \<times> Y) ?TP S \<subseteq> closure_on Y TY (pi2 ` S))"
      by (rule iffD1[OF hEq hcont2])
    show ?thesis
      by (rule conjunct2[OF hMapCl])
  qed

  have hpi1_img_cl:
    "pi1 ` closure_on (X \<times> Y) ?TP (A \<times> B) \<subseteq> closure_on X TX (pi1 ` (A \<times> B))"
  proof -
    have hImp:
      "A \<times> B \<subseteq> X \<times> Y \<longrightarrow>
        pi1 ` closure_on (X \<times> Y) ?TP (A \<times> B) \<subseteq> closure_on X TX (pi1 ` (A \<times> B))"
      by (rule spec[where x="A \<times> B", OF hpi1_cl])
    show ?thesis
      by (rule mp[OF hImp hABsubXY])
  qed

  have hpi2_img_cl:
    "pi2 ` closure_on (X \<times> Y) ?TP (A \<times> B) \<subseteq> closure_on Y TY (pi2 ` (A \<times> B))"
  proof -
    have hImp:
      "A \<times> B \<subseteq> X \<times> Y \<longrightarrow>
        pi2 ` closure_on (X \<times> Y) ?TP (A \<times> B) \<subseteq> closure_on Y TY (pi2 ` (A \<times> B))"
      by (rule spec[where x="A \<times> B", OF hpi2_cl])
    show ?thesis
      by (rule mp[OF hImp hABsubXY])
  qed

  have hpi1p_clAB: "pi1 p \<in> closure_on X TX (pi1 ` (A \<times> B))"
  proof -
    have hpi1p_img: "pi1 p \<in> pi1 ` closure_on (X \<times> Y) ?TP (A \<times> B)"
      by (rule imageI[OF hp])
    show ?thesis
      by (rule subsetD[OF hpi1_img_cl hpi1p_img])
  qed

  have hpi2p_clAB: "pi2 p \<in> closure_on Y TY (pi2 ` (A \<times> B))"
  proof -
    have hpi2p_img: "pi2 p \<in> pi2 ` closure_on (X \<times> Y) ?TP (A \<times> B)"
      by (rule imageI[OF hp])
    show ?thesis
      by (rule subsetD[OF hpi2_img_cl hpi2p_img])
  qed

  have hpi1_subA: "pi1 ` (A \<times> B) \<subseteq> A"
  proof (rule subsetI)
    fix x
    assume hx: "x \<in> pi1 ` (A \<times> B)"
    obtain q where hqAB: "q \<in> A \<times> B" and hxq: "pi1 q = x"
      using hx by blast
    obtain a b where hqab: "q = (a, b)"
      by (cases q, simp)
    have haA: "a \<in> A"
      using hqAB hqab by simp
    have hxfst: "x = a"
      using hxq hqab unfolding pi1_def by simp
    show "x \<in> A"
      using haA hxfst by simp
  qed

  have hpi2_subB: "pi2 ` (A \<times> B) \<subseteq> B"
  proof (rule subsetI)
    fix y0
    assume hy0: "y0 \<in> pi2 ` (A \<times> B)"
    obtain q where hqAB: "q \<in> A \<times> B" and hyq: "pi2 q = y0"
      using hy0 by blast
    obtain a b where hqab: "q = (a, b)"
      by (cases q, simp)
    have hbB: "b \<in> B"
      using hqAB hqab by simp
    have hyb: "y0 = b"
      using hyq hqab unfolding pi2_def by simp
    show "y0 \<in> B"
      using hbB hyb by simp
  qed

  have hcl_pi1AB_sub: "closure_on X TX (pi1 ` (A \<times> B)) \<subseteq> closure_on X TX A"
    by (rule closure_on_mono[OF hpi1_subA])
  have hcl_pi2AB_sub: "closure_on Y TY (pi2 ` (A \<times> B)) \<subseteq> closure_on Y TY B"
    by (rule closure_on_mono[OF hpi2_subB])

  have hpi1p_clA: "pi1 p \<in> closure_on X TX A"
    by (rule subsetD[OF hcl_pi1AB_sub hpi1p_clAB])
  have hpi2p_clB: "pi2 p \<in> closure_on Y TY B"
    by (rule subsetD[OF hcl_pi2AB_sub hpi2p_clAB])

  show "p \<in> (closure_on X TX A) \<times> (closure_on Y TY B)"
    using hpi1p_clA hpi2p_clB unfolding pi1_def pi2_def by (cases p, simp)
qed

(** from \S31 Theorem 31.2 (Hausdorff/regular: subspaces and products) [top1.tex:4075] **)
theorem Theorem_31_2:
  shows "(\<forall>X TX Y. is_hausdorff_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> is_hausdorff_on Y (subspace_topology X TX Y))"
    and "(\<forall>X TX Y TY. is_hausdorff_on X TX \<and> is_hausdorff_on Y TY
            \<longrightarrow> is_hausdorff_on (X \<times> Y) (product_topology_on TX TY))"
    and "(\<forall>X TX Y. top1_regular_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_regular_on Y (subspace_topology X TX Y))"
    and "(\<forall>X TX Y TY. top1_regular_on X TX \<and> top1_regular_on Y TY
            \<longrightarrow> top1_regular_on (X \<times> Y) (product_topology_on TX TY))"
proof -
  have hHausdProd:
    "\<forall>X1 T1 X2 T2.
      is_hausdorff_on X1 T1 \<and> is_hausdorff_on X2 T2 \<longrightarrow>
      is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2)"
    using Theorem_17_11 by blast
  have hHausdSub:
    "\<forall>X T Y. is_hausdorff_on X T \<and> Y \<subseteq> X \<longrightarrow> is_hausdorff_on Y (subspace_topology X T Y)"
    using Theorem_17_11 by blast

  show "(\<forall>X TX Y. is_hausdorff_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> is_hausdorff_on Y (subspace_topology X TX Y))"
    by (rule hHausdSub)
  show "(\<forall>X TX Y TY. is_hausdorff_on X TX \<and> is_hausdorff_on Y TY
            \<longrightarrow> is_hausdorff_on (X \<times> Y) (product_topology_on TX TY))"
    by (rule hHausdProd)
  show "(\<forall>X TX Y. top1_regular_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_regular_on Y (subspace_topology X TX Y))"
  proof (intro allI impI)
    fix X TX Y
    assume h: "top1_regular_on X TX \<and> Y \<subseteq> X"
    have hR: "top1_regular_on X TX"
      using h by blast
    have hYX: "Y \<subseteq> X"
      using h by blast
    show "top1_regular_on Y (subspace_topology X TX Y)"
      by (rule Theorem_31_2_regular_subspace[OF hR hYX])
  qed
  show "(\<forall>X TX Y TY. top1_regular_on X TX \<and> top1_regular_on Y TY
            \<longrightarrow> top1_regular_on (X \<times> Y) (product_topology_on TX TY))"
  proof (intro allI impI)
    fix X TX Y TY
    assume h: "top1_regular_on X TX \<and> top1_regular_on Y TY"
    have hRX: "top1_regular_on X TX" and hRY: "top1_regular_on Y TY"
      using h by blast+

    have hT1X: "top1_T1_on X TX"
      using hRX unfolding top1_regular_on_def by (rule conjunct1)
    have hT1Y: "top1_T1_on Y TY"
      using hRY unfolding top1_regular_on_def by (rule conjunct1)

    have hTopX: "is_topology_on X TX"
      using hT1X unfolding top1_T1_on_def by (rule conjunct1)
    have hTopY: "is_topology_on Y TY"
      using hT1Y unfolding top1_T1_on_def by (rule conjunct1)

    have hX_TX: "X \<in> TX"
      by (rule conjunct1[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]])
    have hY_TY: "Y \<in> TY"
      by (rule conjunct1[OF conjunct2[OF hTopY[unfolded is_topology_on_def]]])

    let ?TP = "product_topology_on TX TY"
    have hTopXY: "is_topology_on (X \<times> Y) ?TP"
      by (rule product_topology_on_is_topology_on[OF hTopX hTopY])

    have hHausdX: "is_hausdorff_on X TX"
      by (rule regular_imp_hausdorff_on[OF hRX])
    have hHausdY: "is_hausdorff_on Y TY"
      by (rule regular_imp_hausdorff_on[OF hRY])

    have hHausdXY: "is_hausdorff_on (X \<times> Y) ?TP"
    proof -
      have hImp: "is_hausdorff_on X TX \<and> is_hausdorff_on Y TY \<longrightarrow> is_hausdorff_on (X \<times> Y) ?TP"
      proof -
        have h1:
          "\<forall>T1 X2 T2. is_hausdorff_on X T1 \<and> is_hausdorff_on X2 T2
            \<longrightarrow> is_hausdorff_on (X \<times> X2) (product_topology_on T1 T2)"
          using hHausdProd by (rule spec[where x=X])
        have h2:
          "\<forall>X2 T2. is_hausdorff_on X TX \<and> is_hausdorff_on X2 T2
            \<longrightarrow> is_hausdorff_on (X \<times> X2) (product_topology_on TX T2)"
          using h1 by (rule spec[where x=TX])
        have h3:
          "\<forall>T2. is_hausdorff_on X TX \<and> is_hausdorff_on Y T2
            \<longrightarrow> is_hausdorff_on (X \<times> Y) (product_topology_on TX T2)"
          using h2 by (rule spec[where x=Y])
        have h4:
          "is_hausdorff_on X TX \<and> is_hausdorff_on Y TY
            \<longrightarrow> is_hausdorff_on (X \<times> Y) (product_topology_on TX TY)"
          using h3 by (rule spec[where x=TY])
        show ?thesis
          using h4 by simp
      qed
      show ?thesis
        apply (rule mp[OF hImp])
        apply (intro conjI)
         apply (rule hHausdX)
        apply (rule hHausdY)
        done
    qed

    have hT1XY: "top1_T1_on (X \<times> Y) ?TP"
      by (rule hausdorff_imp_T1_on[OF hHausdXY])

    show "top1_regular_on (X \<times> Y) ?TP"
      unfolding top1_regular_on_def
    proof (intro conjI)
      show "top1_T1_on (X \<times> Y) ?TP"
        by (rule hT1XY)
      show "\<forall>p\<in>X \<times> Y. \<forall>C. closedin_on (X \<times> Y) ?TP C \<and> p \<notin> C \<longrightarrow>
        (\<exists>U V. neighborhood_of p (X \<times> Y) ?TP U \<and> V \<in> ?TP \<and> C \<subseteq> V \<and> U \<inter> V = {})"
      proof (intro ballI allI impI)
        fix p C
        assume hpXY: "p \<in> X \<times> Y"
        assume hC: "closedin_on (X \<times> Y) ?TP C \<and> p \<notin> C"
        have hCcl: "closedin_on (X \<times> Y) ?TP C"
          using hC by blast
        have hpnotC: "p \<notin> C"
          using hC by blast

        have hCsubXY: "C \<subseteq> X \<times> Y"
          by (rule closedin_sub[OF hCcl])

        let ?W = "(X \<times> Y) - C"
        have hWopen: "?W \<in> ?TP"
          by (rule closedin_diff_open[OF hCcl])
        have hpW: "p \<in> ?W"
          using hpXY hpnotC by blast

        obtain U0 V0 where hU0: "U0 \<in> TX" and hV0: "V0 \<in> TY"
            and hpU0V0: "p \<in> U0 \<times> V0" and hrect_sub: "U0 \<times> V0 \<subseteq> ?W"
          by (rule top1_product_open_contains_rect[OF hWopen hpW])

        obtain x0 y0 where hp_def: "p = (x0, y0)"
          by (cases p, simp)
	        have hx0X_hy0Y: "x0 \<in> X \<and> y0 \<in> Y"
	          using hpXY by (simp add: hp_def)
	        have hx0X: "x0 \<in> X"
	          using hx0X_hy0Y by (elim conjE)
	        have hy0Y: "y0 \<in> Y"
	          using hx0X_hy0Y by (elim conjE)

	        have hx0U0_hy0V0: "x0 \<in> U0 \<and> y0 \<in> V0"
	          using hpU0V0 by (simp add: hp_def)
	        have hx0U0: "x0 \<in> U0"
	          using hx0U0_hy0V0 by (elim conjE)
	        have hy0V0: "y0 \<in> V0"
	          using hx0U0_hy0V0 by (elim conjE)

        let ?Ux = "U0 \<inter> X"
        let ?Uy = "V0 \<inter> Y"

        have hUx: "?Ux \<in> TX"
          by (rule topology_inter2[OF hTopX hU0 hX_TX])
        have hUy: "?Uy \<in> TY"
          by (rule topology_inter2[OF hTopY hV0 hY_TY])
        have hUx_subX: "?Ux \<subseteq> X" by blast
        have hUy_subY: "?Uy \<subseteq> Y" by blast

        have hx0Ux: "x0 \<in> ?Ux" using hx0U0 hx0X by blast
        have hy0Uy: "y0 \<in> ?Uy" using hy0V0 hy0Y by blast

        have hUxUy_sub: "?Ux \<times> ?Uy \<subseteq> ?W"
        proof -
          have hsub1: "?Ux \<times> ?Uy \<subseteq> U0 \<times> V0"
            by blast
          show ?thesis
            by (rule subset_trans[OF hsub1 hrect_sub])
        qed

        have exVx: "\<exists>Vx. Vx \<in> TX \<and> Vx \<subseteq> X \<and> x0 \<in> Vx \<and> closure_on X TX Vx \<subseteq> ?Ux"
          by (rule regular_refine_point_into_open[OF hRX hx0X hUx hUx_subX hx0Ux])
        obtain Vx where hVx: "Vx \<in> TX" and hVx_subX: "Vx \<subseteq> X" and hx0Vx: "x0 \<in> Vx"
            and hclVx: "closure_on X TX Vx \<subseteq> ?Ux"
          using exVx by blast

        have exVy: "\<exists>Vy. Vy \<in> TY \<and> Vy \<subseteq> Y \<and> y0 \<in> Vy \<and> closure_on Y TY Vy \<subseteq> ?Uy"
          by (rule regular_refine_point_into_open[OF hRY hy0Y hUy hUy_subY hy0Uy])
        obtain Vy where hVy: "Vy \<in> TY" and hVy_subY: "Vy \<subseteq> Y" and hy0Vy: "y0 \<in> Vy"
            and hclVy: "closure_on Y TY Vy \<subseteq> ?Uy"
          using exVy by blast

        let ?U = "Vx \<times> Vy"
        have hUopen: "?U \<in> ?TP"
          by (rule product_rect_open[OF hVx hVy])
        have hpU: "p \<in> ?U"
          using hp_def hx0Vx hy0Vy by simp

        have hUsubXY: "?U \<subseteq> X \<times> Y"
          using hVx_subX hVy_subY by blast

        have hclU_sub:
          "closure_on (X \<times> Y) ?TP ?U
            \<subseteq> (closure_on X TX Vx) \<times> (closure_on Y TY Vy)"
          by (rule closure_on_product_rect_subset_prod_closure[OF hTopX hTopY hVx_subX hVy_subY])
        have hcl_prod_sub_W: "closure_on (X \<times> Y) ?TP ?U \<subseteq> ?W"
        proof -
          have hprod_sub_UxUy:
            "(closure_on X TX Vx) \<times> (closure_on Y TY Vy) \<subseteq> ?Ux \<times> ?Uy"
            using hclVx hclVy by blast
          have hcl_sub_UxUy:
            "closure_on (X \<times> Y) ?TP ?U \<subseteq> ?Ux \<times> ?Uy"
            by (rule subset_trans[OF hclU_sub hprod_sub_UxUy])
          show ?thesis
            by (rule subset_trans[OF hcl_sub_UxUy hUxUy_sub])
        qed

        have hclU_closed: "closedin_on (X \<times> Y) ?TP (closure_on (X \<times> Y) ?TP ?U)"
          by (rule closure_on_closed[OF hTopXY hUsubXY])
        have hVopen: "(X \<times> Y) - closure_on (X \<times> Y) ?TP ?U \<in> ?TP"
          by (rule closedin_diff_open[OF hclU_closed])

        let ?V = "(X \<times> Y) - closure_on (X \<times> Y) ?TP ?U"

        have hC_sub_V: "C \<subseteq> ?V"
        proof (rule subsetI)
          fix c
          assume hc: "c \<in> C"
          have hcXY: "c \<in> X \<times> Y"
            using hCsubXY hc by blast
          show "c \<in> ?V"
          proof (rule DiffI)
            show "c \<in> X \<times> Y" by (rule hcXY)
            show "c \<notin> closure_on (X \<times> Y) ?TP ?U"
            proof
              assume hccl: "c \<in> closure_on (X \<times> Y) ?TP ?U"
              have "c \<in> (X \<times> Y) - C"
                using hcl_prod_sub_W hccl by blast
              thus False
                using hc by blast
            qed
          qed
        qed

        have hUsub_clU: "?U \<subseteq> closure_on (X \<times> Y) ?TP ?U"
          by (rule subset_closure_on)
        have hdisj: "?U \<inter> ?V = {}"
        proof (rule equalityI)
          show "?U \<inter> ?V \<subseteq> {}"
          proof (rule subsetI)
            fix z
            assume hz: "z \<in> ?U \<inter> ?V"
            have hzU: "z \<in> ?U" and hznot: "z \<notin> closure_on (X \<times> Y) ?TP ?U"
              using hz by blast+
            have "z \<in> closure_on (X \<times> Y) ?TP ?U"
              by (rule subsetD[OF hUsub_clU hzU])
            thus "z \<in> {}"
              using hznot by blast
          qed
          show "{} \<subseteq> ?U \<inter> ?V" by blast
        qed

        have hnbhd: "neighborhood_of p (X \<times> Y) ?TP ?U"
          unfolding neighborhood_of_def
          by (intro conjI hUopen hpU)

        show "\<exists>U V. neighborhood_of p (X \<times> Y) ?TP U \<and> V \<in> ?TP \<and> C \<subseteq> V \<and> U \<inter> V = {}"
          apply (rule exI[where x="?U"])
          apply (rule exI[where x="?V"])
          apply (intro conjI)
             apply (rule hnbhd)
            apply (rule hVopen)
           apply (rule hC_sub_V)
          apply (rule hdisj)
          done
      qed
    qed
  qed
qed

(** from \S31 Lemma 31.1(a) [top1.tex:~4065] **)
theorem Lemma_31_1a:
  "top1_regular_on X T \<longleftrightarrow>
     (top1_T1_on X T \<and>
      (\<forall>x\<in>X. \<forall>U. U \<in> T \<and> U \<subseteq> X \<and> x \<in> U
         \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U)))"
proof (rule iffI)
  assume hR: "top1_regular_on X T"
  have hT1: "top1_T1_on X T"
    using hR unfolding top1_regular_on_def by (rule conjunct1)
  show "top1_T1_on X T \<and>
      (\<forall>x\<in>X. \<forall>U. U \<in> T \<and> U \<subseteq> X \<and> x \<in> U
         \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U))"
  proof (intro conjI)
    show "top1_T1_on X T"
      by (rule hT1)
    show "\<forall>x\<in>X. \<forall>U. U \<in> T \<and> U \<subseteq> X \<and> x \<in> U
      \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U)"
    proof (intro ballI allI impI)
      fix x U
      assume hxX: "x \<in> X"
      assume hU: "U \<in> T \<and> U \<subseteq> X \<and> x \<in> U"
      have hUT: "U \<in> T" and hUX: "U \<subseteq> X" and hxU: "x \<in> U"
        using hU by blast+
      show "\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U"
        by (rule regular_refine_point_into_open[OF hR hxX hUT hUX hxU])
    qed
  qed
next
  assume h: "top1_T1_on X T \<and>
      (\<forall>x\<in>X. \<forall>U. U \<in> T \<and> U \<subseteq> X \<and> x \<in> U
         \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U))"
  have hT1: "top1_T1_on X T"
    using h by blast
  have hTop: "is_topology_on X T"
    using hT1 unfolding top1_T1_on_def by blast
  have hShrink:
    "\<forall>x\<in>X. \<forall>U. U \<in> T \<and> U \<subseteq> X \<and> x \<in> U
      \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U)"
    using h by blast

  show "top1_regular_on X T"
    unfolding top1_regular_on_def
  proof (intro conjI)
    show "top1_T1_on X T"
      by (rule hT1)
    show "\<forall>x\<in>X. \<forall>C. closedin_on X T C \<and> x \<notin> C
      \<longrightarrow> (\<exists>U V. neighborhood_of x X T U \<and> V \<in> T \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro ballI allI impI)
      fix x C
      assume hxX: "x \<in> X"
      assume hC: "closedin_on X T C \<and> x \<notin> C"
      have hCcl: "closedin_on X T C"
        using hC by blast
      have hxnotC: "x \<notin> C"
        using hC by blast
      have hCX: "C \<subseteq> X"
        by (rule closedin_sub[OF hCcl])
      have hXmC: "X - C \<in> T"
        by (rule closedin_diff_open[OF hCcl])
      have hxXmC: "x \<in> X - C"
        using hxX hxnotC by blast

      obtain V where hV: "V \<in> T" and hVX: "V \<subseteq> X" and hxV: "x \<in> V"
          and hclV: "closure_on X T V \<subseteq> X - C"
        using hShrink[rule_format, OF hxX, of "X - C"] hXmC hxXmC
        by blast

      have hclV_closed: "closedin_on X T (closure_on X T V)"
        by (rule closure_on_closed[OF hTop hVX])
      have hW: "X - closure_on X T V \<in> T"
        by (rule closedin_diff_open[OF hclV_closed])

      have hCsubW: "C \<subseteq> X - closure_on X T V"
      proof (rule subsetI)
        fix c assume hc: "c \<in> C"
        have hcX: "c \<in> X" using hCX hc by blast
        show "c \<in> X - closure_on X T V"
        proof (rule DiffI)
          show "c \<in> X" by (rule hcX)
          show "c \<notin> closure_on X T V"
          proof
            assume hccl: "c \<in> closure_on X T V"
            have "c \<in> X - C"
              using hclV hccl by blast
            thus False
              using hc by blast
          qed
        qed
      qed

      have hnbV: "neighborhood_of x X T V"
        unfolding neighborhood_of_def by (intro conjI, rule hV, rule hxV)
      have hdisj: "V \<inter> (X - closure_on X T V) = {}"
      proof (rule equalityI)
        show "V \<inter> (X - closure_on X T V) \<subseteq> {}"
        proof (rule subsetI)
          fix z assume hz: "z \<in> V \<inter> (X - closure_on X T V)"
          have hzV: "z \<in> V" and hznot: "z \<notin> closure_on X T V"
            using hz by blast+
          have hVsub: "V \<subseteq> closure_on X T V"
            by (rule subset_closure_on)
          have "z \<in> closure_on X T V"
            by (rule subsetD[OF hVsub hzV])
          thus "z \<in> {}"
            using hznot by blast
        qed
        show "{} \<subseteq> V \<inter> (X - closure_on X T V)"
          by simp
      qed

      show "\<exists>U W. neighborhood_of x X T U \<and> W \<in> T \<and> C \<subseteq> W \<and> U \<inter> W = {}"
        by (rule exI[where x=V], rule exI[where x="X - closure_on X T V"],
            intro conjI, rule hnbV, rule hW, rule hCsubW, rule hdisj)
    qed
  qed
qed

section \<open>\<S>32 Normal Spaces\<close>

(** from \S32 Definition (Normal space) [top1.tex:~4170] **)
definition top1_normal_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_normal_on X T \<longleftrightarrow>
     top1_T1_on X T \<and>
     (\<forall>C D. closedin_on X T C \<and> closedin_on X T D \<and> C \<inter> D = {}
        \<longrightarrow> (\<exists>U V. U \<in> T \<and> V \<in> T \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {}))"

(** from \S32 Theorem 32.1 (Regular + second-countable \<Longrightarrow> normal) [top1.tex:~4178] **)
theorem Theorem_32_1:
  assumes hR: "top1_regular_on X TX"
  assumes h2nd: "top1_second_countable_on X TX"
  shows "top1_normal_on X TX"
proof -
  have hT1: "top1_T1_on X TX"
    using hR unfolding top1_regular_on_def by (rule conjunct1)
  have hTop: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])

  have mk_countable_cover:
    "\<And>A B. closedin_on X TX A \<Longrightarrow> closedin_on X TX B \<Longrightarrow> A \<inter> B = {}
      \<Longrightarrow> \<exists>Uc. top1_countable Uc \<and> Uc \<subseteq> TX \<and> A \<subseteq> \<Union>Uc
            \<and> (\<forall>U\<in>Uc. closure_on X TX U \<subseteq> X - B)"
  proof -
    fix A B
    assume hAcl: "closedin_on X TX A"
    assume hBcl: "closedin_on X TX B"
    assume hdisj: "A \<inter> B = {}"
    have hAX: "A \<subseteq> X"
      by (rule closedin_sub[OF hAcl])
    have hXB: "X - B \<in> TX"
      by (rule closedin_diff_open[OF hBcl])
    have hXBsub: "X - B \<subseteq> X"
      by blast

    have exU: "\<forall>a\<in>A. \<exists>U. U \<in> TX \<and> U \<subseteq> X \<and> a \<in> U \<and> closure_on X TX U \<subseteq> X - B"
    proof (intro ballI)
      fix a assume haA: "a \<in> A"
      have haX: "a \<in> X"
        using hAX haA by blast
      have haXB: "a \<in> X - B"
      proof -
        have hanB: "a \<notin> B"
        proof
          assume haB: "a \<in> B"
          have "a \<in> A \<inter> B"
            using haA haB by blast
          thus False
            using hdisj by blast
        qed
        show ?thesis
          using haX hanB by blast
      qed
      have exV: "\<exists>V. V \<in> TX \<and> V \<subseteq> X \<and> a \<in> V \<and> closure_on X TX V \<subseteq> X - B"
        by (rule regular_refine_point_into_open[OF hR haX hXB hXBsub haXB])
      obtain V where hV: "V \<in> TX" and hVX: "V \<subseteq> X" and haV: "a \<in> V"
          and hclV: "closure_on X TX V \<subseteq> X - B"
        using exV by blast
      show "\<exists>U. U \<in> TX \<and> U \<subseteq> X \<and> a \<in> U \<and> closure_on X TX U \<subseteq> X - B"
        by (rule exI[where x=V], intro conjI, rule hV, rule hVX, rule haV, rule hclV)
    qed

    obtain f where hf:
      "\<forall>a\<in>A. f a \<in> TX \<and> f a \<subseteq> X \<and> a \<in> f a \<and> closure_on X TX (f a) \<subseteq> X - B"
      using bchoice[OF exU] by blast

    have hcovA: "A \<subseteq> \<Union>(f ` A)"
    proof (rule subsetI)
      fix a assume haA: "a \<in> A"
      have ha_in: "a \<in> f a"
        using hf haA by blast
      have "f a \<in> f ` A"
        by (rule imageI[OF haA])
      thus "a \<in> \<Union>(f ` A)"
        using ha_in by blast
    qed

    have hfT: "f ` A \<subseteq> TX"
      apply (rule subsetI)
      apply (erule imageE)
      using hf by blast

    obtain Uc where hUc_cnt: "top1_countable Uc" and hUc_sub: "Uc \<subseteq> f ` A" and hUc_cov: "A \<subseteq> \<Union>Uc"
      using second_countable_countable_subcover_of_closed[OF h2nd hAcl hfT hcovA] by blast

    have hUc_sub_TX: "Uc \<subseteq> TX"
      using hUc_sub hfT by blast

    have hUc_cl: "\<forall>U\<in>Uc. closure_on X TX U \<subseteq> X - B"
    proof (intro ballI)
      fix U assume hU: "U \<in> Uc"
      have hUfA: "U \<in> f ` A"
        using hUc_sub hU by blast
      obtain a where haA: "a \<in> A" and hUeq: "U = f a"
        using hUfA by blast
      have "closure_on X TX (f a) \<subseteq> X - B"
        using hf haA by blast
      thus "closure_on X TX U \<subseteq> X - B"
        using hUeq by simp
    qed

    show "\<exists>Uc. top1_countable Uc \<and> Uc \<subseteq> TX \<and> A \<subseteq> \<Union>Uc
            \<and> (\<forall>U\<in>Uc. closure_on X TX U \<subseteq> X - B)"
      by (rule exI[where x=Uc], intro conjI, rule hUc_cnt, rule hUc_sub_TX, rule hUc_cov, rule hUc_cl)
  qed

  show ?thesis
    unfolding top1_normal_on_def
  proof (intro conjI)
    show "top1_T1_on X TX"
      by (rule hT1)
    show "\<forall>C D. closedin_on X TX C \<and> closedin_on X TX D \<and> C \<inter> D = {}
        \<longrightarrow> (\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro allI impI)
      fix C D
      assume hCD: "closedin_on X TX C \<and> closedin_on X TX D \<and> C \<inter> D = {}"
      have hCcl: "closedin_on X TX C"
        using hCD by blast
      have hDcl: "closedin_on X TX D"
        using hCD by blast
      have hdisj: "C \<inter> D = {}"
        using hCD by blast

      have exUc:
        "\<exists>Uc. top1_countable Uc \<and> Uc \<subseteq> TX \<and> C \<subseteq> \<Union>Uc
          \<and> (\<forall>U\<in>Uc. closure_on X TX U \<subseteq> X - D)"
        by (rule mk_countable_cover[OF hCcl hDcl hdisj])
      obtain Uc where hUc_cnt: "top1_countable Uc" and hUc_sub: "Uc \<subseteq> TX" and hUc_cov: "C \<subseteq> \<Union>Uc"
          and hUc_cl: "\<forall>U\<in>Uc. closure_on X TX U \<subseteq> X - D"
        using exUc by blast

      have hdisjDC: "D \<inter> C = {}"
        using hdisj by (simp add: Int_commute)
      have exVc:
        "\<exists>Vc. top1_countable Vc \<and> Vc \<subseteq> TX \<and> D \<subseteq> \<Union>Vc
          \<and> (\<forall>V\<in>Vc. closure_on X TX V \<subseteq> X - C)"
        by (rule mk_countable_cover[OF hDcl hCcl hdisjDC])
      obtain Vc where hVc_cnt: "top1_countable Vc" and hVc_sub: "Vc \<subseteq> TX" and hVc_cov: "D \<subseteq> \<Union>Vc"
          and hVc_cl: "\<forall>V\<in>Vc. closure_on X TX V \<subseteq> X - C"
        using exVc by blast

      obtain iU :: "'a set \<Rightarrow> nat" where hiU: "inj_on iU Uc"
        using hUc_cnt unfolding top1_countable_def by blast
      obtain iV :: "'a set \<Rightarrow> nat" where hiV: "inj_on iV Vc"
        using hVc_cnt unfolding top1_countable_def by blast

      define U where "U n = \<Union>{S \<in> Uc. iU S = n}" for n
      define V where "V n = \<Union>{S \<in> Vc. iV S = n}" for n

      have hUopen: "\<forall>n. U n \<in> TX"
      proof (intro allI)
        fix n
        have "{S \<in> Uc. iU S = n} \<subseteq> TX"
          using hUc_sub by blast
        thus "U n \<in> TX"
          unfolding U_def using union_TX by blast
      qed
      have hVopen: "\<forall>n. V n \<in> TX"
      proof (intro allI)
        fix n
        have "{S \<in> Vc. iV S = n} \<subseteq> TX"
          using hVc_sub by blast
        thus "V n \<in> TX"
          unfolding V_def using union_TX by blast
      qed

      have hUsubX: "\<forall>n. U n \<subseteq> X"
      proof (intro allI subsetI)
        fix n x
        assume hx: "x \<in> U n"
        have hx': "x \<in> \<Union>{S \<in> Uc. iU S = n}"
          using hx by (simp only: U_def)
        then obtain S where hS: "S \<in> Uc" and hi: "iU S = n" and hxS: "x \<in> S"
          by blast
        have "closure_on X TX S \<subseteq> X - D"
          using hUc_cl hS by blast
        have hScl: "S \<subseteq> closure_on X TX S"
          by (rule subset_closure_on)
        have hSsubXD: "S \<subseteq> X - D"
          by (rule subset_trans[OF hScl \<open>closure_on X TX S \<subseteq> X - D\<close>])
        have "S \<subseteq> X"
          by (rule subset_trans[OF hSsubXD Diff_subset])
        show "x \<in> X"
          using hxS \<open>S \<subseteq> X\<close> by blast
      qed
      have hVsubX: "\<forall>n. V n \<subseteq> X"
      proof (intro allI subsetI)
        fix n x
        assume hx: "x \<in> V n"
        have hx': "x \<in> \<Union>{S \<in> Vc. iV S = n}"
          using hx by (simp only: V_def)
        then obtain S where hS: "S \<in> Vc" and hi: "iV S = n" and hxS: "x \<in> S"
          by blast
        have "closure_on X TX S \<subseteq> X - C"
          using hVc_cl hS by blast
        have hScl: "S \<subseteq> closure_on X TX S"
          by (rule subset_closure_on)
        have hSsubXC: "S \<subseteq> X - C"
          by (rule subset_trans[OF hScl \<open>closure_on X TX S \<subseteq> X - C\<close>])
        have "S \<subseteq> X"
          by (rule subset_trans[OF hSsubXC Diff_subset])
        show "x \<in> X"
          using hxS \<open>S \<subseteq> X\<close> by blast
      qed

      have hUc_to_U: "\<forall>S\<in>Uc. S \<subseteq> U (iU S)"
      proof (intro ballI)
        fix S assume hS: "S \<in> Uc"
        have "S \<in> {T \<in> Uc. iU T = iU S}"
          using hS by blast
        hence "S \<subseteq> \<Union>{T \<in> Uc. iU T = iU S}"
          by blast
        thus "S \<subseteq> U (iU S)"
          unfolding U_def by simp
      qed

      have hVc_to_V: "\<forall>S\<in>Vc. S \<subseteq> V (iV S)"
      proof (intro ballI)
        fix S assume hS: "S \<in> Vc"
        have "S \<in> {T \<in> Vc. iV T = iV S}"
          using hS by blast
        hence "S \<subseteq> \<Union>{T \<in> Vc. iV T = iV S}"
          by blast
        thus "S \<subseteq> V (iV S)"
          unfolding V_def by simp
      qed

      have hCcovUV: "C \<subseteq> (\<Union>n. U n)"
      proof (rule subsetI)
        fix x assume hxC: "x \<in> C"
        have hxUc: "x \<in> \<Union>Uc"
          using hUc_cov hxC by blast
        then obtain S where hSUc: "S \<in> Uc" and hxS: "x \<in> S"
          by blast
        have hSsub: "S \<subseteq> U (iU S)"
          using hUc_to_U hSUc by blast
        have hxU: "x \<in> U (iU S)"
          using hxS hSsub by blast
        show "x \<in> (\<Union>n. U n)"
        proof -
          have "U (iU S) \<in> range U"
            by blast
          have "x \<in> \<Union>(range U)"
            by (rule UnionI, rule \<open>U (iU S) \<in> range U\<close>, rule hxU)
          thus ?thesis
            by simp
        qed
      qed

      have hDcovUV: "D \<subseteq> (\<Union>n. V n)"
      proof (rule subsetI)
        fix x assume hxD: "x \<in> D"
        have hxVc: "x \<in> \<Union>Vc"
          using hVc_cov hxD by blast
        then obtain S where hSVc: "S \<in> Vc" and hxS: "x \<in> S"
          by blast
        have hSsub: "S \<subseteq> V (iV S)"
          using hVc_to_V hSVc by blast
        have hxV: "x \<in> V (iV S)"
          using hxS hSsub by blast
        show "x \<in> (\<Union>n. V n)"
        proof -
          have "V (iV S) \<in> range V"
            by blast
          have "x \<in> \<Union>(range V)"
            by (rule UnionI, rule \<open>V (iV S) \<in> range V\<close>, rule hxV)
          thus ?thesis
            by simp
        qed
      qed

      define ClU where "ClU n = closure_on X TX (U n)" for n
      define ClV where "ClV n = closure_on X TX (V n)" for n

      have hClU_closed: "\<forall>n. closedin_on X TX (ClU n)"
      proof (intro allI)
        fix n
        have "U n \<subseteq> X"
          using hUsubX by blast
        thus "closedin_on X TX (ClU n)"
          unfolding ClU_def by (rule closure_on_closed[OF hTop])
      qed
      have hClV_closed: "\<forall>n. closedin_on X TX (ClV n)"
      proof (intro allI)
        fix n
        have "V n \<subseteq> X"
          using hVsubX by blast
        thus "closedin_on X TX (ClV n)"
          unfolding ClV_def by (rule closure_on_closed[OF hTop])
      qed

      have hClU_sub: "\<forall>n. ClU n \<subseteq> X - D"
      proof (intro allI)
        fix n
        let ?P = "{S \<in> Uc. iU S = n}"
        have hUeq: "U n = \<Union>?P"
          unfolding U_def by simp
        show "ClU n \<subseteq> X - D"
        proof (cases "?P = {}")
          case True
          have "U n = \<Union>?P"
            by (rule hUeq)
          also have "... = \<Union>{}"
            by (simp only: True)
          also have "... = {}"
            by (simp only: Union_empty)
          finally have "U n = {}" .
          hence "ClU n = closure_on X TX {}"
            unfolding ClU_def by simp
          have empty_closed: "closedin_on X TX {}"
          proof (rule closedin_intro)
            show "{} \<subseteq> X" by simp
            have "X \<in> TX"
              by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
            thus "X - {} \<in> TX" by simp
          qed
          have "closure_on X TX {} \<subseteq> {}"
            by (rule closure_on_subset_of_closed[OF empty_closed], simp)
          hence "ClU n \<subseteq> {}"
            using \<open>ClU n = closure_on X TX {}\<close> by simp
          thus ?thesis by blast
        next
          case False
          obtain S where hSP: "S \<in> ?P"
            using False by blast
          have hSUc: "S \<in> Uc" and hi: "iU S = n"
            using hSP by blast+
          have huniq: "\<forall>T\<in>?P. T = S"
          proof (intro ballI)
            fix T assume hT: "T \<in> ?P"
            have hTUc: "T \<in> Uc" and hTi: "iU T = n"
              using hT by blast+
            have "iU T = iU S"
              using hTi hi by simp
            thus "T = S"
              using hiU hTUc hSUc unfolding inj_on_def by blast
          qed
          have hPsub: "?P \<subseteq> {S}"
            using huniq by blast
          have hS_in: "S \<in> ?P"
            by (rule hSP)
          have "S \<subseteq> \<Union>?P"
            using hS_in by blast
          have "\<Union>?P \<subseteq> S"
            using hPsub by blast
          have hUnionP: "\<Union>?P = S"
            by (rule equalityI, rule \<open>\<Union>?P \<subseteq> S\<close>, rule \<open>S \<subseteq> \<Union>?P\<close>)
          have "U n = S"
            unfolding hUeq using hUnionP by simp
          hence "ClU n = closure_on X TX S"
            unfolding ClU_def by simp
          have "closure_on X TX S \<subseteq> X - D"
            using hUc_cl hSUc by blast
          thus ?thesis
            using \<open>ClU n = closure_on X TX S\<close> by simp
        qed
      qed

      have hClV_sub: "\<forall>n. ClV n \<subseteq> X - C"
      proof (intro allI)
        fix n
        let ?P = "{S \<in> Vc. iV S = n}"
        have hVeq: "V n = \<Union>?P"
          unfolding V_def by simp
        show "ClV n \<subseteq> X - C"
        proof (cases "?P = {}")
          case True
          have "V n = \<Union>?P"
            by (rule hVeq)
          also have "... = \<Union>{}"
            by (simp only: True)
          also have "... = {}"
            by (simp only: Union_empty)
          finally have "V n = {}" .
          hence "ClV n = closure_on X TX {}"
            unfolding ClV_def by simp
          have empty_closed: "closedin_on X TX {}"
          proof (rule closedin_intro)
            show "{} \<subseteq> X" by simp
            have "X \<in> TX"
              by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
            thus "X - {} \<in> TX" by simp
          qed
          have "closure_on X TX {} \<subseteq> {}"
            by (rule closure_on_subset_of_closed[OF empty_closed], simp)
          hence "ClV n \<subseteq> {}"
            using \<open>ClV n = closure_on X TX {}\<close> by simp
          thus ?thesis by blast
        next
          case False
          obtain S where hSP: "S \<in> ?P"
            using False by blast
          have hSVc: "S \<in> Vc" and hi: "iV S = n"
            using hSP by blast+
          have huniq: "\<forall>T\<in>?P. T = S"
          proof (intro ballI)
            fix T assume hT: "T \<in> ?P"
            have hTVc: "T \<in> Vc" and hTi: "iV T = n"
              using hT by blast+
            have "iV T = iV S"
              using hTi hi by simp
            thus "T = S"
              using hiV hTVc hSVc unfolding inj_on_def by blast
          qed
          have hPsub: "?P \<subseteq> {S}"
            using huniq by blast
          have hS_in: "S \<in> ?P"
            by (rule hSP)
          have "S \<subseteq> \<Union>?P"
            using hS_in by blast
          have "\<Union>?P \<subseteq> S"
            using hPsub by blast
          have hUnionP: "\<Union>?P = S"
            by (rule equalityI, rule \<open>\<Union>?P \<subseteq> S\<close>, rule \<open>S \<subseteq> \<Union>?P\<close>)
          have "V n = S"
            unfolding hVeq using hUnionP by simp
          hence "ClV n = closure_on X TX S"
            unfolding ClV_def by simp
          have "closure_on X TX S \<subseteq> X - C"
            using hVc_cl hSVc by blast
          thus ?thesis
            using \<open>ClV n = closure_on X TX S\<close> by simp
        qed
      qed

      define KClU where "KClU n = \<Union>((\<lambda>i. ClU i) ` {i. i \<le> n})" for n
      define KClV where "KClV n = \<Union>((\<lambda>i. ClV i) ` {i. i \<le> n})" for n

      have hKClU_closed: "\<forall>n. closedin_on X TX (KClU n)"
      proof (intro allI)
        fix n
        have hfin: "finite {i::nat. i \<le> n}"
          by simp
        have hall: "\<forall>A\<in>(\<lambda>i. ClU i) ` {i. i \<le> n}. closedin_on X TX A"
        proof (intro ballI)
          fix A assume hA: "A \<in> (\<lambda>i. ClU i) ` {i. i \<le> n}"
          then obtain i where hi: "i \<le> n" and hAe: "A = ClU i"
            by blast
          show "closedin_on X TX A"
            using hClU_closed hAe by blast
        qed
        show "closedin_on X TX (KClU n)"
          unfolding KClU_def
          by (rule closedin_Union_finite[OF hTop], rule finite_imageI[OF hfin], rule hall)
      qed

      have hKClV_closed: "\<forall>n. closedin_on X TX (KClV n)"
      proof (intro allI)
        fix n
        have hfin: "finite {i::nat. i \<le> n}"
          by simp
        have hall: "\<forall>A\<in>(\<lambda>i. ClV i) ` {i. i \<le> n}. closedin_on X TX A"
        proof (intro ballI)
          fix A assume hA: "A \<in> (\<lambda>i. ClV i) ` {i. i \<le> n}"
          then obtain i where hi: "i \<le> n" and hAe: "A = ClV i"
            by blast
          show "closedin_on X TX A"
            using hClV_closed hAe by blast
        qed
        show "closedin_on X TX (KClV n)"
          unfolding KClV_def
          by (rule closedin_Union_finite[OF hTop], rule finite_imageI[OF hfin], rule hall)
      qed

      define U' where "U' n = U n \<inter> (X - KClV n)" for n
      define V' where "V' n = V n \<inter> (X - KClU n)" for n

      have hU'open: "\<forall>n. U' n \<in> TX"
      proof (intro allI)
        fix n
        have hXm: "X - KClV n \<in> TX"
          by (rule closedin_diff_open[OF hKClV_closed[rule_format, of n]])
        have "U n \<in> TX"
          using hUopen by blast
        have "U n \<inter> (X - KClV n) \<in> TX"
          by (rule topology_inter2[OF hTop \<open>U n \<in> TX\<close> hXm])
        thus "U' n \<in> TX"
          unfolding U'_def by simp
      qed
      have hV'open: "\<forall>n. V' n \<in> TX"
      proof (intro allI)
        fix n
        have hXm: "X - KClU n \<in> TX"
          by (rule closedin_diff_open[OF hKClU_closed[rule_format, of n]])
        have "V n \<in> TX"
          using hVopen by blast
        have "V n \<inter> (X - KClU n) \<in> TX"
          by (rule topology_inter2[OF hTop \<open>V n \<in> TX\<close> hXm])
        thus "V' n \<in> TX"
          unfolding V'_def by simp
      qed

      define Ubig where "Ubig = (\<Union>n. U' n)"
      define Vbig where "Vbig = (\<Union>n. V' n)"

      have hUbig_open: "Ubig \<in> TX"
      proof -
        have "range U' \<subseteq> TX"
          using hU'open by blast
        have "\<Union>(range U') \<in> TX"
          by (rule union_TX[rule_format], rule \<open>range U' \<subseteq> TX\<close>)
        thus ?thesis
          unfolding Ubig_def by simp
      qed

      have hVbig_open: "Vbig \<in> TX"
      proof -
        have "range V' \<subseteq> TX"
          using hV'open by blast
        have "\<Union>(range V') \<in> TX"
          by (rule union_TX[rule_format], rule \<open>range V' \<subseteq> TX\<close>)
        thus ?thesis
          unfolding Vbig_def by simp
      qed

      have hCsubUbig: "C \<subseteq> Ubig"
      proof (rule subsetI)
        fix x assume hxC: "x \<in> C"
        have hxU: "x \<in> (\<Union>n. U n)"
          using hCcovUV hxC by blast
        obtain n where hxn: "x \<in> U n"
          using hxU by blast
        have hxnot: "x \<notin> KClV n"
        proof
          assume hxK: "x \<in> KClV n"
          then obtain i where hi: "i \<le> n" and hxi: "x \<in> ClV i"
            unfolding KClV_def by blast
          have "x \<in> X - C"
            using hClV_sub[rule_format, of i] hxi by blast
          thus False
            using hxC by blast
        qed
        have hxX: "x \<in> X"
          using hUsubX[rule_format, of n] hxn by blast
        have hxXm: "x \<in> X - KClV n"
          by (rule DiffI, rule hxX, rule hxnot)
        have hxInt: "x \<in> U n \<inter> (X - KClV n)"
          by (rule IntI, rule hxn, rule hxXm)
        have "x \<in> U' n"
          unfolding U'_def using hxInt by simp
        hence "x \<in> Ubig"
          unfolding Ubig_def
          by blast
        thus "x \<in> Ubig" .
      qed

      have hDsubVbig: "D \<subseteq> Vbig"
      proof (rule subsetI)
        fix x assume hxD: "x \<in> D"
        have hxV: "x \<in> (\<Union>n. V n)"
          using hDcovUV hxD by blast
        obtain n where hxn: "x \<in> V n"
          using hxV by blast
        have hxnot: "x \<notin> KClU n"
        proof
          assume hxK: "x \<in> KClU n"
          then obtain i where hi: "i \<le> n" and hxi: "x \<in> ClU i"
            unfolding KClU_def by blast
          have "x \<in> X - D"
            using hClU_sub[rule_format, of i] hxi by blast
          thus False
            using hxD by blast
        qed
        have hxX: "x \<in> X"
          using hVsubX[rule_format, of n] hxn by blast
        have hxXm: "x \<in> X - KClU n"
          by (rule DiffI, rule hxX, rule hxnot)
        have hxInt: "x \<in> V n \<inter> (X - KClU n)"
          by (rule IntI, rule hxn, rule hxXm)
        have "x \<in> V' n"
          unfolding V'_def using hxInt by simp
        hence "x \<in> Vbig"
          unfolding Vbig_def by blast
        thus "x \<in> Vbig" .
      qed

      have hdisjUV: "Ubig \<inter> Vbig = {}"
      proof (rule equalityI)
        show "Ubig \<inter> Vbig \<subseteq> {}"
        proof (rule subsetI)
          fix x assume hx: "x \<in> Ubig \<inter> Vbig"
          have hxU: "x \<in> Ubig" and hxV: "x \<in> Vbig"
            using hx by blast+
          obtain j where hxj: "x \<in> U' j"
            using hxU unfolding Ubig_def by blast
          obtain k where hxk: "x \<in> V' k"
            using hxV unfolding Vbig_def by blast
          have hcase: "j \<le> k \<or> k \<le> j"
          proof (cases "j \<le> k")
            case True
            show ?thesis
              using True by blast
          next
            case False
            have "k \<le> j"
              using False by simp
            thus ?thesis
              by blast
          qed
          show "x \<in> {}"
          proof (rule disjE[OF hcase])
            assume hjk: "j \<le> k"
            have hxUj: "x \<in> U j"
              using hxj unfolding U'_def by blast
            have hxClUj: "x \<in> ClU j"
            proof -
              have hsub: "U j \<subseteq> closure_on X TX (U j)"
                by (rule subset_closure_on)
              have "x \<in> closure_on X TX (U j)"
                by (rule subsetD[OF hsub hxUj])
              thus ?thesis
                unfolding ClU_def by simp
            qed
            have hClUj_in: "ClU j \<subseteq> KClU k"
              unfolding KClU_def using hjk by blast
            have hxK: "x \<in> KClU k"
              using hClUj_in hxClUj by blast
            have hxnotK: "x \<notin> KClU k"
              using hxk unfolding V'_def by blast
            show "x \<in> {}"
              using hxK hxnotK by blast
          next
            assume hkj: "k \<le> j"
            have hxVk: "x \<in> V k"
              using hxk unfolding V'_def by blast
            have hxClVk: "x \<in> ClV k"
            proof -
              have hsub: "V k \<subseteq> closure_on X TX (V k)"
                by (rule subset_closure_on)
              have "x \<in> closure_on X TX (V k)"
                by (rule subsetD[OF hsub hxVk])
              thus ?thesis
                unfolding ClV_def by simp
            qed
            have hClVk_in: "ClV k \<subseteq> KClV j"
              unfolding KClV_def using hkj by blast
            have hxK: "x \<in> KClV j"
              using hClVk_in hxClVk by blast
            have hxnotK: "x \<notin> KClV j"
              using hxj unfolding U'_def by blast
            show "x \<in> {}"
              using hxK hxnotK by blast
          qed
        qed
        show "{} \<subseteq> Ubig \<inter> Vbig"
          by simp
      qed

      show "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {}"
        by (rule exI[where x=Ubig], rule exI[where x=Vbig],
            intro conjI, rule hUbig_open, rule hVbig_open, rule hCsubUbig, rule hDsubVbig, rule hdisjUV)
    qed
  qed
qed

(** from \S32 Theorem 32.2 (Every metrizable space is normal) [top1.tex:4202] **)
theorem Theorem_32_2:
  assumes hmet: "top1_metrizable_on X TX"
  shows "top1_normal_on X TX"
proof -
  obtain d where hd: "top1_metric_on X d" and hTX: "TX = top1_metric_topology_on X d"
    using hmet unfolding top1_metrizable_on_def by blast

  have hTop: "is_topology_on X TX"
    unfolding hTX by (rule top1_metric_topology_on_is_topology_on[OF hd])

  have hHausd: "is_hausdorff_on X TX"
  proof (unfold is_hausdorff_on_def, intro conjI)
    show "is_topology_on X TX" by (rule hTop)
    show "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
        (\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
    proof (intro ballI impI)
      fix x y
      assume hxX: "x \<in> X" and hyX: "y \<in> X" and hxy: "x \<noteq> y"

      have hnonneg: "\<forall>a\<in>X. \<forall>b\<in>X. 0 \<le> d a b"
        using hd unfolding top1_metric_on_def by blast
      have hsym: "\<forall>a\<in>X. \<forall>b\<in>X. d a b = d b a"
        using hd unfolding top1_metric_on_def by blast
      have htri: "\<forall>a\<in>X. \<forall>b\<in>X. \<forall>c\<in>X. d a c \<le> d a b + d b c"
        using hd unfolding top1_metric_on_def by blast
      have h0iff: "\<forall>a\<in>X. \<forall>b\<in>X. d a b = 0 \<longleftrightarrow> a = b"
        using hd unfolding top1_metric_on_def by blast

      have hdx0: "d x y \<noteq> 0"
      proof
        assume h0: "d x y = 0"
        have "x = y" using h0iff hxX hyX h0 by blast
        thus False using hxy by contradiction
      qed
      have hdxy_pos: "0 < d x y"
      proof (rule ccontr)
        assume hnot: "\<not> 0 < d x y"
        have hle: "d x y \<le> 0" using hnot by linarith
        have hge: "0 \<le> d x y" using hnonneg hxX hyX by blast
        have "d x y = 0" using hge hle by linarith
        thus False using hdx0 by contradiction
      qed

      define r where "r = d x y / 2"
      have hr: "0 < r" unfolding r_def using hdxy_pos by linarith

      let ?U = "top1_ball_on X d x r"
      let ?V = "top1_ball_on X d y r"

      have hUopen: "?U \<in> TX"
        unfolding hTX by (rule top1_ball_open_in_metric_topology[OF hd hxX hr])
      have hVopen: "?V \<in> TX"
        unfolding hTX by (rule top1_ball_open_in_metric_topology[OF hd hyX hr])

      have h0xx: "d x x = 0"
        using h0iff hxX by blast
      have h0yy: "d y y = 0"
        using h0iff hyX by blast
      have hxU: "x \<in> ?U"
        unfolding top1_ball_on_def using hxX h0xx hr by simp
      have hyV: "y \<in> ?V"
        unfolding top1_ball_on_def using hyX h0yy hr by simp

      have hdisj: "?U \<inter> ?V = {}"
      proof (rule ccontr)
        assume hne: "?U \<inter> ?V \<noteq> {}"
        obtain z where hz: "z \<in> ?U \<inter> ?V"
          using hne by blast
        have hzU: "z \<in> ?U" and hzV: "z \<in> ?V" using hz by blast+
        have hzX: "z \<in> X"
          using hzU unfolding top1_ball_on_def by blast
        have hdxz: "d x z < r"
          using hzU unfolding top1_ball_on_def by blast
        have hdyz: "d y z < r"
          using hzV unfolding top1_ball_on_def by blast
        have hdz_y: "d z y < r"
          using hsym hyX hzX hdyz by simp

        have "d x y \<le> d x z + d z y"
          using htri hxX hzX hyX by blast
        also have "... < r + r"
          using hdxz hdz_y by linarith
        also have "... = d x y"
          unfolding r_def by simp
        finally have "d x y < d x y" .
        thus False by simp
      qed

      show "\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {}"
      proof -
        have hnbU: "neighborhood_of x X TX (top1_ball_on X d x r)"
          unfolding neighborhood_of_def using hUopen hxU by blast
        have hnbV: "neighborhood_of y X TX (top1_ball_on X d y r)"
          unfolding neighborhood_of_def using hVopen hyV by blast
        show ?thesis
          apply (rule exI[where x="top1_ball_on X d x r"])
          apply (rule exI[where x="top1_ball_on X d y r"])
          apply (intro conjI)
            apply (rule hnbU)
           apply (rule hnbV)
          apply (rule hdisj)
          done
      qed
    qed
  qed

  have hT1: "top1_T1_on X TX"
    by (rule hausdorff_imp_T1_on[OF hHausd])

  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])

  show ?thesis
    unfolding top1_normal_on_def
  proof (intro conjI)
    show "top1_T1_on X TX" by (rule hT1)
    show "\<forall>A B. closedin_on X TX A \<and> closedin_on X TX B \<and> A \<inter> B = {}
        \<longrightarrow> (\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro allI impI)
      fix A B
      assume hAB: "closedin_on X TX A \<and> closedin_on X TX B \<and> A \<inter> B = {}"
      have hAcl: "closedin_on X TX A" and hBcl: "closedin_on X TX B" and hdisjAB: "A \<inter> B = {}"
        using hAB by blast+
      have hAX: "A \<subseteq> X" by (rule closedin_sub[OF hAcl])
      have hBX: "B \<subseteq> X" by (rule closedin_sub[OF hBcl])
      have hXA_open: "X - A \<in> TX" by (rule closedin_diff_open[OF hAcl])
      have hXB_open: "X - B \<in> TX" by (rule closedin_diff_open[OF hBcl])

      have hnonneg: "\<forall>a\<in>X. \<forall>b\<in>X. 0 \<le> d a b"
        using hd unfolding top1_metric_on_def by blast
      have hsym: "\<forall>a\<in>X. \<forall>b\<in>X. d a b = d b a"
        using hd unfolding top1_metric_on_def by blast
      have htri: "\<forall>a\<in>X. \<forall>b\<in>X. \<forall>c\<in>X. d a c \<le> d a b + d b c"
        using hd unfolding top1_metric_on_def by blast
      have h0iff: "\<forall>a\<in>X. \<forall>b\<in>X. d a b = 0 \<longleftrightarrow> a = b"
        using hd unfolding top1_metric_on_def by blast

      have ex_epsA:
        "\<forall>a\<in>A. \<exists>e. 0 < e \<and> top1_ball_on X d a e \<subseteq> X - B"
      proof (intro ballI)
        fix a assume haA: "a \<in> A"
        have haX: "a \<in> X" using hAX haA by blast
        have haXB: "a \<in> X - B"
        proof -
          have haB: "a \<notin> B"
          proof
            assume haB: "a \<in> B"
            have "a \<in> A \<inter> B" using haA haB by blast
            thus False using hdisjAB by blast
          qed
          show ?thesis using haX haB by blast
        qed

        have hmem: "X - B \<in> topology_generated_by_basis X (top1_metric_basis_on X d)"
          using hXB_open unfolding hTX top1_metric_topology_on_def by simp
        have hdef: "(X - B) \<subseteq> X \<and> (\<forall>x\<in>(X - B). \<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> (X - B))"
          using hmem unfolding topology_generated_by_basis_def by blast
        have hxprop: "\<forall>x\<in>(X - B). \<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> (X - B)"
          by (rule conjunct2[OF hdef])
        obtain b0 where hb0: "b0 \<in> top1_metric_basis_on X d" and ha_in: "a \<in> b0" and hb0sub: "b0 \<subseteq> X - B"
          using hxprop haXB by blast
        obtain x0 e0 where hx0X: "x0 \<in> X" and he0: "0 < e0" and hb0eq: "b0 = top1_ball_on X d x0 e0"
          using hb0 unfolding top1_metric_basis_on_def by blast
        have ha_ball: "a \<in> top1_ball_on X d x0 e0"
          using ha_in hb0eq by simp
        have haX': "a \<in> X" using haX .
        have hdist: "d x0 a < e0"
          using ha_ball unfolding top1_ball_on_def by blast

        define e where "e = e0 - d x0 a"
        have he: "0 < e" unfolding e_def using he0 hdist by linarith

        have hsub: "top1_ball_on X d a e \<subseteq> top1_ball_on X d x0 e0"
        proof (rule subsetI)
          fix z assume hz: "z \<in> top1_ball_on X d a e"
          have hzX: "z \<in> X" and hdaz: "d a z < e"
            using hz unfolding top1_ball_on_def by blast+
          have hx0a: "d x0 a = d a x0"
            using hsym hx0X haX' by blast
          have hdx0z_le: "d x0 z \<le> d x0 a + d a z"
            using htri hx0X haX' hzX by blast
          have "d x0 z < d x0 a + e"
            using hdx0z_le hdaz by linarith
          also have "... = e0"
            unfolding e_def by simp
          finally have "d x0 z < e0" .
          show "z \<in> top1_ball_on X d x0 e0"
            unfolding top1_ball_on_def using hzX \<open>d x0 z < e0\<close> by blast
        qed

        have hsub': "top1_ball_on X d a e \<subseteq> X - B"
          using hsub hb0sub hb0eq by blast
        show "\<exists>e. 0 < e \<and> top1_ball_on X d a e \<subseteq> X - B"
          by (rule exI[where x=e], intro conjI, rule he, rule hsub')
      qed

      have ex_epsB:
        "\<forall>b\<in>B. \<exists>e. 0 < e \<and> top1_ball_on X d b e \<subseteq> X - A"
      proof (intro ballI)
        fix b assume hbB: "b \<in> B"
        have hbX: "b \<in> X" using hBX hbB by blast
        have hbXA: "b \<in> X - A"
        proof -
          have hbA: "b \<notin> A"
          proof
            assume hbA: "b \<in> A"
            have "b \<in> A \<inter> B" using hbA hbB by blast
            thus False using hdisjAB by blast
          qed
          show ?thesis using hbX hbA by blast
        qed

        have hmem: "X - A \<in> topology_generated_by_basis X (top1_metric_basis_on X d)"
          using hXA_open unfolding hTX top1_metric_topology_on_def by simp
        have hdef: "(X - A) \<subseteq> X \<and> (\<forall>x\<in>(X - A). \<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> (X - A))"
          using hmem unfolding topology_generated_by_basis_def by blast
        have hxprop: "\<forall>x\<in>(X - A). \<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> (X - A)"
          by (rule conjunct2[OF hdef])
        obtain b0 where hb0: "b0 \<in> top1_metric_basis_on X d" and hb_in: "b \<in> b0" and hb0sub: "b0 \<subseteq> X - A"
          using hxprop hbXA by blast
        obtain x0 e0 where hx0X: "x0 \<in> X" and he0: "0 < e0" and hb0eq: "b0 = top1_ball_on X d x0 e0"
          using hb0 unfolding top1_metric_basis_on_def by blast
        have hb_ball: "b \<in> top1_ball_on X d x0 e0"
          using hb_in hb0eq by simp
        have hdist: "d x0 b < e0"
          using hb_ball unfolding top1_ball_on_def by blast

        define e where "e = e0 - d x0 b"
        have he: "0 < e" unfolding e_def using he0 hdist by linarith

        have hsub: "top1_ball_on X d b e \<subseteq> top1_ball_on X d x0 e0"
        proof (rule subsetI)
          fix z assume hz: "z \<in> top1_ball_on X d b e"
          have hzX: "z \<in> X" and hdbz: "d b z < e"
            using hz unfolding top1_ball_on_def by blast+
          have hdx0z_le: "d x0 z \<le> d x0 b + d b z"
            using htri hx0X hbX hzX by blast
          have "d x0 z < d x0 b + e"
            using hdx0z_le hdbz by linarith
          also have "... = e0"
            unfolding e_def by simp
          finally have "d x0 z < e0" .
          show "z \<in> top1_ball_on X d x0 e0"
            unfolding top1_ball_on_def using hzX \<open>d x0 z < e0\<close> by blast
        qed

        have hsub': "top1_ball_on X d b e \<subseteq> X - A"
          using hsub hb0sub hb0eq by blast
        show "\<exists>e. 0 < e \<and> top1_ball_on X d b e \<subseteq> X - A"
          by (rule exI[where x=e], intro conjI, rule he, rule hsub')
      qed

      obtain epsA where hepsA:
        "\<forall>a\<in>A. 0 < epsA a \<and> top1_ball_on X d a (epsA a) \<subseteq> X - B"
        using bchoice[OF ex_epsA] by blast
      obtain epsB where hepsB:
        "\<forall>b\<in>B. 0 < epsB b \<and> top1_ball_on X d b (epsB b) \<subseteq> X - A"
        using bchoice[OF ex_epsB] by blast

      define U where "U = \<Union>{top1_ball_on X d a (epsA a / 2) | a. a \<in> A}"
      define V where "V = \<Union>{top1_ball_on X d b (epsB b / 2) | b. b \<in> B}"

      have hUopen: "U \<in> TX"
      proof -
        define Uc where "Uc = {top1_ball_on X d a (epsA a / 2) | a. a \<in> A}"
        have hUc_sub: "Uc \<subseteq> TX"
        proof (rule subsetI)
          fix W assume hW: "W \<in> Uc"
          obtain a where haA: "a \<in> A" and hWeq: "W = top1_ball_on X d a (epsA a / 2)"
            using hW unfolding Uc_def by blast
          have haX: "a \<in> X" using hAX haA by blast
          have hpos: "0 < epsA a / 2"
          proof -
            have "0 < epsA a" using hepsA haA by blast
            thus ?thesis by linarith
          qed
          have "top1_ball_on X d a (epsA a / 2) \<in> TX"
            unfolding hTX by (rule top1_ball_open_in_metric_topology[OF hd haX hpos])
          thus "W \<in> TX" using hWeq by simp
        qed
        have hUnion: "\<Union>Uc \<in> TX"
          by (rule union_TX[rule_format, OF hUc_sub])
        show ?thesis
        proof -
          have hUeq: "U = \<Union>Uc"
            by (simp add: U_def Uc_def)
          show ?thesis
            by (subst hUeq, rule hUnion)
        qed
      qed

      have hVopen: "V \<in> TX"
      proof -
        define Vc where "Vc = {top1_ball_on X d b (epsB b / 2) | b. b \<in> B}"
        have hVc_sub: "Vc \<subseteq> TX"
        proof (rule subsetI)
          fix W assume hW: "W \<in> Vc"
          obtain b where hbB: "b \<in> B" and hWeq: "W = top1_ball_on X d b (epsB b / 2)"
            using hW unfolding Vc_def by blast
          have hbX: "b \<in> X" using hBX hbB by blast
          have hpos: "0 < epsB b / 2"
          proof -
            have "0 < epsB b" using hepsB hbB by blast
            thus ?thesis by linarith
          qed
          have "top1_ball_on X d b (epsB b / 2) \<in> TX"
            unfolding hTX by (rule top1_ball_open_in_metric_topology[OF hd hbX hpos])
          thus "W \<in> TX" using hWeq by simp
        qed
        have hUnion: "\<Union>Vc \<in> TX"
          by (rule union_TX[rule_format, OF hVc_sub])
        show ?thesis
        proof -
          have hVeq: "V = \<Union>Vc"
            by (simp add: V_def Vc_def)
          show ?thesis
            by (subst hVeq, rule hUnion)
        qed
      qed

      have hA_sub_U: "A \<subseteq> U"
      proof (rule subsetI)
        fix a assume haA: "a \<in> A"
        have haX: "a \<in> X" using hAX haA by blast
        have h0aa: "d a a = 0"
          using h0iff haX by blast
        have hpos: "0 < epsA a / 2"
        proof -
          have "0 < epsA a" using hepsA haA by blast
          thus ?thesis by linarith
        qed
        have ha_in: "a \<in> top1_ball_on X d a (epsA a / 2)"
          unfolding top1_ball_on_def using haX h0aa hpos by simp
        have hmem: "top1_ball_on X d a (epsA a / 2) \<in> {top1_ball_on X d a (epsA a / 2) | a. a \<in> A}"
          using haA by blast
        show "a \<in> U"
          unfolding U_def by (rule UnionI[OF hmem ha_in])
      qed

      have hB_sub_V: "B \<subseteq> V"
      proof (rule subsetI)
        fix b assume hbB: "b \<in> B"
        have hbX: "b \<in> X" using hBX hbB by blast
        have h0bb: "d b b = 0"
          using h0iff hbX by blast
        have hpos: "0 < epsB b / 2"
        proof -
          have "0 < epsB b" using hepsB hbB by blast
          thus ?thesis by linarith
        qed
        have hb_in: "b \<in> top1_ball_on X d b (epsB b / 2)"
          unfolding top1_ball_on_def using hbX h0bb hpos by simp
        have hmem: "top1_ball_on X d b (epsB b / 2) \<in> {top1_ball_on X d b (epsB b / 2) | b. b \<in> B}"
          using hbB by blast
        show "b \<in> V"
          unfolding V_def by (rule UnionI[OF hmem hb_in])
      qed

      have hUV_disj: "U \<inter> V = {}"
      proof (rule ccontr)
        assume hne: "U \<inter> V \<noteq> {}"
        obtain z where hz: "z \<in> U \<inter> V"
          using hne by blast
        have hzU: "z \<in> U" and hzV: "z \<in> V" using hz by blast+
        obtain a where haA: "a \<in> A" and hza: "z \<in> top1_ball_on X d a (epsA a / 2)"
          using hzU unfolding U_def by blast
        obtain b where hbB: "b \<in> B" and hzb: "z \<in> top1_ball_on X d b (epsB b / 2)"
          using hzV unfolding V_def by blast

        have haX: "a \<in> X" using hAX haA by blast
        have hbX: "b \<in> X" using hBX hbB by blast
        have hzX: "z \<in> X"
          using hza unfolding top1_ball_on_def by blast

        have hdaz: "d a z < epsA a / 2"
          using hza unfolding top1_ball_on_def by blast
        have hdbz: "d b z < epsB b / 2"
          using hzb unfolding top1_ball_on_def by blast
        have hdzb: "d z b < epsB b / 2"
          using hsym hbX hzX hdbz by simp
        have hdab: "d a b \<le> d a z + d z b"
          using htri haX hzX hbX by blast
        have hsum_lt: "d a z + d z b < epsA a / 2 + epsB b / 2"
          using hdaz hdzb by linarith
        have hdab_lt0: "d a b < epsA a / 2 + epsB b / 2"
          by (rule le_less_trans[OF hdab hsum_lt])
        have heq: "epsA a / 2 + epsB b / 2 = (epsA a + epsB b) / 2"
          by (simp add: add_divide_distrib)
        have hdab_lt: "d a b < (epsA a + epsB b) / 2"
          using hdab_lt0 heq by simp

        have hAavoid: "top1_ball_on X d b (epsB b) \<subseteq> X - A"
          using hepsB hbB by blast
        have hBavoid: "top1_ball_on X d a (epsA a) \<subseteq> X - B"
          using hepsA haA by blast

        show False
        proof (cases "epsA a \<le> epsB b")
          case True
          have hdba_lt: "d b a < epsB b"
          proof -
            have hdbasym: "d b a = d a b" using hsym haX hbX by simp
            have "d b a < (epsA a + epsB b) / 2"
              using hdab_lt hdbasym by simp
            also have "... \<le> epsB b"
            proof -
              have hle: "epsA a + epsB b \<le> epsB b * 2"
                using True by linarith
              show ?thesis
                using hle by (simp add: divide_le_eq)
            qed
            finally show ?thesis .
          qed
          have ha_in_ball: "a \<in> top1_ball_on X d b (epsB b)"
            unfolding top1_ball_on_def using haX hdba_lt by blast
          have ha_notA: "a \<in> X - A"
            using hAavoid ha_in_ball by blast
          have "a \<notin> A" using ha_notA by blast
          thus False using haA by contradiction
        next
          case False
          have hb_in_ball: "b \<in> top1_ball_on X d a (epsA a)"
          proof -
            have hdab_lt2: "d a b < epsA a"
            proof -
              have hle: "epsA a + epsB b \<le> epsA a * 2"
                using False by linarith
              have hmid: "(epsA a + epsB b) / 2 \<le> epsA a"
                using hle by (simp add: divide_le_eq)
              show ?thesis using hdab_lt hmid by linarith
            qed
            show ?thesis
              unfolding top1_ball_on_def using hbX hdab_lt2 by blast
          qed
          have hb_notB: "b \<in> X - B"
            using hBavoid hb_in_ball by blast
          have "b \<notin> B" using hb_notB by blast
          thus False using hbB by contradiction
        qed
      qed

      show "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = {}"
        apply (rule exI[where x=U])
        apply (rule exI[where x=V])
        apply (intro conjI)
            apply (rule hUopen)
           apply (rule hVopen)
          apply (rule hA_sub_U)
         apply (rule hB_sub_V)
        apply (rule hUV_disj)
        done
    qed
  qed
qed

(** Normality gives the standard "shrinking lemma" form used in the Urysohn construction:
    if a closed set lies inside an open set, we can find an open neighborhood whose closure
    is still inside the original open set. **)
lemma normal_refine_closed_into_open:
  assumes hN: "top1_normal_on X T"
  assumes hA: "closedin_on X T A"
  assumes hU: "U \<in> T"
  assumes hUX: "U \<subseteq> X"
  assumes hAU: "A \<subseteq> U"
  shows "\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U"
proof -
  have hT1: "top1_T1_on X T"
    using hN unfolding top1_normal_on_def by (rule conjunct1)
  have hTop: "is_topology_on X T"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)
  have hXT: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])

  have hSep:
    "\<forall>C D. closedin_on X T C \<and> closedin_on X T D \<and> C \<inter> D = {}
       \<longrightarrow> (\<exists>U V. U \<in> T \<and> V \<in> T \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {})"
    using hN unfolding top1_normal_on_def by (rule conjunct2)

  let ?C = "X - U"

  have hU'open: "X \<inter> U \<in> T"
    by (rule topology_inter2[OF hTop hXT hU])
  have hCcl: "closedin_on X T ?C"
    apply (rule closedin_intro)
     apply (rule Diff_subset)
    apply (simp only: Diff_Diff_Int)
    apply (simp only: Int_absorb1[OF hUX])
    apply (rule hU)
    done

  have hAdisjC: "A \<inter> ?C = {}"
  proof (rule equalityI)
    show "A \<inter> ?C \<subseteq> {}"
    proof (rule subsetI)
      fix x assume hx: "x \<in> A \<inter> ?C"
      have hxA: "x \<in> A" and hxC: "x \<in> ?C" using hx by blast+
      have hxU: "x \<in> U" using hAU hxA by blast
      have hxnotU: "x \<notin> U" using hxC by blast
      show "x \<in> {}" using hxnotU hxU by blast
    qed
    show "{} \<subseteq> A \<inter> ?C" by (rule empty_subsetI)
  qed

  have hSepAC:
    "closedin_on X T A \<and> closedin_on X T ?C \<and> A \<inter> ?C = {}
      \<longrightarrow> (\<exists>U0 V0. U0 \<in> T \<and> V0 \<in> T \<and> A \<subseteq> U0 \<and> ?C \<subseteq> V0 \<and> U0 \<inter> V0 = {})"
    by (rule spec[where x="?C", OF spec[where x=A, OF hSep]])

  have hSepAC2: "\<exists>U0 V0. U0 \<in> T \<and> V0 \<in> T \<and> A \<subseteq> U0 \<and> ?C \<subseteq> V0 \<and> U0 \<inter> V0 = {}"
    apply (rule mp[OF hSepAC])
    apply (intro conjI)
      apply (rule hA)
     apply (rule hCcl)
    apply (rule hAdisjC)
    done

  obtain U0 V0 where hU0: "U0 \<in> T" and hV0: "V0 \<in> T"
      and hAU0: "A \<subseteq> U0" and hCV0: "?C \<subseteq> V0" and hdisj: "U0 \<inter> V0 = {}"
    using hSepAC2 by blast

  let ?V = "X \<inter> U0"
  let ?W = "X \<inter> V0"

  have hVopen: "?V \<in> T"
    by (rule topology_inter2[OF hTop hXT hU0])
  have hWopen: "?W \<in> T"
    by (rule topology_inter2[OF hTop hXT hV0])

  have hVsubX: "?V \<subseteq> X" by blast
  have hAsubX: "A \<subseteq> X" by (rule closedin_sub[OF hA])
  have hAsubV: "A \<subseteq> ?V" using hAsubX hAU0 by blast

  have hCV0': "?C \<subseteq> ?W"
    using hCV0 by blast

  have hVdisjW: "?V \<inter> ?W = {}"
    using hdisj by blast

  have hVsubXmW: "?V \<subseteq> X - ?W"
  proof (rule subsetI)
    fix x assume hxV: "x \<in> ?V"
    have hxX: "x \<in> X" using hxV by blast
    have hxnotW: "x \<notin> ?W"
    proof
      assume hxW: "x \<in> ?W"
      have "x \<in> ?V \<inter> ?W" using hxV hxW by blast
      thus False using hVdisjW by blast
    qed
    show "x \<in> X - ?W" using hxX hxnotW by blast
  qed

  have hXmW_closed: "closedin_on X T (X - ?W)"
  proof (rule closedin_intro)
    show "X - ?W \<subseteq> X" by (rule Diff_subset)
    show "X - (X - ?W) \<in> T"
    proof -
      have eq: "X - (X - ?W) = X \<inter> ?W" by blast
      have "X \<inter> ?W \<in> T"
        by (rule topology_inter2[OF hTop hXT hWopen])
      thus ?thesis using eq by simp
    qed
  qed

  have hclV_sub_XmW: "closure_on X T ?V \<subseteq> X - ?W"
    by (rule closure_on_subset_of_closed[OF hXmW_closed hVsubXmW])

  have hXmW_sub_U: "X - ?W \<subseteq> U"
  proof -
    have hXmW_sub_XmC: "X - ?W \<subseteq> X - ?C"
      by (rule Diff_mono, rule subset_refl, rule hCV0')
    have hXmC_eq: "X - ?C = X \<inter> U"
      by blast
    have "X - ?W \<subseteq> X \<inter> U"
      using hXmW_sub_XmC hXmC_eq by simp
    also have "... \<subseteq> U" by blast
    finally show ?thesis .
  qed

  have hclV_sub_U: "closure_on X T ?V \<subseteq> U"
    by (rule subset_trans[OF hclV_sub_XmW hXmW_sub_U])

  show ?thesis
    apply (rule exI[where x="?V"])
    apply (intro conjI)
       apply (rule hVopen)
      apply (rule hVsubX)
     apply (rule hAsubV)
    apply (rule hclV_sub_U)
    done
qed

(** from \S31 Lemma 31.1(b) [top1.tex:~4090] **)
theorem Lemma_31_1b:
  "top1_normal_on X T \<longleftrightarrow>
     (top1_T1_on X T \<and>
      (\<forall>A U. closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U
         \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U)))"
proof (rule iffI)
  assume hN: "top1_normal_on X T"
  have hT1: "top1_T1_on X T"
    using hN unfolding top1_normal_on_def by blast
  show "top1_T1_on X T \<and>
      (\<forall>A U. closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U
         \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U))"
  proof (intro conjI)
    show "top1_T1_on X T"
      by (rule hT1)
    show "\<forall>A U. closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U
      \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U)"
    proof (intro allI impI)
      fix A U
      assume hAU: "closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U"
      have hA: "closedin_on X T A" and hU: "U \<in> T" and hUX: "U \<subseteq> X" and hAsubU: "A \<subseteq> U"
        using hAU by blast+
      show "\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U"
        by (rule normal_refine_closed_into_open[OF hN hA hU hUX hAsubU])
    qed
  qed
next
  assume h:
    "top1_T1_on X T \<and>
      (\<forall>A U. closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U
         \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U))"
  have hT1: "top1_T1_on X T"
    using h by blast
  have hTop: "is_topology_on X T"
    using hT1 unfolding top1_T1_on_def by blast
  have hShrink:
    "\<forall>A U. closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U
      \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U)"
    using h by blast

  show "top1_normal_on X T"
    unfolding top1_normal_on_def
  proof (intro conjI)
    show "top1_T1_on X T"
      by (rule hT1)
    show "\<forall>C D. closedin_on X T C \<and> closedin_on X T D \<and> C \<inter> D = {}
      \<longrightarrow> (\<exists>U V. U \<in> T \<and> V \<in> T \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro allI impI)
      fix C D
      assume hCD: "closedin_on X T C \<and> closedin_on X T D \<and> C \<inter> D = {}"
      have hC: "closedin_on X T C" and hD: "closedin_on X T D" and hdisj: "C \<inter> D = {}"
        using hCD by blast+
      have hDX: "D \<subseteq> X"
        by (rule closedin_sub[OF hD])
      have hU: "X - D \<in> T"
        by (rule closedin_diff_open[OF hD])
      have hUX: "X - D \<subseteq> X"
        by blast
      have hCsub: "C \<subseteq> X - D"
      proof (rule subsetI)
        fix x assume hxC: "x \<in> C"
        have hxX: "x \<in> X"
          using closedin_sub[OF hC] hxC by blast
        have hxnotD: "x \<notin> D"
        proof
          assume hxD: "x \<in> D"
          have "x \<in> C \<inter> D" using hxC hxD by blast
          thus False using hdisj by blast
        qed
        show "x \<in> X - D"
          using hxX hxnotD by blast
      qed
      obtain V where hV: "V \<in> T" and hVX: "V \<subseteq> X" and hCV: "C \<subseteq> V"
          and hclV: "closure_on X T V \<subseteq> X - D"
        using hShrink[rule_format, OF conjI[OF hC conjI[OF hU conjI[OF hUX hCsub]]]] by blast

      have hclV_closed: "closedin_on X T (closure_on X T V)"
        by (rule closure_on_closed[OF hTop hVX])
      have hW: "X - closure_on X T V \<in> T"
        by (rule closedin_diff_open[OF hclV_closed])

      have hDsubW: "D \<subseteq> X - closure_on X T V"
      proof (rule subsetI)
        fix d assume hd: "d \<in> D"
        have hdX: "d \<in> X" using hDX hd by blast
        show "d \<in> X - closure_on X T V"
        proof (rule DiffI)
          show "d \<in> X" by (rule hdX)
          show "d \<notin> closure_on X T V"
          proof
            assume hdcl: "d \<in> closure_on X T V"
            have "d \<in> X - D"
              using hclV hdcl by blast
            thus False
              using hd by blast
          qed
        qed
      qed

      have hdisjUV: "V \<inter> (X - closure_on X T V) = {}"
      proof (rule equalityI)
        show "V \<inter> (X - closure_on X T V) \<subseteq> {}"
        proof (rule subsetI)
          fix z assume hz: "z \<in> V \<inter> (X - closure_on X T V)"
          have hzV: "z \<in> V" and hznot: "z \<notin> closure_on X T V"
            using hz by blast+
          have hVsub: "V \<subseteq> closure_on X T V"
            by (rule subset_closure_on)
          have "z \<in> closure_on X T V"
            by (rule subsetD[OF hVsub hzV])
          thus "z \<in> {}"
            using hznot by blast
        qed
        show "{} \<subseteq> V \<inter> (X - closure_on X T V)"
          by simp
      qed

      show "\<exists>U W. U \<in> T \<and> W \<in> T \<and> C \<subseteq> U \<and> D \<subseteq> W \<and> U \<inter> W = {}"
        by (rule exI[where x=V], rule exI[where x="X - closure_on X T V"],
            intro conjI, rule hV, rule hW, rule hCV, rule hDsubW, rule hdisjUV)
    qed
  qed
qed

(** Lemma 31.1 as a single combined statement (parts (a) and (b)). **)
theorem Lemma_31_1:
  shows "top1_regular_on X T \<longleftrightarrow>
           (top1_T1_on X T \<and>
            (\<forall>x\<in>X. \<forall>U. U \<in> T \<and> U \<subseteq> X \<and> x \<in> U
               \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U)))"
    and "top1_normal_on X T \<longleftrightarrow>
           (top1_T1_on X T \<and>
            (\<forall>A U. closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U
               \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U)))"
proof -
  show "top1_regular_on X T \<longleftrightarrow>
           (top1_T1_on X T \<and>
            (\<forall>x\<in>X. \<forall>U. U \<in> T \<and> U \<subseteq> X \<and> x \<in> U
               \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> x \<in> V \<and> closure_on X T V \<subseteq> U)))"
    by (rule Lemma_31_1a)
  show "top1_normal_on X T \<longleftrightarrow>
           (top1_T1_on X T \<and>
            (\<forall>A U. closedin_on X T A \<and> U \<in> T \<and> U \<subseteq> X \<and> A \<subseteq> U
               \<longrightarrow> (\<exists>V. V \<in> T \<and> V \<subseteq> X \<and> A \<subseteq> V \<and> closure_on X T V \<subseteq> U)))"
    by (rule Lemma_31_1b)
qed

(** Insertion lemma: in a normal space, one can fit an open set between an open set and
    an open superset of its closure (used for the rational-indexed construction in the
    Urysohn lemma). **)
lemma normal_insert_open_between:
  assumes hN: "top1_normal_on X T"
  assumes hU: "U \<in> T" and hUX: "U \<subseteq> X"
  assumes hV: "V \<in> T" and hVX: "V \<subseteq> X"
  assumes hcl: "closure_on X T U \<subseteq> V"
  shows "\<exists>W. W \<in> T \<and> W \<subseteq> X \<and> closure_on X T U \<subseteq> W \<and> closure_on X T W \<subseteq> V"
proof -
  have hT1: "top1_T1_on X T"
    using hN unfolding top1_normal_on_def by (rule conjunct1)
  have hTop: "is_topology_on X T"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  have hUcl: "closedin_on X T (closure_on X T U)"
    by (rule closure_on_closed[OF hTop hUX])

  have hRef:
    "\<exists>W. W \<in> T \<and> W \<subseteq> X \<and> closure_on X T U \<subseteq> W \<and> closure_on X T W \<subseteq> V"
    apply (rule normal_refine_closed_into_open[OF hN hUcl hV hVX hcl])
    done
  show ?thesis
    using hRef .
qed

(** Normal (as defined in top1.tex) implies regular. **)
lemma normal_imp_regular_on:
  assumes hN: "top1_normal_on X T"
  shows "top1_regular_on X T"
proof -
  have hT1: "top1_T1_on X T"
    using hN unfolding top1_normal_on_def by blast
  have hSep:
    "\<forall>C D. closedin_on X T C \<and> closedin_on X T D \<and> C \<inter> D = {}
       \<longrightarrow> (\<exists>U V. U \<in> T \<and> V \<in> T \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {})"
    using hN unfolding top1_normal_on_def by blast

  show ?thesis
    unfolding top1_regular_on_def
  proof (intro conjI)
    show "top1_T1_on X T"
      by (rule hT1)
    show "\<forall>x\<in>X. \<forall>C. closedin_on X T C \<and> x \<notin> C \<longrightarrow>
        (\<exists>U V. neighborhood_of x X T U \<and> V \<in> T \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro ballI allI impI)
      fix x C
      assume hxX: "x \<in> X"
      assume hC: "closedin_on X T C \<and> x \<notin> C"
      have hCcl: "closedin_on X T C" and hxC: "x \<notin> C"
        using hC by blast+

      have hsing_cl: "closedin_on X T {x}"
        using hT1 hxX unfolding top1_T1_on_def by blast
      have hdisj: "{x} \<inter> C = {}"
        using hxC by blast

      have hSep1:
        "closedin_on X T {x} \<and> closedin_on X T C \<and> {x} \<inter> C = {}
          \<longrightarrow> (\<exists>U V. U \<in> T \<and> V \<in> T \<and> {x} \<subseteq> U \<and> C \<subseteq> V \<and> U \<inter> V = {})"
      proof -
        have h1:
          "\<forall>D. closedin_on X T {x} \<and> closedin_on X T D \<and> {x} \<inter> D = {}
            \<longrightarrow> (\<exists>U V. U \<in> T \<and> V \<in> T \<and> {x} \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {})"
          by (rule spec[where x="{x}", OF hSep])
        show ?thesis
          by (rule spec[where x=C, OF h1])
      qed

      have hSep2: "\<exists>U V. U \<in> T \<and> V \<in> T \<and> {x} \<subseteq> U \<and> C \<subseteq> V \<and> U \<inter> V = {}"
        apply (rule mp[OF hSep1])
        apply (intro conjI)
          apply (rule hsing_cl)
         apply (rule hCcl)
        apply (rule hdisj)
        done

      obtain U V where hUT: "U \<in> T" and hVT: "V \<in> T"
          and hUx: "{x} \<subseteq> U" and hCV: "C \<subseteq> V" and hUV: "U \<inter> V = {}"
        using hSep2 by blast

      have hxU: "x \<in> U"
        using hUx by blast
      have hnbhd: "neighborhood_of x X T U"
        unfolding neighborhood_of_def using hUT hxU by blast

      show "\<exists>U V. neighborhood_of x X T U \<and> V \<in> T \<and> C \<subseteq> V \<and> U \<inter> V = {}"
        apply (rule exI[where x=U])
        apply (rule exI[where x=V])
        apply (intro conjI)
           apply (rule hnbhd)
          apply (rule hVT)
         apply (rule hCV)
        apply (rule hUV)
        done
    qed
  qed
qed

(** from \S32 Theorem 32.3 (Every compact Hausdorff space is normal) [top1.tex:4217] **)
theorem Theorem_32_3:
  assumes hcomp: "top1_compact_on X TX"
  assumes hH: "is_hausdorff_on X TX"
  shows "top1_normal_on X TX"
proof -
  have hTop: "is_topology_on X TX"
    using hcomp unfolding top1_compact_on_def by blast
  have hT1: "top1_T1_on X TX"
    by (rule hausdorff_imp_T1_on[OF hH])

  have empty_TX: "{} \<in> TX"
    by (rule conjunct1[OF hTop[unfolded is_topology_on_def]])
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])
  have inter_TX: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])

  show ?thesis
    unfolding top1_normal_on_def
  proof (intro conjI)
    show "top1_T1_on X TX" by (rule hT1)
    show "\<forall>A B. closedin_on X TX A \<and> closedin_on X TX B \<and> A \<inter> B = {}
        \<longrightarrow> (\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro allI impI)
      fix A B
      assume hAB: "closedin_on X TX A \<and> closedin_on X TX B \<and> A \<inter> B = {}"
      have hAcl: "closedin_on X TX A" and hBcl: "closedin_on X TX B" and hdisj: "A \<inter> B = {}"
        using hAB by blast+
      have hAX: "A \<subseteq> X" by (rule closedin_sub[OF hAcl])
      have hBX: "B \<subseteq> X" by (rule closedin_sub[OF hBcl])

      show "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = {}"
	      proof (cases "A = {} \<or> B = {}")
	        case True
	        show ?thesis
	        proof (cases "A = {}")
	          case True
          show ?thesis
            apply (rule exI[where x="{}"])
            apply (rule exI[where x=X])
            apply (intro conjI)
                apply (rule empty_TX)
               apply (rule X_TX)
              apply (simp only: True)
             apply (rule hBX)
            apply simp
            done
        next
          case False
          have hBemp: "B = {}" using True False by blast
          show ?thesis
            apply (rule exI[where x=X])
            apply (rule exI[where x="{}"])
            apply (intro conjI)
                apply (rule X_TX)
               apply (rule empty_TX)
              apply (rule hAX)
             apply (simp only: hBemp)
            apply simp
            done
        qed
      next
        case False
        have hAne: "A \<noteq> {}" and hBne: "B \<noteq> {}"
          using False by blast+

        have hAX: "A \<subseteq> X" by (rule closedin_sub[OF hAcl])
        have hBX: "B \<subseteq> X" by (rule closedin_sub[OF hBcl])

        have hAcomp: "top1_compact_on A (subspace_topology X TX A)"
          by (rule Theorem_26_2[OF hcomp hAcl])
        have hBcomp: "top1_compact_on B (subspace_topology X TX B)"
          by (rule Theorem_26_2[OF hcomp hBcl])

        have ex_pair:
          "\<forall>a\<in>A. \<exists>p. (fst p) \<in> TX \<and> (snd p) \<in> TX \<and> a \<in> fst p \<and> B \<subseteq> snd p \<and> fst p \<inter> snd p = {}"
        proof (intro ballI)
          fix a assume haA: "a \<in> A"
          have haX: "a \<in> X" using hAX haA by blast
          have haB: "a \<notin> B"
          proof
            assume haB: "a \<in> B"
            have "a \<in> A \<inter> B" using haA haB by blast
            thus False using hdisj by blast
          qed
          obtain U V where hU: "U \<in> TX" and hV: "V \<in> TX" and haU: "a \<in> U" and hBV: "B \<subseteq> V" and hUV: "U \<inter> V = {}"
            using Lemma_26_4[OF hH hBX hBcomp haX haB] by blast
          show "\<exists>p. (fst p) \<in> TX \<and> (snd p) \<in> TX \<and> a \<in> fst p \<and> B \<subseteq> snd p \<and> fst p \<inter> snd p = {}"
            apply (rule exI[where x="(U, V)"])
            apply (simp only: fst_conv snd_conv hU hV haU hBV hUV)
            done
        qed

        obtain p where hp:
          "\<forall>a\<in>A. (fst (p a)) \<in> TX \<and> (snd (p a)) \<in> TX \<and> a \<in> fst (p a)
                 \<and> B \<subseteq> snd (p a) \<and> fst (p a) \<inter> snd (p a) = {}"
          using bchoice[OF ex_pair] by blast

        define Uc where "Uc = {A \<inter> fst (p a) | a. a \<in> A}"
        have hUc_sub: "Uc \<subseteq> subspace_topology X TX A"
        proof (rule subsetI)
          fix W
          assume hW: "W \<in> Uc"
          obtain a where haA: "a \<in> A" and hWeq: "W = A \<inter> fst (p a)"
            using hW unfolding Uc_def by blast
          have hUopen: "fst (p a) \<in> TX"
            using hp haA by blast
          show "W \<in> subspace_topology X TX A"
            unfolding subspace_topology_def
            apply (rule CollectI)
            apply (rule exI[where x="fst (p a)"])
            apply (intro conjI)
             apply (simp only: hWeq)
            apply (rule hUopen)
            done
        qed

        have hA_cov: "A \<subseteq> \<Union>Uc"
        proof (rule subsetI)
          fix a assume haA: "a \<in> A"
          have hpa: "a \<in> fst (p a)"
            using hp haA by blast
          have haInt: "a \<in> A \<inter> fst (p a)"
            using haA hpa by blast
          have hMem: "A \<inter> fst (p a) \<in> Uc"
            unfolding Uc_def using haA by blast
          show "a \<in> \<Union>Uc"
            by (rule UnionI[OF hMem haInt])
        qed

        have compact_coverA:
          "\<forall>Vc. Vc \<subseteq> subspace_topology X TX A \<and> A \<subseteq> \<Union>Vc
             \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Vc \<and> A \<subseteq> \<Union>F)"
          using hAcomp unfolding top1_compact_on_def by blast

        have hCover_imp: "Uc \<subseteq> subspace_topology X TX A \<and> A \<subseteq> \<Union>Uc
             \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F)"
          by (rule spec[where x=Uc, OF compact_coverA])
        have hCover: "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
          by (rule mp[OF hCover_imp], intro conjI, rule hUc_sub, rule hA_cov)
        obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "A \<subseteq> \<Union>F"
          using hCover by blast

        have hFne: "F \<noteq> {}"
        proof
          assume hFe: "F = {}"
          have "A \<subseteq> \<Union>{}" using hFcov hFe by simp
          hence "A = {}" by blast
          thus False using hAne by contradiction
        qed

        have ex_idx: "\<forall>W\<in>F. \<exists>a. a \<in> A \<and> W = A \<inter> fst (p a)"
        proof (intro ballI)
          fix W assume hWF: "W \<in> F"
          have hWU: "W \<in> Uc" using hFsub hWF by blast
          obtain a where haA: "a \<in> A" and hWeq: "W = A \<inter> fst (p a)"
            using hWU unfolding Uc_def by blast
          show "\<exists>a. a \<in> A \<and> W = A \<inter> fst (p a)"
            by (rule exI[where x=a], intro conjI, rule haA, rule hWeq)
        qed

        obtain sel where hsel:
          "\<forall>W\<in>F. sel W \<in> A \<and> W = A \<inter> fst (p (sel W))"
          using bchoice[OF ex_idx] by blast

        define I where "I = sel ` F"
        have hIfin: "finite I"
          unfolding I_def using hFfin by (rule finite_imageI)
        have hIne: "I \<noteq> {}"
          unfolding I_def using hFne by blast
        have hIsubA: "I \<subseteq> A"
          unfolding I_def using hsel by blast

        define U where "U = \<Union>((fst \<circ> p) ` I)"
        define V where "V = \<Inter>((snd \<circ> p) ` I)"

        have hUp_sub: "((fst \<circ> p) ` I) \<subseteq> TX"
        proof (rule subsetI)
          fix W assume hW: "W \<in> (fst \<circ> p) ` I"
          have exa: "\<exists>a\<in>I. W = (fst \<circ> p) a"
            using hW by (rule iffD1[OF image_iff])
          obtain a where haI: "a \<in> I" and hWeq0: "W = (fst \<circ> p) a"
            using exa by blast
          have hWeq: "W = fst (p a)"
            using hWeq0 by simp
          have haA: "a \<in> A" using hIsubA haI by blast
          have hUopen: "fst (p a) \<in> TX" using hp haA by blast
          show "W \<in> TX" using hUopen hWeq by simp
        qed
        have hVp_sub: "((snd \<circ> p) ` I) \<subseteq> TX"
        proof (rule subsetI)
          fix W assume hW: "W \<in> (snd \<circ> p) ` I"
          have exa: "\<exists>a\<in>I. W = (snd \<circ> p) a"
            using hW by (rule iffD1[OF image_iff])
          obtain a where haI: "a \<in> I" and hWeq0: "W = (snd \<circ> p) a"
            using exa by blast
          have hWeq: "W = snd (p a)"
            using hWeq0 by simp
          have haA: "a \<in> A" using hIsubA haI by blast
          have hVopen': "snd (p a) \<in> TX" using hp haA by blast
          show "W \<in> TX" using hVopen' hWeq by simp
        qed

        have hUopen: "U \<in> TX"
          unfolding U_def by (rule union_TX[rule_format, OF hUp_sub])
        have hVopen: "V \<in> TX"
        proof -
          have hF0: "finite ((snd \<circ> p) ` I)"
            using hIfin by (rule finite_imageI)
          have hF0ne: "((snd \<circ> p) ` I) \<noteq> {}"
            using hIne by blast
          have "finite ((snd \<circ> p) ` I) \<and> ((snd \<circ> p) ` I) \<noteq> {} \<and> ((snd \<circ> p) ` I) \<subseteq> TX"
            using hF0 hF0ne hVp_sub by blast
          hence "\<Inter>((snd \<circ> p) ` I) \<in> TX"
            using inter_TX by blast
          thus ?thesis unfolding V_def by simp
        qed

        have hA_sub_U: "A \<subseteq> U"
        proof (rule subsetI)
          fix x assume hxA: "x \<in> A"
          have hxUF: "x \<in> \<Union>F" using hFcov hxA by blast
          obtain W where hWF: "W \<in> F" and hxW: "x \<in> W"
            using hxUF by blast
          have hselW: "sel W \<in> A" and hWeq: "W = A \<inter> fst (p (sel W))"
            using hsel hWF by blast+
          have hxU: "x \<in> fst (p (sel W))"
            using hxW hWeq by blast
          have hmemI: "sel W \<in> I"
            unfolding I_def using hWF by blast
          have hmemUfam: "fst (p (sel W)) \<in> (fst \<circ> p) ` I"
          proof -
            have "(fst \<circ> p) (sel W) \<in> (fst \<circ> p) ` I"
              by (rule imageI[OF hmemI])
            thus ?thesis by simp
          qed
          show "x \<in> U"
            unfolding U_def by (rule UnionI[OF hmemUfam hxU])
        qed

        have hB_sub_V: "B \<subseteq> V"
        proof (rule subsetI)
          fix b assume hbB: "b \<in> B"
          show "b \<in> V"
            unfolding V_def
          proof (rule InterI)
            fix W assume hW: "W \<in> (snd \<circ> p) ` I"
            have exa: "\<exists>a\<in>I. W = (snd \<circ> p) a"
              using hW by (rule iffD1[OF image_iff])
            obtain a where haI: "a \<in> I" and hWeq0: "W = (snd \<circ> p) a"
              using exa by blast
            have hWeq: "W = snd (p a)"
              using hWeq0 by simp
            have haA: "a \<in> A" using hIsubA haI by blast
            have hBV: "B \<subseteq> snd (p a)" using hp haA by blast
            show "b \<in> W"
              using hBV hbB hWeq by blast
          qed
        qed

        have hUV_disj: "U \<inter> V = {}"
        proof (rule ccontr)
          assume hne: "U \<inter> V \<noteq> {}"
          obtain x where hx: "x \<in> U \<inter> V"
            using hne by blast
          have hxU: "x \<in> U" and hxV: "x \<in> V" using hx by blast+
          obtain W where hW: "W \<in> (fst \<circ> p) ` I" and hxW: "x \<in> W"
            using hxU unfolding U_def by blast
          have exa: "\<exists>a\<in>I. W = (fst \<circ> p) a"
            using hW by (rule iffD1[OF image_iff])
          obtain a where haI: "a \<in> I" and hWeq0: "W = (fst \<circ> p) a"
            using exa by blast
          have hWeq: "W = fst (p a)"
            using hWeq0 by simp
          have haA: "a \<in> A" using hIsubA haI by blast
          have hxVpa: "x \<in> snd (p a)"
          proof -
            have hmem: "snd (p a) \<in> (snd \<circ> p) ` I"
            proof -
              have "(snd \<circ> p) a \<in> (snd \<circ> p) ` I"
                by (rule imageI[OF haI])
              thus ?thesis by simp
            qed
            have hxV': "x \<in> \<Inter>((snd \<circ> p) ` I)"
              using hxV unfolding V_def by simp
            show ?thesis
              by (rule InterD[OF hxV' hmem])
          qed
          have hdisjpa: "fst (p a) \<inter> snd (p a) = {}"
            using hp haA by blast
          have "x \<in> fst (p a) \<inter> snd (p a)"
            using hxW hxVpa hWeq by blast
          thus False using hdisjpa by blast
        qed

        show ?thesis
          apply (rule exI[where x=U])
          apply (rule exI[where x=V])
          apply (intro conjI)
              apply (rule hUopen)
             apply (rule hVopen)
            apply (rule hA_sub_U)
           apply (rule hB_sub_V)
          apply (rule hUV_disj)
          done
      qed
    qed
  qed
qed

(** from \S32 Theorem 32.4 (Every well-ordered set is normal in the order topology) [top1.tex:4230] **)
text \<open>
  For a well-ordered type, we follow the proof in @{file \<open>top1.tex\<close>}:
  in the order topology, half-open intervals \<open>(x,y]\<close> are open; using such intervals
  one can separate disjoint closed sets.
\<close>

lemma wellorder_Least_le_all:
  fixes a0 :: "'a::wellorder"
  defines "a0 \<equiv> (LEAST a. True)"
  shows "\<forall>x. a0 \<le> x"
proof (intro allI)
  fix x
  have "True" by simp
  thus "a0 \<le> x"
    unfolding a0_def
    by (rule Least_le)
qed

lemma wellorder_min_lt_if_ne:
  fixes a0 :: "'a::wellorder"
  assumes ha0: "\<forall>x. a0 \<le> x"
  assumes hne: "x \<noteq> a0"
  shows "a0 < x"
proof -
  have "a0 \<le> x"
    by (rule spec[OF ha0])
  thus ?thesis
    using hne by simp
qed

lemma wellorder_Ioc_open_in_order_topology:
  fixes x y :: "'a::wellorder"
  assumes hxy: "x < y"
  shows "{x <.. y} \<in> (order_topology_on_UNIV::'a set set)"
proof (cases "\<exists>z. y < z")
  case True
  define s where "s = (LEAST z. y < z)"
  have hys: "y < s"
    unfolding s_def by (rule LeastI_ex[OF True])
  have hLeast: "\<And>t. y < t \<Longrightarrow> s \<le> t"
    unfolding s_def by (rule Least_le)

  have hEq: "{x <.. y} = open_interval x s"
  proof (rule set_eqI)
    fix t
    show "t \<in> {x <.. y} \<longleftrightarrow> t \<in> open_interval x s"
    proof (rule iffI)
      assume ht: "t \<in> {x <.. y}"
      have hxt: "x < t"
        using ht by simp
      have hty: "t \<le> y"
        using ht by simp
      have hts: "t < s"
        by (rule le_less_trans[OF hty hys])
      show "t \<in> open_interval x s"
        unfolding open_interval_def using hxt hts by simp
	    next
	      assume ht: "t \<in> open_interval x s"
		      have hxt_hts: "x < t \<and> t < s"
		        using ht by (simp add: open_interval_def)
		      have hxt: "x < t"
		        using hxt_hts by (elim conjE)
		      have hts: "t < s"
		        using hxt_hts by (elim conjE)
	      have hty: "t \<le> y"
	      proof (rule ccontr)
	        assume hnot: "\<not> t \<le> y"
        have hylt: "y < t"
          using hnot by simp
        have hsle: "s \<le> t"
          by (rule hLeast[OF hylt])
        show False
          using hts hsle by simp
      qed
      show "t \<in> {x <.. y}"
        using hxt hty by simp
    qed
  qed

  have hxs: "x < s"
    by (rule less_trans[OF hxy hys])
  have "open_interval x s \<in> (order_topology_on_UNIV::'a set set)"
    by (rule open_interval_in_order_topology[OF hxs])
  thus ?thesis
    unfolding hEq .
next
  case False
  have hTop: "\<forall>t. t \<le> y"
  proof (intro allI)
    fix t
    show "t \<le> y"
    proof (rule ccontr)
      assume hnot: "\<not> t \<le> y"
      have "y < t"
        using hnot by simp
      thus False
        using False by blast
    qed
  qed

  have hEq: "{x <.. y} = open_ray_gt x"
  proof (rule set_eqI)
    fix t
    show "t \<in> {x <.. y} \<longleftrightarrow> t \<in> open_ray_gt x"
    proof (rule iffI)
      assume ht: "t \<in> {x <.. y}"
      have hxt: "x < t" using ht by simp
      show "t \<in> open_ray_gt x"
        unfolding open_ray_gt_def using hxt by simp
	    next
	      assume ht: "t \<in> open_ray_gt x"
	      have hxt: "x < t"
	        using ht unfolding open_ray_gt_def by simp
	      have hty: "t \<le> y"
	        by (rule spec[OF hTop])
	      show "t \<in> {x <.. y}"
	        using hxt hty by simp
	    qed
	  qed

  have "open_ray_gt x \<in> (order_topology_on_UNIV::'a set set)"
    by (rule open_ray_gt_in_order_topology)
  thus ?thesis
    unfolding hEq .
qed

lemma wellorder_basis_refine_Ioc:
  fixes a :: "'a::wellorder"
  fixes a0 :: "'a"
  assumes ha0: "\<forall>x. a0 \<le> x"
  assumes hne: "a \<noteq> a0"
  assumes hb: "b \<in> basis_order_topology"
  assumes hab: "a \<in> b"
  shows "\<exists>x<a. {x <.. a} \<subseteq> b"
proof -
  have ha0lt: "a0 < a"
    by (rule wellorder_min_lt_if_ne[OF ha0 hne])
  have ha0le: "a0 \<le> a"
    using ha0 by simp

  from hb have hbU:
    "b \<in> {open_interval u v | u v. u < v}
     \<or> b \<in> {open_ray_gt u | u. True}
     \<or> b \<in> {open_ray_lt u | u. True}
     \<or> b = (UNIV::'a set)"
    unfolding basis_order_topology_def by blast

  show ?thesis
  proof (rule disjE[OF hbU])
    assume h1: "b \<in> {open_interval u v | u v. u < v}"
    then obtain u v where huv: "u < v" and hbeq: "b = open_interval u v"
      by blast
	    have hua_hav: "u < a \<and> a < v"
	      using hab unfolding hbeq open_interval_def by simp
	    have hua: "u < a"
	      using hua_hav by (elim conjE)
	    have hav: "a < v"
	      using hua_hav by (elim conjE)
    show "\<exists>x<a. {x <.. a} \<subseteq> b"
    proof (rule exI[where x=u], intro conjI)
      show "u < a" by (rule hua)
      show "{u <.. a} \<subseteq> b"
      proof (rule subsetI)
        fix t assume ht: "t \<in> {u <.. a}"
        have hut: "u < t"
          using ht by simp
        have hta: "t \<le> a"
          using ht by simp
        have htv: "t < v"
          by (rule le_less_trans[OF hta hav])
        show "t \<in> b"
          unfolding hbeq open_interval_def using hut htv by simp
      qed
    qed
  next
    assume hrest: "b \<in> {open_ray_gt u | u. True}
      \<or> b \<in> {open_ray_lt u | u. True}
      \<or> b = (UNIV::'a set)"
    show ?thesis
    proof (rule disjE[OF hrest])
      assume h2: "b \<in> {open_ray_gt u | u. True}"
      then obtain u where hbeq: "b = open_ray_gt u" by blast
      have hua: "u < a"
        using hab unfolding hbeq open_ray_gt_def by simp
	      show "\<exists>x<a. {x <.. a} \<subseteq> b"
	      proof (rule exI[where x=u], intro conjI)
	        show "u < a" by (rule hua)
	        show "{u <.. a} \<subseteq> b"
	        proof (rule subsetI)
	          fix t assume ht: "t \<in> {u <.. a}"
	          have "u < t"
	            using ht by simp
	          thus "t \<in> b"
	            unfolding hbeq open_ray_gt_def by simp
	        qed
	      qed
	    next
	      assume hrest2: "b \<in> {open_ray_lt u | u. True} \<or> b = (UNIV::'a set)"
	      show ?thesis
      proof (rule disjE[OF hrest2])
        assume h3: "b \<in> {open_ray_lt u | u. True}"
        then obtain u where hbeq: "b = open_ray_lt u" by blast
        have hau: "a < u"
          using hab unfolding hbeq open_ray_lt_def by simp
	        show "\<exists>x<a. {x <.. a} \<subseteq> b"
	        proof (rule exI[where x=a0], intro conjI)
	          show "a0 < a" by (rule ha0lt)
	          show "{a0 <.. a} \<subseteq> b"
	          proof (rule subsetI)
	            fix t assume ht: "t \<in> {a0 <.. a}"
	            have hta: "t \<le> a"
	              using ht by simp
	            have htu: "t < u"
	              by (rule le_less_trans[OF hta hau])
	            show "t \<in> b"
	              unfolding hbeq open_ray_lt_def using htu by simp
	          qed
	        qed
	      next
	        assume h4: "b = (UNIV::'a set)"
        show "\<exists>x<a. {x <.. a} \<subseteq> b"
        proof (rule exI[where x=a0], intro conjI)
          show "a0 < a" by (rule ha0lt)
          show "{a0 <.. a} \<subseteq> b"
            unfolding h4 by simp
        qed
      qed
    qed
  qed
qed

lemma wellorder_open_refine_Ioc:
  fixes a :: "'a::wellorder"
  fixes a0 :: "'a"
  assumes ha0: "\<forall>x. a0 \<le> x"
  assumes hne: "a \<noteq> a0"
  assumes hU: "U \<in> (order_topology_on_UNIV::'a set set)"
  assumes haU: "a \<in> U"
  shows "\<exists>x<a. {x <.. a} \<subseteq> U"
proof -
  have hgen:
    "U \<in> topology_generated_by_basis (UNIV::'a set) basis_order_topology"
    using hU unfolding order_topology_on_UNIV_def by simp
  have hcov:
    "\<exists>b\<in>basis_order_topology. a \<in> b \<and> b \<subseteq> U"
    using hgen haU unfolding topology_generated_by_basis_def by blast
  then obtain b where hb: "b \<in> basis_order_topology" and hab: "a \<in> b" and hbsub: "b \<subseteq> U"
    by blast
  obtain x where hxa: "x < a" and hxsub: "{x <.. a} \<subseteq> b"
    using wellorder_basis_refine_Ioc[OF ha0 hne hb hab] by blast
  have "{x <.. a} \<subseteq> U"
    by (rule subset_trans[OF hxsub hbsub])
  show ?thesis
    by (rule exI[where x=x], intro conjI, rule hxa, rule \<open>{x <.. a} \<subseteq> U\<close>)
qed

lemma wellorder_min_singleton_open:
  fixes a0 :: "'a::wellorder"
  defines "a0 \<equiv> (LEAST a. True)"
  shows "{a0} \<in> (order_topology_on_UNIV::'a set set)"
proof (cases "\<exists>z. a0 < z")
  case True
  define s where "s = (LEAST z. a0 < z)"
  have ha0s: "a0 < s"
    unfolding s_def by (rule LeastI_ex[OF True])
  have hLeast: "\<And>t. a0 < t \<Longrightarrow> s \<le> t"
    unfolding s_def by (rule Least_le)

  have ha0le: "\<forall>x. a0 \<le> x"
    unfolding a0_def by (rule wellorder_Least_le_all)

  have hEq: "{a0} = open_ray_lt s"
  proof (rule set_eqI)
    fix t
    show "t \<in> {a0} \<longleftrightarrow> t \<in> open_ray_lt s"
    proof (rule iffI)
      assume ht: "t \<in> {a0}"
      have "t = a0" using ht by simp
      hence "t < s" using ha0s by simp
      thus "t \<in> open_ray_lt s"
        unfolding open_ray_lt_def by simp
    next
      assume ht: "t \<in> open_ray_lt s"
      have hts: "t < s"
        using ht unfolding open_ray_lt_def by simp
      have "t \<le> a0"
      proof (rule ccontr)
        assume hnot: "\<not> t \<le> a0"
        have ha0t: "a0 < t"
          using hnot by simp
        have hsle: "s \<le> t"
          by (rule hLeast[OF ha0t])
        show False
          using hts hsle by simp
      qed
      have hta0: "t = a0"
      proof -
        have ha0t: "a0 \<le> t"
          by (rule spec[OF ha0le])
        show ?thesis
          using ha0t \<open>t \<le> a0\<close> by simp
      qed
      show "t \<in> {a0}"
        using hta0 by simp
    qed
  qed

  have "open_ray_lt s \<in> (order_topology_on_UNIV::'a set set)"
    by (rule open_ray_lt_in_order_topology)
  thus ?thesis
    unfolding hEq by simp
next
  case False
  have hTop: "is_topology_on (UNIV::'a set) (order_topology_on_UNIV::'a set set)"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hAll: "\<forall>t. t = a0"
  proof (intro allI)
    fix t
    have "a0 \<le> t"
      unfolding a0_def by (rule Least_le, simp)
    moreover have "t \<le> a0"
    proof (rule ccontr)
      assume hnot: "\<not> t \<le> a0"
      have "a0 < t" using hnot by simp
      thus False using False by blast
    qed
    ultimately show "t = a0" by simp
  qed
  have hUNIV: "UNIV = ({a0}::'a set)"
    by (rule set_eqI, simp add: hAll)
  have "UNIV \<in> (order_topology_on_UNIV::'a set set)"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
  thus ?thesis
    unfolding hUNIV by simp
qed

theorem Theorem_32_4:
  shows "top1_normal_on (UNIV::'a::wellorder set) (order_topology_on_UNIV::'a set set)"
proof -
  let ?X = "(UNIV::'a set)"
  let ?T = "(order_topology_on_UNIV::'a set set)"

  have hHaus: "is_hausdorff_on ?X ?T"
    by (rule conjunct1[OF Theorem_17_11])
  have hT1: "top1_T1_on ?X ?T"
    by (rule hausdorff_imp_T1_on[OF hHaus])
  have hTop: "is_topology_on ?X ?T"
    using hT1 unfolding top1_T1_on_def by blast

	  have union_T: "\<And>U. U \<subseteq> ?T \<Longrightarrow> (\<Union>U) \<in> ?T"
	  proof -
	    fix U assume hU: "U \<subseteq> ?T"
	    have hUnion: "\<forall>U'. U' \<subseteq> ?T \<longrightarrow> (\<Union>U') \<in> ?T"
	      by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])
	    have hImp: "U \<subseteq> ?T \<longrightarrow> (\<Union>U) \<in> ?T"
	      by (rule spec[OF hUnion])
	    show "(\<Union>U) \<in> ?T"
	      by (rule mp[OF hImp hU])
	  qed

  define a0 :: 'a where "a0 = (LEAST a. True)"
  have ha0: "\<forall>x. a0 \<le> x"
    unfolding a0_def by (rule wellorder_Least_le_all)

  show ?thesis
    unfolding top1_normal_on_def
  proof (intro conjI)
    show "top1_T1_on ?X ?T" by (rule hT1)
    show "\<forall>A B. closedin_on ?X ?T A \<and> closedin_on ?X ?T B \<and> A \<inter> B = {}
        \<longrightarrow> (\<exists>U V. U \<in> ?T \<and> V \<in> ?T \<and> A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro allI impI)
      fix A B
      assume hAB: "closedin_on ?X ?T A \<and> closedin_on ?X ?T B \<and> A \<inter> B = {}"
      have hAcl: "closedin_on ?X ?T A" and hBcl: "closedin_on ?X ?T B" and hdisj: "A \<inter> B = {}"
        using hAB by blast+

      show "\<exists>U V. U \<in> ?T \<and> V \<in> ?T \<and> A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = {}"
      proof (cases "A = {} \<or> B = {}")
        case True
        show ?thesis
	        proof (cases "A = {}")
	          case True
	          have "({}::'a set) \<in> ?T"
	            by (rule conjunct1[OF hTop[unfolded is_topology_on_def]])
	          moreover have "UNIV \<in> ?T"
	            by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
	          then have hempty: "({}::'a set) \<in> ?T" and huniv: "UNIV \<in> ?T"
	            using calculation by blast+
	          show ?thesis
	          proof (rule exI[where x="{}"])
	            show "\<exists>V. {} \<in> ?T \<and> V \<in> ?T \<and> A \<subseteq> {} \<and> B \<subseteq> V \<and> {} \<inter> V = {}"
	            proof (rule exI[where x=UNIV], intro conjI)
	              show "{} \<in> ?T" by (rule hempty)
	              show "UNIV \<in> ?T" by (rule huniv)
	              show "A \<subseteq> {}" using True by simp
	              show "B \<subseteq> UNIV" by simp
	              show "{} \<inter> UNIV = {}" by simp
	            qed
	          qed
	        next
	          case False
	          have hBemp: "B = {}" using True False by blast
	          have "UNIV \<in> ?T"
	            by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
	          moreover have "({}::'a set) \<in> ?T"
	            by (rule conjunct1[OF hTop[unfolded is_topology_on_def]])
	          then have huniv: "UNIV \<in> ?T" and hempty: "({}::'a set) \<in> ?T"
	            using calculation by blast+
	          show ?thesis
	          proof (rule exI[where x=UNIV])
	            show "\<exists>V. UNIV \<in> ?T \<and> V \<in> ?T \<and> A \<subseteq> UNIV \<and> B \<subseteq> V \<and> UNIV \<inter> V = {}"
	            proof (rule exI[where x="{}"], intro conjI)
	              show "UNIV \<in> ?T" by (rule huniv)
	              show "{} \<in> ?T" by (rule hempty)
	              show "A \<subseteq> UNIV" by simp
	              show "B \<subseteq> {}" using hBemp by simp
	              show "UNIV \<inter> {} = {}" by simp
	            qed
	          qed
	        qed
      next
        case False

        have hA0: "a0 \<notin> A \<or> a0 \<in> A" by blast
        show ?thesis
        proof (cases "a0 \<in> A")
          case True
          have ha0B: "a0 \<notin> B"
          proof
            assume ha0B: "a0 \<in> B"
            have "a0 \<in> A \<inter> B" using True ha0B by blast
            thus False using hdisj by blast
          qed

          have hsing_open: "{a0} \<in> ?T"
            unfolding a0_def by (rule wellorder_min_singleton_open)

          (* choose intervals for points of A - {a0} disjoint from B *)
	          have hexA: "\<forall>a\<in>A - {a0}. \<exists>x<a. {x <.. a} \<subseteq> ?X - B"
	          proof (intro ballI)
	            fix a assume ha: "a \<in> A - {a0}"
	            have haA: "a \<in> A" and hne: "a \<noteq> a0" using ha by blast+
	            have haX: "a \<in> ?X" by simp
            have haB: "a \<notin> B"
            proof
              assume haB: "a \<in> B"
              have "a \<in> A \<inter> B" using haA haB by blast
              thus False using hdisj by blast
            qed
	            have hUopen: "?X - B \<in> ?T"
	              by (rule closedin_diff_open[OF hBcl])
	            have hnbd: "a \<in> ?X - B" using haX haB by blast
	            show "\<exists>x<a. {x <.. a} \<subseteq> ?X - B"
	              by (rule wellorder_open_refine_Ioc[OF ha0 hne hUopen hnbd])
	          qed
	          obtain xA where hxA: "\<forall>a\<in>A - {a0}. xA a < a \<and> {xA a <.. a} \<subseteq> ?X - B"
	            using bchoice[OF hexA] by blast

	          have hexB: "\<forall>b\<in>B. \<exists>y<b. {y <.. b} \<subseteq> ?X - A"
	          proof (intro ballI)
	            fix b assume hb: "b \<in> B"
	            have hbX: "b \<in> ?X" by simp
            have hbA: "b \<notin> A"
            proof
              assume hbA: "b \<in> A"
              have "b \<in> A \<inter> B" using hbA hb by blast
              thus False using hdisj by blast
            qed
            have hne: "b \<noteq> a0"
              using hb ha0B by blast
	            have hUopen: "?X - A \<in> ?T"
	              by (rule closedin_diff_open[OF hAcl])
	            have hnbd: "b \<in> ?X - A" using hbX hbA by blast
	            show "\<exists>y<b. {y <.. b} \<subseteq> ?X - A"
	              by (rule wellorder_open_refine_Ioc[OF ha0 hne hUopen hnbd])
	          qed
	          obtain yB where hyB: "\<forall>b\<in>B. yB b < b \<and> {yB b <.. b} \<subseteq> ?X - A"
	            using bchoice[OF hexB] by blast

	          define U where "U = {a0} \<union> (\<Union>a\<in>A - {a0}. {xA a <.. a})"
	          define V where "V = (\<Union>b\<in>B. {yB b <.. b})"

          have hUopen: "U \<in> ?T"
          proof -
	            have hFam: "{{xA a <.. a} | a. a \<in> A - {a0}} \<subseteq> ?T"
	            proof (rule subsetI)
	              fix W assume hW: "W \<in> {{xA a <.. a} | a. a \<in> A - {a0}}"
	              then obtain a where ha: "a \<in> A - {a0}" and hWeq: "W = {xA a <.. a}"
	                by blast
	              have hxa: "xA a < a"
	                using hxA ha by blast
	              have "{xA a <.. a} \<in> ?T"
	                by (rule wellorder_Ioc_open_in_order_topology[OF hxa])
	              thus "W \<in> ?T"
	                using hWeq by simp
	            qed
	            have hUnion: "(\<Union>{{xA a <.. a} | a. a \<in> A - {a0}}) \<in> ?T"
	              by (rule union_T[OF hFam])
	            have hEq: "(\<Union>{{xA a <.. a} | a. a \<in> A - {a0}}) = (\<Union>a\<in>A - {a0}. {xA a <.. a})"
	              by blast
	            have hPart: "(\<Union>a\<in>A - {a0}. {xA a <.. a}) \<in> ?T"
	              using hUnion unfolding hEq by simp
	            have hsub: "{ {a0}, (\<Union>a\<in>A - {a0}. {xA a <.. a}) } \<subseteq> ?T"
	              using hsing_open hPart by simp
	            have "(\<Union>{ {a0}, (\<Union>a\<in>A - {a0}. {xA a <.. a}) }) \<in> ?T"
	              by (rule union_T[OF hsub])
	            thus ?thesis
	              unfolding U_def by simp
	          qed

	          have hVopen: "V \<in> ?T"
	          proof -
	            have hFam: "{{yB b <.. b} | b. b \<in> B} \<subseteq> ?T"
	            proof (rule subsetI)
	              fix W assume hW: "W \<in> {{yB b <.. b} | b. b \<in> B}"
	              then obtain b where hb: "b \<in> B" and hWeq: "W = {yB b <.. b}"
	                by blast
	              have hyb: "yB b < b"
	                using hyB hb by blast
	              have "{yB b <.. b} \<in> ?T"
	                by (rule wellorder_Ioc_open_in_order_topology[OF hyb])
	              thus "W \<in> ?T"
	                using hWeq by simp
	            qed
	            have hUnion: "(\<Union>{{yB b <.. b} | b. b \<in> B}) \<in> ?T"
	              by (rule union_T[OF hFam])
	            have hEq: "(\<Union>{{yB b <.. b} | b. b \<in> B}) = (\<Union>b\<in>B. {yB b <.. b})"
	              by blast
	            show ?thesis
	              unfolding V_def using hUnion hEq by simp
	          qed

          have hA_sub: "A \<subseteq> U"
          proof (rule subsetI)
            fix a assume haA: "a \<in> A"
            show "a \<in> U"
            proof (cases "a = a0")
              case True
              show ?thesis
                unfolding U_def using True by simp
            next
              case False
	              have ha: "a \<in> A - {a0}"
	                using haA False by blast
	              have hxa: "xA a < a"
	                using hxA ha by blast
	              have "a \<in> {xA a <.. a}"
	                using hxa by simp
	              thus ?thesis
	                unfolding U_def using ha by blast
	            qed
	          qed

          have hB_sub: "B \<subseteq> V"
          proof (rule subsetI)
	            fix b assume hbB: "b \<in> B"
	            have hyb: "yB b < b"
	              using hyB hbB by blast
	            have "b \<in> {yB b <.. b}"
	              using hyb by simp
	            thus "b \<in> V"
	              unfolding V_def using hbB by blast
	          qed

          have hUV_disj: "U \<inter> V = {}"
          proof (rule equalityI)
            show "U \<inter> V \<subseteq> {}"
            proof (rule subsetI)
              fix z assume hz: "z \<in> U \<inter> V"
              have hzU: "z \<in> U" and hzV: "z \<in> V" using hz by blast+

	              have hzA0: "z = a0 \<or> z \<in> (\<Union>a\<in>A - {a0}. {xA a <.. a})"
	                using hzU unfolding U_def by blast
              show "z \<in> {}"
	              proof (cases "z = a0")
	                case True
	                have "z \<notin> V"
		                proof
		                  assume hzVin: "z \<in> V"
		                  then obtain b where hbB: "b \<in> B" and hzI: "z \<in> {yB b <.. b}"
		                    unfolding V_def by blast
		                  have hybz: "yB b < z"
		                    using hzI by simp
		                  have ha0yb: "a0 \<le> yB b"
		                    by (rule spec[OF ha0])
		                  have "a0 < z"
		                    by (rule le_less_trans[OF ha0yb hybz])
		                  thus False
		                    using True by simp
	                qed
	                thus ?thesis using hzV by blast
		              next
		                case False
		                then obtain a where ha: "a \<in> A - {a0}" and hzIa: "z \<in> {xA a <.. a}"
		                  using hzA0 unfolding Union_eq by blast
		                have haA: "a \<in> A"
		                  using ha by simp
		                have ha0ne: "a \<noteq> a0"
		                  using ha by blast
		                have hzIa': "z \<in> {xA a <.. a}"
		                  by (rule hzIa)
		                obtain b where hbB: "b \<in> B" and hzIb: "z \<in> {yB b <.. b}"
		                  using hzV unfolding V_def by blast
                have haB: "a \<notin> B"
                proof
                  assume "a \<in> B"
                  have "a \<in> A \<inter> B" using haA \<open>a \<in> B\<close> by blast
                  thus False using hdisj by blast
                qed
                have hneab: "a \<noteq> b"
                  using haA haB hbB by blast
                have hcase: "a < b \<or> b < a"
                  using hneab neq_iff by blast
                show ?thesis
	                proof (rule disjE[OF hcase])
	                  assume hablt: "a < b"
	                  have hbprop: "{yB b <.. b} \<subseteq> ?X - A"
	                    using hyB hbB by blast
	                  have hyb: "yB b < b"
	                    using hyB hbB by blast
	                  have hzb1: "z \<le> a"
	                    using hzIa' by simp
	                  have hzb2: "yB b < z"
	                    using hzIb by simp
                  show "z \<in> {}"
	                  proof (cases "a \<le> yB b")
	                    case True
	                    have "z \<le> yB b"
	                      by (rule order_trans[OF hzb1 True])
	                    have "yB b < yB b"
	                      by (rule less_le_trans[OF hzb2 \<open>z \<le> yB b\<close>])
	                    thus ?thesis by simp
	                  next
	                    case False
		                    have hyb_a: "yB b < a"
		                      using False by simp
	                    have "a \<le> b"
	                      using hablt by simp
	                    have "a \<in> {yB b <.. b}"
	                      using hyb_a \<open>a \<le> b\<close> by simp
		                    hence "a \<in> ?X - A"
		                      by (rule subsetD[OF hbprop])
		                    have False using haA \<open>a \<in> ?X - A\<close> by simp
		                    thus ?thesis by simp
		                  qed
		              next
		                assume hbalt: "b < a"
		                  have hxAa: "xA a < a \<and> {xA a <.. a} \<subseteq> ?X - B"
		                    by (rule bspec[OF hxA ha])
		                  have haprop: "{xA a <.. a} \<subseteq> ?X - B"
		                    by (rule conjunct2[OF hxAa])
		                  have hxa: "xA a < a"
		                    by (rule conjunct1[OF hxAa])
		                  have hzb1: "z \<le> b"
		                    using hzIb by simp
		                  have hzb2: "xA a < z"
		                    using hzIa' by simp
	                  show "z \<in> {}"
	                  proof (cases "b \<le> xA a")
	                    case True
	                    have "z \<le> xA a"
	                      by (rule order_trans[OF hzb1 True])
	                    have "xA a < xA a"
	                      by (rule less_le_trans[OF hzb2 \<open>z \<le> xA a\<close>])
	                    thus ?thesis by simp
	                  next
	                    case False
		                    have hxa_b: "xA a < b"
		                      using False by simp
	                    have "b \<le> a"
	                      using hbalt by simp
	                    have "b \<in> {xA a <.. a}"
	                      using hxa_b \<open>b \<le> a\<close> by simp
		                    hence "b \<in> ?X - B"
		                      by (rule subsetD[OF haprop])
		                    have False using hbB \<open>b \<in> ?X - B\<close> by simp
		                    thus ?thesis by simp
		                  qed
	                qed
	              qed
            qed
            show "{} \<subseteq> U \<inter> V" by simp
          qed

          show ?thesis
            apply (rule exI[where x=U])
            apply (rule exI[where x=V])
            using hUopen hVopen hA_sub hB_sub hUV_disj by blast
	        next
	          case False
	          show ?thesis
	          proof (cases "a0 \<in> B")
	            case True
	            (* symmetric to the previous case: construct neighborhoods with {a0} on the B-side *)
	            have ha0A: "a0 \<notin> A"
	              using \<open>a0 \<notin> A\<close> .
	            have ha0B: "a0 \<in> B"
	              using True .

	            have hsing_open: "{a0} \<in> ?T"
	              unfolding a0_def by (rule wellorder_min_singleton_open)

	            have hexB: "\<forall>b\<in>B - {a0}. \<exists>x<b. {x <.. b} \<subseteq> ?X - A"
	            proof (intro ballI)
	              fix b assume hb: "b \<in> B - {a0}"
	              have hbB: "b \<in> B" and hne: "b \<noteq> a0"
	                using hb by blast+
	              have hbX: "b \<in> ?X" by simp
	              have hbA: "b \<notin> A"
	              proof
	                assume hbA: "b \<in> A"
	                have "b \<in> A \<inter> B" using hbA hbB by blast
	                thus False using hdisj by blast
	              qed
	              have hUopen: "?X - A \<in> ?T"
	                by (rule closedin_diff_open[OF hAcl])
	              have hnbd: "b \<in> ?X - A"
	                using hbX hbA by blast
	              show "\<exists>x<b. {x <.. b} \<subseteq> ?X - A"
	                by (rule wellorder_open_refine_Ioc[OF ha0 hne hUopen hnbd])
	            qed
	            obtain xB where hxB: "\<forall>b\<in>B - {a0}. xB b < b \<and> {xB b <.. b} \<subseteq> ?X - A"
	              using bchoice[OF hexB] by blast

	            have hexA: "\<forall>a\<in>A. \<exists>y<a. {y <.. a} \<subseteq> ?X - B"
	            proof (intro ballI)
	              fix a assume haA': "a \<in> A"
	              have hne: "a \<noteq> a0"
	                using ha0A haA' by blast
	              have haX: "a \<in> ?X" by simp
	              have haB: "a \<notin> B"
	              proof
	                assume haB: "a \<in> B"
	                have "a \<in> A \<inter> B" using haA' haB by blast
	                thus False using hdisj by blast
	              qed
	              have hUopen: "?X - B \<in> ?T"
	                by (rule closedin_diff_open[OF hBcl])
	              have hnbd: "a \<in> ?X - B"
	                using haX haB by blast
	              show "\<exists>y<a. {y <.. a} \<subseteq> ?X - B"
	                by (rule wellorder_open_refine_Ioc[OF ha0 hne hUopen hnbd])
	            qed
	            obtain yA where hyA: "\<forall>a\<in>A. yA a < a \<and> {yA a <.. a} \<subseteq> ?X - B"
	              using bchoice[OF hexA] by blast

	            define U where "U = {a0} \<union> (\<Union>b\<in>B - {a0}. {xB b <.. b})"
	            define V where "V = (\<Union>a\<in>A. {yA a <.. a})"

	            have hUopen: "U \<in> ?T"
	            proof -
	              have hFam: "{{xB b <.. b} | b. b \<in> B - {a0}} \<subseteq> ?T"
	              proof (rule subsetI)
	                fix W assume hW: "W \<in> {{xB b <.. b} | b. b \<in> B - {a0}}"
	                then obtain b where hb: "b \<in> B - {a0}" and hWeq: "W = {xB b <.. b}"
	                  by blast
	                have hxb: "xB b < b"
	                  using hxB hb by blast
	                have "{xB b <.. b} \<in> ?T"
	                  by (rule wellorder_Ioc_open_in_order_topology[OF hxb])
	                thus "W \<in> ?T"
	                  using hWeq by simp
	              qed
	              have hUnion: "(\<Union>{{xB b <.. b} | b. b \<in> B - {a0}}) \<in> ?T"
	                by (rule union_T[OF hFam])
	              have hEq: "(\<Union>{{xB b <.. b} | b. b \<in> B - {a0}}) = (\<Union>b\<in>B - {a0}. {xB b <.. b})"
	                by blast
	              have hPart: "(\<Union>b\<in>B - {a0}. {xB b <.. b}) \<in> ?T"
	                using hUnion unfolding hEq by simp
	              have hsub: "{ {a0}, (\<Union>b\<in>B - {a0}. {xB b <.. b}) } \<subseteq> ?T"
	                using hsing_open hPart by simp
	              have "(\<Union>{ {a0}, (\<Union>b\<in>B - {a0}. {xB b <.. b}) }) \<in> ?T"
	                by (rule union_T[OF hsub])
	              thus ?thesis
	                unfolding U_def by simp
	            qed

	            have hVopen: "V \<in> ?T"
	            proof -
	              have hFam: "{{yA a <.. a} | a. a \<in> A} \<subseteq> ?T"
	              proof (rule subsetI)
	                fix W assume hW: "W \<in> {{yA a <.. a} | a. a \<in> A}"
	                then obtain a where ha: "a \<in> A" and hWeq: "W = {yA a <.. a}"
	                  by blast
	                have hya: "yA a < a"
	                  using hyA ha by blast
	                have "{yA a <.. a} \<in> ?T"
	                  by (rule wellorder_Ioc_open_in_order_topology[OF hya])
	                thus "W \<in> ?T"
	                  using hWeq by simp
	              qed
	              have hUnion: "(\<Union>{{yA a <.. a} | a. a \<in> A}) \<in> ?T"
	                by (rule union_T[OF hFam])
	              have hEq: "(\<Union>{{yA a <.. a} | a. a \<in> A}) = (\<Union>a\<in>A. {yA a <.. a})"
	                by blast
	              show ?thesis
	                unfolding V_def using hUnion hEq by simp
	            qed

	            have hB_sub: "B \<subseteq> U"
	            proof (rule subsetI)
	              fix b assume hbB: "b \<in> B"
	              show "b \<in> U"
	              proof (cases "b = a0")
	                case True
	                show ?thesis unfolding U_def using True by simp
	              next
	                case False
	                have hb: "b \<in> B - {a0}"
	                  using hbB False by blast
	                have hxb: "xB b < b"
	                  using hxB hb by blast
	                have "b \<in> {xB b <.. b}"
	                  using hxb by simp
	                thus ?thesis
	                  unfolding U_def using hb by blast
	              qed
	            qed

	            have hA_sub: "A \<subseteq> V"
	            proof (rule subsetI)
	              fix a assume haA': "a \<in> A"
	              have hya: "yA a < a"
	                using hyA haA' by blast
	              have "a \<in> {yA a <.. a}"
	                using hya by simp
	              thus "a \<in> V"
	                unfolding V_def using haA' by blast
	            qed

	            have hUV_disj: "U \<inter> V = {}"
	            proof (rule equalityI)
	              show "U \<inter> V \<subseteq> {}"
	              proof (rule subsetI)
	                fix z assume hz: "z \<in> U \<inter> V"
	                have hzU: "z \<in> U" and hzV: "z \<in> V" using hz by blast+
	                have hzA0: "z = a0 \<or> z \<in> (\<Union>b\<in>B - {a0}. {xB b <.. b})"
	                  using hzU unfolding U_def by blast
	                show "z \<in> {}"
	                proof (cases "z = a0")
	                  case True
	                  have "z \<notin> V"
	                  proof
	                    assume hzVin: "z \<in> V"
	                    then obtain a where haA': "a \<in> A" and hzI: "z \<in> {yA a <.. a}"
	                      unfolding V_def by blast
	                    have hyaz: "yA a < z"
	                      using hzI by simp
	                    have ha0ya: "a0 \<le> yA a"
	                      by (rule spec[OF ha0])
	                    have "a0 < z"
	                      by (rule le_less_trans[OF ha0ya hyaz])
	                    thus False
	                      using True by simp
	                  qed
	                  thus ?thesis using hzV by blast
	                next
	                  case False
	                  then obtain b where hb: "b \<in> B - {a0}" and hzIb: "z \<in> {xB b <.. b}"
	                    using hzA0 by blast
	                  obtain a where haA': "a \<in> A" and hzIa: "z \<in> {yA a <.. a}"
	                    using hzV unfolding V_def by blast
	                  have haB: "a \<notin> B"
	                  proof
	                    assume "a \<in> B"
	                    have "a \<in> A \<inter> B" using haA' \<open>a \<in> B\<close> by blast
	                    thus False using hdisj by blast
	                  qed
	                  have hbB: "b \<in> B"
	                    using hb by blast
	                  have hbA: "b \<notin> A"
	                  proof
	                    assume "b \<in> A"
	                    have "b \<in> A \<inter> B" using \<open>b \<in> A\<close> hbB by blast
	                    thus False using hdisj by blast
	                  qed
	                  have hneab: "a \<noteq> b"
	                    using haA' hbA hbB by blast
	                  have hcase: "a < b \<or> b < a"
	                    using hneab neq_iff by blast
	                  show ?thesis
	                  proof (rule disjE[OF hcase])
	                    assume hablt: "a < b"
	                    have hxBb: "xB b < b \<and> {xB b <.. b} \<subseteq> ?X - A"
	                      by (rule bspec[OF hxB hb])
	                    have hxbb: "xB b < b"
	                      by (rule conjunct1[OF hxBb])
	                    have hbprop: "{xB b <.. b} \<subseteq> ?X - A"
	                      by (rule conjunct2[OF hxBb])
	                    have hzb1: "z \<le> a"
	                      using hzIa by simp
	                    have hzb2: "xB b < z"
	                      using hzIb by simp
	                    show "z \<in> {}"
	                    proof (cases "a \<le> xB b")
	                      case True
	                      have "z \<le> xB b"
	                        by (rule order_trans[OF hzb1 True])
	                      have "xB b < xB b"
	                        by (rule less_le_trans[OF hzb2 \<open>z \<le> xB b\<close>])
	                      thus ?thesis by simp
	                    next
	                      case False
	                      have hxba: "xB b < a"
	                        using False by simp
	                      have "a \<le> b"
	                        using hablt by simp
	                      have "a \<in> {xB b <.. b}"
	                        using hxba \<open>a \<le> b\<close> by simp
	                      hence "a \<in> ?X - A"
	                        by (rule subsetD[OF hbprop])
	                      have False using haA' \<open>a \<in> ?X - A\<close> by simp
	                      thus ?thesis by simp
	                    qed
	                  next
	                    assume hbalt: "b < a"
	                    have hyAa: "yA a < a \<and> {yA a <.. a} \<subseteq> ?X - B"
	                      by (rule bspec[OF hyA haA'])
	                    have hyya: "yA a < a"
	                      by (rule conjunct1[OF hyAa])
	                    have haprop: "{yA a <.. a} \<subseteq> ?X - B"
	                      by (rule conjunct2[OF hyAa])
	                    have hzb1: "z \<le> b"
	                      using hzIb by simp
	                    have hzb2: "yA a < z"
	                      using hzIa by simp
	                    show "z \<in> {}"
	                    proof (cases "b \<le> yA a")
	                      case True
	                      have "z \<le> yA a"
	                        by (rule order_trans[OF hzb1 True])
	                      have "yA a < yA a"
	                        by (rule less_le_trans[OF hzb2 \<open>z \<le> yA a\<close>])
	                      thus ?thesis by simp
	                    next
	                      case False
	                      have hyab: "yA a < b"
	                        using False by simp
	                      have "b \<le> a"
	                        using hbalt by simp
	                      have "b \<in> {yA a <.. a}"
	                        using hyab \<open>b \<le> a\<close> by simp
	                      hence "b \<in> ?X - B"
	                        by (rule subsetD[OF haprop])
	                      have False using hbB \<open>b \<in> ?X - B\<close> by simp
	                      thus ?thesis by simp
	                    qed
	                  qed
	                qed
	              qed
	              show "{} \<subseteq> U \<inter> V" by simp
	            qed

		            show ?thesis
		              apply (rule exI[where x=V])
		              apply (rule exI[where x=U])
		              using hUopen hVopen hB_sub hA_sub hUV_disj by (simp add: Int_commute)
		          next
	            case False
	            (* main case: a0 not in A and not in B *)
	            have ha0A: "a0 \<notin> A" using \<open>a0 \<notin> A\<close> .
	            have ha0B: "a0 \<notin> B" using False .

	            have hexA: "\<forall>a\<in>A. \<exists>x<a. {x <.. a} \<subseteq> ?X - B"
	            proof (intro ballI)
	              fix a assume haA: "a \<in> A"
	              have hne: "a \<noteq> a0"
	                using ha0A haA by blast
              have haB: "a \<notin> B"
              proof
                assume haB: "a \<in> B"
                have "a \<in> A \<inter> B" using haA haB by blast
                thus False using hdisj by blast
              qed
	              have hUopen: "?X - B \<in> ?T"
	                by (rule closedin_diff_open[OF hBcl])
	              have hnbd: "a \<in> ?X - B" using haB by simp
	              show "\<exists>x<a. {x <.. a} \<subseteq> ?X - B"
	                by (rule wellorder_open_refine_Ioc[OF ha0 hne hUopen hnbd])
	            qed
	            obtain xA where hxA: "\<forall>a\<in>A. xA a < a \<and> {xA a <.. a} \<subseteq> ?X - B"
	              using bchoice[OF hexA] by blast

	            have hexB: "\<forall>b\<in>B. \<exists>y<b. {y <.. b} \<subseteq> ?X - A"
	            proof (intro ballI)
	              fix b assume hbB: "b \<in> B"
              have hne: "b \<noteq> a0"
                using ha0B hbB by blast
              have hbA: "b \<notin> A"
              proof
                assume hbA: "b \<in> A"
                have "b \<in> A \<inter> B" using hbA hbB by blast
                thus False using hdisj by blast
              qed
	              have hUopen: "?X - A \<in> ?T"
	                by (rule closedin_diff_open[OF hAcl])
	              have hnbd: "b \<in> ?X - A" using hbA by simp
	              show "\<exists>y<b. {y <.. b} \<subseteq> ?X - A"
	                by (rule wellorder_open_refine_Ioc[OF ha0 hne hUopen hnbd])
	            qed
	            obtain yB where hyB: "\<forall>b\<in>B. yB b < b \<and> {yB b <.. b} \<subseteq> ?X - A"
	              using bchoice[OF hexB] by blast

	            define U where "U = (\<Union>a\<in>A. {xA a <.. a})"
	            define V where "V = (\<Union>b\<in>B. {yB b <.. b})"

            have hUopen: "U \<in> ?T"
            proof -
	              have hFam: "{{xA a <.. a} | a. a \<in> A} \<subseteq> ?T"
	              proof (rule subsetI)
	                fix W assume hW: "W \<in> {{xA a <.. a} | a. a \<in> A}"
	                then obtain a where haA: "a \<in> A" and hWeq: "W = {xA a <.. a}"
	                  by blast
	                have hxa: "xA a < a"
	                  using hxA haA by blast
	                have "{xA a <.. a} \<in> ?T"
	                  by (rule wellorder_Ioc_open_in_order_topology[OF hxa])
	                thus "W \<in> ?T"
	                  using hWeq by simp
	              qed
	              have hUnion: "(\<Union>{{xA a <.. a} | a. a \<in> A}) \<in> ?T"
	                by (rule union_T[OF hFam])
	              have hEq: "(\<Union>{{xA a <.. a} | a. a \<in> A}) = (\<Union>a\<in>A. {xA a <.. a})"
	                by blast
	              show ?thesis
	                unfolding U_def using hUnion hEq by simp
	            qed

            have hVopen: "V \<in> ?T"
            proof -
	              have hFam: "{{yB b <.. b} | b. b \<in> B} \<subseteq> ?T"
	              proof (rule subsetI)
	                fix W assume hW: "W \<in> {{yB b <.. b} | b. b \<in> B}"
	                then obtain b where hbB: "b \<in> B" and hWeq: "W = {yB b <.. b}"
	                  by blast
	                have hyb: "yB b < b"
	                  using hyB hbB by blast
	                have "{yB b <.. b} \<in> ?T"
	                  by (rule wellorder_Ioc_open_in_order_topology[OF hyb])
	                thus "W \<in> ?T"
	                  using hWeq by simp
	              qed
	              have hUnion: "(\<Union>{{yB b <.. b} | b. b \<in> B}) \<in> ?T"
	                by (rule union_T[OF hFam])
	              have hEq: "(\<Union>{{yB b <.. b} | b. b \<in> B}) = (\<Union>b\<in>B. {yB b <.. b})"
	                by blast
	              show ?thesis
	                unfolding V_def using hUnion hEq by simp
	            qed

            have hA_sub: "A \<subseteq> U"
            proof (rule subsetI)
	              fix a assume haA: "a \<in> A"
	              have hxa: "xA a < a"
	                using hxA haA by blast
	              have "a \<in> {xA a <.. a}"
	                using hxa by simp
	              thus "a \<in> U"
	                unfolding U_def using haA by blast
	            qed

            have hB_sub: "B \<subseteq> V"
            proof (rule subsetI)
	              fix b assume hbB: "b \<in> B"
	              have hyb: "yB b < b"
	                using hyB hbB by blast
	              have "b \<in> {yB b <.. b}"
	                using hyb by simp
	              thus "b \<in> V"
	                unfolding V_def using hbB by blast
	            qed

            have hUV_disj: "U \<inter> V = {}"
            proof (rule equalityI)
              show "U \<inter> V \<subseteq> {}"
              proof (rule subsetI)
	                fix z assume hz: "z \<in> U \<inter> V"
	                have hzU: "z \<in> U" and hzV: "z \<in> V" using hz by blast+
	                obtain a where haA: "a \<in> A" and hzIa: "z \<in> {xA a <.. a}"
	                  using hzU unfolding U_def by blast
	                obtain b where hbB: "b \<in> B" and hzIb: "z \<in> {yB b <.. b}"
	                  using hzV unfolding V_def by blast

                have haB: "a \<notin> B"
                proof
                  assume "a \<in> B"
                  have "a \<in> A \<inter> B" using haA \<open>a \<in> B\<close> by blast
                  thus False using hdisj by blast
                qed
                have hneab: "a \<noteq> b"
                  using haA haB hbB by blast
                have hcase: "a < b \<or> b < a"
                  using hneab neq_iff by blast

                show "z \<in> {}"
	                proof (rule disjE[OF hcase])
	                  assume hablt: "a < b"
	                  have hbprop: "{yB b <.. b} \<subseteq> ?X - A"
	                    using hyB hbB by blast
	                  have hzb1: "z \<le> a" using hzIa by simp
	                  have hzb2: "yB b < z" using hzIb by simp
                  show ?thesis
	                  proof (cases "a \<le> yB b")
	                    case True
	                    have "z \<le> yB b"
	                      by (rule order_trans[OF hzb1 True])
	                    have "yB b < yB b"
	                      by (rule less_le_trans[OF hzb2 \<open>z \<le> yB b\<close>])
	                    thus ?thesis by simp
	                  next
	                    case False
		                    have hyb_a: "yB b < a"
		                      using False by simp
	                    have "a \<le> b"
	                      using hablt by simp
		                    have "a \<in> {yB b <.. b}"
		                      using hyb_a \<open>a \<le> b\<close> by simp
		                    hence "a \<in> ?X - A"
		                      by (rule subsetD[OF hbprop])
		                    have False using haA \<open>a \<in> ?X - A\<close> by simp
		                    thus ?thesis by simp
		                  qed
		                next
		                  assume hbalt: "b < a"
		                  have hxAa: "xA a < a \<and> {xA a <.. a} \<subseteq> ?X - B"
		                    by (rule bspec[OF hxA haA])
		                  have haprop: "{xA a <.. a} \<subseteq> ?X - B"
		                    by (rule conjunct2[OF hxAa])
		                  have hxa: "xA a < a"
		                    by (rule conjunct1[OF hxAa])
		                  have hzb1: "z \<le> b" using hzIb by simp
		                  have hzb2: "xA a < z" using hzIa by simp
	                  show ?thesis
	                  proof (cases "b \<le> xA a")
	                    case True
	                    have "z \<le> xA a"
	                      by (rule order_trans[OF hzb1 True])
	                    have "xA a < xA a"
	                      by (rule less_le_trans[OF hzb2 \<open>z \<le> xA a\<close>])
	                    thus ?thesis by simp
	                  next
	                    case False
		                    have hxa_b: "xA a < b"
		                      using False by simp
	                    have "b \<le> a"
	                      using hbalt by simp
		                    have "b \<in> {xA a <.. a}"
		                      using hxa_b \<open>b \<le> a\<close> by simp
		                    hence "b \<in> ?X - B"
		                      by (rule subsetD[OF haprop])
		                    have False using hbB \<open>b \<in> ?X - B\<close> by simp
		                    thus ?thesis by simp
		                  qed
		                qed
              qed
              show "{} \<subseteq> U \<inter> V" by simp
            qed

	            show ?thesis
	              apply (rule exI[where x=U])
	              apply (rule exI[where x=V])
	              apply (intro conjI)
	                   apply (rule hUopen)
	                  apply (rule hVopen)
	                 apply (rule hA_sub)
	                apply (rule hB_sub)
	              apply (rule hUV_disj)
	              done
	          qed
	        qed
	      qed
	    qed
	  qed
qed

section \<open>\<S>33 The Urysohn Lemma\<close>

definition top1_closed_interval :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "top1_closed_interval a b = {t. a \<le> t \<and> t \<le> b}"

definition top1_closed_interval_topology :: "real \<Rightarrow> real \<Rightarrow> real set set" where
  "top1_closed_interval_topology a b =
     subspace_topology UNIV order_topology_on_UNIV (top1_closed_interval a b)"

(** Helper for the Urysohn lemma (Step 1 in top1.tex): start with the open set
    U\<^sub>1 = X - B and shrink an open neighborhood of A so that its closure stays inside U\<^sub>1. **)
lemma normal_urysohn_initial_step:
  assumes hN: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hB: "closedin_on X TX B"
  assumes hdisj: "A \<inter> B = {}"
  shows "\<exists>U0. U0 \<in> TX \<and> U0 \<subseteq> X \<and> A \<subseteq> U0 \<and> closure_on X TX U0 \<subseteq> (X - B)"
proof -
  have hBX: "B \<subseteq> X" by (rule closedin_sub[OF hB])
  have hU1_open: "X - B \<in> TX" by (rule closedin_diff_open[OF hB])
  have hU1_subX: "X - B \<subseteq> X" by (rule Diff_subset)

  have hA_sub_U1: "A \<subseteq> X - B"
  proof (rule subsetI)
    fix x assume hxA: "x \<in> A"
    have hxX: "x \<in> X" by (rule subsetD[OF closedin_sub[OF hA] hxA])
    have hxnotB: "x \<notin> B"
    proof
      assume hxB: "x \<in> B"
      have "x \<in> A \<inter> B"
        by (rule IntI[OF hxA hxB])
      thus False using hdisj by simp
    qed
    show "x \<in> X - B" using hxX hxnotB by simp
  qed

  have hexU0:
    "\<exists>U0. U0 \<in> TX \<and> U0 \<subseteq> X \<and> A \<subseteq> U0 \<and> closure_on X TX U0 \<subseteq> (X - B)"
    by (rule normal_refine_closed_into_open[OF hN hA hU1_open hU1_subX hA_sub_U1])
  obtain U0 where hU0:
      "U0 \<in> TX \<and> U0 \<subseteq> X \<and> A \<subseteq> U0 \<and> closure_on X TX U0 \<subseteq> (X - B)"
    using hexU0 by (elim exE)
  show ?thesis by (rule exI[where x=U0], rule hU0)
qed

(** Dyadic rationals and the standard recursive open-set construction used in the Urysohn lemma. **)
definition top1_dyadic :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "top1_dyadic n k = (real k) / (2 ^ n)"

fun top1_urysohn_U ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set" where
  "top1_urysohn_U X TX U0 U1 0 k =
     (if k = 0 then U0 else if k = 1 then U1 else {})"
| "top1_urysohn_U X TX U0 U1 (Suc n) k =
     (if even k then top1_urysohn_U X TX U0 U1 n (k div 2)
      else (SOME W.
              W \<in> TX \<and> W \<subseteq> X
              \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 n (k div 2)) \<subseteq> W
              \<and> closure_on X TX W \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div 2))))"

lemma top1_urysohn_U_even:
  shows "top1_urysohn_U X TX U0 U1 (Suc n) (2 * k) = top1_urysohn_U X TX U0 U1 n k"
  by simp

lemma top1_urysohn_U_pow2_scale:
  shows "top1_urysohn_U X TX U0 U1 (n + m) (k * ((2::nat) ^ m)) = top1_urysohn_U X TX U0 U1 n k"
proof (induction m arbitrary: n k)
  case 0
  show ?case by simp
next
  case (Suc m)
  have "top1_urysohn_U X TX U0 U1 (n + Suc m) (k * ((2::nat) ^ Suc m))
        = top1_urysohn_U X TX U0 U1 (Suc (n + m)) (2 * (k * (2 ^ m)))"
    by (simp add: power_Suc mult.assoc mult.left_commute mult.commute)
  also have "... = top1_urysohn_U X TX U0 U1 (n + m) (k * (2 ^ m))"
    by (simp add: top1_urysohn_U_even)
  also have "... = top1_urysohn_U X TX U0 U1 n k"
    by (rule Suc.IH)
  finally show ?case .
qed

lemma top1_urysohn_U_endpoints:
  shows "top1_urysohn_U X TX U0 U1 n 0 = U0"
    and "top1_urysohn_U X TX U0 U1 n ((2::nat) ^ n) = U1"
proof -
  show "top1_urysohn_U X TX U0 U1 n 0 = U0"
  proof (induction n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    have "top1_urysohn_U X TX U0 U1 (Suc n) 0 = top1_urysohn_U X TX U0 U1 n (0 div 2)"
      by simp
    thus ?case using Suc.IH by simp
  qed
  show "top1_urysohn_U X TX U0 U1 n ((2::nat) ^ n) = U1"
  proof (induction n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    have "even ((2::nat) ^ Suc n)" by simp
    have "top1_urysohn_U X TX U0 U1 (Suc n) ((2::nat) ^ Suc n)
          = top1_urysohn_U X TX U0 U1 n (((2::nat) ^ Suc n) div 2)"
      using \<open>even ((2::nat) ^ Suc n)\<close> by simp
    also have "(((2::nat) ^ Suc n) div 2) = ((2::nat) ^ n)"
      by simp
    also have "top1_urysohn_U X TX U0 U1 n ((2::nat) ^ n) = U1"
      by (rule Suc.IH)
    finally show ?case .
  qed
qed

lemma top1_urysohn_U_odd_step_properties:
  assumes hN: "top1_normal_on X TX"
  assumes hkodd: "odd k"
  assumes hL: "top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<in> TX"
              "top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<subseteq> X"
  assumes hR: "top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat))) \<in> TX"
              "top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat))) \<subseteq> X"
  assumes hcl: "closure_on X TX (top1_urysohn_U X TX U0 U1 n (k div (2::nat)))
                  \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"
  shows "top1_urysohn_U X TX U0 U1 (Suc n) k \<in> TX
          \<and> top1_urysohn_U X TX U0 U1 (Suc n) k \<subseteq> X
          \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 n (k div (2::nat)))
                \<subseteq> top1_urysohn_U X TX U0 U1 (Suc n) k
          \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 (Suc n) k)
                \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"
proof -
  let ?UL = "top1_urysohn_U X TX U0 U1 n (k div (2::nat))"
  let ?UR = "top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"

  have hex:
    "\<exists>W. W \<in> TX \<and> W \<subseteq> X \<and> closure_on X TX ?UL \<subseteq> W \<and> closure_on X TX W \<subseteq> ?UR"
    apply (rule normal_insert_open_between[where U="?UL" and V="?UR"])
          apply (rule hN)
         apply (rule hL(1))
        apply (rule hL(2))
       apply (rule hR(1))
      apply (rule hR(2))
     apply (rule hcl)
    done

  have hSome:
    "(SOME W. W \<in> TX \<and> W \<subseteq> X \<and> closure_on X TX ?UL \<subseteq> W \<and> closure_on X TX W \<subseteq> ?UR)
        \<in> TX
     \<and> (SOME W. W \<in> TX \<and> W \<subseteq> X \<and> closure_on X TX ?UL \<subseteq> W \<and> closure_on X TX W \<subseteq> ?UR)
        \<subseteq> X
     \<and> closure_on X TX ?UL
        \<subseteq> (SOME W. W \<in> TX \<and> W \<subseteq> X \<and> closure_on X TX ?UL \<subseteq> W \<and> closure_on X TX W \<subseteq> ?UR)
     \<and> closure_on X TX
          (SOME W. W \<in> TX \<and> W \<subseteq> X \<and> closure_on X TX ?UL \<subseteq> W \<and> closure_on X TX W \<subseteq> ?UR)
        \<subseteq> ?UR"
    using someI_ex[OF hex] by simp

  have hEq:
    "top1_urysohn_U X TX U0 U1 (Suc n) k =
       (SOME W. W \<in> TX \<and> W \<subseteq> X \<and> closure_on X TX ?UL \<subseteq> W \<and> closure_on X TX W \<subseteq> ?UR)"
    using hkodd by simp

  show ?thesis
    unfolding hEq
    using hSome
    by simp
qed

lemma top1_urysohn_U_basic_properties:
  assumes hN: "top1_normal_on X TX"
  assumes hU0: "U0 \<in> TX" "U0 \<subseteq> X"
  assumes hU1: "U1 \<in> TX" "U1 \<subseteq> X"
  assumes hcl01: "closure_on X TX U0 \<subseteq> U1"
  shows "(\<forall>n k. k \<le> ((2::nat) ^ n) \<longrightarrow>
            (top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X))
     \<and> (\<forall>n k. k < ((2::nat) ^ n) \<longrightarrow>
            closure_on X TX (top1_urysohn_U X TX U0 U1 n k) \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k))"
proof -
  have hP:
    "(\<forall>k\<le>(2::nat) ^ n.
        top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X)
     \<and> (\<forall>k<(2::nat) ^ n.
          closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
            \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k))"
    for n
  proof (induction n)
    case 0
    have hGood0:
      "\<forall>k\<le>(2::nat) ^ 0. top1_urysohn_U X TX U0 U1 0 k \<in> TX \<and> top1_urysohn_U X TX U0 U1 0 k \<subseteq> X"
    proof (intro allI impI)
      fix k assume hk: "k \<le> (2::nat) ^ 0"
      have hk': "k = 0 \<or> k = Suc 0"
      proof (cases k)
        case 0
        show ?thesis
          using 0 by simp
      next
        case (Suc m)
        have hm0: "m = 0"
        proof -
          have "Suc m \<le> (2::nat) ^ 0"
            using hk by (simp add: Suc)
          hence "Suc m \<le> (1::nat)"
            by simp
          hence "m = 0"
            by simp
          thus ?thesis .
        qed
        show ?thesis
          using Suc hm0 by simp
      qed
      then show "top1_urysohn_U X TX U0 U1 0 k \<in> TX \<and> top1_urysohn_U X TX U0 U1 0 k \<subseteq> X"
      proof
        assume h0: "k = 0"
        show ?thesis
          using hU0 by (simp add: h0)
      next
        assume h1: "k = Suc 0"
        show ?thesis
          using hU1 by (simp add: h1)
      qed
    qed

    have hStep0:
      "\<forall>k<(2::nat) ^ 0. closure_on X TX (top1_urysohn_U X TX U0 U1 0 k)
              \<subseteq> top1_urysohn_U X TX U0 U1 0 (Suc k)"
    proof (intro allI impI)
      fix k assume hk: "k < (2::nat) ^ 0"
      have h0: "k = 0"
        using hk by simp
      show "closure_on X TX (top1_urysohn_U X TX U0 U1 0 k)
              \<subseteq> top1_urysohn_U X TX U0 U1 0 (Suc k)"
        using hcl01 by (simp add: h0)
    qed

    show ?case
      apply (intro conjI)
       apply (rule hGood0)
      apply (rule hStep0)
      done
  next
    case (Suc n)
    have good_n:
      "\<forall>k\<le>(2::nat) ^ n. top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X"
      using Suc.IH by (rule conjunct1)
    have step_n:
      "\<forall>k<(2::nat) ^ n. closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
              \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k)"
      using Suc.IH by (rule conjunct2)

    have good_Suc:
      "\<forall>k\<le>(2::nat) ^ Suc n. top1_urysohn_U X TX U0 U1 (Suc n) k \<in> TX
            \<and> top1_urysohn_U X TX U0 U1 (Suc n) k \<subseteq> X"
    proof (intro allI impI)
      fix k assume hk: "k \<le> (2::nat) ^ Suc n"
      show "top1_urysohn_U X TX U0 U1 (Suc n) k \<in> TX
              \<and> top1_urysohn_U X TX U0 U1 (Suc n) k \<subseteq> X"
      proof (cases "even k")
        case True
        have hkdiv: "k div (2::nat) \<le> (2::nat) ^ n"
        proof -
          have "k div (2::nat) \<le> ((2::nat) ^ Suc n) div (2::nat)"
            by (rule div_le_mono[OF hk])
          also have "((2::nat) ^ Suc n) div (2::nat) = (2::nat) ^ n"
            by simp
          finally show ?thesis .
        qed
        have hL: "top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<in> TX
                    \<and> top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<subseteq> X"
          by (rule good_n[rule_format, OF hkdiv])
        show ?thesis
          using True hL by simp
      next
        case False
        have hkodd: "odd k"
          using False by simp

        have hkdiv_lt: "k div (2::nat) < (2::nat) ^ n"
        proof -
          obtain m where hk2: "k = 2 * m + 1"
            using hkodd by (rule oddE)

          have hm_lt: "m < (2::nat) ^ n"
          proof -
            have h2m_lt_k: "2 * m < k"
              unfolding hk2 by simp
            have h2m_lt: "2 * m < (2::nat) ^ Suc n"
              by (rule less_le_trans[OF h2m_lt_k hk])
            have h2m_lt': "2 * m < 2 * ((2::nat) ^ n)"
              using h2m_lt by (simp add: power_Suc mult.commute mult.assoc)
            show ?thesis
              using h2m_lt' by (simp add: mult_less_cancel1)
          qed

          show ?thesis
            unfolding hk2
            using hm_lt
            by simp
        qed
        have hkdiv_le: "k div (2::nat) \<le> (2::nat) ^ n"
          by (rule less_imp_le[OF hkdiv_lt])
        have hkdiv_suc_le: "Suc (k div (2::nat)) \<le> (2::nat) ^ n"
          by (rule Suc_leI[OF hkdiv_lt])

        have hL: "top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<in> TX
                    \<and> top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<subseteq> X"
          by (rule good_n[rule_format, OF hkdiv_le])
        have hR: "top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat))) \<in> TX
                    \<and> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat))) \<subseteq> X"
          by (rule good_n[rule_format, OF hkdiv_suc_le])
        have hcl:
          "closure_on X TX (top1_urysohn_U X TX U0 U1 n (k div (2::nat)))
             \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"
          by (rule step_n[rule_format, OF hkdiv_lt])

        have hodd_props:
          "top1_urysohn_U X TX U0 U1 (Suc n) k \<in> TX
            \<and> top1_urysohn_U X TX U0 U1 (Suc n) k \<subseteq> X"
        proof -
          have hall:
            "top1_urysohn_U X TX U0 U1 (Suc n) k \<in> TX
              \<and> top1_urysohn_U X TX U0 U1 (Suc n) k \<subseteq> X
              \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 n (k div (2::nat)))
                    \<subseteq> top1_urysohn_U X TX U0 U1 (Suc n) k
              \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 (Suc n) k)
                    \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"
            by (rule top1_urysohn_U_odd_step_properties[OF hN hkodd
                  conjunct1[OF hL] conjunct2[OF hL]
                  conjunct1[OF hR] conjunct2[OF hR] hcl])
          show ?thesis
            apply (intro conjI)
             apply (rule conjunct1[OF hall])
            apply (rule conjunct1[OF conjunct2[OF hall]])
            done
        qed
        show ?thesis
          by (rule hodd_props)
      qed
    qed

    have step_Suc:
      "\<forall>k<(2::nat) ^ Suc n. closure_on X TX (top1_urysohn_U X TX U0 U1 (Suc n) k)
              \<subseteq> top1_urysohn_U X TX U0 U1 (Suc n) (Suc k)"
    proof (intro allI impI)
      fix k assume hk: "k < (2::nat) ^ Suc n"
      show "closure_on X TX (top1_urysohn_U X TX U0 U1 (Suc n) k)
              \<subseteq> top1_urysohn_U X TX U0 U1 (Suc n) (Suc k)"
      proof (cases "even k")
        case True
        obtain m where hk2: "k = 2 * m"
          using True by (rule evenE)

        have hm_lt: "m < (2::nat) ^ n"
        proof -
          have hk': "2 * m < (2::nat) ^ Suc n"
            using hk unfolding hk2 .
          have hk'': "2 * m < 2 * ((2::nat) ^ n)"
            using hk' by (simp add: power_Suc mult.commute mult.assoc)
          show ?thesis
            using hk'' by (simp add: mult_less_cancel1)
        qed
        have hm_le: "m \<le> (2::nat) ^ n"
          by (rule less_imp_le[OF hm_lt])
        have hSm_le: "Suc m \<le> (2::nat) ^ n"
          by (rule Suc_leI[OF hm_lt])

        have hcl_m:
          "closure_on X TX (top1_urysohn_U X TX U0 U1 n m)
             \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc m)"
          by (rule step_n[rule_format, OF hm_lt])

        have hLm: "top1_urysohn_U X TX U0 U1 n m \<in> TX \<and> top1_urysohn_U X TX U0 U1 n m \<subseteq> X"
          by (rule good_n[rule_format, OF hm_le])
        have hRm: "top1_urysohn_U X TX U0 U1 n (Suc m) \<in> TX \<and> top1_urysohn_U X TX U0 U1 n (Suc m) \<subseteq> X"
          by (rule good_n[rule_format, OF hSm_le])

        have hOdd1:
          "closure_on X TX (top1_urysohn_U X TX U0 U1 n m)
            \<subseteq> top1_urysohn_U X TX U0 U1 (Suc n) (Suc k)"
        proof -
          have hk1odd: "odd (Suc k)"
            using True by simp
          have hk1eq: "Suc k = Suc (2 * m)"
            using hk2 by simp
          have hk1eq': "Suc k = 2 * m + 1"
            using hk1eq by simp

          have hDiv: "(Suc k) div (2::nat) = m"
            using hk1eq' by simp

          have hOddAll:
            "top1_urysohn_U X TX U0 U1 (Suc n) (Suc k) \<in> TX
              \<and> top1_urysohn_U X TX U0 U1 (Suc n) (Suc k) \<subseteq> X
              \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 n ((Suc k) div (2::nat)))
                    \<subseteq> top1_urysohn_U X TX U0 U1 (Suc n) (Suc k)
              \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 (Suc n) (Suc k))
                    \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc ((Suc k) div (2::nat)))"
          proof -
            have hL1_open: "top1_urysohn_U X TX U0 U1 n ((Suc k) div (2::nat)) \<in> TX"
              unfolding hDiv by (rule conjunct1[OF hLm])
            have hL1_subX: "top1_urysohn_U X TX U0 U1 n ((Suc k) div (2::nat)) \<subseteq> X"
              unfolding hDiv by (rule conjunct2[OF hLm])
            have hR1_open: "top1_urysohn_U X TX U0 U1 n (Suc ((Suc k) div (2::nat))) \<in> TX"
              unfolding hDiv by (rule conjunct1[OF hRm])
            have hR1_subX: "top1_urysohn_U X TX U0 U1 n (Suc ((Suc k) div (2::nat))) \<subseteq> X"
              unfolding hDiv by (rule conjunct2[OF hRm])
            have hcl1:
              "closure_on X TX (top1_urysohn_U X TX U0 U1 n ((Suc k) div (2::nat)))
                 \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc ((Suc k) div (2::nat)))"
              unfolding hDiv
              using hcl_m
              by simp
            show ?thesis
              using top1_urysohn_U_odd_step_properties[OF hN hk1odd hL1_open hL1_subX hR1_open hR1_subX hcl1] .
          qed

          show ?thesis
            using hOddAll
            unfolding hDiv
            by simp
        qed

        have hEqk: "top1_urysohn_U X TX U0 U1 (Suc n) k = top1_urysohn_U X TX U0 U1 n m"
          using True unfolding hk2 by simp
        show ?thesis
          unfolding hEqk using hOdd1 .
      next
        case False
        obtain m where hk2: "k = 2 * m + 1"
          using False by (rule oddE)
        have hkodd: "odd k"
          using False by simp

        have hm_lt: "m < (2::nat) ^ n"
        proof -
          have h2m_lt: "2 * m < (2::nat) ^ Suc n"
          proof -
            have "2 * m < 2 * m + 1"
              by simp
            moreover have "2 * m + 1 < (2::nat) ^ Suc n"
              using hk unfolding hk2 .
            ultimately show ?thesis
              by (rule less_trans)
          qed
          have h2m_lt': "2 * m < 2 * ((2::nat) ^ n)"
            using h2m_lt by (simp add: power_Suc mult.commute mult.assoc)
          show ?thesis
            using h2m_lt' by (simp add: mult_less_cancel1)
        qed
        have hm_le: "m \<le> (2::nat) ^ n"
          by (rule less_imp_le[OF hm_lt])
        have hSm_le: "Suc m \<le> (2::nat) ^ n"
          by (rule Suc_leI[OF hm_lt])

        have hL: "top1_urysohn_U X TX U0 U1 n m \<in> TX \<and> top1_urysohn_U X TX U0 U1 n m \<subseteq> X"
          by (rule good_n[rule_format, OF hm_le])
        have hR: "top1_urysohn_U X TX U0 U1 n (Suc m) \<in> TX \<and> top1_urysohn_U X TX U0 U1 n (Suc m) \<subseteq> X"
          by (rule good_n[rule_format, OF hSm_le])
        have hcl_m:
          "closure_on X TX (top1_urysohn_U X TX U0 U1 n m)
             \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc m)"
          by (rule step_n[rule_format, OF hm_lt])

        have hDiv: "k div (2::nat) = m"
          unfolding hk2 by simp

        have hOddProps:
          "closure_on X TX (top1_urysohn_U X TX U0 U1 (Suc n) k)
              \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"
        proof -
          have hL1_open: "top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<in> TX"
            unfolding hDiv by (rule conjunct1[OF hL])
          have hL1_subX: "top1_urysohn_U X TX U0 U1 n (k div (2::nat)) \<subseteq> X"
            unfolding hDiv by (rule conjunct2[OF hL])
          have hR1_open: "top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat))) \<in> TX"
            unfolding hDiv by (rule conjunct1[OF hR])
          have hR1_subX: "top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat))) \<subseteq> X"
            unfolding hDiv by (rule conjunct2[OF hR])
          have hcl1:
            "closure_on X TX (top1_urysohn_U X TX U0 U1 n (k div (2::nat)))
               \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"
            unfolding hDiv
            using hcl_m
            by simp
          have hOddAll:
            "top1_urysohn_U X TX U0 U1 (Suc n) k \<in> TX
              \<and> top1_urysohn_U X TX U0 U1 (Suc n) k \<subseteq> X
              \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 n (k div (2::nat)))
                    \<subseteq> top1_urysohn_U X TX U0 U1 (Suc n) k
              \<and> closure_on X TX (top1_urysohn_U X TX U0 U1 (Suc n) k)
                    \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))"
            using top1_urysohn_U_odd_step_properties[OF hN hkodd hL1_open hL1_subX hR1_open hR1_subX hcl1] .
          show ?thesis
            using hOddAll by simp
        qed

        have hEqR: "top1_urysohn_U X TX U0 U1 n (Suc (k div (2::nat)))
                      = top1_urysohn_U X TX U0 U1 n (Suc m)"
          unfolding hDiv by simp
        have hEqk1: "top1_urysohn_U X TX U0 U1 (Suc n) (Suc k)
                      = top1_urysohn_U X TX U0 U1 n (Suc m)"
          unfolding hk2 by simp

        show ?thesis
          using hOddProps
          unfolding hEqR hEqk1
          by simp
      qed
    qed

    show ?case
      apply (intro conjI)
       apply (rule good_Suc)
      apply (rule step_Suc)
      done
  qed

  have hGood:
    "\<forall>n k. k \<le> (2::nat) ^ n \<longrightarrow>
       top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X"
  proof (intro allI impI)
    fix n k assume hk: "k \<le> (2::nat) ^ n"
    have hGood_n:
      "\<forall>k\<le>(2::nat) ^ n. top1_urysohn_U X TX U0 U1 n k \<in> TX
            \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X"
      using hP[of n] by (rule conjunct1)
    have hImp:
      "k \<le> (2::nat) ^ n \<longrightarrow>
        top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X"
      using hGood_n by (rule spec[where x=k])
    show "top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X"
      by (rule mp[OF hImp hk])
  qed

  have hStep:
    "\<forall>n k. k < (2::nat) ^ n \<longrightarrow>
       closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
         \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k)"
  proof (intro allI impI)
    fix n k assume hk: "k < (2::nat) ^ n"
    have hStep_n:
      "\<forall>k<(2::nat) ^ n. closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
            \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k)"
      using hP[of n] by (rule conjunct2)
    have hImp:
      "k < (2::nat) ^ n \<longrightarrow>
        closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
          \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k)"
      using hStep_n by (rule spec[where x=k])
    show "closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
            \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k)"
      by (rule mp[OF hImp hk])
  qed

  show ?thesis
    apply (intro conjI)
     apply (rule hGood)
    apply (rule hStep)
    done
qed

(** Monotonicity facts for the dyadic family of open sets (needed in the Urysohn construction). **)

lemma top1_dyadic_pow2_scale:
  shows "top1_dyadic (n + m) (k * ((2::nat) ^ m)) = top1_dyadic n k"
  unfolding top1_dyadic_def
  by (simp add: power_add field_simps)

lemma top1_dyadic_lt_same_denom_iff:
  shows "top1_dyadic n k < top1_dyadic n l \<longleftrightarrow> k < l"
proof -
  have hpos: "(0::real) < (2::nat) ^ n"
    by simp
  show ?thesis
    unfolding top1_dyadic_def
    by (simp add: divide_less_cancel hpos)
qed

lemma exists_pow2_inv_lt:
  fixes eps :: real
  assumes heps: "0 < eps"
  shows "\<exists>n::nat. (1::real) / ((2::real) ^ n) < eps"
proof -
  obtain N :: nat where hN: "1 / eps < real N"
    using heps reals_Archimedean2 by blast
  have hN2: "real N < (2::real) ^ N"
    by (simp add: of_nat_less_two_power)
  have hlt: "1 / eps < (2::real) ^ N"
    by (rule less_trans[OF hN hN2])
  have hpos2: "(0::real) < (2::real) ^ N"
    by simp
  have "1 < eps * ((2::real) ^ N)"
    using hlt heps
    by (simp add: field_simps)
  hence "1 / ((2::real) ^ N) < eps"
    using hpos2
    by (simp add: field_simps)
  thus ?thesis
    by (rule exI[where x=N])
qed

lemma exists_top1_dyadic_between_01:
  fixes c d :: real
  assumes hc: "0 \<le> c"
  assumes hcd: "c < d"
  assumes hd: "d \<le> 1"
  shows "\<exists>n k. k \<le> (2::nat) ^ n \<and> c < top1_dyadic n k \<and> top1_dyadic n k < d"
proof -
  have heps: "0 < d - c"
    using hcd by simp
  obtain n :: nat where hn: "1 / ((2::real) ^ n) < d - c"
    using exists_pow2_inv_lt[OF heps] by blast

  let ?x = "c * ((2::real) ^ n)"
  let ?z = "\<lfloor>?x\<rfloor>"
  let ?m = "?z + 1"
  let ?k = "nat ?m"

  have hx_nonneg: "0 \<le> ?x"
    using hc by simp
  have hz_nonneg: "0 \<le> ?z"
    using hx_nonneg by (simp add: zero_le_floor)
  have hm_pos: "0 < ?m"
    using hz_nonneg by simp
  have hintk: "int ?k = ?m"
  proof -
    have hm_nonneg: "0 \<le> ?m"
      using hm_pos by simp
    show ?thesis
      by (simp add: hm_nonneg)
  qed
  have hreal_k: "real ?k = of_int ?m"
  proof -
    have "real ?k = of_int (int ?k)"
      by simp
    also have "... = of_int ?m"
      by (simp only: hintk)
    finally show ?thesis .
  qed

  have hlt1: "?x < of_int ?m"
    by (simp add: floor_correct)
  have hgt_c: "c < (of_int ?m) / ((2::real) ^ n)"
  proof -
    have hpos: "(0::real) < (2::real) ^ n"
      by simp
    have hdiv: "?x / ((2::real) ^ n) = c"
      by (simp add: field_simps)
    have "?x / ((2::real) ^ n) < (of_int ?m) / ((2::real) ^ n)"
      by (rule divide_strict_right_mono[OF hlt1 hpos])
    thus ?thesis
      by (simp add: hdiv)
  qed

  have hle1: "of_int ?m \<le> ?x + 1"
    by (simp add: of_int_floor_le)
  have hlt_d: "(of_int ?m) / ((2::real) ^ n) < d"
  proof -
    have hpos: "(0::real) < (2::real) ^ n"
      by simp
    have "(of_int ?m) / ((2::real) ^ n) \<le> (?x + 1) / ((2::real) ^ n)"
      using hle1 hpos by (simp add: divide_right_mono)
    also have "... = c + 1 / ((2::real) ^ n)"
      by (simp add: field_simps)
    also have "... < d"
    proof -
      have "1 / ((2::real) ^ n) < d - c"
        by (rule hn)
      thus ?thesis
        by linarith
    qed
    finally show ?thesis .
  qed

  have hk_le: "?k \<le> (2::nat) ^ n"
  proof -
    have hlt1': "real ?k / ((2::real) ^ n) < d"
      using hlt_d hreal_k by simp
    have hlt1'': "real ?k / ((2::real) ^ n) < 1"
      using hlt1' hd by (rule less_le_trans)
    have hpos: "(0::real) < (2::real) ^ n"
      by simp
    have "real ?k < (2::real) ^ n"
      using hlt1'' hpos by (simp add: divide_less_eq)
    hence "?k < (2::nat) ^ n"
      by simp
    thus ?thesis
      by (rule less_imp_le)
  qed

  have hdyad_eq: "top1_dyadic n ?k = (of_int ?m) / ((2::real) ^ n)"
    by (simp add: top1_dyadic_def hreal_k)
  have hdyad_gt: "c < top1_dyadic n ?k"
    using hgt_c by (simp add: hdyad_eq)
  have hdyad_lt: "top1_dyadic n ?k < d"
    using hlt_d by (simp add: hdyad_eq)

  show ?thesis
    apply (rule exI[where x=n])
    apply (rule exI[where x="nat (?z + 1)"])
    apply (intro conjI)
      apply (rule hk_le)
     apply (rule hdyad_gt)
    apply (rule hdyad_lt)
    done
qed

lemma top1_urysohn_U_mono_same_level:
  assumes hN: "top1_normal_on X TX"
  assumes hU0: "U0 \<in> TX" "U0 \<subseteq> X"
  assumes hU1: "U1 \<in> TX" "U1 \<subseteq> X"
  assumes hcl01: "closure_on X TX U0 \<subseteq> U1"
  assumes hk: "k \<le> l"
  assumes hl: "l \<le> (2::nat) ^ n"
  shows "top1_urysohn_U X TX U0 U1 n k \<subseteq> top1_urysohn_U X TX U0 U1 n l"
proof -
  have hstep:
    "\<forall>j<((2::nat) ^ n).
      closure_on X TX (top1_urysohn_U X TX U0 U1 n j)
        \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc j)"
  proof -
    have hBoth:
      "(\<forall>n k. k \<le> ((2::nat) ^ n) \<longrightarrow>
            (top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X))
       \<and> (\<forall>n k. k < ((2::nat) ^ n) \<longrightarrow>
            closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
              \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k))"
      by (rule top1_urysohn_U_basic_properties[OF hN hU0 hU1 hcl01])
    show ?thesis
      using hBoth by blast
  qed

  have hsucc:
    "\<And>j. j < (2::nat) ^ n \<Longrightarrow>
      top1_urysohn_U X TX U0 U1 n j \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc j)"
  proof -
    fix j assume hj: "j < (2::nat) ^ n"
    have "top1_urysohn_U X TX U0 U1 n j \<subseteq>
            closure_on X TX (top1_urysohn_U X TX U0 U1 n j)"
      by (rule subset_closure_on)
    also have "... \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc j)"
      by (rule hstep[rule_format, OF hj])
    finally show "top1_urysohn_U X TX U0 U1 n j \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc j)" .
  qed

  have hmono:
    "\<And>l0 k0. k0 \<le> l0 \<Longrightarrow> l0 \<le> (2::nat) ^ n \<Longrightarrow>
      top1_urysohn_U X TX U0 U1 n k0 \<subseteq> top1_urysohn_U X TX U0 U1 n l0"
  proof -
    fix l0 k0 :: nat
    assume hk0: "k0 \<le> l0"
    assume hl0: "l0 \<le> (2::nat) ^ n"
    show "top1_urysohn_U X TX U0 U1 n k0 \<subseteq> top1_urysohn_U X TX U0 U1 n l0"
      using hk0 hl0
    proof (induction l0 arbitrary: k0)
      case 0
      have hk0': "k0 = 0"
        using 0(1) by simp
      show ?case
        unfolding hk0' by simp
    next
      case (Suc l0)
      show ?case
      proof (cases "k0 = Suc l0")
        case True
        show ?thesis
          unfolding True by simp
      next
        case False
        have hk0': "k0 \<le> l0"
          using Suc.prems False by simp
        have hl0': "l0 \<le> (2::nat) ^ n"
          using Suc.prems by simp
        have IH: "top1_urysohn_U X TX U0 U1 n k0 \<subseteq> top1_urysohn_U X TX U0 U1 n l0"
          by (rule Suc.IH[OF hk0' hl0'])
        have hl0lt: "l0 < (2::nat) ^ n"
          using Suc.prems by simp
        have hstep': "top1_urysohn_U X TX U0 U1 n l0 \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc l0)"
          by (rule hsucc[OF hl0lt])
        show ?thesis
          by (rule subset_trans[OF IH hstep'])
      qed
    qed
  qed

  show ?thesis
    by (rule hmono[OF hk hl])
qed

lemma top1_urysohn_U_closure_mono_same_level:
  assumes hN: "top1_normal_on X TX"
  assumes hU0: "U0 \<in> TX" "U0 \<subseteq> X"
  assumes hU1: "U1 \<in> TX" "U1 \<subseteq> X"
  assumes hcl01: "closure_on X TX U0 \<subseteq> U1"
  assumes hk: "k < l"
  assumes hl: "l \<le> (2::nat) ^ n"
  shows "closure_on X TX (top1_urysohn_U X TX U0 U1 n k) \<subseteq> top1_urysohn_U X TX U0 U1 n l"
proof -
  have hBoth:
    "(\<forall>n k. k \<le> ((2::nat) ^ n) \<longrightarrow>
          (top1_urysohn_U X TX U0 U1 n k \<in> TX \<and> top1_urysohn_U X TX U0 U1 n k \<subseteq> X))
     \<and> (\<forall>n k. k < ((2::nat) ^ n) \<longrightarrow>
          closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
            \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k))"
    by (rule top1_urysohn_U_basic_properties[OF hN hU0 hU1 hcl01])
  have hstep:
    "\<forall>j<((2::nat) ^ n).
      closure_on X TX (top1_urysohn_U X TX U0 U1 n j)
        \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc j)"
    using hBoth by blast

  have hk': "k < (2::nat) ^ n"
    using hk hl by (rule less_le_trans)
  have hcl_succ:
    "closure_on X TX (top1_urysohn_U X TX U0 U1 n k)
        \<subseteq> top1_urysohn_U X TX U0 U1 n (Suc k)"
    by (rule hstep[rule_format, OF hk'])

  have hmono:
    "top1_urysohn_U X TX U0 U1 n (Suc k) \<subseteq> top1_urysohn_U X TX U0 U1 n l"
  proof -
    have hk_suc: "Suc k \<le> l"
      using hk by simp
    show ?thesis
      by (rule top1_urysohn_U_mono_same_level[OF hN hU0 hU1 hcl01 hk_suc hl])
  qed

  show ?thesis
    by (rule subset_trans[OF hcl_succ hmono])
qed

lemma top1_urysohn_U_closure_mono_dyadic:
  assumes hN: "top1_normal_on X TX"
  assumes hU0: "U0 \<in> TX" "U0 \<subseteq> X"
  assumes hU1: "U1 \<in> TX" "U1 \<subseteq> X"
  assumes hcl01: "closure_on X TX U0 \<subseteq> U1"
  assumes hk1: "k1 \<le> (2::nat) ^ n1"
  assumes hk2: "k2 \<le> (2::nat) ^ n2"
  assumes hlt: "top1_dyadic n1 k1 < top1_dyadic n2 k2"
  shows "closure_on X TX (top1_urysohn_U X TX U0 U1 n1 k1) \<subseteq> top1_urysohn_U X TX U0 U1 n2 k2"
proof -
  let ?m = "n1 + n2"
  let ?k1 = "k1 * ((2::nat) ^ n2)"
  let ?k2 = "k2 * ((2::nat) ^ n1)"

  have hk2m: "?k2 \<le> (2::nat) ^ ?m"
    using hk2 by (simp add: power_add mult.assoc)

  have hk1k2: "?k1 < ?k2"
  proof -
    have hEq1: "top1_dyadic ?m ?k1 = top1_dyadic n1 k1"
      by (simp add: top1_dyadic_pow2_scale)
    have hEq2: "top1_dyadic ?m ?k2 = top1_dyadic n2 k2"
    proof -
      have hEq2': "top1_dyadic (n2 + n1) (k2 * ((2::nat) ^ n1)) = top1_dyadic n2 k2"
        by (simp add: top1_dyadic_pow2_scale)
      show ?thesis
        using hEq2' by (simp add: add.commute)
    qed

    have hlt_level: "top1_dyadic ?m ?k1 < top1_dyadic ?m ?k2"
      using hlt unfolding sym[OF hEq1] sym[OF hEq2] .

    show ?thesis
      using hlt_level by (simp add: top1_dyadic_lt_same_denom_iff)
  qed

  have hcl_level:
    "closure_on X TX (top1_urysohn_U X TX U0 U1 ?m ?k1) \<subseteq> top1_urysohn_U X TX U0 U1 ?m ?k2"
    by (rule top1_urysohn_U_closure_mono_same_level[OF hN hU0 hU1 hcl01 hk1k2 hk2m])

  have hEq1: "top1_urysohn_U X TX U0 U1 ?m ?k1 = top1_urysohn_U X TX U0 U1 n1 k1"
    by (simp add: top1_urysohn_U_pow2_scale)
  have hEq2: "top1_urysohn_U X TX U0 U1 ?m ?k2 = top1_urysohn_U X TX U0 U1 n2 k2"
  proof -
    have hEq2': "top1_urysohn_U X TX U0 U1 (n2 + n1) (k2 * ((2::nat) ^ n1)) = top1_urysohn_U X TX U0 U1 n2 k2"
      by (simp add: top1_urysohn_U_pow2_scale)
    show ?thesis
      using hEq2' by (simp add: add.commute)
  qed

  show ?thesis
    unfolding sym[OF hEq1] sym[OF hEq2]
    using hcl_level .
qed

lemma top1_urysohn_unit_interval:
  assumes hN: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hB: "closedin_on X TX B"
  assumes hdisj: "A \<inter> B = {}"
  shows "\<exists>f. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f
            \<and> (\<forall>x\<in>A. f x = 0) \<and> (\<forall>x\<in>B. f x = 1)"
proof -
  have hT1: "top1_T1_on X TX"
    using hN unfolding top1_normal_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  have hexU0:
    "\<exists>U0. U0 \<in> TX \<and> U0 \<subseteq> X \<and> A \<subseteq> U0 \<and> closure_on X TX U0 \<subseteq> (X - B)"
    by (rule normal_urysohn_initial_step[OF hN hA hB hdisj])
  obtain U0 where hU0:
    "U0 \<in> TX \<and> U0 \<subseteq> X \<and> A \<subseteq> U0 \<and> closure_on X TX U0 \<subseteq> (X - B)"
    using hexU0 by (elim exE)
  have hU0_open: "U0 \<in> TX"
    by (rule conjunct1[OF hU0])
  have hU0_subX: "U0 \<subseteq> X"
    by (rule conjunct1[OF conjunct2[OF hU0]])

  let ?U1 = "X - B"
  have hU1_open: "?U1 \<in> TX"
    by (rule closedin_diff_open[OF hB])
  have hU1_subX: "?U1 \<subseteq> X"
    by (rule Diff_subset)
  have hcl01: "closure_on X TX U0 \<subseteq> ?U1"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hU0]]])

  define U where "U n k = top1_urysohn_U X TX U0 ?U1 n k" for n k

  have hU_basic:
    "(\<forall>n k. k \<le> ((2::nat) ^ n) \<longrightarrow> (U n k \<in> TX \<and> U n k \<subseteq> X))
     \<and> (\<forall>n k. k < ((2::nat) ^ n) \<longrightarrow> closure_on X TX (U n k) \<subseteq> U n (Suc k))"
    unfolding U_def
    by (rule top1_urysohn_U_basic_properties[OF hN hU0_open hU0_subX hU1_open hU1_subX hcl01])

  have U_open: "U n k \<in> TX" if hk: "k \<le> ((2::nat) ^ n)" for n k
  proof -
    have hbasic:
      "\<forall>n k. k \<le> ((2::nat) ^ n) \<longrightarrow> (U n k \<in> TX \<and> U n k \<subseteq> X)"
      by (rule conjunct1[OF hU_basic])
    have hnk_imp: "k \<le> ((2::nat) ^ n) \<longrightarrow> (U n k \<in> TX \<and> U n k \<subseteq> X)"
      by (rule spec[OF spec[OF hbasic, of n], of k])
    have hnk: "U n k \<in> TX \<and> U n k \<subseteq> X"
      by (rule mp[OF hnk_imp hk])
    show ?thesis by (rule conjunct1[OF hnk])
  qed
  have U_subX: "U n k \<subseteq> X" if hk: "k \<le> ((2::nat) ^ n)" for n k
  proof -
    have hbasic:
      "\<forall>n k. k \<le> ((2::nat) ^ n) \<longrightarrow> (U n k \<in> TX \<and> U n k \<subseteq> X)"
      by (rule conjunct1[OF hU_basic])
    have hnk_imp: "k \<le> ((2::nat) ^ n) \<longrightarrow> (U n k \<in> TX \<and> U n k \<subseteq> X)"
      by (rule spec[OF spec[OF hbasic, of n], of k])
    have hnk: "U n k \<in> TX \<and> U n k \<subseteq> X"
      by (rule mp[OF hnk_imp hk])
    show ?thesis by (rule conjunct2[OF hnk])
  qed

  have closure_U_subX: "closure_on X TX (U n k) \<subseteq> X" if hk: "k \<le> ((2::nat) ^ n)" for n k
    apply (rule closure_on_subset_carrier[OF hTopX])
    apply (rule U_subX[OF hk])
    done

  define S where
    "S x = insert 1 {top1_dyadic n k | n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k}"
    for x
  define f where "f x = Inf (S x)" for x

  have S_ne: "S x \<noteq> {}" for x
    unfolding S_def by simp

  have dyadic_nonneg: "0 \<le> top1_dyadic n k" for n k
    unfolding top1_dyadic_def
    by (simp add: divide_nonneg_pos)

  have dyadic_le1: "top1_dyadic n k \<le> 1" if hk: "k \<le> (2::nat) ^ n" for n k
  proof -
    have hk': "real k \<le> real ((2::nat) ^ n)"
      using hk by simp
    have hk'': "real k \<le> (2::real) ^ n"
      using hk' by simp
    have hpos: "(0::real) < (2::real) ^ n"
      by simp
    have "top1_dyadic n k \<le> ((2::real) ^ n) / ((2::real) ^ n)"
      unfolding top1_dyadic_def
      using hk'' hpos by (simp add: divide_right_mono)
    thus ?thesis
      by simp
  qed

  have S_bdd_below: "bdd_below (S x)" for x
    unfolding bdd_below_def
  proof (rule exI[where x=0], intro ballI)
    fix r assume hr: "r \<in> S x"
    show "0 \<le> r"
    proof (cases "r = 1")
      case True
      show ?thesis by (simp add: True)
    next
      case False
      have "r \<in> {top1_dyadic n k |n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k}"
        using hr False unfolding S_def by simp
      have hex: "\<exists>n k. r = top1_dyadic n k \<and> k \<le> (2::nat) ^ n \<and> x \<in> U n k"
        using \<open>r \<in> {top1_dyadic n k |n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k}\<close> by simp
      then obtain n k where hr_eq: "r = top1_dyadic n k"
        by (elim exE conjE)
      show ?thesis
        unfolding hr_eq by (rule dyadic_nonneg)
    qed
  qed

  have S_ge0: "0 \<le> r" if hr: "r \<in> S x" for x r
  proof (cases "r = 1")
    case True
    show ?thesis by (simp add: True)
  next
    case False
    have "r \<in> {top1_dyadic n k | n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k}"
      using hr False unfolding S_def by simp
    have hex: "\<exists>n k. r = top1_dyadic n k \<and> k \<le> (2::nat) ^ n \<and> x \<in> U n k"
      using \<open>r \<in> {top1_dyadic n k | n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k}\<close> by simp
    then obtain n k where hr_eq: "r = top1_dyadic n k"
      by (elim exE conjE)
    show ?thesis
      unfolding hr_eq by (rule dyadic_nonneg)
  qed

  have f_le1: "f x \<le> 1" for x
    unfolding f_def
    apply (rule cInf_lower)
     apply (simp add: S_def)
    apply (rule S_bdd_below)
    done

  have f_ge0: "0 \<le> f x" for x
    unfolding f_def
  proof (rule cInf_greatest)
    show "S x \<noteq> {}"
      by (rule S_ne)
    fix r assume hr: "r \<in> S x"
    show "0 \<le> r"
      by (rule S_ge0[OF hr])
  qed

  have f_in_I: "f x \<in> top1_closed_interval 0 1" if hx: "x \<in> X" for x
  proof -
    have h0: "0 \<le> f x"
      by (rule f_ge0)
    have h1: "f x \<le> 1"
      by (rule f_le1)
    show ?thesis
      unfolding top1_closed_interval_def using h0 h1 by simp
  qed

  have f_le_dyadic_if_in:
    "f x \<le> top1_dyadic n k"
    if hk: "k \<le> (2::nat) ^ n" and hxU: "x \<in> U n k"
    for x n k
  proof -
    have hmem0: "top1_dyadic n k \<in> {top1_dyadic n' k' |n' k'. k' \<le> (2::nat) ^ n' \<and> x \<in> U n' k'}"
    proof -
      have "\<exists>n' k'. top1_dyadic n k = top1_dyadic n' k'
            \<and> k' \<le> (2::nat) ^ n' \<and> x \<in> U n' k'"
        apply (rule exI[where x=n])
        apply (rule exI[where x=k])
        apply (intro conjI)
          apply simp
         apply (rule hk)
        apply (rule hxU)
        done
      thus ?thesis by simp
    qed
    have hmem: "top1_dyadic n k \<in> S x"
      unfolding S_def
      apply (rule insertI2)
      apply (rule hmem0)
      done
    show ?thesis
      unfolding f_def
      apply (rule cInf_lower)
       apply (rule hmem)
      apply (rule S_bdd_below)
      done
  qed

  have dyadic_le_f_if_notin_U:
    "top1_dyadic n k \<le> f x"
    if hk: "k \<le> (2::nat) ^ n" and hxX: "x \<in> X" and hxnot: "x \<notin> U n k"
    for x n k
  proof -
    have h1: "top1_dyadic n k \<le> 1"
      by (rule dyadic_le1[OF hk])
    show ?thesis
      unfolding f_def
    proof (rule cInf_greatest)
      show "S x \<noteq> {}"
        by (rule S_ne)
      fix r assume hr: "r \<in> S x"
      show "top1_dyadic n k \<le> r"
      proof (cases "r = 1")
        case True
        show ?thesis using h1 by (simp add: True)
      next
        case False
        have "r \<in> {top1_dyadic m l |m l. l \<le> (2::nat) ^ m \<and> x \<in> U m l}"
          using hr False unfolding S_def by simp
        have hex: "\<exists>m l. r = top1_dyadic m l \<and> l \<le> (2::nat) ^ m \<and> x \<in> U m l"
          using \<open>r \<in> {top1_dyadic m l |m l. l \<le> (2::nat) ^ m \<and> x \<in> U m l}\<close> by simp
        then obtain m l where hr_eq: "r = top1_dyadic m l" and hlm: "l \<le> (2::nat) ^ m" and hxUm: "x \<in> U m l"
          by (elim exE conjE)
        have hnotlt: "\<not> top1_dyadic m l < top1_dyadic n k"
        proof
          assume hlt: "top1_dyadic m l < top1_dyadic n k"
          have hcl: "closure_on X TX (U m l) \<subseteq> U n k"
            unfolding U_def
            by (rule top1_urysohn_U_closure_mono_dyadic[OF hN hU0_open hU0_subX hU1_open hU1_subX hcl01 hlm hk hlt])
          have hxcl: "x \<in> closure_on X TX (U m l)"
            by (rule subsetD[OF subset_closure_on, OF hxUm])
          have "x \<in> U n k"
            by (rule subsetD[OF hcl hxcl])
          thus False using hxnot by contradiction
        qed
        show ?thesis
          unfolding hr_eq using hnotlt by simp
      qed
    qed
  qed

  have dyadic_le_f_if_notin_closure:
    "top1_dyadic n k \<le> f x"
    if hk: "k \<le> (2::nat) ^ n" and hxX: "x \<in> X" and hxnot: "x \<notin> closure_on X TX (U n k)"
    for x n k
  proof -
    have h1: "top1_dyadic n k \<le> 1"
      by (rule dyadic_le1[OF hk])
    show ?thesis
      unfolding f_def
    proof (rule cInf_greatest)
      show "S x \<noteq> {}"
        by (rule S_ne)
      fix r assume hr: "r \<in> S x"
      show "top1_dyadic n k \<le> r"
      proof (cases "r = 1")
        case True
        show ?thesis using h1 by (simp add: True)
      next
        case False
        have "r \<in> {top1_dyadic m l |m l. l \<le> (2::nat) ^ m \<and> x \<in> U m l}"
          using hr False unfolding S_def by simp
        have hex: "\<exists>m l. r = top1_dyadic m l \<and> l \<le> (2::nat) ^ m \<and> x \<in> U m l"
          using \<open>r \<in> {top1_dyadic m l |m l. l \<le> (2::nat) ^ m \<and> x \<in> U m l}\<close> by simp
        then obtain m l where hr_eq: "r = top1_dyadic m l" and hlm: "l \<le> (2::nat) ^ m" and hxUm: "x \<in> U m l"
          by (elim exE conjE)
        have hnotlt: "\<not> top1_dyadic m l < top1_dyadic n k"
        proof
          assume hlt: "top1_dyadic m l < top1_dyadic n k"
          have hcl: "closure_on X TX (U m l) \<subseteq> U n k"
            unfolding U_def
            by (rule top1_urysohn_U_closure_mono_dyadic[OF hN hU0_open hU0_subX hU1_open hU1_subX hcl01 hlm hk hlt])
          have hxclm: "x \<in> closure_on X TX (U m l)"
            by (rule subsetD[OF subset_closure_on, OF hxUm])
          have hxUnk: "x \<in> U n k"
            by (rule subsetD[OF hcl hxclm])
          have hxclnk: "x \<in> closure_on X TX (U n k)"
            by (rule subsetD[OF subset_closure_on, OF hxUnk])
          thus False using hxnot by contradiction
        qed
        show ?thesis
          unfolding hr_eq using hnotlt by simp
      qed
    qed
  qed

  have f_lt_dyadic_imp_in:
    "x \<in> U n k"
    if hk: "k \<le> (2::nat) ^ n" and hxX: "x \<in> X" and hlt: "f x < top1_dyadic n k"
    for x n k
  proof (rule ccontr)
    assume hxnot: "x \<notin> U n k"
    have "top1_dyadic n k \<le> f x"
      by (rule dyadic_le_f_if_notin_U[OF hk hxX hxnot])
    thus False using hlt by simp
  qed

  have f_le_dyadic_if_in_closure:
    "f x \<le> top1_dyadic n k"
    if hk: "k \<le> (2::nat) ^ n" and hxX: "x \<in> X" and hxcl: "x \<in> closure_on X TX (U n k)"
    for x n k
  proof (cases "top1_dyadic n k = 1")
    case True
    show ?thesis
      using f_le1 unfolding True .
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume hlt: "\<not> f x \<le> top1_dyadic n k"
      have hlt': "top1_dyadic n k < f x"
        using hlt by simp
      let ?d = "(top1_dyadic n k + f x) / 2"
      have hd1: "top1_dyadic n k < ?d"
        using hlt' by simp
      have hd2: "?d < f x"
        using hlt' by simp
      have hd0: "0 \<le> top1_dyadic n k"
        by (rule dyadic_nonneg)
      have hd_le1: "?d \<le> 1"
        using f_le1[of x] dyadic_le1[OF hk] by simp
      have hex_ml:
        "\<exists>m l. l \<le> (2::nat) ^ m
          \<and> top1_dyadic n k < top1_dyadic m l \<and> top1_dyadic m l < ?d"
        by (rule exists_top1_dyadic_between_01[OF hd0 hd1 hd_le1])
      obtain m l where hlm: "l \<le> (2::nat) ^ m"
        and hbetween: "top1_dyadic n k < top1_dyadic m l" "top1_dyadic m l < ?d"
        using hex_ml by (elim exE conjE)
      have hcl_m: "closure_on X TX (U n k) \<subseteq> U m l"
        unfolding U_def
        by (rule top1_urysohn_U_closure_mono_dyadic[OF hN hU0_open hU0_subX hU1_open hU1_subX hcl01 hk hlm hbetween(1)])
      have hxUm: "x \<in> U m l"
        by (rule subsetD[OF hcl_m hxcl])
      have "f x \<le> top1_dyadic m l"
        by (rule f_le_dyadic_if_in[OF hlm hxUm])
      thus False
        using hbetween(2) hd2 by simp
    qed
  qed

  have f_on_A: "f x = 0" if hxA: "x \<in> A" for x
  proof -
    have hA_sub_U0: "A \<subseteq> U0"
      by (rule conjunct1[OF conjunct2[OF conjunct2[OF hU0]]])
    have hxU0': "x \<in> U0"
      by (rule subsetD[OF hA_sub_U0 hxA])
    have hxU0: "x \<in> U 0 0"
      unfolding U_def by (simp add: top1_urysohn_U_endpoints hxU0')
    have hmem0: "0 \<in> S x"
    proof -
      have hmem0': "0 \<in> {top1_dyadic n k |n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k}"
      proof -
        have "\<exists>n k. 0 = top1_dyadic n k \<and> k \<le> (2::nat) ^ n \<and> x \<in> U n k"
        proof (intro exI[where x=0] exI[where x=0] conjI)
          show "0 = top1_dyadic 0 0"
            by (simp add: top1_dyadic_def)
          show "0 \<le> (2::nat) ^ 0"
            by simp
          show "x \<in> U 0 0"
            by (rule hxU0)
        qed
        thus ?thesis
          by simp
      qed
      show ?thesis
        unfolding S_def using hmem0' by (intro insertI2)
    qed
    have "Inf (S x) = 0"
    proof (rule cInf_eq_minimum)
      show "0 \<in> S x"
        by (rule hmem0)
      fix r assume hr: "r \<in> S x"
      show "0 \<le> r"
        by (rule S_ge0[OF hr])
    qed
    thus ?thesis
      unfolding f_def .
  qed

  have f_on_B: "f x = 1" if hxB: "x \<in> B" for x
  proof -
    have hxnotU1: "x \<notin> ?U1"
      using hxB by simp
    have hBsubX: "B \<subseteq> X"
      by (rule closedin_sub[OF hB])
    have hxX: "x \<in> X"
      by (rule subsetD[OF hBsubX hxB])
    have hnone:
      "\<not> (\<exists>n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k)"
	    proof
	      assume "\<exists>n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k"
	      then obtain n k where hk: "k \<le> (2::nat) ^ n" and hxUk: "x \<in> U n k"
	        by (elim exE conjE)
      have hU1_eq: "U n ((2::nat) ^ n) = ?U1"
        unfolding U_def by (simp add: top1_urysohn_U_endpoints)
      have hxU1': "x \<in> U n ((2::nat) ^ n)"
	      proof -
	        have hmono: "U n k \<subseteq> U n ((2::nat) ^ n)"
	          unfolding U_def
	          by (rule top1_urysohn_U_mono_same_level[OF hN hU0_open hU0_subX hU1_open hU1_subX hcl01 hk order_refl])
	        show ?thesis
	          by (rule subsetD[OF hmono hxUk])
	      qed
      have "x \<in> ?U1"
        unfolding sym[OF hU1_eq] using hxU1' .
      thus False using hxnotU1 by contradiction
	    qed
	    have hS: "S x = {1}"
	    proof (rule set_eqI)
	      fix r
	      show "r \<in> S x \<longleftrightarrow> r \<in> {1}"
	      proof
		        assume hr: "r \<in> S x"
		        have "r = 1 \<or> (\<exists>n k. r = top1_dyadic n k \<and> k \<le> (2::nat) ^ n \<and> x \<in> U n k)"
		          using hr unfolding S_def by simp
		        thus "r \<in> {1}"
		        proof
		          assume "r = 1"
		          thus ?thesis by simp
		        next
		          assume "\<exists>n k. r = top1_dyadic n k \<and> k \<le> (2::nat) ^ n \<and> x \<in> U n k"
		          then have "\<exists>n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k"
		          proof (elim exE conjE)
		            fix n k
		            assume "r = top1_dyadic n k"
		            assume hk: "k \<le> (2::nat) ^ n"
		            assume hxUk: "x \<in> U n k"
		            show "\<exists>n k. k \<le> (2::nat) ^ n \<and> x \<in> U n k"
		              apply (rule exI[where x=n])
		              apply (rule exI[where x=k])
		              apply (intro conjI)
		               apply (rule hk)
		              apply (rule hxUk)
		              done
		          qed
		          thus ?thesis
		            using hnone by contradiction
		        qed
	      next
	        assume hr: "r \<in> {1}"
	        show "r \<in> S x"
	          using hr unfolding S_def by simp
	      qed
	    qed
	    show ?thesis
	      unfolding f_def
	      by (simp add: hS)
	  qed

  have pre_ray_gt_open: "\<And>c. {x \<in> X. f x \<in> open_ray_gt c} \<in> TX"
  proof -
    fix c
    show "{x \<in> X. f x \<in> open_ray_gt c} \<in> TX"
	    proof (cases "1 \<le> c")
	      case True
	      have "{x \<in> X. f x \<in> open_ray_gt c} = {}"
	      proof (rule set_eqI)
	        fix x
	        show "x \<in> {x \<in> X. f x \<in> open_ray_gt c} \<longleftrightarrow> x \<in> {}"
	        proof
	          assume hx: "x \<in> {x \<in> X. f x \<in> open_ray_gt c}"
	          have hgt: "c < f x"
	            using hx unfolding open_ray_gt_def by simp
	          have hle: "f x \<le> 1"
	            by (rule f_le1)
	          have False
	            using True hgt hle by linarith
	          thus "x \<in> {}"
	            by simp
	        next
	          assume "x \<in> {}"
	          thus "x \<in> {x \<in> X. f x \<in> open_ray_gt c}"
	            by simp
	        qed
	      qed
      have hEmpty: "{} \<in> TX"
        by (rule conjunct1[OF hTopX[unfolded is_topology_on_def]])
      show ?thesis
        by (simp add: hEmpty \<open>{x \<in> X. f x \<in> open_ray_gt c} = {}\<close>)
	    next
	      case False
	      show ?thesis
	      proof (cases "c < 0")
	        case True
	        have hEq: "{x \<in> X. f x \<in> open_ray_gt c} = X"
	        proof (rule set_eqI)
	          fix x
	          show "x \<in> {x \<in> X. f x \<in> open_ray_gt c} \<longleftrightarrow> x \<in> X"
	          proof
	            assume hx: "x \<in> {x \<in> X. f x \<in> open_ray_gt c}"
	            show "x \<in> X"
	              using hx by simp
	          next
	            assume hxX: "x \<in> X"
	            have hfxge0: "0 \<le> f x"
	              by (rule f_ge0)
	            have hlt: "c < f x"
	              using True hfxge0 by linarith
	            show "x \<in> {x \<in> X. f x \<in> open_ray_gt c}"
	              unfolding open_ray_gt_def using hxX hlt by simp
	          qed
	        qed
	        have hX_open: "X \<in> TX"
	          using hTopX unfolding is_topology_on_def by blast
	        show ?thesis
	          using hEq hX_open by simp
      next
        case False
        have hc0: "0 \<le> c"
          using False by simp
        have hc_lt1: "c < 1"
          using \<open>\<not> 1 \<le> c\<close> by simp
        define UC where
          "UC = {X - closure_on X TX (U n k) | n k. k \<le> (2::nat) ^ n \<and> c < top1_dyadic n k}"
        have hUC_open: "\<forall>V\<in>UC. V \<in> TX"
        proof
          fix V assume hV: "V \<in> UC"
          obtain n k where hk: "k \<le> (2::nat) ^ n" and hdy: "c < top1_dyadic n k" and hVeq: "V = X - closure_on X TX (U n k)"
            using hV unfolding UC_def by blast
          have hcl_closed: "closedin_on X TX (closure_on X TX (U n k))"
          proof (rule closure_on_closed[OF hTopX])
            show "U n k \<subseteq> X"
              by (rule U_subX[OF hk])
          qed
          show "V \<in> TX"
            unfolding hVeq by (rule closedin_diff_open[OF hcl_closed])
        qed

        have hpre_eq: "{x \<in> X. f x \<in> open_ray_gt c} = \<Union>UC"
        proof (rule set_eqI)
          fix x
          show "x \<in> {x \<in> X. f x \<in> open_ray_gt c} \<longleftrightarrow> x \<in> \<Union>UC"
          proof (rule iffI)
            assume hx: "x \<in> {x \<in> X. f x \<in> open_ray_gt c}"
            have hxX: "x \<in> X" using hx by simp
            have hgt: "c < f x"
              using hx unfolding open_ray_gt_def by simp
            obtain n k where hk: "k \<le> (2::nat) ^ n"
              and hbetween: "c < top1_dyadic n k" "top1_dyadic n k < f x"
              using exists_top1_dyadic_between_01[OF hc0 hgt f_le1[of x]] by blast
            have hxnotcl: "x \<notin> closure_on X TX (U n k)"
            proof
              assume hxcl: "x \<in> closure_on X TX (U n k)"
              have hd0: "0 \<le> top1_dyadic n k"
                by (rule dyadic_nonneg)
              obtain m l where hlm: "l \<le> (2::nat) ^ m"
                and hbetween2: "top1_dyadic n k < top1_dyadic m l" "top1_dyadic m l < f x"
                using exists_top1_dyadic_between_01[OF hd0 hbetween(2) f_le1[of x]] by blast
              have hcl_m: "closure_on X TX (U n k) \<subseteq> U m l"
                unfolding U_def
                by (rule top1_urysohn_U_closure_mono_dyadic[OF hN hU0_open hU0_subX hU1_open hU1_subX hcl01 hk hlm hbetween2(1)])
              have hxUm: "x \<in> U m l"
                by (rule subsetD[OF hcl_m hxcl])
              have hfxle: "f x \<le> top1_dyadic m l"
                by (rule f_le_dyadic_if_in[OF hlm hxUm])
              show False
                using hfxle hbetween2(2) by simp
            qed
            have "X - closure_on X TX (U n k) \<in> UC"
              unfolding UC_def using hk hbetween(1) by blast
            hence "x \<in> \<Union>UC"
              using hxX hxnotcl by blast
            thus "x \<in> \<Union>UC" .
          next
            assume hx: "x \<in> \<Union>UC"
            then obtain V where hV: "V \<in> UC" and hxV: "x \<in> V"
              by blast
            obtain n k where hk: "k \<le> (2::nat) ^ n" and hdy: "c < top1_dyadic n k"
              and hVeq: "V = X - closure_on X TX (U n k)"
              using hV unfolding UC_def by blast
            have hxX: "x \<in> X"
              using hxV unfolding hVeq by simp
            have hxnotcl: "x \<notin> closure_on X TX (U n k)"
              using hxV unfolding hVeq by simp
            have hle: "top1_dyadic n k \<le> f x"
              by (rule dyadic_le_f_if_notin_closure[OF hk hxX hxnotcl])
            have "c < f x"
              using hdy hle by simp
            thus "x \<in> {x \<in> X. f x \<in> open_ray_gt c}"
              unfolding open_ray_gt_def using hxX by simp
          qed
        qed

        have hUC_sub: "UC \<subseteq> TX"
          using hUC_open by blast
        have "\<Union>UC \<in> TX"
          using conjunct1[OF conjunct2[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]]] hUC_sub
          by blast
        thus ?thesis
          unfolding hpre_eq .
      qed
    qed
  qed

  have pre_ray_lt_open: "\<And>c. {x \<in> X. f x \<in> open_ray_lt c} \<in> TX"
  proof -
    fix c
    show "{x \<in> X. f x \<in> open_ray_lt c} \<in> TX"
	    proof (cases "c \<le> 0")
	      case True
	      have "{x \<in> X. f x \<in> open_ray_lt c} = {}"
	      proof (rule set_eqI)
	        fix x
	        show "x \<in> {x \<in> X. f x \<in> open_ray_lt c} \<longleftrightarrow> x \<in> {}"
	        proof
	          assume hx: "x \<in> {x \<in> X. f x \<in> open_ray_lt c}"
	          have hfxlt: "f x < c"
	            using hx unfolding open_ray_lt_def by simp
	          have hfxge0: "0 \<le> f x"
	            by (rule f_ge0)
	          have False
	            using True hfxlt hfxge0 by linarith
	          thus "x \<in> {}"
	            by simp
	        next
	          assume "x \<in> {}"
	          thus "x \<in> {x \<in> X. f x \<in> open_ray_lt c}"
	            by simp
	        qed
	      qed
	      have hEmpty: "{} \<in> TX"
	        by (rule conjunct1[OF hTopX[unfolded is_topology_on_def]])
	      show ?thesis
	        by (simp add: hEmpty \<open>{x \<in> X. f x \<in> open_ray_lt c} = {}\<close>)
    next
      case False
      show ?thesis
	      proof (cases "1 < c")
	        case True
	        have hEq: "{x \<in> X. f x \<in> open_ray_lt c} = X"
	        proof (rule set_eqI)
	          fix x
	          show "x \<in> {x \<in> X. f x \<in> open_ray_lt c} \<longleftrightarrow> x \<in> X"
	          proof
	            assume hx: "x \<in> {x \<in> X. f x \<in> open_ray_lt c}"
	            show "x \<in> X"
	              using hx by simp
	          next
	            assume hxX: "x \<in> X"
	            have hfxle1: "f x \<le> 1"
	              by (rule f_le1)
	            have hfxltc: "f x < c"
	              using hfxle1 True by (rule le_less_trans)
	            show "x \<in> {x \<in> X. f x \<in> open_ray_lt c}"
	              unfolding open_ray_lt_def using hxX hfxltc by simp
	          qed
	        qed
	        have hX_open: "X \<in> TX"
	          using hTopX unfolding is_topology_on_def by blast
	        show ?thesis
	          using hEq hX_open by simp
	      next
	        case False
	        have hc01: "0 < c"
	          using \<open>\<not> c \<le> 0\<close> by simp
	        have hc_le1: "c \<le> 1"
	          using False by (simp add: not_less)
	        define UC where
	          "UC = {U n k | n k. k \<le> (2::nat) ^ n \<and> top1_dyadic n k < c}"
	        have hUC_open: "\<forall>V\<in>UC. V \<in> TX"
	          unfolding UC_def using U_open by blast
        have hpre_eq: "{x \<in> X. f x \<in> open_ray_lt c} = \<Union>UC"
        proof (rule set_eqI)
          fix x
          show "x \<in> {x \<in> X. f x \<in> open_ray_lt c} \<longleftrightarrow> x \<in> \<Union>UC"
          proof (rule iffI)
            assume hx: "x \<in> {x \<in> X. f x \<in> open_ray_lt c}"
            have hxX: "x \<in> X" using hx by simp
            have hfx: "f x < c"
              using hx unfolding open_ray_lt_def by simp
            have h0fx: "0 \<le> f x"
              by (rule f_ge0)
            obtain n k where hk: "k \<le> (2::nat) ^ n"
              and hbetween: "f x < top1_dyadic n k" "top1_dyadic n k < c"
              using exists_top1_dyadic_between_01[OF h0fx hfx hc_le1] by blast
            have hxUk: "x \<in> U n k"
              by (rule f_lt_dyadic_imp_in[OF hk hxX hbetween(1)])
            have "U n k \<in> UC"
              unfolding UC_def using hk hbetween(2) by blast
            thus "x \<in> \<Union>UC"
              using hxUk by blast
          next
            assume hx: "x \<in> \<Union>UC"
	            then obtain V where hV: "V \<in> UC" and hxV: "x \<in> V"
	              by blast
	            obtain n k where hk: "k \<le> (2::nat) ^ n" and hdy: "top1_dyadic n k < c" and hVeq: "V = U n k"
	              using hV unfolding UC_def by blast
	            have hxUnk: "x \<in> U n k"
	              using hxV hVeq by simp
	            have hfxle: "f x \<le> top1_dyadic n k"
	              by (rule f_le_dyadic_if_in[OF hk hxUnk])
	            have "f x < c"
	              using hfxle hdy by simp
	            thus "x \<in> {x \<in> X. f x \<in> open_ray_lt c}"
	              unfolding open_ray_lt_def using hxV hVeq U_subX[OF hk] by blast
	          qed
        qed
        have hUC_sub: "UC \<subseteq> TX"
          using hUC_open by blast
        have "\<Union>UC \<in> TX"
          using conjunct1[OF conjunct2[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]]] hUC_sub
          by blast
        thus ?thesis
          unfolding hpre_eq .
      qed
	  qed
	  qed
	
	  have pre_basis_open:
	    "{x \<in> X. f x \<in> b} \<in> TX"
	    if hb: "b \<in> (basis_order_topology::real set set)"
	    for b
	  proof -
	    have hb_cases:
	      "(\<exists>a c. a < c \<and> b = open_interval a c)
	       \<or> (\<exists>a. b = open_ray_gt a)
	       \<or> (\<exists>a. b = open_ray_lt a)
	       \<or> b = (UNIV::real set)"
	      by (rule basis_order_topology_cases[OF hb])
    show ?thesis
    proof (rule disjE[OF hb_cases])
	      assume hInt: "\<exists>a c. a < c \<and> b = open_interval a c"
	      then obtain a c where hbEq: "b = open_interval a c"
	        by blast
	      have hGt: "{x \<in> X. f x \<in> open_ray_gt a} \<in> TX"
	        by (rule pre_ray_gt_open)
	      have hLt: "{x \<in> X. f x \<in> open_ray_lt c} \<in> TX"
	        by (rule pre_ray_lt_open)
	      have hInter: "{x \<in> X. f x \<in> open_ray_gt a} \<inter> {x \<in> X. f x \<in> open_ray_lt c} \<in> TX"
	        by (rule topology_inter2[OF hTopX hGt hLt])
	      have hEq:
	        "{x \<in> X. f x \<in> b} = {x \<in> X. f x \<in> open_ray_gt a} \<inter> {x \<in> X. f x \<in> open_ray_lt c}"
	      proof -
	        have "{x \<in> X. f x \<in> open_interval a c}
	            = {x \<in> X. f x \<in> open_ray_gt a} \<inter> {x \<in> X. f x \<in> open_ray_lt c}"
	          unfolding open_interval_def open_ray_gt_def open_ray_lt_def
	          by (rule set_eqI) (simp add: conj_assoc conj_left_commute conj_commute)
	        thus ?thesis
	          unfolding hbEq .
	      qed
	      show ?thesis
	        by (simp add: hEq hInter)
	    next
	      assume hGt: "(\<exists>a. b = open_ray_gt a) \<or> (\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
      show ?thesis
      proof (rule disjE[OF hGt])
	        assume h1: "\<exists>a. b = open_ray_gt a"
	        then obtain a where hbEq: "b = open_ray_gt a"
	          by blast
	        show ?thesis
	          unfolding hbEq by (rule pre_ray_gt_open)
		      next
		        assume h2: "(\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
		        show ?thesis
		        proof (rule disjE[OF h2])
		          assume h21: "\<exists>a. b = open_ray_lt a"
		          then obtain a where hbEq: "b = open_ray_lt a"
		            by blast
		          show ?thesis
		            unfolding hbEq by (rule pre_ray_lt_open)
		        next
		          assume hbEq: "b = (UNIV::real set)"
		          have hX_open: "X \<in> TX"
		            using hTopX unfolding is_topology_on_def by blast
		          show ?thesis
		            unfolding hbEq using hX_open by simp
		        qed
		      qed
		    qed
		  qed
	
	  have hBasis: "basis_for (UNIV::real set) (basis_order_topology::real set set) order_topology_on_UNIV"
	    unfolding basis_for_def order_topology_on_UNIV_def
	    by (intro conjI basis_order_topology_is_basis_on_UNIV refl)
	
	  have f_cont_order: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
	  proof (rule top1_continuous_map_on_generated_by_basis)
	    show "is_topology_on X TX"
	      by (rule hTopX)
	    show "basis_for (UNIV::real set) (basis_order_topology::real set set) order_topology_on_UNIV"
	      by (rule hBasis)
	    show "\<forall>x\<in>X. f x \<in> (UNIV::real set)"
	      by simp
	    show "\<forall>b\<in>(basis_order_topology::real set set). {x \<in> X. f x \<in> b} \<in> TX"
	    proof (intro ballI)
	      fix b assume hb: "b \<in> (basis_order_topology::real set set)"
	      show "{x \<in> X. f x \<in> b} \<in> TX"
	        by (rule pre_basis_open[OF hb])
	    qed
	  qed
	
		  have hfimg: "f ` X \<subseteq> top1_closed_interval 0 1"
		  proof (rule subsetI)
		    fix y assume hy: "y \<in> f ` X"
		    have hex: "\<exists>x\<in>X. y = f x"
		      using hy by (simp only: image_iff)
		    obtain x where hxX: "x \<in> X" and hyEq: "y = f x"
		      using hex by (elim bexE)
		    show "y \<in> top1_closed_interval 0 1"
		      unfolding hyEq by (rule f_in_I[OF hxX])
		  qed
	
	  have f_cont_I:
	    "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f"
		  proof -
		    have hTopUNIV: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
		      by (rule order_topology_on_UNIV_is_topology_on)
		    have hStep:
		      "top1_continuous_map_on X TX (top1_closed_interval 0 1)
		        (subspace_topology (UNIV::real set) order_topology_on_UNIV (top1_closed_interval 0 1)) f"
		      apply (rule Theorem_18_2(5)[OF hTopX hTopUNIV hTopUNIV, rule_format, where W="top1_closed_interval 0 1" and f=f])
		      apply (rule conjI)
		       apply (rule f_cont_order)
		      apply (rule conjI)
		       apply simp
		      apply (rule hfimg)
		      done
		    show ?thesis
		      unfolding top1_closed_interval_topology_def
		      by (rule hStep)
		  qed
	
		  show ?thesis
		  proof (rule exI[where x=f], intro conjI)
		    show "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f"
		      by (rule f_cont_I)
		    show "\<forall>x\<in>A. f x = 0"
		    proof (intro ballI)
		      fix x assume hxA: "x \<in> A"
		      show "f x = 0"
		        by (rule f_on_A[OF hxA])
		    qed
		    show "\<forall>x\<in>B. f x = 1"
		    proof (intro ballI)
		      fix x assume hxB: "x \<in> B"
		      show "f x = 1"
		        by (rule f_on_B[OF hxB])
		    qed
		  qed
		qed

text \<open>(Obsolete in-progress proof attempt removed; see backups.)\<close>

(** from \S33 Theorem 33.1 (Urysohn lemma) [top1.tex:4382] **)
theorem Theorem_33_1:
  fixes a b :: real
  assumes hX: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hB: "closedin_on X TX B"
  assumes hdisj: "A \<inter> B = {}"
  assumes hab: "a \<le> b"
  shows "\<exists>f. top1_continuous_map_on X TX (top1_closed_interval a b) (top1_closed_interval_topology a b) f
            \<and> (\<forall>x\<in>A. f x = a) \<and> (\<forall>x\<in>B. f x = b)"
proof (cases "a = b")
  case True
  let ?J = "top1_closed_interval a b"
  let ?TJ = "top1_closed_interval_topology a b"

  have hTopX': "is_topology_on X TX"
  proof -
    have hT1: "top1_T1_on X TX"
      using hX unfolding top1_normal_on_def by (rule conjunct1)
    show ?thesis
      using hT1 unfolding top1_T1_on_def by (rule conjunct1)
  qed
  have hTopJ: "is_topology_on ?J ?TJ"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF order_topology_on_UNIV_is_topology_on], simp)
  have haJ: "a \<in> ?J"
    unfolding top1_closed_interval_def using hab True by simp

  have hConstAll: "\<forall>y0\<in>?J. top1_continuous_map_on X TX ?J ?TJ (\<lambda>x. y0)"
    by (rule Theorem_18_2(1)[OF hTopX' hTopJ hTopJ])
  have hconst: "top1_continuous_map_on X TX ?J ?TJ (\<lambda>x. a)"
    using hConstAll haJ by (rule bspec)

  show ?thesis
  proof (rule exI[where x="\<lambda>x. a"], intro conjI)
    show "top1_continuous_map_on X TX ?J ?TJ (\<lambda>x. a)"
      by (rule hconst)
    show "\<forall>x\<in>A. (\<lambda>x. a) x = a"
      by simp
    show "\<forall>x\<in>B. (\<lambda>x. a) x = b"
      using True by simp
  qed
next
  case False
  have hab': "a < b"
    using hab False by linarith

  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?J = "top1_closed_interval a b"
  let ?TJ = "top1_closed_interval_topology a b"

  have hTopX': "is_topology_on X TX"
  proof -
    have hT1: "top1_T1_on X TX"
      using hX unfolding top1_normal_on_def by (rule conjunct1)
    show ?thesis
      using hT1 unfolding top1_T1_on_def by (rule conjunct1)
  qed
  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF order_topology_on_UNIV_is_topology_on], simp)
  have hTopJ: "is_topology_on ?J ?TJ"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF order_topology_on_UNIV_is_topology_on], simp)
  have hTopUNIV: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  
  have hex_f0:
    "\<exists>f0. top1_continuous_map_on X TX ?I ?TI f0
       \<and> (\<forall>x\<in>A. f0 x = 0)
       \<and> (\<forall>x\<in>B. f0 x = 1)"
    by (rule top1_urysohn_unit_interval[OF hX hA hB hdisj])
  obtain f0 where hf0:
    "top1_continuous_map_on X TX ?I ?TI f0
     \<and> (\<forall>x\<in>A. f0 x = 0)
     \<and> (\<forall>x\<in>B. f0 x = 1)"
    using hex_f0 by (elim exE)

  define g where "g t = a + (b - a) * t" for t
  have hSlope: "0 < b - a"
    using hab' by simp

  have I_inter_ray_gt: "\<And>c. ?I \<inter> open_ray_gt c \<in> ?TI"
  proof -
    fix c
    show "?I \<inter> open_ray_gt c \<in> ?TI"
      unfolding top1_closed_interval_topology_def subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="open_ray_gt c"])
      apply (intro conjI)
       apply simp
      apply (rule open_ray_gt_in_order_topology)
      done
  qed

  have I_inter_ray_lt: "\<And>c. ?I \<inter> open_ray_lt c \<in> ?TI"
  proof -
    fix c
    show "?I \<inter> open_ray_lt c \<in> ?TI"
      unfolding top1_closed_interval_topology_def subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="open_ray_lt c"])
      apply (intro conjI)
       apply simp
      apply (rule open_ray_lt_in_order_topology)
      done
  qed

  have pre_ray_gt_g: "{t \<in> ?I. g t \<in> open_ray_gt c} \<in> ?TI" for c
  proof -
    have hEq:
      "{t \<in> ?I. g t \<in> open_ray_gt c} = ?I \<inter> open_ray_gt ((c - a) / (b - a))"
      unfolding g_def open_ray_gt_def
      apply (rule set_eqI)
      apply (simp add: algebra_simps pos_divide_less_eq[OF hSlope])
      done
    show ?thesis
      unfolding hEq by (rule I_inter_ray_gt)
  qed

  have pre_ray_lt_g: "{t \<in> ?I. g t \<in> open_ray_lt c} \<in> ?TI" for c
  proof -
    have hEq:
      "{t \<in> ?I. g t \<in> open_ray_lt c} = ?I \<inter> open_ray_lt ((c - a) / (b - a))"
      unfolding g_def open_ray_lt_def
      apply (rule set_eqI)
      apply (simp add: algebra_simps pos_less_divide_eq[OF hSlope])
      done
    show ?thesis
      unfolding hEq by (rule I_inter_ray_lt)
  qed

  have pre_basis_g: "\<forall>B\<in>(basis_order_topology::real set set). {t \<in> ?I. g t \<in> B} \<in> ?TI"
  proof (intro ballI)
    fix B assume hB: "B \<in> (basis_order_topology::real set set)"
    have hCases:
      "(\<exists>u v. u < v \<and> B = open_interval u v)
       \<or> (\<exists>u. B = open_ray_gt u)
       \<or> (\<exists>u. B = open_ray_lt u)
       \<or> B = (UNIV::real set)"
      by (rule basis_order_topology_cases[OF hB])
    show "{t \<in> ?I. g t \<in> B} \<in> ?TI"
    proof (rule disjE[OF hCases])
      assume hInt: "\<exists>u v. u < v \<and> B = open_interval u v"
      from hInt obtain u v where huv: "u < v" and hBeq: "B = open_interval u v"
        by (elim exE conjE)
      have hEq:
        "{t \<in> ?I. g t \<in> B} = {t \<in> ?I. g t \<in> open_ray_gt u} \<inter> {t \<in> ?I. g t \<in> open_ray_lt v}"
        unfolding hBeq open_interval_def open_ray_gt_def open_ray_lt_def
        by (rule set_eqI) (simp add: conj_assoc conj_left_commute conj_commute)
      have hGt: "{t \<in> ?I. g t \<in> open_ray_gt u} \<in> ?TI"
        by (rule pre_ray_gt_g)
      have hLt: "{t \<in> ?I. g t \<in> open_ray_lt v} \<in> ?TI"
        by (rule pre_ray_lt_g)
      have hInter: "{t \<in> ?I. g t \<in> open_ray_gt u} \<inter> {t \<in> ?I. g t \<in> open_ray_lt v} \<in> ?TI"
        by (rule topology_inter2[OF hTopI hGt hLt])
      show ?thesis
        unfolding hEq using hInter .
    next
      assume hRest: "(\<exists>u. B = open_ray_gt u) \<or> (\<exists>u. B = open_ray_lt u) \<or> B = (UNIV::real set)"
      show ?thesis
      proof (rule disjE[OF hRest])
        assume h1: "\<exists>u. B = open_ray_gt u"
        then obtain u where hBeq: "B = open_ray_gt u"
          by (elim exE)
        show ?thesis
          unfolding hBeq by (rule pre_ray_gt_g)
      next
        assume h2: "(\<exists>u. B = open_ray_lt u) \<or> B = (UNIV::real set)"
        show ?thesis
        proof (rule disjE[OF h2])
          assume h21: "\<exists>u. B = open_ray_lt u"
          then obtain u where hBeq: "B = open_ray_lt u"
            by (elim exE)
          show ?thesis
            unfolding hBeq by (rule pre_ray_lt_g)
        next
          assume hBeq: "B = (UNIV::real set)"
          have hI_open: "?I \<in> ?TI"
            by (rule conjunct1[OF conjunct2[OF hTopI[unfolded is_topology_on_def]]])
          show ?thesis
            unfolding hBeq using hI_open by simp
        qed
      qed
    qed
  qed

  have hBasis: "basis_for (UNIV::real set) (basis_order_topology::real set set) order_topology_on_UNIV"
    unfolding basis_for_def order_topology_on_UNIV_def
    by (intro conjI basis_order_topology_is_basis_on_UNIV refl)

  have g_cont_order: "top1_continuous_map_on ?I ?TI (UNIV::real set) order_topology_on_UNIV g"
  proof (rule top1_continuous_map_on_generated_by_basis)
    show "is_topology_on ?I ?TI"
      by (rule hTopI)
    show "basis_for (UNIV::real set) (basis_order_topology::real set set) order_topology_on_UNIV"
      by (rule hBasis)
    show "\<forall>t\<in>?I. g t \<in> (UNIV::real set)"
      by simp
    show "\<forall>B\<in>(basis_order_topology::real set set). {t \<in> ?I. g t \<in> B} \<in> ?TI"
      by (rule pre_basis_g)
  qed

  have g_img: "g ` ?I \<subseteq> ?J"
  proof (rule subsetI)
    fix y assume hy: "y \<in> g ` ?I"
    have hex: "\<exists>t\<in>?I. y = g t"
      using hy by (simp only: image_iff)
    obtain t where htI: "t \<in> ?I" and hyEq: "y = g t"
      using hex by (elim bexE)
    have ht01: "0 \<le> t \<and> t \<le> 1"
      using htI unfolding top1_closed_interval_def by simp
    have ht0: "0 \<le> t"
      by (rule conjunct1[OF ht01])
    have ht1: "t \<le> 1"
      by (rule conjunct2[OF ht01])
    have hba0: "0 \<le> b - a"
      using hab by simp
    have h0: "a \<le> g t"
      unfolding g_def using ht0 hba0 by (simp add: mult_nonneg_nonneg)
    have h1: "g t \<le> b"
    proof -
      have "(b - a) * t \<le> (b - a) * 1"
        using ht1 hba0 by (rule mult_left_mono)
      hence "(b - a) * t \<le> b - a"
        by simp
      thus ?thesis
        unfolding g_def by simp
    qed
    show "y \<in> ?J"
      unfolding hyEq top1_closed_interval_def using h0 h1 by simp
  qed
  
  have g_cont_J: "top1_continuous_map_on ?I ?TI ?J ?TJ g"
  proof -
    have hStep:
      "top1_continuous_map_on ?I ?TI ?J (subspace_topology (UNIV::real set) order_topology_on_UNIV ?J) g"
      apply (rule Theorem_18_2(5)[OF hTopI hTopUNIV hTopUNIV, rule_format, where W="?J" and f=g])
      apply (rule conjI)
       apply (rule g_cont_order)
      apply (rule conjI)
       apply simp
      apply (rule g_img)
      done
    show ?thesis
      unfolding top1_closed_interval_topology_def[of a b]
      by (rule hStep)
  qed
  
  have comp_cont: "top1_continuous_map_on X TX ?J ?TJ (g \<circ> f0)"
  proof -
    have hComp:
      "(\<forall>f h. top1_continuous_map_on X TX ?I ?TI f \<and> top1_continuous_map_on ?I ?TI ?J ?TJ h
             \<longrightarrow> top1_continuous_map_on X TX ?J ?TJ (h \<circ> f))"
      by (rule Theorem_18_2(3)[OF hTopX' hTopI hTopJ])
    have hf0_cont: "top1_continuous_map_on X TX ?I ?TI f0"
      by (rule conjunct1[OF hf0])
    have hImp:
      "top1_continuous_map_on X TX ?I ?TI f0 \<and> top1_continuous_map_on ?I ?TI ?J ?TJ g
        \<longrightarrow> top1_continuous_map_on X TX ?J ?TJ (g \<circ> f0)"
    proof -
      have h1:
        "\<forall>h. top1_continuous_map_on X TX ?I ?TI f0 \<and> top1_continuous_map_on ?I ?TI ?J ?TJ h
              \<longrightarrow> top1_continuous_map_on X TX ?J ?TJ (h \<circ> f0)"
        by (rule spec[OF hComp, of f0])
      show ?thesis
        by (rule spec[OF h1, of g])
    qed
    show ?thesis
      apply (rule mp[OF hImp])
      apply (intro conjI)
       apply (rule hf0_cont)
      apply (rule g_cont_J)
      done
  qed

  show ?thesis
  proof (rule exI[where x="g \<circ> f0"], intro conjI)
    show "top1_continuous_map_on X TX ?J ?TJ (g \<circ> f0)"
      by (rule comp_cont)
    show "\<forall>x\<in>A. (g \<circ> f0) x = a"
      using hf0 unfolding g_def by simp
    show "\<forall>x\<in>B. (g \<circ> f0) x = b"
      using hf0 unfolding g_def by simp
  qed
qed

subsection \<open>Completely regular spaces\<close>

(** A space is completely regular if it is T1 and points can be separated from closed sets
    by continuous functions into the unit interval. **)
definition top1_completely_regular_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_completely_regular_on X T \<longleftrightarrow>
     top1_T1_on X T \<and>
     (\<forall>x0\<in>X. \<forall>A. closedin_on X T A \<and> x0 \<notin> A \<longrightarrow>
        (\<exists>f::'a \<Rightarrow> real.
            top1_continuous_map_on X T (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f
            \<and> f x0 = 1 \<and> (\<forall>x\<in>A. f x = 0)))"

(** Completely regular implies regular (cf. discussion following the Urysohn lemma in top1.tex). **)
lemma completely_regular_imp_regular_on:
  assumes hCR: "top1_completely_regular_on X TX"
  shows "top1_regular_on X TX"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?c = "(1 / 2 :: real)"
  let ?L = "?I \<inter> open_ray_lt ?c"
  let ?G = "?I \<inter> open_ray_gt ?c"

  have hT1: "top1_T1_on X TX"
    using hCR unfolding top1_completely_regular_on_def by (rule conjunct1)
  have hSep:
    "\<forall>x0\<in>X. \<forall>A. closedin_on X TX A \<and> x0 \<notin> A \<longrightarrow>
       (\<exists>f::'a \<Rightarrow> real.
           top1_continuous_map_on X TX ?I ?TI f \<and> f x0 = 1 \<and> (\<forall>x\<in>A. f x = 0))"
    using hCR unfolding top1_completely_regular_on_def by (rule conjunct2)

  have hL_open: "?L \<in> ?TI"
    unfolding top1_closed_interval_topology_def subspace_topology_def
    apply (rule CollectI)
    apply (rule exI[where x="open_ray_lt ?c"])
    apply (intro conjI)
     apply simp
    apply (rule open_ray_lt_in_order_topology)
    done

  have hG_open: "?G \<in> ?TI"
    unfolding top1_closed_interval_topology_def subspace_topology_def
    apply (rule CollectI)
    apply (rule exI[where x="open_ray_gt ?c"])
    apply (intro conjI)
     apply simp
    apply (rule open_ray_gt_in_order_topology)
    done

  have hdisj_cod: "?G \<inter> ?L = {}"
  proof (rule equalityI)
    show "?G \<inter> ?L \<subseteq> {}"
    proof (rule subsetI)
      fix t assume ht: "t \<in> ?G \<inter> ?L"
      have htG0: "t \<in> ?G"
        using ht by simp
      have htL0: "t \<in> ?L"
        using ht by simp
      have htG: "t \<in> open_ray_gt ?c"
        using htG0 by simp
      have htL: "t \<in> open_ray_lt ?c"
        using htL0 by simp
      have "?c < t" using htG unfolding open_ray_gt_def by simp
      moreover have "t < ?c" using htL unfolding open_ray_lt_def by simp
      ultimately have False by linarith
      thus "t \<in> {}" by simp
    qed
    show "{} \<subseteq> ?G \<inter> ?L" by (rule empty_subsetI)
  qed

  show ?thesis
    unfolding top1_regular_on_def
  proof (intro conjI)
    show "top1_T1_on X TX" by (rule hT1)
    show "\<forall>x\<in>X. \<forall>C. closedin_on X TX C \<and> x \<notin> C \<longrightarrow>
        (\<exists>U V. neighborhood_of x X TX U \<and> V \<in> TX \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro ballI allI impI)
      fix x C
      assume hxX: "x \<in> X"
      assume hC: "closedin_on X TX C \<and> x \<notin> C"
      have hCcl: "closedin_on X TX C"
        by (rule conjunct1[OF hC])
      have hxC: "x \<notin> C"
        by (rule conjunct2[OF hC])

      have hSepx: "\<forall>A. closedin_on X TX A \<and> x \<notin> A \<longrightarrow>
         (\<exists>f::'a \<Rightarrow> real.
             top1_continuous_map_on X TX ?I ?TI f \<and> f x = 1 \<and> (\<forall>z\<in>A. f z = 0))"
        by (rule bspec[OF hSep hxX])
      have hSepC:
        "closedin_on X TX C \<and> x \<notin> C \<longrightarrow>
         (\<exists>f::'a \<Rightarrow> real.
             top1_continuous_map_on X TX ?I ?TI f \<and> f x = 1 \<and> (\<forall>z\<in>C. f z = 0))"
        by (rule spec[where x=C, OF hSepx])
      have hexF:
        "\<exists>f::'a \<Rightarrow> real.
          top1_continuous_map_on X TX ?I ?TI f \<and> f x = 1 \<and> (\<forall>z\<in>C. f z = 0)"
        apply (rule mp[OF hSepC])
        apply (intro conjI)
         apply (rule hCcl)
        apply (rule hxC)
        done

      obtain f where hfcont: "top1_continuous_map_on X TX ?I ?TI f"
          and hfx: "f x = 1" and hfC0: "\<forall>z\<in>C. f z = 0"
        using hexF by (elim exE conjE)

      let ?U = "{z\<in>X. f z \<in> ?G}"
      let ?V = "{z\<in>X. f z \<in> ?L}"

      have hU_open: "?U \<in> TX"
      proof -
        have hpre: "\<forall>V\<in>?TI. {z\<in>X. f z \<in> V} \<in> TX"
          by (rule conjunct2[OF hfcont[unfolded top1_continuous_map_on_def]])
        show ?thesis
          using hpre hG_open by (rule bspec)
      qed
      have hV_open: "?V \<in> TX"
      proof -
        have hpre: "\<forall>V\<in>?TI. {z\<in>X. f z \<in> V} \<in> TX"
          by (rule conjunct2[OF hfcont[unfolded top1_continuous_map_on_def]])
        show ?thesis
          using hpre hL_open by (rule bspec)
      qed

      have hxc: "x \<in> ?U"
      proof -
        have h1I: "1 \<in> ?I"
          unfolding top1_closed_interval_def by simp
        have h1G: "1 \<in> open_ray_gt ?c"
          unfolding open_ray_gt_def by simp
        have "f x \<in> ?G"
          using hfx h1I h1G by simp
        thus ?thesis using hxX by simp
      qed

      have hC_sub_V: "C \<subseteq> ?V"
      proof (rule subsetI)
        fix z assume hzC: "z \<in> C"
        have hzX: "z \<in> X" by (rule subsetD[OF closedin_sub[OF hCcl] hzC])
        have hfz: "f z = 0" using hfC0 hzC by (rule bspec)
        have h0I: "0 \<in> ?I"
          unfolding top1_closed_interval_def by simp
        have h0L: "0 \<in> open_ray_lt ?c"
          unfolding open_ray_lt_def by simp
        have "f z \<in> ?L"
          using hfz h0I h0L by simp
        thus "z \<in> ?V" using hzX by simp
      qed

      have hUV_disj: "?U \<inter> ?V = {}"
      proof (rule equalityI)
        show "?U \<inter> ?V \<subseteq> {}"
		        proof (rule subsetI)
		          fix z assume hz: "z \<in> ?U \<inter> ?V"
		          have hzU: "z \<in> ?U"
		            using hz by simp
		          have hzV: "z \<in> ?V"
		            using hz by simp
		          have hzG: "f z \<in> ?G"
		            using hzU by simp
		          have hzL: "f z \<in> ?L"
		            using hzV by simp
		          have "f z \<in> ?G \<inter> ?L"
		            by (rule IntI[OF hzG hzL])
		          hence False using hdisj_cod by simp
		          thus "z \<in> {}" by simp
		        qed
	        show "{} \<subseteq> ?U \<inter> ?V" by (rule empty_subsetI)
	      qed

      have hnbhd: "neighborhood_of x X TX ?U"
        unfolding neighborhood_of_def
        apply (intro conjI)
         apply (rule hU_open)
        apply (rule hxc)
        done

      show "\<exists>U V. neighborhood_of x X TX U \<and> V \<in> TX \<and> C \<subseteq> V \<and> U \<inter> V = {}"
        apply (rule exI[where x="?U"])
        apply (rule exI[where x="?V"])
        apply (intro conjI)
           apply (rule hnbhd)
          apply (rule hV_open)
         apply (rule hC_sub_V)
        apply (rule hUV_disj)
        done
    qed
  qed
qed

(** from \S33 Theorem 33.2 (Subspaces of completely regular spaces are completely regular)
    [top1.tex:4542] **)
theorem Theorem_33_2_subspace:
  assumes hCR: "top1_completely_regular_on X TX"
  assumes hYX: "Y \<subseteq> X"
  shows "top1_completely_regular_on Y (subspace_topology X TX Y)"
proof -
  let ?TY = "subspace_topology X TX Y"
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"

  have hT1X: "top1_T1_on X TX"
    using hCR unfolding top1_completely_regular_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1X unfolding top1_T1_on_def by (rule conjunct1)

  have hTopY: "is_topology_on Y ?TY"
    by (rule subspace_topology_is_topology_on[OF hTopX hYX])

  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    apply (rule subspace_topology_is_topology_on)
     apply (rule order_topology_on_UNIV_is_topology_on)
    apply simp
    done

  have hSepX:
    "\<forall>x0\<in>X. \<forall>A. closedin_on X TX A \<and> x0 \<notin> A \<longrightarrow>
       (\<exists>f::'a \<Rightarrow> real.
           top1_continuous_map_on X TX ?I ?TI f \<and> f x0 = 1 \<and> (\<forall>x\<in>A. f x = 0))"
    using hCR unfolding top1_completely_regular_on_def by (rule conjunct2)

  have hT1Y: "top1_T1_on Y ?TY"
  proof (unfold top1_T1_on_def, intro conjI)
    show "is_topology_on Y ?TY" by (rule hTopY)
    show "\<forall>y\<in>Y. closedin_on Y ?TY {y}"
    proof (intro ballI)
      fix y assume hyY: "y \<in> Y"
      have hyX: "y \<in> X" using hyY hYX by blast
      have hsingX: "closedin_on X TX {y}"
        using hT1X hyX unfolding top1_T1_on_def by blast
      have hiff: "closedin_on Y ?TY {y} \<longleftrightarrow> (\<exists>C. closedin_on X TX C \<and> {y} = C \<inter> Y)"
        by (rule Theorem_17_2[OF hTopX hYX])
      have hex: "\<exists>C. closedin_on X TX C \<and> {y} = C \<inter> Y"
        apply (rule exI[where x="{y}"])
        apply (intro conjI)
         apply (rule hsingX)
        using hyY by blast
      show "closedin_on Y ?TY {y}"
        using hiff hex by blast
    qed
  qed

  show ?thesis
    unfolding top1_completely_regular_on_def
  proof (intro conjI)
    show "top1_T1_on Y ?TY" by (rule hT1Y)
    show "\<forall>y0\<in>Y. \<forall>A. closedin_on Y ?TY A \<and> y0 \<notin> A \<longrightarrow>
      (\<exists>f::'a \<Rightarrow> real.
          top1_continuous_map_on Y ?TY ?I ?TI f \<and> f y0 = 1 \<and> (\<forall>x\<in>A. f x = 0))"
    proof (intro ballI allI impI)
      fix y0 A
      assume hy0Y: "y0 \<in> Y"
      assume hA0: "closedin_on Y ?TY A \<and> y0 \<notin> A"
      have hAclY: "closedin_on Y ?TY A" and hy0A: "y0 \<notin> A"
        using hA0 by blast+

      have hAsubY: "A \<subseteq> Y" by (rule closedin_sub[OF hAclY])
      have hAsubX: "A \<subseteq> X" using hAsubY hYX by blast
      have hy0X: "y0 \<in> X" using hy0Y hYX by blast

      let ?C = "closure_on X TX A"

      have hCcl: "closedin_on X TX ?C"
        by (rule closure_on_closed[OF hTopX hAsubX])

      have hclY_eq: "closure_on Y ?TY A = A"
      proof (rule equalityI)
        show "closure_on Y ?TY A \<subseteq> A"
          by (rule closure_on_subset_of_closed[OF hAclY subset_refl])
        show "A \<subseteq> closure_on Y ?TY A"
          by (rule subset_closure_on)
      qed

      have hcl_subspace: "closure_on Y ?TY A = closure_on X TX A \<inter> Y"
        by (rule Theorem_17_4[OF hTopX hAsubY hYX])

      have hy0notC: "y0 \<notin> ?C"
      proof
        assume hy0C: "y0 \<in> ?C"
        have "y0 \<in> ?C \<inter> Y" using hy0C hy0Y by blast
        hence "y0 \<in> closure_on Y ?TY A"
          using hcl_subspace by simp
        hence "y0 \<in> A"
          using hclY_eq by simp
        thus False using hy0A by contradiction
      qed

      have hSepy0:
        "\<forall>B. closedin_on X TX B \<and> y0 \<notin> B \<longrightarrow>
           (\<exists>f::'a \<Rightarrow> real.
               top1_continuous_map_on X TX ?I ?TI f \<and> f y0 = 1 \<and> (\<forall>x\<in>B. f x = 0))"
        by (rule bspec[OF hSepX hy0X])

      have hSepC:
        "closedin_on X TX ?C \<and> y0 \<notin> ?C \<longrightarrow>
           (\<exists>f::'a \<Rightarrow> real.
               top1_continuous_map_on X TX ?I ?TI f \<and> f y0 = 1 \<and> (\<forall>x\<in>?C. f x = 0))"
        by (rule spec[where x="?C", OF hSepy0])

      have hexF:
        "\<exists>f::'a \<Rightarrow> real.
          top1_continuous_map_on X TX ?I ?TI f \<and> f y0 = 1 \<and> (\<forall>x\<in>?C. f x = 0)"
        apply (rule mp[OF hSepC])
        apply (intro conjI)
         apply (rule hCcl)
        apply (rule hy0notC)
        done

      obtain f where hfcontX: "top1_continuous_map_on X TX ?I ?TI f"
          and hfy0: "f y0 = 1" and hfC: "\<forall>x\<in>?C. f x = 0"
        using hexF by blast

      have hfcontY: "top1_continuous_map_on Y ?TY ?I ?TI f"
      proof -
        have hRules: "\<forall>A f. top1_continuous_map_on X TX ?I ?TI f \<and> A \<subseteq> X
           \<longrightarrow> top1_continuous_map_on A (subspace_topology X TX A) ?I ?TI f"
          by (rule Theorem_18_2(4)[OF hTopX hTopI hTopI])
        have h1: "\<forall>g. top1_continuous_map_on X TX ?I ?TI g \<and> Y \<subseteq> X
           \<longrightarrow> top1_continuous_map_on Y (subspace_topology X TX Y) ?I ?TI g"
          by (rule spec[where x=Y, OF hRules])
        have hImp: "top1_continuous_map_on X TX ?I ?TI f \<and> Y \<subseteq> X
           \<longrightarrow> top1_continuous_map_on Y (subspace_topology X TX Y) ?I ?TI f"
          by (rule spec[where x=f, OF h1])
        have hPrem: "top1_continuous_map_on X TX ?I ?TI f \<and> Y \<subseteq> X"
          apply (intro conjI)
           apply (rule hfcontX)
          apply (rule hYX)
          done
        show ?thesis
          by (rule mp[OF hImp hPrem])
      qed

      have hA_sub_C: "A \<subseteq> ?C"
        by (rule subset_closure_on)

      have hfA: "\<forall>x\<in>A. f x = 0"
      proof (intro ballI)
        fix x assume hxA: "x \<in> A"
        have hxC: "x \<in> ?C" using hA_sub_C hxA by blast
        show "f x = 0" using hfC hxC by blast
      qed

      show "\<exists>f::'a \<Rightarrow> real.
          top1_continuous_map_on Y ?TY ?I ?TI f \<and> f y0 = 1 \<and> (\<forall>x\<in>A. f x = 0)"
        apply (rule exI[where x=f])
        apply (intro conjI)
          apply (rule hfcontY)
         apply (rule hfy0)
        apply (rule hfA)
        done
    qed
  qed
qed

(** Continuity of the binary operation \<open>min\<close> on the unit interval, with respect to the
    subspace order topology. This is a small piece of "real-analytic" infrastructure needed
    for product constructions in \S33. **)
lemma top1_continuous_min_unit_interval:
  shows "top1_continuous_map_on
      (top1_closed_interval 0 1 \<times> top1_closed_interval 0 1)
      (product_topology_on (top1_closed_interval_topology 0 1) (top1_closed_interval_topology 0 1))
      (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)
      (\<lambda>p::real \<times> real. min (pi1 p) (pi2 p))"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?m = "(\<lambda>p::real \<times> real. min (pi1 p) (pi2 p))"

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hI_UNIV: "?I \<subseteq> (UNIV::real set)"
    by simp

  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF hTopR], rule hI_UNIV)

  have hTopII: "is_topology_on (?I \<times> ?I) (product_topology_on ?TI ?TI)"
    by (rule product_topology_on_is_topology_on[OF hTopI hTopI])

  have hI_in_TI: "?I \<in> ?TI"
    using hTopI unfolding is_topology_on_def by blast

  have union_TII: "\<forall>U. U \<subseteq> (product_topology_on ?TI ?TI) \<longrightarrow> (\<Union>U) \<in> (product_topology_on ?TI ?TI)"
    using hTopII unfolding is_topology_on_def by blast

  have hray_gt_TI: "\<forall>a. ?I \<inter> open_ray_gt a \<in> ?TI"
  proof (intro allI)
    fix a
    show "?I \<inter> open_ray_gt a \<in> ?TI"
      unfolding top1_closed_interval_topology_def subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="open_ray_gt a"])
      apply (intro conjI)
       apply simp
      apply (rule open_ray_gt_in_order_topology)
      done
  qed

  have hray_lt_TI: "\<forall>a. ?I \<inter> open_ray_lt a \<in> ?TI"
  proof (intro allI)
    fix a
    show "?I \<inter> open_ray_lt a \<in> ?TI"
      unfolding top1_closed_interval_topology_def subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="open_ray_lt a"])
      apply (intro conjI)
       apply simp
      apply (rule open_ray_lt_in_order_topology)
      done
  qed

  have hinterval_TI: "\<forall>a b. a < b \<longrightarrow> ?I \<inter> open_interval a b \<in> ?TI"
  proof (intro allI impI)
    fix a b :: real
    assume hab: "a < b"
    show "?I \<inter> open_interval a b \<in> ?TI"
      unfolding top1_closed_interval_topology_def subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="open_interval a b"])
      apply (intro conjI)
       apply simp
      apply (rule open_interval_in_order_topology[OF hab])
      done
  qed

  have hm_cont_R: "top1_continuous_map_on (?I \<times> ?I) (product_topology_on ?TI ?TI)
      (UNIV::real set) order_topology_on_UNIV ?m"
  proof -
    have hBasisR: "basis_for (UNIV::real set) basis_order_topology order_topology_on_UNIV"
      by (rule basis_for_order_topology_on_UNIV)

    have hpre: "\<forall>b\<in>(basis_order_topology::real set set).
        {p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> basis_order_topology"
      have hcases:
        "(\<exists>a c. a < c \<and> b = open_interval a c)
         \<or> (\<exists>a. b = open_ray_gt a)
         \<or> (\<exists>a. b = open_ray_lt a)
         \<or> b = (UNIV::real set)"
        by (rule basis_order_topology_cases[OF hb])
      show "{p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
      proof (rule disjE[OF hcases])
        assume hbint: "\<exists>a c. a < c \<and> b = open_interval a c"
        then obtain a c where hac: "a < c" and hbeq: "b = open_interval a c"
          by blast
        let ?U = "?I \<inter> open_interval a c"
        let ?G = "?I \<inter> open_ray_gt a"

        have hU_TI: "?U \<in> ?TI"
          using hinterval_TI hac by blast
        have hG_TI: "?G \<in> ?TI"
          using hray_gt_TI by blast

        have hUrect: "?U \<times> ?G \<in> product_topology_on ?TI ?TI"
          by (rule product_rect_open[OF hU_TI hG_TI])
        have hGrect: "?G \<times> ?U \<in> product_topology_on ?TI ?TI"
          by (rule product_rect_open[OF hG_TI hU_TI])

	          have hUn: "(\<Union>{?U \<times> ?G, ?G \<times> ?U}) \<in> product_topology_on ?TI ?TI"
	        proof -
	          have "{?U \<times> ?G, ?G \<times> ?U} \<subseteq> product_topology_on ?TI ?TI"
	          proof -
	            have hsub1: "{?G \<times> ?U} \<subseteq> product_topology_on ?TI ?TI"
	              apply (rule insert_subsetI)
	               apply (rule hGrect)
	              apply simp
	              done
	            show ?thesis
	              apply (rule insert_subsetI)
	               apply (rule hUrect)
	              apply (rule hsub1)
	              done
	          qed
	          show ?thesis
	            using union_TII \<open>{?U \<times> ?G, ?G \<times> ?U} \<subseteq> product_topology_on ?TI ?TI\<close> by blast
	        qed

        have hEq:
          "{p \<in> ?I \<times> ?I. ?m p \<in> b} = (?U \<times> ?G) \<union> (?G \<times> ?U)"
        proof (rule set_eqI)
          fix p
          show "p \<in> {p \<in> ?I \<times> ?I. ?m p \<in> b} \<longleftrightarrow> p \<in> (?U \<times> ?G) \<union> (?G \<times> ?U)"
          proof
            assume hp: "p \<in> {p \<in> ?I \<times> ?I. ?m p \<in> b}"
            have hpmem:
              "p \<in> ?I \<times> ?I \<and> a < fst p \<and> a < snd p \<and> (fst p < c \<or> snd p < c)"
              using hp unfolding hbeq top1_closed_interval_def open_interval_def open_ray_gt_def pi1_def pi2_def
              by (simp add: min_less_iff_conj min_less_iff_disj)
            have hpI: "p \<in> ?I \<times> ?I"
              using hpmem by blast
            have ha: "a < fst p"
              using hpmem by blast
            have hb': "a < snd p"
              using hpmem by blast
            have hdisc: "fst p < c \<or> snd p < c"
              using hpmem by blast
            have hfstI: "fst p \<in> ?I"
              using hpI by (cases p, simp add: mem_Times_iff)
            have hsndI: "snd p \<in> ?I"
              using hpI by (cases p, simp add: mem_Times_iff)
            show "p \<in> (?U \<times> ?G) \<union> (?G \<times> ?U)"
            proof (cases "fst p < c")
              case True
              have hfstU: "fst p \<in> ?U"
                using hfstI ha True by (simp add: open_interval_def)
              have hsndG: "snd p \<in> ?G"
                using hsndI hb' by (simp add: open_ray_gt_def)
              have "p \<in> ?U \<times> ?G"
                using hfstU hsndG by (cases p, simp add: mem_Times_iff)
              thus ?thesis by blast
            next
              case False
              have hsndc: "snd p < c"
                using hdisc False by blast
              have hsndU: "snd p \<in> ?U"
                using hsndI hb' hsndc by (simp add: open_interval_def)
              have hfstG: "fst p \<in> ?G"
                using hfstI ha by (simp add: open_ray_gt_def)
              have "p \<in> ?G \<times> ?U"
                using hfstG hsndU by (cases p, simp add: mem_Times_iff)
              thus ?thesis by blast
            qed
          next
            assume hp: "p \<in> (?U \<times> ?G) \<union> (?G \<times> ?U)"
            have hp1: "p \<in> ?U \<times> ?G \<or> p \<in> ?G \<times> ?U"
              using hp by blast
            show "p \<in> {p \<in> ?I \<times> ?I. ?m p \<in> b}"
            proof (rule disjE[OF hp1])
              assume hUG: "p \<in> ?U \<times> ?G"
              have hfstU: "fst p \<in> ?U"
                using hUG by (cases p, simp add: mem_Times_iff)
              have hsndG: "snd p \<in> ?G"
                using hUG by (cases p, simp add: mem_Times_iff)
              have hfstmem: "fst p \<in> ?I \<and> a < fst p \<and> fst p < c"
                using hfstU by (simp add: open_interval_def)
              have hfstI: "fst p \<in> ?I"
                using hfstmem by blast
              have ha: "a < fst p"
                using hfstmem by blast
              have hfstc: "fst p < c"
                using hfstmem by blast

              have hsndmem: "snd p \<in> ?I \<and> a < snd p"
                using hsndG by (simp add: open_ray_gt_def)
              have hsndI: "snd p \<in> ?I"
                using hsndmem by blast
              have hb': "a < snd p"
                using hsndmem by blast
              have hpI: "p \<in> ?I \<times> ?I"
                using hfstI hsndI by (cases p, simp add: mem_Times_iff)
              have "?m p \<in> b"
                using ha hb' hfstc unfolding hbeq open_interval_def open_ray_gt_def pi1_def pi2_def
                by (simp add: min_less_iff_conj min_less_iff_disj)
              thus ?thesis
                using hpI by simp
            next
              assume hGU: "p \<in> ?G \<times> ?U"
              have hfstG: "fst p \<in> ?G"
                using hGU by (cases p, simp add: mem_Times_iff)
              have hsndU: "snd p \<in> ?U"
                using hGU by (cases p, simp add: mem_Times_iff)
              have hfstmem: "fst p \<in> ?I \<and> a < fst p"
                using hfstG by (simp add: open_ray_gt_def)
              have hfstI: "fst p \<in> ?I"
                using hfstmem by blast
              have ha: "a < fst p"
                using hfstmem by blast

              have hsndmem: "snd p \<in> ?I \<and> a < snd p \<and> snd p < c"
                using hsndU by (simp add: open_interval_def)
              have hsndI: "snd p \<in> ?I"
                using hsndmem by blast
              have hb': "a < snd p"
                using hsndmem by blast
              have hsndc: "snd p < c"
                using hsndmem by blast
              have hpI: "p \<in> ?I \<times> ?I"
                using hfstI hsndI by (cases p, simp add: mem_Times_iff)
              have "?m p \<in> b"
                using ha hb' hsndc unfolding hbeq open_interval_def open_ray_gt_def pi1_def pi2_def
                by (simp add: min_less_iff_conj min_less_iff_disj)
              thus ?thesis
                using hpI by simp
            qed
          qed
        qed

        show "{p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
          using hUn hEq by simp
      next
        assume hbgt: "(\<exists>a. b = open_ray_gt a)
          \<or> (\<exists>a. b = open_ray_lt a)
          \<or> b = (UNIV::real set)"
          show "{p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
          proof (rule disjE[OF hbgt])
            assume hbgt': "\<exists>a. b = open_ray_gt a"
            then obtain a where hbeq: "b = open_ray_gt a" by blast
          let ?G = "?I \<inter> open_ray_gt a"
          have hG_TI: "?G \<in> ?TI"
            using hray_gt_TI by blast
          have hrect: "?G \<times> ?G \<in> product_topology_on ?TI ?TI"
            by (rule product_rect_open[OF hG_TI hG_TI])
          have hEq:
            "{p \<in> ?I \<times> ?I. ?m p \<in> b} = ?G \<times> ?G"
          proof (rule set_eqI)
	            fix p
	            show "p \<in> {p \<in> ?I \<times> ?I. ?m p \<in> b} \<longleftrightarrow> p \<in> ?G \<times> ?G"
	              unfolding hbeq top1_closed_interval_def open_ray_gt_def pi1_def pi2_def
	              by (cases p, simp add: hbeq top1_closed_interval_def open_ray_gt_def pi1_def pi2_def
	                mem_Times_iff min_less_iff_conj conj_assoc conj_commute conj_left_commute)
          qed
	          show "{p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
	            using hrect hEq by simp
	        next
          assume hblt: "(\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
            show "{p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
          proof (rule disjE[OF hblt])
            assume hblt': "\<exists>a. b = open_ray_lt a"
            then obtain a where hbeq: "b = open_ray_lt a" by blast
            let ?L = "?I \<inter> open_ray_lt a"

            have hL_TI: "?L \<in> ?TI"
              using hray_lt_TI by blast
            have hLrect: "?L \<times> ?I \<in> product_topology_on ?TI ?TI"
              by (rule product_rect_open[OF hL_TI hI_in_TI])
            have hRrect: "?I \<times> ?L \<in> product_topology_on ?TI ?TI"
              by (rule product_rect_open[OF hI_in_TI hL_TI])

	            have hUn: "(\<Union>{?L \<times> ?I, ?I \<times> ?L}) \<in> product_topology_on ?TI ?TI"
	            proof -
	              have "{?L \<times> ?I, ?I \<times> ?L} \<subseteq> product_topology_on ?TI ?TI"
	              proof -
	                have hsub1: "{?I \<times> ?L} \<subseteq> product_topology_on ?TI ?TI"
	                  apply (rule insert_subsetI)
	                   apply (rule hRrect)
	                  apply simp
	                  done
	                show ?thesis
	                  apply (rule insert_subsetI)
	                   apply (rule hLrect)
	                  apply (rule hsub1)
	                  done
	              qed
	              show ?thesis
	                using union_TII \<open>{?L \<times> ?I, ?I \<times> ?L} \<subseteq> product_topology_on ?TI ?TI\<close> by blast
	            qed

            have hEq:
              "{p \<in> ?I \<times> ?I. ?m p \<in> b} = (?L \<times> ?I) \<union> (?I \<times> ?L)"
            proof (rule set_eqI)
              fix p
	              show "p \<in> {p \<in> ?I \<times> ?I. ?m p \<in> b} \<longleftrightarrow> p \<in> (?L \<times> ?I) \<union> (?I \<times> ?L)"
	                unfolding hbeq top1_closed_interval_def open_ray_lt_def pi1_def pi2_def
	                by (cases p, simp add: mem_Times_iff min_less_iff_disj conj_disj_distribL
	                  conj_assoc conj_commute conj_left_commute)
	            qed

            show "{p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
              using hUn hEq by simp
          next
            assume hbeq: "b = (UNIV::real set)"
            have hrect: "?I \<times> ?I \<in> product_topology_on ?TI ?TI"
              by (rule product_rect_open[OF hI_in_TI hI_in_TI])
            have hEq: "{p \<in> ?I \<times> ?I. ?m p \<in> b} = ?I \<times> ?I"
              unfolding hbeq by simp
            show "{p \<in> ?I \<times> ?I. ?m p \<in> b} \<in> product_topology_on ?TI ?TI"
              using hrect hEq by simp
          qed
        qed
      qed
    qed

    have hmap: "\<forall>p\<in>?I \<times> ?I. ?m p \<in> (UNIV::real set)"
      by simp

    show ?thesis
      by (rule top1_continuous_map_on_generated_by_basis[OF hTopII hBasisR hmap hpre])
  qed

  have hm_image: "?m ` (?I \<times> ?I) \<subseteq> ?I"
  proof (rule subsetI)
    fix t assume ht: "t \<in> ?m ` (?I \<times> ?I)"
	    then obtain p where hp: "p \<in> ?I \<times> ?I" and htdef: "t = ?m p"
	      by blast
	    have hpi12: "pi1 p \<in> ?I \<and> pi2 p \<in> ?I"
	      using hp unfolding pi1_def pi2_def by (simp add: mem_Times_iff)
	    have hpi1: "pi1 p \<in> ?I"
	      by (rule conjunct1[OF hpi12])
	    have hpi2: "pi2 p \<in> ?I"
	      by (rule conjunct2[OF hpi12])
    have hpi1': "0 \<le> pi1 p \<and> pi1 p \<le> 1"
      using hpi1 unfolding top1_closed_interval_def by blast
    have hpi2': "0 \<le> pi2 p \<and> pi2 p \<le> 1"
      using hpi2 unfolding top1_closed_interval_def by blast

    have h0: "0 \<le> min (pi1 p) (pi2 p)"
    proof (cases "pi1 p \<le> pi2 p")
      case True
      then show ?thesis using hpi1' unfolding min_def by simp
    next
      case False
      then show ?thesis using hpi2' unfolding min_def by simp
    qed

    have h1: "min (pi1 p) (pi2 p) \<le> 1"
    proof (cases "pi1 p \<le> pi2 p")
      case True
      then show ?thesis using hpi1' unfolding min_def by simp
    next
      case False
      then show ?thesis using hpi2' unfolding min_def by simp
    qed

    show "t \<in> ?I"
      unfolding htdef top1_closed_interval_def
      using h0 h1 by blast
  qed

  have hm_cont_I: "top1_continuous_map_on (?I \<times> ?I) (product_topology_on ?TI ?TI) ?I ?TI ?m"
  proof -
    have hTopProd: "is_topology_on (?I \<times> ?I) (product_topology_on ?TI ?TI)"
      by (rule hTopII)
    have hTopR': "is_topology_on (UNIV::real set) order_topology_on_UNIV"
      by (rule hTopR)
    have hRR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
      by (rule hTopR)
    have hRule:
      "\<forall>W f. top1_continuous_map_on (?I \<times> ?I) (product_topology_on ?TI ?TI) (UNIV::real set) order_topology_on_UNIV f
           \<and> W \<subseteq> (UNIV::real set) \<and> f ` (?I \<times> ?I) \<subseteq> W
           \<longrightarrow> top1_continuous_map_on (?I \<times> ?I) (product_topology_on ?TI ?TI) W
                (subspace_topology (UNIV::real set) order_topology_on_UNIV W) f"
      by (rule Theorem_18_2(5)[OF hTopProd hTopR' hRR])

    have hSubspace: "subspace_topology (UNIV::real set) order_topology_on_UNIV ?I = ?TI"
      unfolding top1_closed_interval_topology_def by simp

    have "top1_continuous_map_on (?I \<times> ?I) (product_topology_on ?TI ?TI) ?I
            (subspace_topology (UNIV::real set) order_topology_on_UNIV ?I) ?m"
      apply (rule hRule[rule_format, of ?m ?I])
      apply (intro conjI)
       apply (rule hm_cont_R)
       apply simp
       apply (rule hm_image)
      done
    thus ?thesis
      using hSubspace by simp
  qed

  show ?thesis
    by (rule hm_cont_I)
qed

(** Product part of Theorem 33.2 (proved in top1.tex for arbitrary products). The present
    development only contains a binary product topology and does not yet have the needed
    real-analytic infrastructure (continuous arithmetic on the unit interval). **)
theorem Theorem_33_2_product:
  assumes hCRX: "top1_completely_regular_on X TX"
  assumes hCRY: "top1_completely_regular_on Y TY"
  shows "top1_completely_regular_on (X \<times> Y) (product_topology_on TX TY)"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?TP = "product_topology_on TX TY"
  let ?m = "(\<lambda>q::real \<times> real. min (pi1 q) (pi2 q))"

  have hT1X: "top1_T1_on X TX"
    using hCRX unfolding top1_completely_regular_on_def by blast
  have hT1Y: "top1_T1_on Y TY"
    using hCRY unfolding top1_completely_regular_on_def by blast

  have hTopX: "is_topology_on X TX"
    using hT1X unfolding top1_T1_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hT1Y unfolding top1_T1_on_def by blast
  have hTopXY: "is_topology_on (X \<times> Y) ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopX hTopY])

  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    apply (rule subspace_topology_is_topology_on)
     apply (rule order_topology_on_UNIV_is_topology_on)
    apply simp
    done
  have hTopII: "is_topology_on (?I \<times> ?I) (product_topology_on ?TI ?TI)"
    by (rule product_topology_on_is_topology_on[OF hTopI hTopI])

  have hRegX: "top1_regular_on X TX"
    by (rule completely_regular_imp_regular_on[OF hCRX])
  have hRegY: "top1_regular_on Y TY"
    by (rule completely_regular_imp_regular_on[OF hCRY])
  have hHausdX: "is_hausdorff_on X TX"
    by (rule regular_imp_hausdorff_on[OF hRegX])
  have hHausdY: "is_hausdorff_on Y TY"
    by (rule regular_imp_hausdorff_on[OF hRegY])

  have hHausdProd: "is_hausdorff_on (X \<times> Y) ?TP"
  proof -
    have hprod: "\<forall>X1 T1 X2 T2.
        is_hausdorff_on X1 T1 \<and> is_hausdorff_on X2 T2 \<longrightarrow>
        is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2)"
      using Theorem_17_11 by blast
    have hImp: "is_hausdorff_on X TX \<and> is_hausdorff_on Y TY \<longrightarrow> is_hausdorff_on (X \<times> Y) ?TP"
      using hprod by blast
    have hPrem: "is_hausdorff_on X TX \<and> is_hausdorff_on Y TY"
      using hHausdX hHausdY by blast
    show ?thesis
      by (rule mp[OF hImp hPrem])
  qed

  have hT1Prod: "top1_T1_on (X \<times> Y) ?TP"
    by (rule hausdorff_imp_T1_on[OF hHausdProd])

  have hSepX:
    "\<forall>x0\<in>X. \<forall>A. closedin_on X TX A \<and> x0 \<notin> A \<longrightarrow>
       (\<exists>f::'a \<Rightarrow> real.
           top1_continuous_map_on X TX ?I ?TI f \<and> f x0 = 1 \<and> (\<forall>x\<in>A. f x = 0))"
    using hCRX unfolding top1_completely_regular_on_def by blast
  have hSepY:
    "\<forall>y0\<in>Y. \<forall>B. closedin_on Y TY B \<and> y0 \<notin> B \<longrightarrow>
       (\<exists>g::'b \<Rightarrow> real.
           top1_continuous_map_on Y TY ?I ?TI g \<and> g y0 = 1 \<and> (\<forall>y\<in>B. g y = 0))"
    using hCRY unfolding top1_completely_regular_on_def by blast

  show ?thesis
    unfolding top1_completely_regular_on_def
  proof (intro conjI)
    show "top1_T1_on (X \<times> Y) ?TP"
      by (rule hT1Prod)
    show "\<forall>p0\<in>X \<times> Y. \<forall>A. closedin_on (X \<times> Y) ?TP A \<and> p0 \<notin> A \<longrightarrow>
       (\<exists>F::('a \<times> 'b) \<Rightarrow> real.
           top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI F \<and> F p0 = 1 \<and> (\<forall>p\<in>A. F p = 0))"
    proof (intro ballI allI impI)
      fix p0 A
      assume hp0: "p0 \<in> X \<times> Y"
      assume hA0: "closedin_on (X \<times> Y) ?TP A \<and> p0 \<notin> A"
      have hAcl: "closedin_on (X \<times> Y) ?TP A" and hp0A: "p0 \<notin> A"
        using hA0 by blast+

      have hAsub: "A \<subseteq> X \<times> Y"
        by (rule closedin_sub[OF hAcl])
      have hWopen: "(X \<times> Y) - A \<in> ?TP"
        using hAcl unfolding closedin_on_def by blast
      have hp0W: "p0 \<in> (X \<times> Y) - A"
        using hp0 hp0A by blast

      have hWcov: "\<forall>p\<in>(X \<times> Y) - A. \<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> (X \<times> Y) - A"
        using hWopen unfolding product_topology_on_def topology_generated_by_basis_def by blast

      obtain b where hb: "b \<in> product_basis TX TY" and hp0b: "p0 \<in> b" and hbsub: "b \<subseteq> (X \<times> Y) - A"
        using hWcov[rule_format, OF hp0W] by blast
      obtain U V where hU: "U \<in> TX" and hV: "V \<in> TY" and hbeq: "b = U \<times> V"
        using hb unfolding product_basis_def by blast

      have hp0UV: "p0 \<in> U \<times> V"
        using hp0b unfolding hbeq .

      let ?x0 = "pi1 p0"
      let ?y0 = "pi2 p0"
      have hx0: "?x0 \<in> X"
        using hp0 unfolding pi1_def by (simp add: mem_Times_iff)
      have hy0: "?y0 \<in> Y"
        using hp0 unfolding pi2_def by (simp add: mem_Times_iff)
      have hx0U: "?x0 \<in> U"
        using hp0UV unfolding pi1_def by (simp add: mem_Times_iff)
      have hy0V: "?y0 \<in> V"
        using hp0UV unfolding pi2_def by (simp add: mem_Times_iff)

      let ?CX = "X - U"
      let ?CY = "Y - V"

      have hXopen: "X \<in> TX"
        using hTopX unfolding is_topology_on_def by blast
      have hYopen: "Y \<in> TY"
        using hTopY unfolding is_topology_on_def by blast

      have hCXcl: "closedin_on X TX ?CX"
        unfolding closedin_on_def
      proof (intro conjI)
        show "X - U \<subseteq> X" by simp
        have "X \<inter> U \<in> TX"
          by (rule topology_inter2[OF hTopX hXopen hU])
        moreover have "X - (X - U) = X \<inter> U" by blast
        ultimately show "X - (X - U) \<in> TX" by simp
      qed

      have hCYcl: "closedin_on Y TY ?CY"
        unfolding closedin_on_def
      proof (intro conjI)
        show "Y - V \<subseteq> Y" by simp
        have "Y \<inter> V \<in> TY"
          by (rule topology_inter2[OF hTopY hYopen hV])
        moreover have "Y - (Y - V) = Y \<inter> V" by blast
        ultimately show "Y - (Y - V) \<in> TY" by simp
      qed

      have hx0notCX: "?x0 \<notin> ?CX"
        using hx0U by blast
      have hy0notCY: "?y0 \<notin> ?CY"
        using hy0V by blast

      have hSepx0:
        "\<forall>A. closedin_on X TX A \<and> ?x0 \<notin> A \<longrightarrow>
           (\<exists>f::'a \<Rightarrow> real.
               top1_continuous_map_on X TX ?I ?TI f \<and> f ?x0 = 1 \<and> (\<forall>x\<in>A. f x = 0))"
        by (rule bspec[OF hSepX hx0])
      have hSepy0:
        "\<forall>B. closedin_on Y TY B \<and> ?y0 \<notin> B \<longrightarrow>
           (\<exists>g::'b \<Rightarrow> real.
               top1_continuous_map_on Y TY ?I ?TI g \<and> g ?y0 = 1 \<and> (\<forall>y\<in>B. g y = 0))"
        by (rule bspec[OF hSepY hy0])

      have hexF:
        "\<exists>f::'a \<Rightarrow> real.
          top1_continuous_map_on X TX ?I ?TI f \<and> f ?x0 = 1 \<and> (\<forall>x\<in>?CX. f x = 0)"
        apply (rule mp[OF spec[where x="?CX", OF hSepx0]])
        apply (intro conjI)
         apply (rule hCXcl)
        apply (rule hx0notCX)
        done
      have hexG:
        "\<exists>g::'b \<Rightarrow> real.
          top1_continuous_map_on Y TY ?I ?TI g \<and> g ?y0 = 1 \<and> (\<forall>y\<in>?CY. g y = 0)"
        apply (rule mp[OF spec[where x="?CY", OF hSepy0]])
        apply (intro conjI)
         apply (rule hCYcl)
        apply (rule hy0notCY)
        done

      obtain f where hfcont: "top1_continuous_map_on X TX ?I ?TI f"
          and hfx0: "f ?x0 = 1" and hfCX: "\<forall>x\<in>?CX. f x = 0"
        using hexF by blast
      obtain g where hgcont: "top1_continuous_map_on Y TY ?I ?TI g"
          and hgy0: "g ?y0 = 1" and hgCY: "\<forall>y\<in>?CY. g y = 0"
        using hexG by blast

      define h where "h = (\<lambda>p::('a \<times> 'b). (f (pi1 p), g (pi2 p)))"
      define F where "F = (?m \<circ> h)"

      have hpi1: "top1_continuous_map_on (X \<times> Y) ?TP X TX pi1"
        by (rule top1_continuous_pi1[OF hTopX hTopY])
      have hpi2: "top1_continuous_map_on (X \<times> Y) ?TP Y TY pi2"
        by (rule top1_continuous_pi2[OF hTopX hTopY])

      have hfpi1: "top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (f \<circ> pi1)"
        by (rule top1_continuous_map_on_comp[OF hpi1 hfcont])
      have hgpi2: "top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (g \<circ> pi2)"
        by (rule top1_continuous_map_on_comp[OF hpi2 hgcont])

      have hcont: "top1_continuous_map_on (X \<times> Y) ?TP (?I \<times> ?I) (product_topology_on ?TI ?TI) h"
      proof -
        have hEq1: "pi1 \<circ> h = f \<circ> pi1"
          unfolding h_def by (rule ext, simp add: pi1_def pi2_def)
        have hEq2: "pi2 \<circ> h = g \<circ> pi2"
          unfolding h_def by (rule ext, simp add: pi1_def pi2_def)
        have h1: "top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (pi1 \<circ> h)"
          using hfpi1 hEq1 by simp
        have h2: "top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (pi2 \<circ> h)"
          using hgpi2 hEq2 by simp
        have hiff:
          "top1_continuous_map_on (X \<times> Y) ?TP (?I \<times> ?I) (product_topology_on ?TI ?TI) h
           \<longleftrightarrow>
           (top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (pi1 \<circ> h)
            \<and> top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (pi2 \<circ> h))"
          by (rule Theorem_18_4[OF hTopXY hTopI hTopI])
        have "top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (pi1 \<circ> h)
              \<and> top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI (pi2 \<circ> h)"
          using h1 h2 by blast
        thus ?thesis
          by (rule iffD2[OF hiff])
      qed

      have hm_cont: "top1_continuous_map_on (?I \<times> ?I) (product_topology_on ?TI ?TI) ?I ?TI ?m"
        by (rule top1_continuous_min_unit_interval)

      have hFcont: "top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI F"
        unfolding F_def
        by (rule top1_continuous_map_on_comp[OF hcont hm_cont])

      have hFp0: "F p0 = 1"
      proof -
        have hfx: "f (pi1 p0) = 1"
          using hfx0 by simp
        have hgy: "g (pi2 p0) = 1"
          using hgy0 by simp
        show ?thesis
          unfolding F_def h_def using hfx hgy by (simp add: pi1_def pi2_def)
      qed

      have hFA0: "\<forall>p\<in>A. F p = 0"
      proof (intro ballI)
        fix p assume hpA: "p \<in> A"
        have hpXY: "p \<in> X \<times> Y"
          using hAsub hpA by blast
        have hpnotUV: "p \<notin> U \<times> V"
        proof
          assume hpUV: "p \<in> U \<times> V"
          have "p \<in> (X \<times> Y) - A"
            using hbsub hbeq hpUV by blast
          thus False using hpA by blast
        qed
        have hpdisj: "pi1 p \<notin> U \<or> pi2 p \<notin> V"
          using hpnotUV unfolding pi1_def pi2_def by (simp add: mem_Times_iff)

        have h0: "f (pi1 p) = 0 \<or> g (pi2 p) = 0"
        proof (rule disjE[OF hpdisj])
          assume hnu: "pi1 p \<notin> U"
          have hpx: "pi1 p \<in> X"
            using hpXY unfolding pi1_def by (simp add: mem_Times_iff)
          have "pi1 p \<in> X - U"
            using hpx hnu by blast
          hence "f (pi1 p) = 0"
            using hfCX by blast
          thus ?thesis by blast
        next
          assume hnv: "pi2 p \<notin> V"
          have hpy: "pi2 p \<in> Y"
            using hpXY unfolding pi2_def by (simp add: mem_Times_iff)
          have "pi2 p \<in> Y - V"
            using hpy hnv by blast
          hence "g (pi2 p) = 0"
            using hgCY by blast
          thus ?thesis by blast
        qed

        show "F p = 0"
        proof -
          have hFform: "F p = min (f (pi1 p)) (g (pi2 p))"
            unfolding F_def h_def pi1_def pi2_def by simp

          have hpx: "pi1 p \<in> X"
            using hpXY unfolding pi1_def by (simp add: mem_Times_iff)
          have hpy: "pi2 p \<in> Y"
            using hpXY unfolding pi2_def by (simp add: mem_Times_iff)

          have hfxI: "f (pi1 p) \<in> ?I"
            using hfcont hpx unfolding top1_continuous_map_on_def by blast
          have hgyI: "g (pi2 p) \<in> ?I"
            using hgcont hpy unfolding top1_continuous_map_on_def by blast

          have hfx0le: "0 \<le> f (pi1 p)"
            using hfxI unfolding top1_closed_interval_def by blast
          have hgy0le: "0 \<le> g (pi2 p)"
            using hgyI unfolding top1_closed_interval_def by blast

          show "F p = 0"
          proof (cases "f (pi1 p) = 0")
            case True
            have "f (pi1 p) \<le> g (pi2 p)"
              using hgy0le True by simp
            hence "min (f (pi1 p)) (g (pi2 p)) = f (pi1 p)"
              unfolding min_def by simp
            thus ?thesis
              using True hFform by simp
          next
            case False
            have hg0: "g (pi2 p) = 0"
              using h0 False by blast
            have "g (pi2 p) \<le> f (pi1 p)"
              using hfx0le hg0 by simp
            hence "min (f (pi1 p)) (g (pi2 p)) = g (pi2 p)"
              unfolding min_def by simp
            thus ?thesis
              using hg0 hFform by simp
          qed
        qed
      qed

      show "\<exists>F::('a \<times> 'b) \<Rightarrow> real.
          top1_continuous_map_on (X \<times> Y) ?TP ?I ?TI F \<and> F p0 = 1 \<and> (\<forall>p\<in>A. F p = 0)"
        apply (rule exI[where x=F])
        apply (intro conjI)
          apply (rule hFcont)
         apply (rule hFp0)
        apply (rule hFA0)
        done
    qed
  qed
qed

(** from \S33 Theorem 33.2 (Complete regularity: subspaces and products) [top1.tex:4542] **)
theorem Theorem_33_2:
  shows "(\<forall>X TX Y. top1_completely_regular_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_completely_regular_on Y (subspace_topology X TX Y))"
    and "(\<forall>X TX Y TY. top1_completely_regular_on X TX \<and> top1_completely_regular_on Y TY
            \<longrightarrow> top1_completely_regular_on (X \<times> Y) (product_topology_on TX TY))"
proof -
  show "(\<forall>X TX Y. top1_completely_regular_on X TX \<and> Y \<subseteq> X
            \<longrightarrow> top1_completely_regular_on Y (subspace_topology X TX Y))"
  proof (intro allI impI)
    fix X TX Y
    assume h: "top1_completely_regular_on X TX \<and> Y \<subseteq> X"
    have hCR: "top1_completely_regular_on X TX"
      using h by blast
    have hYX: "Y \<subseteq> X"
      using h by blast
    show "top1_completely_regular_on Y (subspace_topology X TX Y)"
      by (rule Theorem_33_2_subspace[OF hCR hYX])
  qed

  show "(\<forall>X TX Y TY. top1_completely_regular_on X TX \<and> top1_completely_regular_on Y TY
            \<longrightarrow> top1_completely_regular_on (X \<times> Y) (product_topology_on TX TY))"
  proof (intro allI impI)
    fix X TX Y TY
    assume h: "top1_completely_regular_on X TX \<and> top1_completely_regular_on Y TY"
    have hCRX: "top1_completely_regular_on X TX"
      using h by blast
    have hCRY: "top1_completely_regular_on Y TY"
      using h by blast
    show "top1_completely_regular_on (X \<times> Y) (product_topology_on TX TY)"
      by (rule Theorem_33_2_product[OF hCRX hCRY])
  qed
qed

section \<open>\<S>34 The Urysohn Metrization Theorem\<close>

(** from \S34 Theorem 34.1 (Urysohn metrization theorem) [top1.tex:4644] **)
theorem Theorem_34_1:
  assumes hreg: "top1_regular_on X TX"
  assumes h2nd: "top1_second_countable_on X TX"
  shows "top1_metrizable_on X TX"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"

  have hT1: "top1_T1_on X TX"
    using hreg unfolding top1_regular_on_def by blast
  have hTop: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by blast

  have hNormal: "top1_normal_on X TX"
    by (rule Theorem_32_1[OF hreg h2nd])

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hI_UNIV: "?I \<subseteq> (UNIV::real set)"
    by simp
  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF hTopR hI_UNIV])

  obtain B where hBcnt: "top1_countable B" and hBfor: "basis_for X B TX"
    using h2nd unfolding top1_second_countable_on_def by blast

  have hBasis: "is_basis_on X B"
    using hBfor unfolding basis_for_def by blast
  have hTXeq: "TX = topology_generated_by_basis X B"
    using hBfor unfolding basis_for_def by blast

  have hBsubX: "\<forall>b\<in>B. b \<subseteq> X"
    using hBasis unfolding is_basis_on_def by blast

  have hBopen: "\<forall>b\<in>B. b \<in> TX"
  proof (intro ballI)
    fix b assume hbB: "b \<in> B"
    have "b \<in> topology_generated_by_basis X B"
      by (rule basis_elem_open_in_generated_topology[OF hBasis hbB])
    thus "b \<in> TX"
      using hTXeq by simp
  qed

  obtain e :: "'a set \<Rightarrow> nat" where heinj: "inj_on e B"
    using hBcnt unfolding top1_countable_def by blast

  define Bseq where
    "Bseq n =
      (if (\<exists>b\<in>B. e b = n) then (SOME b. b \<in> B \<and> e b = n) else {})" for n

  have Bseq_hit: "\<And>b. b \<in> B \<Longrightarrow> Bseq (e b) = b"
  proof -
	    fix b assume hbB: "b \<in> B"
	    have hex: "\<exists>b'\<in>B. e b' = e b"
	      using hbB by blast
	    have hex': "\<exists>b'. b' \<in> B \<and> e b' = e b"
	      using hex by blast
	    have hsome: "(SOME b'. b' \<in> B \<and> e b' = e b) \<in> B \<and> e (SOME b'. b' \<in> B \<and> e b' = e b) = e b"
	      by (rule someI_ex[OF hex'])
    have hmem: "(SOME b'. b' \<in> B \<and> e b' = e b) \<in> B"
      using hsome by blast
	    have heq: "e (SOME b'. b' \<in> B \<and> e b' = e b) = e b"
	      using hsome by blast
	    have "Bseq (e b) = (SOME b'. b' \<in> B \<and> e b' = e b)"
	      unfolding Bseq_def by (simp add: hex)
	    also have "... = b"
	      using heinj hmem hbB heq unfolding inj_on_def by blast
	    finally show "Bseq (e b) = b" .
	  qed

  have basis_refine:
    "\<And>U x. U \<in> TX \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U"
  proof -
    fix U x
    assume hU: "U \<in> TX" and hxU: "x \<in> U"
    have "U \<in> topology_generated_by_basis X B"
      using hU hTXeq by simp
    then show "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U"
      using hxU unfolding topology_generated_by_basis_def by blast
  qed

  have hXin: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])

  have union_TX: "\<forall>K. K \<subseteq> TX \<longrightarrow> (\<Union>K) \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])

  have hUrysohn_nm:
    "\<And>n m. Bseq n \<in> B \<Longrightarrow> Bseq m \<in> B \<Longrightarrow> closure_on X TX (Bseq n) \<subseteq> Bseq m
      \<Longrightarrow> \<exists>f. top1_continuous_map_on X TX ?I ?TI f
            \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1)"
  proof -
    fix n m
    assume hnB: "Bseq n \<in> B"
    assume hmB: "Bseq m \<in> B"
    assume hclsub: "closure_on X TX (Bseq n) \<subseteq> Bseq m"

    have hBmTX: "Bseq m \<in> TX"
      using hBopen hmB by blast
    have hBmX: "Bseq m \<subseteq> X"
      using hBsubX hmB by blast

    have hCcl: "closedin_on X TX (X - Bseq m)"
    proof (rule closedin_intro)
      show "X - Bseq m \<subseteq> X"
        by blast
      show "X - (X - Bseq m) \<in> TX"
        using hBmTX hBmX by (simp add: Diff_Diff_Int Int_absorb1)
	    qed
	
	    have hAcl: "closedin_on X TX (closure_on X TX (Bseq n))"
	      by (rule closure_on_closed[OF hTop], rule hBsubX[rule_format, OF hnB])

    have hdisj: "(X - Bseq m) \<inter> closure_on X TX (Bseq n) = {}"
    proof (rule equalityI)
      show "(X - Bseq m) \<inter> closure_on X TX (Bseq n) \<subseteq> {}"
      proof (rule subsetI)
        fix x assume hx: "x \<in> (X - Bseq m) \<inter> closure_on X TX (Bseq n)"
        have hxcl: "x \<in> closure_on X TX (Bseq n)"
          using hx by blast
        have hxBm: "x \<in> Bseq m"
          using hclsub hxcl by blast
        have hxnot: "x \<notin> Bseq m"
          using hx by blast
        show "x \<in> {}"
          using hxBm hxnot by blast
      qed
      show "{} \<subseteq> (X - Bseq m) \<inter> closure_on X TX (Bseq n)"
        by simp
    qed

	    have hexf:
	      "\<exists>f. top1_continuous_map_on X TX ?I ?TI f
	        \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1)"
	      using Theorem_33_1[OF hNormal hCcl hAcl hdisj, of 0 1] by (simp add: zero_le_one)
	    then obtain f where hf:
	      "top1_continuous_map_on X TX ?I ?TI f
	        \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1)"
	      by blast
	    show "\<exists>f. top1_continuous_map_on X TX ?I ?TI f
	            \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1)"
	      by (rule exI[where x=f], rule hf)
  qed

  define gpair where
    "gpair nm =
      (let n = fst nm; m = snd nm in
        if Bseq n \<in> B \<and> Bseq m \<in> B \<and> closure_on X TX (Bseq n) \<subseteq> Bseq m
        then (SOME f. top1_continuous_map_on X TX ?I ?TI f
              \<and> (\<forall>x\<in>(X - Bseq m). f x = 0)
              \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1))
        else (\<lambda>x. 0))" for nm

  have h0I: "0 \<in> ?I"
    unfolding top1_closed_interval_def by simp
  have hConstAll: "\<forall>y0\<in>?I. top1_continuous_map_on X TX ?I ?TI (\<lambda>x. y0)"
    by (rule Theorem_18_2(1)[OF hTop hTopI hTopI])
  have hconst0: "top1_continuous_map_on X TX ?I ?TI (\<lambda>x. 0)"
    using hConstAll h0I by blast

  have gpair_good:
    "\<And>n m. Bseq n \<in> B \<Longrightarrow> Bseq m \<in> B \<Longrightarrow> closure_on X TX (Bseq n) \<subseteq> Bseq m
      \<Longrightarrow> top1_continuous_map_on X TX ?I ?TI (gpair (n,m))
        \<and> (\<forall>x\<in>(X - Bseq m). gpair (n,m) x = 0)
        \<and> (\<forall>x\<in>closure_on X TX (Bseq n). gpair (n,m) x = 1)"
  proof -
    fix n m
    assume hnB: "Bseq n \<in> B"
    assume hmB: "Bseq m \<in> B"
    assume hclsub: "closure_on X TX (Bseq n) \<subseteq> Bseq m"
    have hex:
      "\<exists>f. top1_continuous_map_on X TX ?I ?TI f
        \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1)"
      using hUrysohn_nm[OF hnB hmB hclsub] by blast
    have hsome:
      "top1_continuous_map_on X TX ?I ?TI
        (SOME f. top1_continuous_map_on X TX ?I ?TI f
          \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1))
       \<and> (\<forall>x\<in>(X - Bseq m). (SOME f. top1_continuous_map_on X TX ?I ?TI f
          \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1)) x = 0)
       \<and> (\<forall>x\<in>closure_on X TX (Bseq n). (SOME f. top1_continuous_map_on X TX ?I ?TI f
          \<and> (\<forall>x\<in>(X - Bseq m). f x = 0) \<and> (\<forall>x\<in>closure_on X TX (Bseq n). f x = 1)) x = 1)"
      by (rule someI_ex[OF hex])
    show "top1_continuous_map_on X TX ?I ?TI (gpair (n,m))
        \<and> (\<forall>x\<in>(X - Bseq m). gpair (n,m) x = 0)
        \<and> (\<forall>x\<in>closure_on X TX (Bseq n). gpair (n,m) x = 1)"
      unfolding gpair_def Let_def using hnB hmB hclsub hsome by simp
  qed

	  have gpair_cont:
	    "\<And>nm. top1_continuous_map_on X TX ?I ?TI (gpair nm)"
	  proof -
    fix nm :: "nat \<times> nat"
    obtain n m where hnm: "nm = (n,m)"
      by (cases nm) simp
    show "top1_continuous_map_on X TX ?I ?TI (gpair nm)"
    proof (cases "Bseq n \<in> B \<and> Bseq m \<in> B \<and> closure_on X TX (Bseq n) \<subseteq> Bseq m")
      case True
      then have "top1_continuous_map_on X TX ?I ?TI (gpair (n,m))"
        using gpair_good by blast
      thus ?thesis
        unfolding hnm by simp
	    next
	      case False
	      have hnot: "\<not> (Bseq n \<in> B \<and> Bseq m \<in> B \<and> closure_on X TX (Bseq n) \<subseteq> Bseq m)"
	        using False by blast
	      have "gpair (n,m) = (\<lambda>x. 0)"
	        unfolding gpair_def Let_def by (simp add: hnot)
	      thus ?thesis
	        unfolding hnm using hconst0 by simp
	    qed
	  qed

  text \<open>
    Step 1 of the Urysohn metrization theorem (top1.tex): extract a countable family of
    continuous functions into the unit interval that can “detect” neighborhoods.
  \<close>

		  let ?pair_code = "(\<lambda>p::(nat \<times> nat). (2 ^ fst p) * (2 * snd p + 1))"

	  have pair_code_inj: "inj_on ?pair_code (UNIV::(nat \<times> nat) set)"
	    unfolding inj_on_def
	  proof (intro ballI impI)
		    fix p q :: "nat \<times> nat"
		    assume hp: "p \<in> (UNIV::(nat \<times> nat) set)" and hq: "q \<in> (UNIV::(nat \<times> nat) set)"
		    assume hEq: "?pair_code p = ?pair_code q"
		    obtain a b where hpab: "p = (a,b)"
		      by (cases p) simp
		    obtain c d where hqcd: "q = (c,d)"
		      by (cases q) simp

    have hodd_b: "\<not> (2::nat) dvd (2 * b + 1)"
      by simp
    have hodd_d: "\<not> (2::nat) dvd (2 * d + 1)"
      by simp

		    have hnot_dvd_a: "\<not> (2 ^ (Suc a)) dvd ?pair_code (a,b)"
		    proof
		      assume hdvd: "(2 ^ (Suc a)) dvd ?pair_code (a,b)"
		      have hcomm: "(2::nat) * 2 ^ a = 2 ^ a * 2"
		        by (simp add: mult.commute)
		      have hdvd': "(2 ^ a * (2::nat)) dvd ?pair_code (a,b)"
		      proof -
		        have "(2::nat) * 2 ^ a dvd ?pair_code (a,b)"
		          using hdvd by (simp only: power_Suc)
		        thus ?thesis
		          by (simp add: hcomm)
		      qed
		      have hEq: "?pair_code (a,b) = (2 ^ a) * (2 * b + 1)"
		        by simp
		      have hdvd0: "(2 ^ a * (2::nat)) dvd ((2 ^ a) * (2 * b + 1))"
		        apply (subst hEq[symmetric])
		        apply (rule hdvd')
		        done
			      have "(2::nat) dvd (2 * b + 1)"
			        using hdvd0 by (simp add: dvd_mult_cancel_left del: mult_Suc_right)
		      thus False
		        using hodd_b by blast
		    qed
	
		    have hnot_dvd_c: "\<not> (2 ^ (Suc c)) dvd ?pair_code (c,d)"
		    proof
		      assume hdvd: "(2 ^ (Suc c)) dvd ?pair_code (c,d)"
		      have hcomm: "(2::nat) * 2 ^ c = 2 ^ c * 2"
		        by (simp add: mult.commute)
		      have hdvd': "(2 ^ c * (2::nat)) dvd ?pair_code (c,d)"
		      proof -
		        have "(2::nat) * 2 ^ c dvd ?pair_code (c,d)"
		          using hdvd by (simp only: power_Suc)
		        thus ?thesis
		          by (simp add: hcomm)
		      qed
		      have hEq: "?pair_code (c,d) = (2 ^ c) * (2 * d + 1)"
		        by simp
		      have hdvd0: "(2 ^ c * (2::nat)) dvd ((2 ^ c) * (2 * d + 1))"
		        apply (subst hEq[symmetric])
		        apply (rule hdvd')
		        done
			      have "(2::nat) dvd (2 * d + 1)"
			        using hdvd0 by (simp add: dvd_mult_cancel_left del: mult_Suc_right)
		      thus False
		        using hodd_d by blast
		    qed

    have hac: "a = c"
    proof (cases a c rule: linorder_cases)
      case less
      have hle: "Suc a \<le> c"
        using less by simp
	      have hdvd: "((2::nat) ^ (Suc a)) dvd ((2::nat) ^ c)"
	      proof -
	        have hdecomp: "Suc a + (c - Suc a) = c"
	          using hle by simp
	        have "(2::nat) ^ c = (2::nat) ^ (Suc a + (c - Suc a))"
	          using hdecomp by simp
	        also have "\<dots> = (2::nat) ^ (Suc a) * (2::nat) ^ (c - Suc a)"
	          by (simp add: power_add)
	        finally have "(2::nat) ^ c = (2::nat) ^ (Suc a) * (2::nat) ^ (c - Suc a)" .
	        thus ?thesis
	          by (rule dvdI)
	      qed
	      have hEq_cd: "?pair_code (c,d) = (2 ^ c) * (2 * d + 1)"
	        by simp
	      have hEq_abcd: "?pair_code (a,b) = ?pair_code (c,d)"
	        using hEq unfolding hpab hqcd by simp
	      have hdiv_cd: "(2 ^ (Suc a)) dvd ?pair_code (c,d)"
	        apply (subst hEq_cd)
	        apply (rule dvd_mult2[OF hdvd])
	        done
	      have hdiv_ab: "(2 ^ (Suc a)) dvd ?pair_code (a,b)"
	        apply (subst hEq_abcd)
	        apply (rule hdiv_cd)
	        done
	      thus ?thesis
	        using hnot_dvd_a by blast
	    next
      case equal
      show ?thesis using equal by simp
    next
      case greater
      have hle: "Suc c \<le> a"
        using greater by simp
	      have hdvd: "((2::nat) ^ (Suc c)) dvd ((2::nat) ^ a)"
	      proof -
	        have hdecomp: "Suc c + (a - Suc c) = a"
	          using hle by simp
	        have "(2::nat) ^ a = (2::nat) ^ (Suc c + (a - Suc c))"
	          using hdecomp by simp
	        also have "\<dots> = (2::nat) ^ (Suc c) * (2::nat) ^ (a - Suc c)"
	          by (simp add: power_add)
	        finally have "(2::nat) ^ a = (2::nat) ^ (Suc c) * (2::nat) ^ (a - Suc c)" .
	        thus ?thesis
	          by (rule dvdI)
	      qed
	      have hEq_ab: "?pair_code (a,b) = (2 ^ a) * (2 * b + 1)"
	        by simp
	      have hEq_abcd: "?pair_code (a,b) = ?pair_code (c,d)"
	        using hEq unfolding hpab hqcd by simp
	      have hdiv_ab: "(2 ^ (Suc c)) dvd ?pair_code (a,b)"
	        apply (subst hEq_ab)
	        apply (rule dvd_mult2[OF hdvd])
	        done
	      have hdiv_cd: "(2 ^ (Suc c)) dvd ?pair_code (c,d)"
	        apply (subst hEq_abcd[symmetric])
	        apply (rule hdiv_ab)
	        done
	      thus ?thesis
	        using hnot_dvd_c by blast
	    qed

	    have hbd: "b = d"
	    proof -
	      have hEq_abcd: "?pair_code (a,b) = ?pair_code (c,d)"
	        using hEq unfolding hpab hqcd by simp
	      have hEq_abd: "?pair_code (a,b) = ?pair_code (a,d)"
	        using hEq_abcd hac by simp
	      have "2 * b + 1 = 2 * d + 1"
	        using hEq_abd by (simp add: mult_left_cancel)
	      hence "2 * b = 2 * d"
	        by simp
	      thus "b = d"
	        by simp
	    qed

    show "p = q"
      unfolding hpab hqcd using hac hbd by simp
  qed

	  have hCntProd: "top1_countable (UNIV::(nat \<times> nat) set)"
	    unfolding top1_countable_def
	    by (rule exI[where x="?pair_code"], rule pair_code_inj)

  define G where "G = gpair ` (UNIV::(nat \<times> nat) set)"
  have hCntG: "top1_countable G"
    unfolding G_def using top1_countable_image[OF hCntProd, of gpair] .

  obtain eG :: "('a \<Rightarrow> real) \<Rightarrow> nat" where heGinj: "inj_on eG G"
    using hCntG unfolding top1_countable_def by blast

  define fseq :: "nat \<Rightarrow> ('a \<Rightarrow> real)" where
    "fseq n =
      (if (\<exists>g\<in>G. eG g = n) then (SOME g. g \<in> G \<and> eG g = n) else (\<lambda>x. 0))" for n

  have fseq_hit: "\<And>g. g \<in> G \<Longrightarrow> fseq (eG g) = g"
  proof -
    fix g assume hgG: "g \<in> G"
    have hex: "\<exists>g'\<in>G. eG g' = eG g"
      using hgG by blast
    have hex': "\<exists>g'. g' \<in> G \<and> eG g' = eG g"
      using hex by blast
    have hsome: "(SOME g'. g' \<in> G \<and> eG g' = eG g) \<in> G \<and> eG (SOME g'. g' \<in> G \<and> eG g' = eG g) = eG g"
      by (rule someI_ex[OF hex'])
    have hmem: "(SOME g'. g' \<in> G \<and> eG g' = eG g) \<in> G"
      using hsome by blast
    have heq: "eG (SOME g'. g' \<in> G \<and> eG g' = eG g) = eG g"
      using hsome by blast
    have "fseq (eG g) = (SOME g'. g' \<in> G \<and> eG g' = eG g)"
      unfolding fseq_def by (simp add: hex)
    also have "... = g"
      using heGinj hmem hgG heq unfolding inj_on_def by blast
    finally show "fseq (eG g) = g" .
  qed

  have fseq_cont: "\<forall>n. top1_continuous_map_on X TX ?I ?TI (fseq n)"
  proof (intro allI)
    fix n
    show "top1_continuous_map_on X TX ?I ?TI (fseq n)"
    proof (cases "\<exists>g\<in>G. eG g = n")
      case True
      then obtain g where hgG: "g \<in> G" and hgn: "eG g = n"
        by blast
      have "fseq n = g"
        using fseq_hit[OF hgG] hgn by simp
      moreover have "top1_continuous_map_on X TX ?I ?TI g"
      proof -
        obtain nm where hnm: "nm \<in> (UNIV::(nat \<times> nat) set)" and hg: "g = gpair nm"
          using hgG unfolding G_def by blast
        show ?thesis
          using gpair_cont[of nm] hg by simp
      qed
      ultimately show ?thesis
        by simp
    next
      case False
      show ?thesis
        unfolding fseq_def using False hconst0 by simp
    qed
  qed

  have fseq_support:
    "\<forall>x0\<in>X. \<forall>U. neighborhood_of x0 X TX U \<longrightarrow>
      (\<exists>n. fseq n x0 = 1 \<and> (\<forall>x\<in>X - U. fseq n x = 0))"
  proof (intro ballI allI impI)
    fix x0 U
    assume hx0X: "x0 \<in> X"
    assume hnb: "neighborhood_of x0 X TX U"
    have hU: "U \<in> TX" and hx0U: "x0 \<in> U"
      using hnb unfolding neighborhood_of_def by blast+

    obtain Bm where hBmB: "Bm \<in> B" and hx0Bm: "x0 \<in> Bm" and hBmU: "Bm \<subseteq> U"
      using basis_refine[OF hU hx0U] by blast

    obtain V where hVT: "V \<in> TX" and hVX: "V \<subseteq> X" and hx0V: "x0 \<in> V" and hclV: "closure_on X TX V \<subseteq> Bm"
      using regular_refine_point_into_open[OF hreg hx0X _ _ hx0Bm] hBopen hBsubX hBmB
      by blast

    obtain Bn where hBnB: "Bn \<in> B" and hx0Bn: "x0 \<in> Bn" and hBnV: "Bn \<subseteq> V"
      using basis_refine[OF hVT hx0V] by blast

    have hclBn: "closure_on X TX Bn \<subseteq> Bm"
    proof -
      have hclmono: "closure_on X TX Bn \<subseteq> closure_on X TX V"
        by (rule closure_on_mono[OF hBnV])
      show ?thesis
        using subset_trans[OF hclmono hclV] .
    qed

    let ?n = "e Bn"
    let ?m = "e Bm"

    have hBseqn: "Bseq ?n = Bn"
      by (rule Bseq_hit[OF hBnB])
    have hBseqm: "Bseq ?m = Bm"
      by (rule Bseq_hit[OF hBmB])

    have hgood: "top1_continuous_map_on X TX ?I ?TI (gpair (?n, ?m))
        \<and> (\<forall>x\<in>(X - Bseq ?m). gpair (?n, ?m) x = 0)
        \<and> (\<forall>x\<in>closure_on X TX (Bseq ?n). gpair (?n, ?m) x = 1)"
      using gpair_good[of ?n ?m] hBseqn hBseqm hclBn hBnB hBmB
      by simp

	    have hx0cl: "x0 \<in> closure_on X TX (Bseq ?n)"
	      unfolding hBseqn by (rule subsetD[OF subset_closure_on, OF hx0Bn])

    have hgx0: "gpair (?n, ?m) x0 = 1"
      using hgood hx0cl by blast

    have hXmU: "X - U \<subseteq> X - Bseq ?m"
      unfolding hBseqm using hBmU by blast

    have hg0: "\<forall>x\<in>X - U. gpair (?n, ?m) x = 0"
    proof (intro ballI)
      fix x assume hx: "x \<in> X - U"
      have hx': "x \<in> X - Bseq ?m"
        using hXmU hx by blast
      show "gpair (?n, ?m) x = 0"
        using hgood hx' by blast
    qed

    have hgG: "gpair (?n, ?m) \<in> G"
      unfolding G_def by blast

    let ?k = "eG (gpair (?n, ?m))"
    have hk: "fseq ?k = gpair (?n, ?m)"
      by (rule fseq_hit[OF hgG])

	    show "\<exists>n. fseq n x0 = 1 \<and> (\<forall>x\<in>X - U. fseq n x = 0)"
	      apply (rule exI[of _ ?k])
	      apply (intro conjI)
	       apply (simp add: hk hgx0)
	      apply (simp add: hk hg0)
	      done
	  qed
	
	  text \<open>
	    Step 2 of the Urysohn metrization theorem (top1.tex): define an explicit metric from the
	    countable family \<open>fseq\<close> and show it induces exactly \<open>TX\<close>.
	  \<close>
	
	  define d :: "'a \<Rightarrow> 'a \<Rightarrow> real" where
	    "d x y = (\<Sum>n. (1/2::real)^n * abs (fseq n x - fseq n y))" for x y
	
	  have fseq_in_I: "\<And>n x. x \<in> X \<Longrightarrow> fseq n x \<in> ?I"
	  proof -
	    fix n x assume hxX: "x \<in> X"
	    have hcont: "top1_continuous_map_on X TX ?I ?TI (fseq n)"
	      using fseq_cont by blast
	    show "fseq n x \<in> ?I"
	      using hcont hxX unfolding top1_continuous_map_on_def by blast
	  qed
	
	  have fseq_bounds: "\<And>n x. x \<in> X \<Longrightarrow> 0 \<le> fseq n x \<and> fseq n x \<le> 1"
	    using fseq_in_I unfolding top1_closed_interval_def by blast
	
	  have fseq_absdiff_le1:
	    "\<And>n x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> abs (fseq n x - fseq n y) \<le> 1"
	  proof -
	    fix n x y
	    assume hxX: "x \<in> X" and hyX: "y \<in> X"
	    have hx: "0 \<le> fseq n x" and hx1: "fseq n x \<le> 1"
	      using fseq_bounds[OF hxX] by blast+
	    have hy: "0 \<le> fseq n y" and hy1: "fseq n y \<le> 1"
	      using fseq_bounds[OF hyX] by blast+
	    have hle1: "fseq n x - fseq n y \<le> 1"
	      using hx1 hy by linarith
		    have hge1: "-1 \<le> fseq n x - fseq n y"
		      using hx hy1 by linarith
		    have hneg: "- (fseq n x - fseq n y) \<le> 1"
		      using hge1 by linarith
			    show "abs (fseq n x - fseq n y) \<le> 1"
			      by (rule abs_leI[OF hle1 hneg])
		  qed
	
	  have summable_geom: "summable (\<lambda>n. (1/2::real)^n)"
	    by (simp add: summable_geometric_iff)
	
		  have suminf_geom: "(\<Sum>n. (1/2::real)^n) = 2"
		  proof -
		    have hnorm: "norm (1/2::real) < 1"
		      by simp
		    have "(\<Sum>n. (1/2::real)^n) = 1 / (1 - (1/2::real))"
		      by (rule suminf_geometric[OF hnorm])
		    thus ?thesis
		      by simp
		  qed
	
	  have d_summable:
	    "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow>
	      summable (\<lambda>n. (1/2::real)^n * abs (fseq n x - fseq n y))"
		  proof -
		    fix x y
		    assume hxX: "x \<in> X" and hyX: "y \<in> X"
		    show "summable (\<lambda>n. (1/2::real)^n * abs (fseq n x - fseq n y))"
		    proof (rule summable_comparison_test'[OF summable_geom, where N=0])
		      fix n
		      assume hn0: "n \<ge> (0::nat)"
		      have hle: "abs (fseq n x - fseq n y) \<le> 1"
		        by (rule fseq_absdiff_le1[OF hxX hyX])
		      have hnonneg: "0 \<le> (1/2::real)^n"
		        by simp
		      have "norm ((1/2::real)^n * abs (fseq n x - fseq n y)) = (1/2::real)^n * abs (fseq n x - fseq n y)"
		        using hnonneg by simp
		      also have "\<dots> \<le> (1/2::real)^n * 1"
		        by (rule mult_left_mono[OF hle]) (rule hnonneg)
		      finally show "norm ((1/2::real)^n * abs (fseq n x - fseq n y)) \<le> (1/2::real)^n"
		        by simp
		    qed
		  qed
	
	  have d_ge_term:
	    "\<And>x y n. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow>
	      (1/2::real)^n * abs (fseq n x - fseq n y) \<le> d x y"
	  proof -
	    fix x y n
	    assume hxX: "x \<in> X" and hyX: "y \<in> X"
	    have hsumm: "summable (\<lambda>k. (1/2::real)^k * abs (fseq k x - fseq k y))"
	      by (rule d_summable[OF hxX hyX])
		    have hnonneg: "\<And>k. 0 \<le> (1/2::real)^k * abs (fseq k x - fseq k y)"
		      by simp
		    have "(\<Sum>k\<in>{n}. (1/2::real)^k * abs (fseq k x - fseq k y))
		          \<le> (\<Sum>k. (1/2::real)^k * abs (fseq k x - fseq k y))"
		      apply (rule sum_le_suminf)
		        apply (rule hsumm)
		       apply simp
		      apply (simp add: hnonneg)
		      done
	    thus "(1/2::real)^n * abs (fseq n x - fseq n y) \<le> d x y"
	      unfolding d_def by simp
	  qed
	
	  have d_refl0: "\<And>x. x \<in> X \<Longrightarrow> d x x = 0"
	  proof -
	    fix x assume hxX: "x \<in> X"
	    show "d x x = 0"
	      unfolding d_def by simp
	  qed
	
	  have d_nonneg: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> 0 \<le> d x y"
	  proof -
	    fix x y
	    assume hxX: "x \<in> X" and hyX: "y \<in> X"
	    have hsumm: "summable (\<lambda>n. (1/2::real)^n * abs (fseq n x - fseq n y))"
	      by (rule d_summable[OF hxX hyX])
	    have hpos: "\<And>n. 0 \<le> (1/2::real)^n * abs (fseq n x - fseq n y)"
	      by simp
	    show "0 \<le> d x y"
	      unfolding d_def
	      by (rule suminf_nonneg[OF hsumm hpos])
	  qed
	
	  have d_sym: "\<And>x y. d x y = d y x"
	    unfolding d_def by (simp add: abs_minus_commute)
	
	  have d_eq0_iff: "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> (d x y = 0 \<longleftrightarrow> x = y)"
	  proof -
	    fix x y
	    assume hxX: "x \<in> X" and hyX: "y \<in> X"
	    show "d x y = 0 \<longleftrightarrow> x = y"
	    proof (intro iffI)
	      assume h0: "d x y = 0"
	      show "x = y"
	      proof (rule ccontr)
	        assume hne: "x \<noteq> y"
	        have hsing: "\<forall>t\<in>X. closedin_on X TX {t}"
	          using hT1 unfolding top1_T1_on_def
	          apply (rule conjunct2)
	          done
	        have hycl: "closedin_on X TX {y}"
	          by (rule bspec[OF hsing hyX])
	        have hU: "X - {y} \<in> TX"
	          using hycl unfolding closedin_on_def
	          apply (rule conjunct2)
	          done
	        have hxU: "x \<in> X - {y}"
	          using hxX hne by blast
	        have hnb: "neighborhood_of x X TX (X - {y})"
	          unfolding neighborhood_of_def using hU hxU by blast
	        obtain n where hn1: "fseq n x = 1" and hn0: "\<forall>u\<in>X - (X - {y}). fseq n u = 0"
	          using fseq_support[rule_format, OF hxX, of "X - {y}"] hnb by blast
	        have hy0: "fseq n y = 0"
	          apply (rule bspec[OF hn0])
	          using hyX
	          apply simp
	          done
	        have habs1: "abs (fseq n x - fseq n y) = 1"
	          using hn1 hy0 by simp
	        have hterm_le: "(1/2::real)^n * abs (fseq n x - fseq n y) \<le> d x y"
	          by (rule d_ge_term[OF hxX hyX])
	        have hpos: "0 < (1/2::real)^n * abs (fseq n x - fseq n y)"
	          using habs1 by simp
	        have "0 < d x y"
	          by (rule less_le_trans[OF hpos hterm_le])
	        thus False
	          using h0 by simp
	      qed
	    next
	      assume "x = y"
	      thus "d x y = 0"
	        unfolding d_def by simp
	    qed
	  qed
	
	  have d_triangle:
	    "\<And>x y z. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> z \<in> X \<Longrightarrow> d x z \<le> d x y + d y z"
	  proof -
	    fix x y z
	    assume hxX: "x \<in> X" and hyX: "y \<in> X" and hzX: "z \<in> X"
	    let ?f = "\<lambda>n. (1/2::real)^n * abs (fseq n x - fseq n z)"
	    let ?g = "\<lambda>n. (1/2::real)^n * abs (fseq n x - fseq n y)"
	    let ?h = "\<lambda>n. (1/2::real)^n * abs (fseq n y - fseq n z)"
	
	    have hsumm_f: "summable ?f"
	      by (rule d_summable[OF hxX hzX])
	    have hsumm_g: "summable ?g"
	      by (rule d_summable[OF hxX hyX])
	    have hsumm_h: "summable ?h"
	      by (rule d_summable[OF hyX hzX])
	    have hsumm_gh: "summable (\<lambda>n. ?g n + ?h n)"
	      by (rule summable_add[OF hsumm_g hsumm_h])
	
	    have hpt: "\<And>n. ?f n \<le> ?g n + ?h n"
	    proof -
	      fix n
	      have habs:
	        "abs (fseq n x - fseq n z)
	           \<le> abs (fseq n x - fseq n y) + abs (fseq n y - fseq n z)"
	      proof -
	        have "fseq n x - fseq n z = (fseq n x - fseq n y) + (fseq n y - fseq n z)"
	          by simp
	        thus ?thesis
	          by (simp add: abs_triangle_ineq)
	      qed
	      have hnonneg: "0 \<le> (1/2::real)^n"
	        by simp
	      have "(1/2::real)^n * abs (fseq n x - fseq n z)
	            \<le> (1/2::real)^n * (abs (fseq n x - fseq n y) + abs (fseq n y - fseq n z))"
	        by (rule mult_left_mono[OF habs hnonneg])
	      also have "\<dots> =
	          (1/2::real)^n * abs (fseq n x - fseq n y) + (1/2::real)^n * abs (fseq n y - fseq n z)"
	        by (simp add: algebra_simps)
	      finally show "?f n \<le> ?g n + ?h n"
	        by simp
	    qed
	
	    have hsuminf_add: "suminf ?g + suminf ?h = (\<Sum>n. ?g n + ?h n)"
	      by (rule suminf_add[OF hsumm_g hsumm_h])
	
	    have "(\<Sum>n. ?f n) \<le> (\<Sum>n. ?g n + ?h n)"
	      by (rule suminf_le[OF hpt hsumm_f hsumm_gh])
	    also have "\<dots> = suminf ?g + suminf ?h"
	      by (simp add: hsuminf_add)
	    finally show "d x z \<le> d x y + d y z"
	      unfolding d_def by simp
	  qed
	
	  have d_metric: "top1_metric_on X d"
	    unfolding top1_metric_on_def
	    apply (intro conjI ballI)
	    subgoal for x
	      using d_refl0 by simp
	    subgoal for x y
	      by (rule d_nonneg)
	    subgoal for x y
	      by (rule d_eq0_iff)
	    subgoal for x y
	      by (rule d_sym)
	    subgoal for x y z
	      by (rule d_triangle)
	    done
	
			  have small_nbhd_in_ball:
			    "\<And>x (e::real). x \<in> X \<Longrightarrow> 0 < e \<Longrightarrow>
			      \<exists>V\<in>TX. x \<in> V \<and> V \<subseteq> top1_ball_on X d x e"
			  proof -
			    fix x
			    fix e :: real
			    assume hxX: "x \<in> X" and he: "0 < e"
	    define eps where "eps = e / 4"
	    have heps: "0 < eps"
	      unfolding eps_def using he by simp
	
		    have he2: "0 < e / 2"
		      using he by simp
		    have hhalf: "(1/2::real) < 1"
		      by simp
		    obtain N where hN: "(1/2::real)^N < e / 2"
		      using real_arch_pow_inv[OF he2 hhalf] by blast
	    (* We use only the first N coordinates and bound the tail by (1/2)^N. *)
	    define In where
	      "In n = (?I \<inter> open_interval (fseq n x - eps) (fseq n x + eps))" for n
	
	    have hIn_open: "\<And>n. n \<le> N \<Longrightarrow> In n \<in> ?TI"
	    proof -
	      fix n assume hn: "n \<le> N"
	      have hop: "open_interval (fseq n x - eps) (fseq n x + eps) \<in> order_topology_on_UNIV"
	      proof -
	        have "fseq n x - eps < fseq n x + eps"
	          using heps by linarith
	        thus ?thesis
	          by (rule open_interval_in_order_topology)
	      qed
	      show "In n \<in> ?TI"
	        unfolding In_def top1_closed_interval_topology_def subspace_topology_def
	        apply (rule CollectI)
	        apply (rule exI[where x="open_interval (fseq n x - eps) (fseq n x + eps)"])
	        using hop by simp
	    qed
	
	    define Vn where "Vn n = {y\<in>X. fseq n y \<in> In n}" for n
	    have hVn_open: "\<And>n. n \<le> N \<Longrightarrow> Vn n \<in> TX"
	    proof -
	      fix n assume hn: "n \<le> N"
	      have hcont: "top1_continuous_map_on X TX ?I ?TI (fseq n)"
	        using fseq_cont by blast
	      have "{y\<in>X. fseq n y \<in> In n} \<in> TX"
	        using hcont hIn_open[OF hn] unfolding top1_continuous_map_on_def by blast
	      thus "Vn n \<in> TX"
	        unfolding Vn_def by simp
	    qed
	
	    define F where "F = Vn ` {..N}"
	    have hFfin: "finite F"
	      unfolding F_def by simp
	    have hFne: "F \<noteq> {}"
	      unfolding F_def by simp
	    have hFsub: "F \<subseteq> TX"
	      unfolding F_def using hVn_open by blast
	
	    have hInterF: "\<Inter>F \<in> TX"
	      using hTop hFfin hFne hFsub unfolding is_topology_on_def by blast
	
		    have hxIn: "\<And>n. n \<le> N \<Longrightarrow> fseq n x \<in> In n"
		    proof -
		      fix n assume hn: "n \<le> N"
		      have hI: "fseq n x \<in> ?I"
		        by (rule fseq_in_I[OF hxX])
		      have hop: "fseq n x \<in> open_interval (fseq n x - eps) (fseq n x + eps)"
		      proof -
		        have "fseq n x - eps < fseq n x"
		          using heps by linarith
		        moreover have "fseq n x < fseq n x + eps"
		          using heps by linarith
		        ultimately show ?thesis
		          unfolding open_interval_def by simp
		      qed
		      show "fseq n x \<in> In n"
		        unfolding In_def using hI hop by blast
		    qed
	
	    have hxVn: "\<And>n. n \<le> N \<Longrightarrow> x \<in> Vn n"
	      unfolding Vn_def using hxX hxIn by blast
	
	    have hxInter: "x \<in> \<Inter>F"
	      unfolding F_def by (simp add: hxVn)
	
	    have hInter_sub_ball: "\<Inter>F \<subseteq> top1_ball_on X d x e"
	    proof (rule subsetI)
	      fix y assume hy: "y \<in> \<Inter>F"
		      have hyX: "y \<in> X"
		      proof -
		        have hV0: "Vn 0 \<in> F"
		          unfolding F_def by simp
		        have hyV0: "y \<in> Vn 0"
		          by (rule InterD[OF hy hV0])
		        thus ?thesis
		          unfolding Vn_def by simp
		      qed
	      (* Bound each of the first Suc N terms by eps, and the tail by (1/2)^N. *)
		      have hfirst: "\<And>n. n \<le> N \<Longrightarrow> abs (fseq n x - fseq n y) < eps"
		      proof -
		        fix n assume hn: "n \<le> N"
		        have hVn: "Vn n \<in> F"
		          unfolding F_def using hn by blast
		        have hyVn: "y \<in> Vn n"
		          by (rule InterD[OF hy hVn])
		        have hyIn: "fseq n y \<in> In n"
		          using hyVn unfolding Vn_def by simp
	        have hxIn': "fseq n x \<in> In n"
	          using hxIn[OF hn] .
			        have "fseq n y \<in> open_interval (fseq n x - eps) (fseq n x + eps)"
			          using hyIn unfolding In_def by blast
			        then have hconj: "fseq n x - eps < fseq n y \<and> fseq n y < fseq n x + eps"
			          unfolding open_interval_def by simp
			        have hleft: "fseq n x - eps < fseq n y"
			          by (rule conjunct1[OF hconj])
			        have hright: "fseq n y < fseq n x + eps"
			          by (rule conjunct2[OF hconj])
		        have habs: "abs (fseq n y - fseq n x) < eps"
		        proof -
		          have "-eps < fseq n y - fseq n x"
		            using hleft by linarith
		          moreover have "fseq n y - fseq n x < eps"
		            using hright by linarith
		          ultimately show ?thesis
		            by (simp add: abs_less_iff)
		        qed
		        show "abs (fseq n x - fseq n y) < eps"
		          using habs by (simp add: abs_minus_commute)
		      qed
	
		      have htail:
		        "(\<Sum>n. (1/2::real)^(n+Suc N) * abs (fseq (n+Suc N) x - fseq (n+Suc N) y)) \<le> (1/2::real)^N"
		      proof -
		        let ?g = "\<lambda>n. (1/2::real)^(n+Suc N) * abs (fseq (n+Suc N) x - fseq (n+Suc N) y)"
		        let ?h = "\<lambda>n. (1/2::real)^(n+Suc N)"
		
		        have hsumm_h: "summable ?h"
		        proof -
		          have hsumm': "summable (\<lambda>n. (1/2::real)^(Suc N) * (1/2::real)^n)"
		            by (rule summable_mult[OF summable_geom])
		          have hfun: "(\<lambda>n. (1/2::real)^(n+Suc N)) = (\<lambda>n. (1/2::real)^(Suc N) * (1/2::real)^n)"
		            by (rule ext) (simp add: power_add mult_ac)
		          show ?thesis
		            unfolding hfun using hsumm' by simp
		        qed
		
		        have hle: "\<And>n. ?g n \<le> ?h n"
		        proof -
		          fix n
		          have hab: "abs (fseq (n+Suc N) x - fseq (n+Suc N) y) \<le> 1"
		            by (rule fseq_absdiff_le1[OF hxX hyX])
		          have hnonneg: "0 \<le> ?h n"
		            by simp
		          have "?g n \<le> ?h n * 1"
		            by (rule mult_left_mono[OF hab hnonneg])
		          thus "?g n \<le> ?h n"
		            by simp
		        qed
		
		        have hsumm_g: "summable ?g"
		        proof -
		          have "\<And>n. norm (?g n) \<le> ?h n"
		          proof -
		            fix n
		            have hnonneg_g: "0 \<le> ?g n"
		              by simp
		            have "norm (?g n) = ?g n"
		              using hnonneg_g by simp
		            also have "\<dots> \<le> ?h n"
		              by (rule hle)
		            finally show "norm (?g n) \<le> ?h n" .
		          qed
		          thus ?thesis
		            by (rule summable_comparison_test'[OF hsumm_h])
		        qed
		
		        have "(\<Sum>n. ?g n) \<le> (\<Sum>n. ?h n)"
		          by (rule suminf_le[OF hle hsumm_g hsumm_h])
		        also have "(\<Sum>n. ?h n) = (1/2::real)^N"
		        proof -
		          have "(\<Sum>n. ?h n) = (\<Sum>n. (1/2::real)^(Suc N) * (1/2::real)^n)"
		            by (rule suminf_cong) (simp add: power_add mult_ac)
		          also have "\<dots> = (1/2::real)^(Suc N) * (\<Sum>n. (1/2::real)^n)"
		            by (rule suminf_mult[OF summable_geom])
		          also have "\<dots> = (1/2::real)^(Suc N) * 2"
		            using suminf_geom by simp
		          also have "\<dots> = (1/2::real)^N"
		            by simp
		          finally show ?thesis .
		        qed
		        finally show ?thesis .
		      qed
	
	      have hsumm: "summable (\<lambda>n. (1/2::real)^n * abs (fseq n x - fseq n y))"
	        by (rule d_summable[OF hxX hyX])
	
	      have hsplit:
	        "d x y =
	          (\<Sum>n. (1/2::real)^(n+Suc N) * abs (fseq (n+Suc N) x - fseq (n+Suc N) y))
	          + (\<Sum>n<Suc N. (1/2::real)^n * abs (fseq n x - fseq n y))"
	        unfolding d_def
	        apply (rule suminf_split_initial_segment)
	        apply (rule hsumm)
	        done
	
		      have hsum_le: "(\<Sum>n<Suc N. (1/2::real)^n * abs (fseq n x - fseq n y))
		          \<le> (\<Sum>n<Suc N. (1/2::real)^n * eps)"
			      proof (rule sum_mono)
			        fix n assume hn: "n \<in> {..<Suc N}"
			        have hnle: "n \<le> N"
			          using hn by simp
			        have habslt: "abs (fseq n x - fseq n y) < eps"
			          by (rule hfirst[OF hnle])
				        have habsle: "abs (fseq n x - fseq n y) \<le> eps"
				          using habslt by (rule less_imp_le)
				        have hnonneg: "0 \<le> (1/2::real)^n"
				          by simp
				        show "(1/2::real)^n * abs (fseq n x - fseq n y) \<le> (1/2::real)^n * eps"
				          by (rule mult_left_mono[OF habsle hnonneg])
					      qed
	      have hsum_le2: "(\<Sum>n<Suc N. (1/2::real)^n * eps) = eps * (\<Sum>n<Suc N. (1/2::real)^n)"
	      proof -
	        have "(\<Sum>n<Suc N. (1/2::real)^n * eps) = (\<Sum>n<Suc N. (1/2::real)^n) * eps"
	          by (simp add: sum_distrib_right[symmetric])
	        also have "\<dots> = eps * (\<Sum>n<Suc N. (1/2::real)^n)"
	          by (simp add: mult.commute)
	        finally show ?thesis .
	      qed
	      have hgeom_le: "(\<Sum>n<Suc N. (1/2::real)^n) \<le> 2"
	      proof -
	        have hsumm: "summable (\<lambda>n. (1/2::real)^n)"
	          by (rule summable_geom)
	        have "(\<Sum>n<Suc N. (1/2::real)^n) \<le> (\<Sum>n. (1/2::real)^n)"
	          apply (rule sum_le_suminf)
	            apply (rule hsumm)
	           apply simp
	          apply simp
	          done
	        also have "\<dots> = 2"
	          by (simp add: suminf_geom)
	        finally show ?thesis
	          by simp
	      qed
	      have hsum_bound: "(\<Sum>n<Suc N. (1/2::real)^n * abs (fseq n x - fseq n y)) \<le> e / 2"
	      proof -
		        have "(\<Sum>n<Suc N. (1/2::real)^n * abs (fseq n x - fseq n y))
		            \<le> eps * (\<Sum>n<Suc N. (1/2::real)^n)"
		          using hsum_le hsum_le2 by simp
		        also have "\<dots> \<le> eps * 2"
		          by (rule mult_left_mono[OF hgeom_le]) (rule less_imp_le[OF heps])
		        also have "\<dots> = e / 2"
		          unfolding eps_def by simp
		        finally show ?thesis .
		      qed
	
	      have "d x y \<le> (1/2::real)^N + e/2"
	        using hsplit htail hsum_bound by linarith
	      also have "\<dots> < e"
	        using hN by linarith
	      finally have "d x y < e" .
	      show "y \<in> top1_ball_on X d x e"
	        unfolding top1_ball_on_def using hyX \<open>d x y < e\<close> by simp
	    qed
	
	    show "\<exists>V\<in>TX. x \<in> V \<and> V \<subseteq> top1_ball_on X d x e"
	      apply (rule bexI[where x="\<Inter>F"])
	       apply (intro conjI)
	        apply (rule hxInter)
	       apply (rule hInter_sub_ball)
	      apply (rule hInterF)
	      done
		  qed
		
			  have ball_open_TX:
			    "\<And>x (e::real). x \<in> X \<Longrightarrow> 0 < e \<Longrightarrow> top1_ball_on X d x e \<in> TX"
			  proof -
			    fix x
			    fix e :: real
			    assume hxX: "x \<in> X" and he: "0 < e"
	    (* Characterize openness via the fixed basis B for TX. *)
	    have hBallSub: "top1_ball_on X d x e \<subseteq> X"
	      unfolding top1_ball_on_def by blast
	    have hcov:
	      "\<forall>y\<in>top1_ball_on X d x e. \<exists>b\<in>B. y \<in> b \<and> b \<subseteq> top1_ball_on X d x e"
	    proof (intro ballI)
	      fix y assume hyBall: "y \<in> top1_ball_on X d x e"
	      have hyX: "y \<in> X"
	        using hyBall unfolding top1_ball_on_def by simp
		      have hyr: "0 < e - d x y"
		        using hyBall unfolding top1_ball_on_def by simp
		      have hpos2: "0 < (e - d x y) / 2"
		        using hyr by simp
		      obtain V where hVT: "V \<in> TX" and hyV: "y \<in> V" and hVsub: "V \<subseteq> top1_ball_on X d y ((e - d x y) / 2)"
		        using small_nbhd_in_ball[OF hyX hpos2] by blast
	      have hVsub': "V \<subseteq> top1_ball_on X d x e"
	      proof (rule subsetI)
		        fix z assume hzV: "z \<in> V"
		        have hzX: "z \<in> X"
		          using hzV hVsub unfolding top1_ball_on_def by blast
		        have hzBall: "z \<in> top1_ball_on X d y ((e - d x y) / 2)"
		          using hzV hVsub by blast
		        have hdz: "d y z < (e - d x y) / 2"
		          using hzBall unfolding top1_ball_on_def by simp
		        have htri_all: "\<forall>x\<in>X. \<forall>y\<in>X. \<forall>z\<in>X. d x z \<le> d x y + d y z"
		          using d_metric unfolding top1_metric_on_def by blast
		        have htri: "d x z \<le> d x y + d y z"
		          using htri_all hxX hyX hzX by blast
		        have hhalf_lt: "(e - d x y) / 2 < e - d x y"
		          using hyr by simp
		        have hdz': "d y z < e - d x y"
		          using hdz hhalf_lt by (rule less_trans)
		        have hsum: "d x y + d y z < e"
		          using hdz' by linarith
		        have "d x z < e"
		          by (rule le_less_trans[OF htri hsum])
		        thus "z \<in> top1_ball_on X d x e"
		          unfolding top1_ball_on_def using hzX by simp
		  qed
	      obtain b where hbB: "b \<in> B" and hyb: "y \<in> b" and hbV: "b \<subseteq> V"
	        using basis_refine[OF hVT hyV] by blast
	      show "\<exists>b\<in>B. y \<in> b \<and> b \<subseteq> top1_ball_on X d x e"
	        apply (rule bexI[where x=b])
	         apply (intro conjI)
	          apply (rule hyb)
	         apply (rule subset_trans[OF hbV hVsub'])
	        apply (rule hbB)
	        done
		  qed
	    have hball: "top1_ball_on X d x e \<in> topology_generated_by_basis X B"
	      unfolding topology_generated_by_basis_def
	      apply (rule CollectI)
	      apply (intro conjI)
	       apply (rule hBallSub)
	      apply (rule hcov)
	      done
		    show "top1_ball_on X d x e \<in> TX"
		      using hball hTXeq by simp
		  qed
	
			  have metric_basis_sub_TX: "top1_metric_basis_on X d \<subseteq> TX"
			  proof (rule subsetI)
			    fix U
			    assume hU: "U \<in> top1_metric_basis_on X d"
			    obtain x e where hxX: "x \<in> X" and he: "0 < (e::real)"
			      and hUeq: "U = top1_ball_on X d x e"
			      using hU unfolding top1_metric_basis_on_def by blast
			    have "top1_ball_on X d x e \<in> TX"
			      by (rule ball_open_TX[OF hxX he])
			    thus "U \<in> TX"
			      using hUeq by simp
			  qed
		
			  have hMet_sub_TX: "top1_metric_topology_on X d \<subseteq> TX"
			  proof -
			    have "topology_generated_by_basis X (top1_metric_basis_on X d) \<subseteq> TX"
			      by (rule topology_generated_by_basis_subset[OF hTop metric_basis_sub_TX])
			    thus ?thesis
			      unfolding top1_metric_topology_on_def .
			  qed
		
		  have hTX_sub_Met: "TX \<subseteq> top1_metric_topology_on X d"
		  proof (rule subsetI)
		    fix U assume hU: "U \<in> TX"
		
		    have hUX: "U \<subseteq> X"
		    proof -
		      have "U \<in> topology_generated_by_basis X B"
		        using hU hTXeq by simp
		      thus "U \<subseteq> X"
		        unfolding topology_generated_by_basis_def by blast
		    qed
		
		    have href:
		      "\<forall>x0\<in>U. \<exists>b\<in>top1_metric_basis_on X d. x0 \<in> b \<and> b \<subseteq> U"
		    proof (intro ballI)
		      fix x0 assume hx0U: "x0 \<in> U"
		      have hx0X: "x0 \<in> X"
		        using hUX hx0U by blast
		      have hnb: "neighborhood_of x0 X TX U"
		        unfolding neighborhood_of_def using hU hx0U by simp
		      obtain n where hnx: "fseq n x0 = 1" and hzero: "\<forall>x\<in>X - U. fseq n x = 0"
		        using fseq_support hx0X hnb by blast
		      define r where "r = (1/2::real)^n / 2"
		      have hrpos: "0 < r"
		        unfolding r_def by simp
		      have hx0ball: "x0 \<in> top1_ball_on X d x0 r"
		        unfolding top1_ball_on_def r_def d_def using hx0X by simp
		      have hsub: "top1_ball_on X d x0 r \<subseteq> U"
		      proof (rule subsetI)
		        fix y assume hy: "y \<in> top1_ball_on X d x0 r"
		        have hyX: "y \<in> X"
		          using hy unfolding top1_ball_on_def by simp
		        show "y \<in> U"
		        proof (rule ccontr)
		          assume hny: "y \<notin> U"
		          have hyout: "y \<in> X - U"
		            using hyX hny by blast
		          have hfy: "fseq n y = 0"
		            using hzero hyout by blast
		          have hge: "(1/2::real)^n \<le> d x0 y"
		          proof -
		            have "(1/2::real)^n * abs (fseq n x0 - fseq n y) \<le> d x0 y"
		              by (rule d_ge_term[OF hx0X hyX])
		            thus ?thesis
		              using hnx hfy by simp
			          qed
			          have "d x0 y < r"
			            using hy unfolding top1_ball_on_def by simp
			          have hlt: "d x0 y < (1/2::real)^n / 2"
			            using \<open>d x0 y < r\<close> unfolding r_def by simp
			          have hpos: "0 < (1/2::real)^n"
			            by simp
			          have hhalf: "(1/2::real)^n / 2 < (1/2::real)^n"
			            using hpos by linarith
			          have "d x0 y < (1/2::real)^n"
			            by (rule less_trans[OF hlt hhalf])
			          thus False
			            using hge by linarith
		        qed
		      qed
		      have hbasis: "top1_ball_on X d x0 r \<in> top1_metric_basis_on X d"
		        unfolding top1_metric_basis_on_def using hx0X hrpos by blast
		      show "\<exists>b\<in>top1_metric_basis_on X d. x0 \<in> b \<and> b \<subseteq> U"
		        apply (rule bexI[where x="top1_ball_on X d x0 r"])
		         apply (intro conjI)
		          apply (rule hx0ball)
		         apply (rule hsub)
		        apply (rule hbasis)
		        done
		    qed
		
		    have "U \<in> topology_generated_by_basis X (top1_metric_basis_on X d)"
		      unfolding topology_generated_by_basis_def
		      apply (rule CollectI)
		      apply (intro conjI)
		       apply (rule hUX)
		      apply (rule href)
		      done
		    thus "U \<in> top1_metric_topology_on X d"
		      unfolding top1_metric_topology_on_def by simp
		  qed
	
	  have hTXeq': "TX = top1_metric_topology_on X d"
	    using hMet_sub_TX hTX_sub_Met by blast
	
		  show "top1_metrizable_on X TX"
		    unfolding top1_metrizable_on_def
		    apply (rule exI[where x=d])
		    apply (intro conjI)
		     apply (rule d_metric)
		    apply (rule hTXeq')
		    done
		qed

(** from \S34 Theorem 34.2 (Imbedding theorem) [top1.tex:4744] **)
theorem Theorem_34_2:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hT1: "\<forall>x\<in>X. closedin_on X TX {x}"
  assumes hfcont: "\<forall>\<alpha>\<in>J. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f \<alpha>)"
  assumes hloc:
    "\<forall>x0\<in>X. \<forall>U. neighborhood_of x0 X TX U \<longrightarrow>
       (\<exists>\<alpha>\<in>J. 0 < f \<alpha> x0 \<and> (\<forall>x\<in>X - U. f \<alpha> x = 0))"
  defines "F x \<equiv> (\<lambda>\<alpha>. if \<alpha> \<in> J then f \<alpha> x else undefined)"
  shows "top1_embedding_on X TX
           (top1_PiE J (\<lambda>_. (UNIV::real set)))
           (top1_product_topology_on J (\<lambda>_. (UNIV::real set)) (\<lambda>_. order_topology_on_UNIV))
           F"
proof -
  let ?XR = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?Y = "top1_PiE J (\<lambda>_. ?XR)"
  let ?TY = "top1_product_topology_on J (\<lambda>_. ?XR) (\<lambda>_. ?TR)"
  let ?W = "F ` X"
  let ?TW = "subspace_topology ?Y ?TY ?W"

  have hTopR: "is_topology_on ?XR ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hTopComp: "\<forall>i\<in>J. is_topology_on ?XR ?TR"
    using hTopR by blast

  have hTopY: "is_topology_on ?Y ?TY"
    by (rule top1_product_topology_on_is_topology_on[OF hTopComp])

  have hFmap: "\<forall>x\<in>X. F x \<in> ?Y"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    show "F x \<in> ?Y"
      unfolding top1_PiE_iff F_def by simp
  qed

  have hcontF_Y: "top1_continuous_map_on X TX ?Y ?TY F"
  proof -
    have hiff:
      "top1_continuous_map_on X TX ?Y ?TY F \<longleftrightarrow>
       (\<forall>i\<in>J. top1_continuous_map_on X TX ?XR ?TR (\<lambda>x. (F x) i))"
      by (rule Theorem_19_6[OF hTopX hTopComp hFmap])

    have hcoords: "\<forall>i\<in>J. top1_continuous_map_on X TX ?XR ?TR (\<lambda>x. (F x) i)"
    proof (intro ballI)
      fix i assume hi: "i \<in> J"
      have hEq: "(\<lambda>x. (F x) i) = f i"
        by (rule ext, simp add: F_def hi)
      show "top1_continuous_map_on X TX ?XR ?TR (\<lambda>x. (F x) i)"
        unfolding hEq using hfcont hi by simp
    qed

    show ?thesis
      by (rule iffD2[OF hiff hcoords])
  qed

  have hWsubY: "?W \<subseteq> ?Y"
  proof (rule subsetI)
    fix y assume hyW: "y \<in> ?W"
    then obtain x where hxX: "x \<in> X" and hyEq: "y = F x"
      by blast
    have "F x \<in> ?Y"
      using hFmap hxX by blast
    thus "y \<in> ?Y"
      using hyEq by simp
  qed

  have hcontF_W: "top1_continuous_map_on X TX ?W ?TW F"
  proof -
    have hrestrict_all:
      "\<forall>W0 g.
        top1_continuous_map_on X TX ?Y ?TY g \<and> W0 \<subseteq> ?Y \<and> g ` X \<subseteq> W0
        \<longrightarrow> top1_continuous_map_on X TX W0 (subspace_topology ?Y ?TY W0) g"
      using Theorem_18_2(5)[OF hTopX hTopY hTopY] .
    have hpre: "top1_continuous_map_on X TX ?Y ?TY F \<and> ?W \<subseteq> ?Y \<and> F ` X \<subseteq> ?W"
      by (intro conjI, rule hcontF_Y, rule hWsubY, simp)
    show ?thesis
      using mp[OF spec[OF spec[OF hrestrict_all, where x="?W"], where x=F] hpre] .
  qed

  have hFinj: "inj_on F X"
  proof (rule inj_onI)
    fix x y
    assume hxX: "x \<in> X"
    assume hyX: "y \<in> X"
    assume hEq: "F x = F y"
    show "x = y"
    proof (rule ccontr)
      assume hxy: "x \<noteq> y"
      have hsing: "closedin_on X TX {y}"
        using hT1 hyX by blast
      have hUopen: "X - {y} \<in> TX"
        using hsing unfolding closedin_on_def by blast
      have hxU: "x \<in> X - {y}"
        using hxX hxy by blast
      have hnbd: "neighborhood_of x X TX (X - {y})"
        unfolding neighborhood_of_def using hUopen hxU by blast

      obtain i where hiJ: "i \<in> J" and hpos: "0 < f i x" and hzero: "\<forall>z\<in>X - (X - {y}). f i z = 0"
        using hloc hxX hnbd by blast

      have hyXU: "y \<in> X - (X - {y})"
        using hyX by simp
      have hfiy: "f i y = 0"
        using hzero hyXU by blast

      have hEqi: "(F x) i = (F y) i"
        using hEq by simp
      have hFix: "(F x) i = f i x"
        by (simp add: F_def hiJ)
      have hFiy: "(F y) i = f i y"
        by (simp add: F_def hiJ)

      have "f i x = f i y"
        using hEqi hFix hFiy by simp
      hence "f i x = 0"
        using hfiy by simp
      thus False
        using hpos by simp
    qed
  qed

  have hTopW: "is_topology_on ?W ?TW"
    by (rule subspace_topology_is_topology_on[OF hTopY hWsubY])

  have hcontInv: "top1_continuous_map_on ?W ?TW X TX (inv_into X F)"
  proof -
    have hiff:
      "top1_continuous_map_on ?W ?TW X TX (inv_into X F) \<longleftrightarrow>
       ((\<forall>y\<in>?W. inv_into X F y \<in> X)
        \<and> (\<forall>y\<in>?W. \<forall>V. neighborhood_of (inv_into X F y) X TX V \<longrightarrow>
             (\<exists>U. neighborhood_of y ?W ?TW U \<and> inv_into X F ` U \<subseteq> V)))"
      using Theorem_18_1(3)[OF hTopW hTopX, of "inv_into X F"] .

    have hmaps: "\<forall>y\<in>?W. inv_into X F y \<in> X"
    proof (intro ballI)
      fix y assume hyW: "y \<in> ?W"
      have hyFX: "y \<in> F ` X"
        using hyW by simp
      show "inv_into X F y \<in> X"
        by (rule inv_into_into[OF hyFX])
    qed

    have hnbd:
      "\<forall>y\<in>?W. \<forall>V. neighborhood_of (inv_into X F y) X TX V \<longrightarrow>
        (\<exists>U. neighborhood_of y ?W ?TW U \<and> inv_into X F ` U \<subseteq> V)"
    proof (intro ballI allI impI)
      fix y V
      assume hyW: "y \<in> ?W"
      assume hV: "neighborhood_of (inv_into X F y) X TX V"

      obtain x0 where hx0X: "x0 \<in> X" and hyEq: "y = F x0"
        using hyW by blast
      have hyinv: "inv_into X F y = x0"
        unfolding hyEq by (rule inv_into_f_f[OF hFinj hx0X])

      have hVx0: "neighborhood_of x0 X TX V"
        using hV hyinv by simp

      obtain i where hiJ: "i \<in> J" and hpos: "0 < f i x0" and hzero: "\<forall>x\<in>X - V. f i x = 0"
        using hloc hx0X hVx0 by blast

      define B where "B = {p \<in> ?Y. p i \<in> open_ray_gt (0::real)}"
      have hopen: "open_ray_gt (0::real) \<in> ?TR"
        by (rule open_ray_gt_in_order_topology)

      have hproj: "top1_continuous_map_on ?Y ?TY ?XR ?TR (\<lambda>p. p i)"
        by (rule top1_continuous_map_on_product_projection[OF hTopComp hiJ])
      have hBopen: "B \<in> ?TY"
      proof -
        have hpre: "\<forall>U\<in>?TR. {p \<in> ?Y. (\<lambda>p. p i) p \<in> U} \<in> ?TY"
          using hproj unfolding top1_continuous_map_on_def by blast
        have "{p \<in> ?Y. p i \<in> open_ray_gt (0::real)} \<in> ?TY"
          using hpre hopen by simp
        thus ?thesis
          unfolding B_def by simp
      qed

      have hyB: "y \<in> B"
      proof -
        have hFy: "(F x0) i = f i x0"
          by (simp add: F_def hiJ)
        have "f i x0 \<in> open_ray_gt (0::real)"
          unfolding open_ray_gt_def using hpos by simp
        hence "F x0 i \<in> open_ray_gt (0::real)"
          using hFy by simp
        thus ?thesis
          unfolding hyEq B_def using hx0X hFmap by simp
      qed

      define U where "U = ?W \<inter> B"
      have hUopen: "U \<in> ?TW"
        unfolding U_def subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x=B])
        using hBopen by simp
      have hyU: "y \<in> U"
        unfolding U_def using hyW hyB by blast
      have hUnbd: "neighborhood_of y ?W ?TW U"
        unfolding neighborhood_of_def using hUopen hyU by blast

      have hUsub: "inv_into X F ` U \<subseteq> V"
      proof (rule subsetI)
        fix z assume hz: "z \<in> inv_into X F ` U"
        then obtain p where hpU: "p \<in> U" and hzEq: "z = inv_into X F p"
          by blast
        have hpW: "p \<in> ?W" and hpB: "p \<in> B"
          using hpU unfolding U_def by blast+
        obtain x where hxX: "x \<in> X" and hpEq: "p = F x"
          using hpW by blast
        have hzEq': "z = x"
          unfolding hzEq hpEq by (rule inv_into_f_f[OF hFinj hxX])

        have hpi: "p i \<in> open_ray_gt (0::real)"
          using hpB unfolding B_def by simp
        have "0 < p i"
          using hpi unfolding open_ray_gt_def by simp
        hence hfxpos: "0 < f i x"
          unfolding hpEq by (simp add: F_def hiJ)

        have hxV: "x \<in> V"
        proof (rule ccontr)
          assume hxnot: "x \<notin> V"
          have hxout: "x \<in> X - V"
            using hxX hxnot by blast
          have "f i x = 0"
            using hzero hxout by blast
          thus False
            using hfxpos by simp
        qed

        show "z \<in> V"
          using hxV hzEq' by simp
      qed

      show "\<exists>U. neighborhood_of y ?W ?TW U \<and> inv_into X F ` U \<subseteq> V"
        by (rule exI[where x=U], intro conjI, rule hUnbd, rule hUsub)
    qed

    show ?thesis
      by (rule iffD2[OF hiff], intro conjI, rule hmaps, rule hnbd)
  qed

  have hbij: "bij_betw F X ?W"
    unfolding bij_betw_def
    apply (intro conjI)
     apply (rule hFinj)
    apply simp
    done

  have hhomeo: "top1_homeomorphism_on X TX ?W ?TW F"
    unfolding top1_homeomorphism_on_def
    apply (intro conjI)
        apply (rule hTopX)
       apply (rule subspace_topology_is_topology_on[OF hTopY hWsubY])
      apply (rule hbij)
     apply (rule hcontF_W)
    apply (rule hcontInv)
    done

  show ?thesis
    unfolding top1_embedding_on_def
    apply (intro conjI)
     apply (rule hWsubY)
    apply (rule hhomeo)
    done
qed

(** Restricting the ambient space of an embedding to a subspace that still contains the image. **)
lemma top1_embedding_on_restrict_codomain_subspace:
  assumes hEmb: "top1_embedding_on X TX Y TY f"
  assumes hYY: "Y' \<subseteq> Y"
  assumes himg: "f ` X \<subseteq> Y'"
  defines "TY' \<equiv> subspace_topology Y TY Y'"
  shows "top1_embedding_on X TX Y' TY' f"
proof -
  have hWsubY: "f ` X \<subseteq> Y"
    using hEmb unfolding top1_embedding_on_def by blast

  have hhomeo:
    "top1_homeomorphism_on X TX (f ` X) (subspace_topology Y TY (f ` X)) f"
    using hEmb unfolding top1_embedding_on_def by blast

  have hsub_eq:
    "subspace_topology Y' TY' (f ` X) = subspace_topology Y TY (f ` X)"
  proof -
    have hsub: "f ` X \<subseteq> Y'"
      by (rule himg)
    have "subspace_topology Y' (subspace_topology Y TY Y') (f ` X) = subspace_topology Y TY (f ` X)"
      by (rule subspace_topology_trans[OF hsub])
    thus ?thesis
      unfolding TY'_def by simp
  qed

  have hhomeo':
    "top1_homeomorphism_on X TX (f ` X) (subspace_topology Y' TY' (f ` X)) f"
    unfolding hsub_eq using hhomeo .

  show ?thesis
    unfolding top1_embedding_on_def
    apply (intro conjI)
     apply (rule himg)
    apply (rule hhomeo')
    done
qed

(** The product topology on \([0,1]^J\) is the subspace topology inherited from \(\<real>^J\). **)
lemma top1_product_topology_on_unit_interval_eq_subspace:
  fixes J :: "'i set"
  shows
    "top1_product_topology_on J (\<lambda>_. top1_closed_interval 0 1) (\<lambda>_. top1_closed_interval_topology 0 1)
     =
     subspace_topology
       (top1_PiE J (\<lambda>_. (UNIV::real set)))
       (top1_product_topology_on J (\<lambda>_. (UNIV::real set)) (\<lambda>_. order_topology_on_UNIV))
       (top1_PiE J (\<lambda>_. top1_closed_interval 0 1))"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?TR = "(\<lambda>_. order_topology_on_UNIV)"
  let ?YR = "top1_PiE J ?XR"
  let ?YI = "top1_PiE J (\<lambda>_. ?I)"
  let ?BR = "top1_product_basis_on J ?XR ?TR"
  let ?TYR = "top1_product_topology_on J ?XR ?TR"
  let ?BI = "top1_product_basis_on J (\<lambda>_. ?I) (\<lambda>_. ?TI)"

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopProdR: "\<forall>i\<in>J. is_topology_on (?XR i) (?TR i)"
    using hTopR by simp

  have hBasisProdR: "basis_for ?YR ?BR ?TYR"
    unfolding basis_for_def top1_product_topology_on_def
    apply (intro conjI)
     apply (rule top1_product_basis_is_basis_on[OF hTopProdR])
    apply simp
    done

  have hYIYR: "?YI \<subseteq> ?YR"
  proof -
    have "\<forall>i\<in>J. (\<lambda>_. ?I) i \<subseteq> ?XR i"
      by simp
    thus ?thesis
      by (rule top1_PiE_mono)
  qed

  define BY where "BY = {b \<inter> ?YI | b. b \<in> ?BR}"
  have hBasisSub: "basis_for ?YI BY (subspace_topology ?YR ?TYR ?YI)"
    by (rule Lemma_16_1[OF hBasisProdR hYIYR, folded BY_def])

  have hBY_eq_BI: "BY = ?BI"
  proof (rule equalityI)
    show "BY \<subseteq> ?BI"
    proof (rule subsetI)
      fix c assume hc: "c \<in> BY"
      obtain b where hb: "b \<in> ?BR" and hcEq: "c = b \<inter> ?YI"
        using hc unfolding BY_def by blast
      obtain U where hbdef: "b = top1_PiE J U"
        and hU: "(\<forall>i\<in>J. U i \<in> order_topology_on_UNIV \<and> U i \<subseteq> (UNIV::real set))
               \<and> finite {i \<in> J. U i \<noteq> (UNIV::real set)}"
        using hb unfolding top1_product_basis_on_def by blast

      define W where "W = (\<lambda>i. ?I \<inter> U i)"
      have hcEq': "c = top1_PiE J W"
      proof -
        have "c = (top1_PiE J (\<lambda>_. ?I)) \<inter> top1_PiE J U"
          unfolding hcEq hbdef by (simp add: Int_commute)
        also have "... = top1_PiE J (\<lambda>i. ?I \<inter> U i)"
          by (simp add: top1_PiE_Int)
        finally show ?thesis
          unfolding W_def by simp
      qed

      have hWcond: "(\<forall>i\<in>J. W i \<in> ?TI \<and> W i \<subseteq> ?I) \<and> finite {i \<in> J. W i \<noteq> ?I}"
      proof (intro conjI)
        show "\<forall>i\<in>J. W i \<in> ?TI \<and> W i \<subseteq> ?I"
        proof (intro ballI)
          fix i assume hi: "i \<in> J"
          have hUi: "U i \<in> order_topology_on_UNIV"
            using hU hi by blast
          have "W i = ?I \<inter> U i"
            unfolding W_def by simp
          moreover have "?I \<inter> U i \<in> ?TI"
            unfolding top1_closed_interval_topology_def subspace_topology_def
            apply (rule CollectI)
            apply (rule exI[where x="U i"])
            using hUi by simp
          ultimately have hWi: "W i \<in> ?TI"
            by simp
          show "W i \<in> ?TI \<and> W i \<subseteq> ?I"
            using hWi unfolding W_def by blast
        qed
        have hfinU: "finite {i \<in> J. U i \<noteq> (UNIV::real set)}"
          using hU by blast
        have hsub:
          "{i \<in> J. W i \<noteq> ?I} \<subseteq> {i \<in> J. U i \<noteq> (UNIV::real set)}"
        proof (rule subsetI)
          fix i assume hi: "i \<in> {i \<in> J. W i \<noteq> ?I}"
          have hiJ: "i \<in> J" and hWi: "W i \<noteq> ?I"
            using hi by blast+
          have "U i \<noteq> (UNIV::real set)"
          proof
            assume hUiU: "U i = (UNIV::real set)"
            have "W i = ?I"
              unfolding W_def using hUiU by simp
            thus False
              using hWi by contradiction
          qed
          show "i \<in> {i \<in> J. U i \<noteq> (UNIV::real set)}"
            using hiJ \<open>U i \<noteq> (UNIV::real set)\<close> by blast
        qed
        have "finite {i \<in> J. W i \<noteq> ?I}"
          by (rule finite_subset[OF hsub hfinU])
        thus "finite {i \<in> J. W i \<noteq> ?I}" .
      qed

      have "top1_PiE J W \<in> ?BI"
        unfolding top1_product_basis_on_def
        apply (rule CollectI)
        apply (rule exI[where x=W])
        using hWcond by blast
      thus "c \<in> ?BI"
        unfolding hcEq' .
    qed
    show "?BI \<subseteq> BY"
    proof (rule subsetI)
      fix c assume hc: "c \<in> ?BI"
      obtain U where hcdef: "c = top1_PiE J U"
        and hU: "(\<forall>i\<in>J. U i \<in> ?TI \<and> U i \<subseteq> ?I) \<and> finite {i \<in> J. U i \<noteq> ?I}"
        using hc unfolding top1_product_basis_on_def by blast

      have hex: "\<forall>i\<in>J. \<exists>V. V \<in> order_topology_on_UNIV \<and> (if U i = ?I then V = (UNIV::real set) else U i = ?I \<inter> V)"
      proof (intro ballI)
        fix i assume hi: "i \<in> J"
        show "\<exists>V. V \<in> order_topology_on_UNIV \<and> (if U i = ?I then V = (UNIV::real set) else U i = ?I \<inter> V)"
        proof (cases "U i = ?I")
          case True
          show ?thesis
            apply (rule exI[where x="UNIV::real set"])
            apply (intro conjI)
             apply (rule conjunct1[OF conjunct2[OF order_topology_on_UNIV_is_topology_on[unfolded is_topology_on_def]]])
            apply (simp add: True)
            done
        next
          case False
          have hUi: "U i \<in> ?TI"
            using hU hi by blast
          obtain V where hV: "V \<in> order_topology_on_UNIV" and hUiEq: "U i = ?I \<inter> V"
            using hUi unfolding top1_closed_interval_topology_def subspace_topology_def by blast
          show ?thesis
            apply (rule exI[where x=V])
            using hV hUiEq False by simp
        qed
      qed

      obtain V where hV:
        "\<forall>i\<in>J. V i \<in> order_topology_on_UNIV \<and> (if U i = ?I then V i = (UNIV::real set) else U i = ?I \<inter> V i)"
        using bchoice[OF hex] by blast

      define b where "b = top1_PiE J V"
      have hb: "b \<in> ?BR"
      proof -
        have hVcond:
          "(\<forall>i\<in>J. V i \<in> order_topology_on_UNIV \<and> V i \<subseteq> (UNIV::real set))
           \<and> finite {i \<in> J. V i \<noteq> (UNIV::real set)}"
        proof (intro conjI)
          show "\<forall>i\<in>J. V i \<in> order_topology_on_UNIV \<and> V i \<subseteq> (UNIV::real set)"
            using hV by blast
          have hfinU: "finite {i \<in> J. U i \<noteq> ?I}"
            using hU by blast
          have hsub:
            "{i \<in> J. V i \<noteq> (UNIV::real set)} \<subseteq> {i \<in> J. U i \<noteq> ?I}"
          proof (rule subsetI)
            fix i assume hi: "i \<in> {i \<in> J. V i \<noteq> (UNIV::real set)}"
            have hiJ: "i \<in> J" and hVi: "V i \<noteq> (UNIV::real set)"
              using hi by blast+
            have "U i \<noteq> ?I"
            proof
              assume hUi: "U i = ?I"
              have hVprop: "if U i = ?I then V i = (UNIV::real set) else U i = ?I \<inter> V i"
                using hV hiJ by blast
              have "V i = (UNIV::real set)"
                using hVprop hUi by simp
              thus False
                using hVi by contradiction
            qed
            show "i \<in> {i \<in> J. U i \<noteq> ?I}"
              using hiJ \<open>U i \<noteq> ?I\<close> by blast
          qed
          have "finite {i \<in> J. V i \<noteq> (UNIV::real set)}"
            by (rule finite_subset[OF hsub hfinU])
          thus "finite {i \<in> J. V i \<noteq> (UNIV::real set)}" .
        qed
        show ?thesis
          unfolding top1_product_basis_on_def b_def
          apply (rule CollectI)
          apply (rule exI[where x=V])
          using hVcond by blast
      qed

      have hEq_on: "\<forall>i\<in>J. ?I \<inter> V i = U i"
      proof (intro ballI)
        fix i assume hi: "i \<in> J"
        show "?I \<inter> V i = U i"
        proof (cases "U i = ?I")
          case True
          have hVprop: "if U i = ?I then V i = (UNIV::real set) else U i = ?I \<inter> V i"
            using hV hi by blast
          have "V i = (UNIV::real set)"
            using hVprop True by simp
          thus ?thesis
            using True by simp
        next
          case False
          have hVprop: "if U i = ?I then V i = (UNIV::real set) else U i = ?I \<inter> V i"
            using hV hi by blast
          have "U i = ?I \<inter> V i"
            using hVprop False by simp
          thus ?thesis
            by simp
        qed
      qed

      have hcEq': "?YI \<inter> b = c"
      proof -
        have "?YI \<inter> b = top1_PiE J (\<lambda>i. ?I \<inter> V i)"
          unfolding b_def by (simp add: top1_PiE_Int)
        also have "... = top1_PiE J U"
          by (rule top1_PiE_cong_on[OF hEq_on])
        finally show ?thesis
          unfolding hcdef by simp
      qed

	      have hcEq2: "c = b \<inter> ?YI"
	        using hcEq' by (simp add: Int_commute)
	      show "c \<in> BY"
	        unfolding BY_def
	      proof (rule CollectI)
	        show "\<exists>b'. c = b' \<inter> ?YI \<and> b' \<in> ?BR"
	        proof (rule exI[where x=b])
	          show "c = b \<inter> ?YI \<and> b \<in> ?BR"
	          proof (intro conjI)
	            show "c = b \<inter> ?YI"
	              by (rule hcEq2)
	            show "b \<in> ?BR"
	              by (rule hb)
	          qed
	        qed
	      qed
	    qed
	  qed

  have hSubEq:
    "subspace_topology ?YR ?TYR ?YI = topology_generated_by_basis ?YI BY"
    using conjunct2[OF hBasisSub[unfolded basis_for_def]] .

  have hProdEq:
    "top1_product_topology_on J (\<lambda>_. ?I) (\<lambda>_. ?TI) = topology_generated_by_basis ?YI ?BI"
    unfolding top1_product_topology_on_def by simp

  show ?thesis
    unfolding hProdEq
    unfolding hSubEq
    unfolding hBY_eq_BI
    by simp
qed

subsection \<open>Auxiliary lemmas for Theorem 34.3 (reverse direction)\<close>

text \<open>
  We use the standard strategy: the cube \<open>[0,1]^J\<close> is completely regular, subspaces inherit complete
  regularity, and complete regularity is invariant under homeomorphism (hence under embedding).
\<close>

lemma top1_abs_metric_on_UNIV_real:
  shows "top1_metric_on (UNIV::real set) (\<lambda>x y. abs (x - y))"
proof (unfold top1_metric_on_def, intro conjI)
  show "\<forall>x\<in>(UNIV::real set). 0 \<le> abs (x - x)"
    by simp
  show "\<forall>x\<in>(UNIV::real set). \<forall>y\<in>(UNIV::real set). 0 \<le> abs (x - y)"
    by simp
  show "\<forall>x\<in>(UNIV::real set). \<forall>y\<in>(UNIV::real set). (abs (x - y) = 0) = (x = y)"
    by simp
  show "\<forall>x\<in>(UNIV::real set). \<forall>y\<in>(UNIV::real set). abs (x - y) = abs (y - x)"
  proof (intro ballI)
    fix x y :: real
    show "abs (x - y) = abs (y - x)"
      by (simp add: abs_minus_commute)
  qed
  show "\<forall>x\<in>(UNIV::real set). \<forall>y\<in>(UNIV::real set). \<forall>z\<in>(UNIV::real set).
          abs (x - z) \<le> abs (x - y) + abs (y - z)"
  proof (intro ballI)
    fix x y z :: real
    show "abs (x - z) \<le> abs (x - y) + abs (y - z)"
    proof -
      have "abs (x - z) = abs ((x - y) + (y - z))"
        by simp
      also have "... \<le> abs (x - y) + abs (y - z)"
        by (rule abs_triangle_ineq)
      finally show ?thesis .
    qed
  qed
qed

lemma open_interval_in_abs_metric_topology:
  fixes a b :: real
  assumes hab: "a < b"
  shows "open_interval a b \<in> top1_metric_topology_on (UNIV::real set) (\<lambda>x y. abs (x - y))"
proof -
  let ?X = "(UNIV::real set)"
  let ?d = "(\<lambda>x y. abs (x - y))"
  have hU: "open_interval a b \<in> topology_generated_by_basis ?X (top1_metric_basis_on ?X ?d)"
    unfolding topology_generated_by_basis_def open_interval_def
  proof (rule CollectI, intro conjI)
    show "{x. a < x \<and> x < b} \<subseteq> (UNIV::real set)"
      by simp
    show "\<forall>x\<in>{x. a < x \<and> x < b}.
          \<exists>ba\<in>top1_metric_basis_on (UNIV::real set) (\<lambda>x y. abs (x - y)). x \<in> ba \<and> ba \<subseteq> {x. a < x \<and> x < b}"
	    proof (intro ballI)
	      fix x :: real
	      assume hx: "x \<in> {x. a < x \<and> x < b}"
	      have hax: "a < x" and hxb: "x < b"
	      proof -
	        have hx_conj: "a < x \<and> x < b"
	          using hx by simp
	        show "a < x"
	          using hx_conj by (rule conjunct1)
	        show "x < b"
	          using hx_conj by (rule conjunct2)
	      qed
	      define e where "e = min (x - a) (b - x)"
	      have hepos: "0 < e"
	        unfolding e_def using hax hxb by simp
      have hxball: "x \<in> top1_ball_on ?X ?d x e"
        unfolding top1_ball_on_def using hepos by simp
      have hball_basis: "top1_ball_on ?X ?d x e \<in> top1_metric_basis_on ?X ?d"
        unfolding top1_metric_basis_on_def using hepos by blast
      have hball_sub: "top1_ball_on ?X ?d x e \<subseteq> {t. a < t \<and> t < b}"
      proof (rule subsetI)
        fix t assume ht: "t \<in> top1_ball_on ?X ?d x e"
        have habs: "abs (x - t) < e"
          using ht unfolding top1_ball_on_def by blast
	        have habs': "abs (t - x) < e"
	          using habs by simp
	        have hconj: "-e < t - x \<and> t - x < e"
	          using habs' by (simp add: abs_less_iff)
	        have hlt0: "-e < t - x"
	          using hconj by blast
	        have hgt0: "t - x < e"
	          using hconj by blast
	        have hlt: "x - e < t"
	          using hlt0 by linarith
	        have hgt: "t < x + e"
	          using hgt0 by linarith
        have "e \<le> x - a"
          unfolding e_def by simp
        hence hle1: "a \<le> x - e"
          by simp
        have "e \<le> b - x"
          unfolding e_def by simp
        hence hle2: "x + e \<le> b"
          by simp
        have "a < t"
          by (rule le_less_trans[OF hle1 hlt])
        moreover have "t < b"
          by (rule less_le_trans[OF hgt hle2])
        ultimately show "t \<in> {t. a < t \<and> t < b}"
          by simp
      qed
      show "\<exists>ba\<in>top1_metric_basis_on ?X ?d. x \<in> ba \<and> ba \<subseteq> {x. a < x \<and> x < b}"
        apply (rule bexI[where x="top1_ball_on ?X ?d x e"])
         apply (intro conjI)
          apply (rule hxball)
         apply (rule hball_sub)
        apply (rule hball_basis)
        done
    qed
  qed
  show ?thesis
    unfolding top1_metric_topology_on_def using hU by simp
qed

lemma open_ray_gt_in_abs_metric_topology:
  fixes a :: real
  shows "open_ray_gt a \<in> top1_metric_topology_on (UNIV::real set) (\<lambda>x y. abs (x - y))"
proof -
  let ?X = "(UNIV::real set)"
  let ?d = "(\<lambda>x y. abs (x - y))"
  have hU: "open_ray_gt a \<in> topology_generated_by_basis ?X (top1_metric_basis_on ?X ?d)"
    unfolding topology_generated_by_basis_def open_ray_gt_def
  proof (rule CollectI, intro conjI)
    show "{x. a < x} \<subseteq> (UNIV::real set)"
      by simp
    show "\<forall>x\<in>{x. a < x}. \<exists>ba\<in>top1_metric_basis_on ?X ?d. x \<in> ba \<and> ba \<subseteq> {x. a < x}"
    proof (intro ballI)
      fix x :: real
      assume hx: "x \<in> {x. a < x}"
      have hax: "a < x" using hx by simp
      define e where "e = x - a"
      have hepos: "0 < e"
        unfolding e_def using hax by simp
      have hxball: "x \<in> top1_ball_on ?X ?d x e"
        unfolding top1_ball_on_def using hepos by simp
      have hball_basis: "top1_ball_on ?X ?d x e \<in> top1_metric_basis_on ?X ?d"
        unfolding top1_metric_basis_on_def using hepos by blast
      have hball_sub: "top1_ball_on ?X ?d x e \<subseteq> {t. a < t}"
      proof (rule subsetI)
        fix t assume ht: "t \<in> top1_ball_on ?X ?d x e"
        have habs: "abs (x - t) < e"
          using ht unfolding top1_ball_on_def by blast
	        have habs': "abs (t - x) < e"
	          using habs by simp
	        have hconj: "-e < t - x \<and> t - x < e"
	          using habs' by (simp add: abs_less_iff)
	        have hlt0: "-e < t - x"
	          using hconj by blast
	        have hlt: "x - e < t"
	          using hlt0 by linarith
        have "x - e = a"
          unfolding e_def by simp
        hence "a < t"
          using hlt by simp
        thus "t \<in> {t. a < t}"
          by simp
      qed
      show "\<exists>ba\<in>top1_metric_basis_on ?X ?d. x \<in> ba \<and> ba \<subseteq> {t. a < t}"
        apply (rule bexI[where x="top1_ball_on ?X ?d x e"])
         apply (intro conjI)
          apply (rule hxball)
         apply (rule hball_sub)
        apply (rule hball_basis)
        done
    qed
  qed
  show ?thesis
    unfolding top1_metric_topology_on_def using hU by simp
qed

lemma open_ray_lt_in_abs_metric_topology:
  fixes a :: real
  shows "open_ray_lt a \<in> top1_metric_topology_on (UNIV::real set) (\<lambda>x y. abs (x - y))"
proof -
  let ?X = "(UNIV::real set)"
  let ?d = "(\<lambda>x y. abs (x - y))"
  have hU: "open_ray_lt a \<in> topology_generated_by_basis ?X (top1_metric_basis_on ?X ?d)"
    unfolding topology_generated_by_basis_def open_ray_lt_def
  proof (rule CollectI, intro conjI)
    show "{x. x < a} \<subseteq> (UNIV::real set)"
      by simp
    show "\<forall>x\<in>{x. x < a}. \<exists>ba\<in>top1_metric_basis_on ?X ?d. x \<in> ba \<and> ba \<subseteq> {t. t < a}"
    proof (intro ballI)
      fix x :: real
      assume hx: "x \<in> {x. x < a}"
      have hxa: "x < a" using hx by simp
      define e where "e = a - x"
      have hepos: "0 < e"
        unfolding e_def using hxa by simp
      have hxball: "x \<in> top1_ball_on ?X ?d x e"
        unfolding top1_ball_on_def using hepos by simp
      have hball_basis: "top1_ball_on ?X ?d x e \<in> top1_metric_basis_on ?X ?d"
        unfolding top1_metric_basis_on_def using hepos by blast
      have hball_sub: "top1_ball_on ?X ?d x e \<subseteq> {t. t < a}"
      proof (rule subsetI)
        fix t assume ht: "t \<in> top1_ball_on ?X ?d x e"
        have habs: "abs (x - t) < e"
          using ht unfolding top1_ball_on_def by blast
	        have habs': "abs (t - x) < e"
	          using habs by simp
	        have hconj: "-e < t - x \<and> t - x < e"
	          using habs' by (simp add: abs_less_iff)
	        have hgt0: "t - x < e"
	          using hconj by blast
	        have hgt: "t < x + e"
	          using hgt0 by linarith
        have "x + e = a"
          unfolding e_def by simp
        hence "t < a"
          using hgt by simp
        thus "t \<in> {t. t < a}"
          by simp
      qed
      show "\<exists>ba\<in>top1_metric_basis_on ?X ?d. x \<in> ba \<and> ba \<subseteq> {t. t < a}"
        apply (rule bexI[where x="top1_ball_on ?X ?d x e"])
         apply (intro conjI)
          apply (rule hxball)
         apply (rule hball_sub)
        apply (rule hball_basis)
        done
    qed
  qed
  show ?thesis
    unfolding top1_metric_topology_on_def using hU by simp
qed

lemma order_topology_on_UNIV_real_eq_abs_metric_topology:
  shows "(order_topology_on_UNIV::real set set) =
    top1_metric_topology_on (UNIV::real set) (\<lambda>x y. abs (x - y))"
proof -
  let ?X = "(UNIV::real set)"
  let ?d = "(\<lambda>x y. abs (x - y))"
  let ?TM = "top1_metric_topology_on ?X ?d"

  have hd: "top1_metric_on ?X ?d"
    by (rule top1_abs_metric_on_UNIV_real)
  have hTopM: "is_topology_on ?X ?TM"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])

  have hBasisSub: "basis_order_topology \<subseteq> ?TM"
  proof (rule subsetI)
    fix b :: "real set"
    assume hb: "b \<in> basis_order_topology"
    have hbC:
      "(\<exists>a c. a < c \<and> b = open_interval a c)
       \<or> (\<exists>a. b = open_ray_gt a)
       \<or> (\<exists>a. b = open_ray_lt a)
       \<or> b = (UNIV::real set)"
      by (rule basis_order_topology_cases[OF hb])
    show "b \<in> ?TM"
    proof (rule disjE[OF hbC])
      assume hI: "\<exists>a c. a < c \<and> b = open_interval a c"
      then obtain a c where hac: "a < c" and hbEq: "b = open_interval a c"
        by blast
      show ?thesis
        unfolding hbEq by (rule open_interval_in_abs_metric_topology[OF hac])
    next
      assume hrest: "(\<exists>a. b = open_ray_gt a) \<or> (\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
      show ?thesis
      proof (rule disjE[OF hrest])
        assume hGt: "\<exists>a. b = open_ray_gt a"
        then obtain a where hbEq: "b = open_ray_gt a"
          by blast
        show ?thesis
          unfolding hbEq by (rule open_ray_gt_in_abs_metric_topology)
      next
        assume hrest2: "(\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
        show ?thesis
        proof (rule disjE[OF hrest2])
          assume hLt: "\<exists>a. b = open_ray_lt a"
          then obtain a where hbEq: "b = open_ray_lt a"
            by blast
          show ?thesis
            unfolding hbEq by (rule open_ray_lt_in_abs_metric_topology)
        next
          assume hbUniv: "b = (UNIV::real set)"
          have hUniv: "UNIV \<in> ?TM"
            by (rule conjunct1[OF conjunct2[OF hTopM[unfolded is_topology_on_def]]])
          show ?thesis
            unfolding hbUniv using hUniv by simp
        qed
      qed
    qed
  qed

  have hOrderSub: "order_topology_on_UNIV \<subseteq> ?TM"
    unfolding order_topology_on_UNIV_def
    by (rule topology_generated_by_basis_subset[OF hTopM hBasisSub])

  have hBallSub: "top1_metric_basis_on ?X ?d \<subseteq> order_topology_on_UNIV"
  proof (rule subsetI)
    fix b :: "real set"
    assume hb: "b \<in> top1_metric_basis_on ?X ?d"
    then obtain x e where he: "0 < e" and hbEq: "b = top1_ball_on ?X ?d x e"
      unfolding top1_metric_basis_on_def by blast
	    have hEq: "top1_ball_on ?X ?d x e = open_interval (x - e) (x + e)"
	    proof (rule set_eqI)
	      fix t :: real
	      show "t \<in> top1_ball_on ?X ?d x e \<longleftrightarrow> t \<in> open_interval (x - e) (x + e)"
	      proof -
	        have hball: "t \<in> top1_ball_on ?X ?d x e \<longleftrightarrow> abs (x - t) < e"
	          unfolding top1_ball_on_def by simp
	        have hint: "t \<in> open_interval (x - e) (x + e) \<longleftrightarrow> (x - e < t \<and> t < x + e)"
	          unfolding open_interval_def by simp
	        have habs_iff1: "abs (x - t) < e \<longleftrightarrow> (x - t < e \<and> t - x < e)"
	          by (simp add: abs_less_iff)
	        have habs_iff2: "(x - t < e \<and> t - x < e) \<longleftrightarrow> (x - e < t \<and> t < x + e)"
	          by linarith
	        have habs_iff: "abs (x - t) < e \<longleftrightarrow> (x - e < t \<and> t < x + e)"
	          using habs_iff1 habs_iff2 by blast
	        show ?thesis
	          unfolding hball hint using habs_iff by blast
	      qed
	    qed
	    have hBasis: "open_interval (x - e) (x + e) \<in> basis_order_topology"
	    proof -
	      have hlt: "x - e < x + e"
	        using he by linarith
	      have hmem: "open_interval (x - e) (x + e) \<in> {open_interval a b |a b. a < b}"
	        using hlt by blast
	      show ?thesis
	        unfolding basis_order_topology_def
	        using hmem by blast
	    qed
	    have hBO: "is_basis_on (UNIV::real set) basis_order_topology"
	      by (rule conjunct1[OF basis_for_order_topology_on_UNIV[unfolded basis_for_def]])
    have hOpen: "open_interval (x - e) (x + e) \<in> order_topology_on_UNIV"
      unfolding order_topology_on_UNIV_def
      by (rule basis_elem_open_in_generated_topology[OF hBO hBasis])
    show "b \<in> order_topology_on_UNIV"
      unfolding hbEq hEq using hOpen by simp
  qed

  have hTopOrder: "is_topology_on ?X (order_topology_on_UNIV::real set set)"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hMetricSub: "?TM \<subseteq> order_topology_on_UNIV"
    unfolding top1_metric_topology_on_def
    by (rule topology_generated_by_basis_subset[OF hTopOrder hBallSub])

  show ?thesis
    apply (rule equalityI)
     apply (rule hOrderSub)
    apply (rule hMetricSub)
    done
qed

lemma subspace_metric_topology_eq_metric_topology:
  assumes hd: "top1_metric_on X d"
  assumes hYX: "Y \<subseteq> X"
  shows "subspace_topology X (top1_metric_topology_on X d) Y = top1_metric_topology_on Y d"
proof -
  let ?TX = "top1_metric_topology_on X d"
  let ?TY = "top1_metric_topology_on Y d"
  have hTopX: "is_topology_on X ?TX"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])
  have hTopSub: "is_topology_on Y (subspace_topology X ?TX Y)"
    by (rule subspace_topology_is_topology_on[OF hTopX hYX])

  have hBsub1: "top1_metric_basis_on Y d \<subseteq> subspace_topology X ?TX Y"
  proof (rule subsetI)
    fix b assume hb: "b \<in> top1_metric_basis_on Y d"
    then obtain x e where hxY: "x \<in> Y" and he: "0 < e" and hbEq: "b = top1_ball_on Y d x e"
      unfolding top1_metric_basis_on_def by blast
    have hxX: "x \<in> X"
      using hYX hxY by blast
    have hballX: "top1_ball_on X d x e \<in> top1_metric_basis_on X d"
      unfolding top1_metric_basis_on_def using hxX he by blast
    have hBasisX: "is_basis_on X (top1_metric_basis_on X d)"
      by (rule top1_metric_basis_is_basis_on[OF hd])
    have hopenX: "top1_ball_on X d x e \<in> ?TX"
      unfolding top1_metric_topology_on_def
      by (rule basis_elem_open_in_generated_topology[OF hBasisX hballX])
    have hEq: "top1_ball_on Y d x e = Y \<inter> top1_ball_on X d x e"
      unfolding top1_ball_on_def using hYX by blast
    show "b \<in> subspace_topology X ?TX Y"
      unfolding hbEq subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="top1_ball_on X d x e"])
      apply (intro conjI)
       apply (simp add: hEq)
      apply (rule hopenX)
      done
  qed

  have hTY_sub: "?TY \<subseteq> subspace_topology X ?TX Y"
  proof -
    have hTY_def: "?TY = topology_generated_by_basis Y (top1_metric_basis_on Y d)"
      unfolding top1_metric_topology_on_def by simp
    have hInc: "topology_generated_by_basis Y (top1_metric_basis_on Y d) \<subseteq> subspace_topology X ?TX Y"
      by (rule topology_generated_by_basis_subset[OF hTopSub hBsub1])
    show ?thesis
      unfolding hTY_def using hInc by simp
  qed

  have hSub_sub: "subspace_topology X ?TX Y \<subseteq> ?TY"
  proof (rule subsetI)
    fix W assume hW: "W \<in> subspace_topology X ?TX Y"
    then obtain U where hU: "U \<in> ?TX" and hWeq: "W = Y \<inter> U"
      unfolding subspace_topology_def by blast
    have hWsub: "W \<subseteq> Y"
      unfolding hWeq by blast

    have hLocal: "\<forall>x\<in>W. \<exists>b\<in>top1_metric_basis_on Y d. x \<in> b \<and> b \<subseteq> W"
    proof (intro ballI)
      fix x assume hxW: "x \<in> W"
      have hxY: "x \<in> Y" and hxU: "x \<in> U"
        using hxW unfolding hWeq by blast+
      have hxX: "x \<in> X"
        using hYX hxY by blast
      obtain e where he: "e > 0" and hballU: "top1_ball_on X d x e \<subseteq> U"
        using top1_metric_open_contains_ball[OF hd hU hxU] by blast
	      have hEq: "top1_ball_on Y d x e = Y \<inter> top1_ball_on X d x e"
	        unfolding top1_ball_on_def using hYX by blast
	      have hxball: "x \<in> top1_ball_on Y d x e"
	      proof -
	        have hxx0: "d x x = 0"
	          using hd hxX unfolding top1_metric_on_def by blast
	        show ?thesis
	          unfolding top1_ball_on_def using hxY he hxx0 by simp
	      qed
      have hballW: "top1_ball_on Y d x e \<subseteq> W"
        unfolding hWeq hEq using hballU by blast
      have hballBasis: "top1_ball_on Y d x e \<in> top1_metric_basis_on Y d"
        unfolding top1_metric_basis_on_def using hxY he by blast
      show "\<exists>b\<in>top1_metric_basis_on Y d. x \<in> b \<and> b \<subseteq> W"
        apply (rule bexI[where x="top1_ball_on Y d x e"])
         apply (intro conjI)
          apply (rule hxball)
         apply (rule hballW)
        apply (rule hballBasis)
        done
    qed

    show "W \<in> ?TY"
      unfolding top1_metric_topology_on_def topology_generated_by_basis_def
      apply (rule CollectI)
      apply (intro conjI)
       apply (rule hWsub)
      apply (rule hLocal)
      done
  qed

  show ?thesis
    apply (rule equalityI)
     apply (rule hSub_sub)
    apply (rule hTY_sub)
    done
qed

lemma top1_closed_interval_metrizable:
  shows "top1_metrizable_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?d = "(\<lambda>x y. abs (x - y))"

  have hdI: "top1_metric_on ?I ?d"
    unfolding top1_metric_on_def
    apply (intro conjI ballI allI)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal
    proof -
      fix x y z :: real
      assume hx: "x \<in> ?I" and hy: "y \<in> ?I" and hz: "z \<in> ?I"
      have "abs (x - z) = abs ((x - y) + (y - z))"
        by simp
      also have "... \<le> abs (x - y) + abs (y - z)"
        by (rule abs_triangle_ineq)
      finally show "abs (x - z) \<le> abs (x - y) + abs (y - z)" .
    qed
    done

  have hTopEq: "order_topology_on_UNIV = top1_metric_topology_on (UNIV::real set) ?d"
    by (rule order_topology_on_UNIV_real_eq_abs_metric_topology)

  have hSubEq:
    "subspace_topology (UNIV::real set) order_topology_on_UNIV ?I =
     top1_metric_topology_on ?I ?d"
  proof -
    have hSubEq':
      "subspace_topology (UNIV::real set) (top1_metric_topology_on (UNIV::real set) ?d) ?I =
       top1_metric_topology_on ?I ?d"
      apply (rule subspace_metric_topology_eq_metric_topology)
       apply (rule top1_abs_metric_on_UNIV_real)
      apply simp
      done
    show ?thesis
      unfolding hTopEq using hSubEq' by simp
  qed

  have hTIeq: "?TI = top1_metric_topology_on ?I ?d"
    unfolding top1_closed_interval_topology_def
    using hSubEq by simp

  show ?thesis
    unfolding top1_metrizable_on_def
    apply (rule exI[where x="?d"])
    apply (intro conjI)
     apply (rule hdI)
    apply (rule hTIeq)
    done
qed

lemma normal_imp_completely_regular_on:
  assumes hN: "top1_normal_on X TX"
  shows "top1_completely_regular_on X TX"
proof -
  have hT1: "top1_T1_on X TX"
    using hN unfolding top1_normal_on_def by blast
  have hsing: "\<forall>x\<in>X. closedin_on X TX {x}"
    using hT1 unfolding top1_T1_on_def by blast

  show ?thesis
    unfolding top1_completely_regular_on_def
  proof (intro conjI)
    show "top1_T1_on X TX"
      by (rule hT1)
    show "\<forall>x0\<in>X. \<forall>A. closedin_on X TX A \<and> x0 \<notin> A \<longrightarrow>
        (\<exists>f::'a \<Rightarrow> real.
            top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f \<and>
            f x0 = 1 \<and> (\<forall>x\<in>A. f x = 0))"
    proof (intro ballI allI impI)
      fix x0 A
      assume hx0: "x0 \<in> X"
      assume hA0: "closedin_on X TX A \<and> x0 \<notin> A"
      have hAcl: "closedin_on X TX A" and hx0A: "x0 \<notin> A"
        using hA0 by blast+
      have hsing0: "closedin_on X TX {x0}"
        using hsing hx0 by blast
      have hdisj: "A \<inter> {x0} = {}"
        using hx0A by blast
	      have hab01: "(0::real) \<le> 1"
	        by simp
	      have hex:
	        "\<exists>f. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f
	             \<and> (\<forall>x\<in>A. f x = 0) \<and> (\<forall>x\<in>{x0}. f x = 1)"
	        by (rule Theorem_33_1[OF hN hAcl hsing0 hdisj hab01])
	      obtain f where hf:
	        "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f
	         \<and> (\<forall>x\<in>A. f x = 0) \<and> (\<forall>x\<in>{x0}. f x = 1)"
	        using hex by blast
      have hfcont: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f"
        using hf by blast
      have hfx0: "f x0 = 1"
        using hf by simp
      have hfA0': "\<forall>x\<in>A. f x = 0"
        using hf by blast
      show "\<exists>f::'a \<Rightarrow> real.
          top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f \<and>
          f x0 = 1 \<and> (\<forall>x\<in>A. f x = 0)"
        apply (rule exI[where x=f])
        apply (intro conjI)
          apply (rule hfcont)
         apply (rule hfx0)
        apply (rule hfA0')
        done
    qed
  qed
qed

lemma top1_closed_interval_completely_regular:
  shows "top1_completely_regular_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
proof -
  have hmet: "top1_metrizable_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
    by (rule top1_closed_interval_metrizable)
  have hN: "top1_normal_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
    by (rule Theorem_32_2[OF hmet])
  show ?thesis
    by (rule normal_imp_completely_regular_on[OF hN])
qed

lemma top1_continuous_min2_unit_interval:
  fixes f g :: "'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hf: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f"
  assumes hg: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) g"
  shows "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<lambda>x. min (f x) (g x))"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?TP = "product_topology_on ?TI ?TI"
  let ?pair = "(\<lambda>x. (f x, g x))"
  let ?m = "(\<lambda>p::real \<times> real. min (pi1 p) (pi2 p))"

  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF order_topology_on_UNIV_is_topology_on], simp)

  have hpi1: "top1_continuous_map_on X TX ?I ?TI (pi1 \<circ> ?pair)"
  proof -
    have hEq: "(pi1 \<circ> ?pair) = f"
      by (rule ext, simp add: o_def pi1_def)
    show ?thesis
      unfolding hEq by (rule hf)
  qed

  have hpi2: "top1_continuous_map_on X TX ?I ?TI (pi2 \<circ> ?pair)"
  proof -
    have hEq: "(pi2 \<circ> ?pair) = g"
      by (rule ext, simp add: o_def pi2_def)
    show ?thesis
      unfolding hEq by (rule hg)
  qed

  have hpair: "top1_continuous_map_on X TX (?I \<times> ?I) ?TP ?pair"
  proof -
    have hiff:
      "top1_continuous_map_on X TX (?I \<times> ?I) ?TP ?pair
       \<longleftrightarrow>
         (top1_continuous_map_on X TX ?I ?TI (pi1 \<circ> ?pair)
          \<and> top1_continuous_map_on X TX ?I ?TI (pi2 \<circ> ?pair))"
      by (rule Theorem_18_4[OF hTopX hTopI hTopI])
    show ?thesis
      apply (rule iffD2[OF hiff])
      apply (intro conjI)
       apply (rule hpi1)
      apply (rule hpi2)
      done
  qed

  have hm: "top1_continuous_map_on (?I \<times> ?I) ?TP ?I ?TI ?m"
    by (rule top1_continuous_min_unit_interval)

  have hEq: "(\<lambda>x. min (f x) (g x)) = ?m \<circ> ?pair"
    by (rule ext, simp add: o_def pi1_def pi2_def)

  show ?thesis
    unfolding hEq by (rule top1_continuous_map_on_comp[OF hpair hm])
qed

(** Basic finiteness helper: enumerate a finite set by a distinct list. **)
lemma finite_distinct_list_of_set:
  assumes hA: "finite A"
  shows "\<exists>xs. set xs = A \<and> distinct xs"
  using hA
proof (induct rule: finite_induct)
  case empty
  show ?case
    by (rule exI[where x="[]"], simp)
next
  case (insert a A)
  obtain xs where hxs: "set xs = A \<and> distinct xs"
    using insert by blast
  have ha: "a \<notin> set xs"
    using insert.hyps hxs by simp
  show ?case
    apply (rule exI[where x="a # xs"])
    using hxs ha by simp
qed

lemma top1_completely_regular_on_product_topology_on:
  assumes hCR: "\<forall>i\<in>I. top1_completely_regular_on (X i) (T i)"
  shows "top1_completely_regular_on (top1_PiE I X) (top1_product_topology_on I X T)"
proof -
  let ?P = "top1_PiE I X"
  let ?TP = "top1_product_topology_on I X T"
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"

  have hT1: "\<forall>i\<in>I. top1_T1_on (X i) (T i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have "top1_completely_regular_on (X i) (T i)"
      using hCR hi by blast
    thus "top1_T1_on (X i) (T i)"
      unfolding top1_completely_regular_on_def by (rule conjunct1)
  qed

  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have "top1_T1_on (X i) (T i)"
      using hT1 hi by blast
    thus "is_topology_on (X i) (T i)"
      unfolding top1_T1_on_def by (rule conjunct1)
  qed

  have hTopP: "is_topology_on ?P ?TP"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  have hHausd: "\<forall>i\<in>I. is_hausdorff_on (X i) (T i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hCRi: "top1_completely_regular_on (X i) (T i)"
      using hCR hi by blast
    have hRegi: "top1_regular_on (X i) (T i)"
      by (rule completely_regular_imp_regular_on[OF hCRi])
    show "is_hausdorff_on (X i) (T i)"
      by (rule regular_imp_hausdorff_on[OF hRegi])
  qed

  have hHausdP: "is_hausdorff_on ?P ?TP"
    by (rule Theorem_19_4_product[OF hHausd])

  have hT1P: "top1_T1_on ?P ?TP"
    by (rule hausdorff_imp_T1_on[OF hHausdP])

  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    apply (rule subspace_topology_is_topology_on)
     apply (rule order_topology_on_UNIV_is_topology_on)
    apply simp
    done

  show ?thesis
    unfolding top1_completely_regular_on_def
  proof (intro conjI)
    show "top1_T1_on ?P ?TP"
      by (rule hT1P)

    show "\<forall>p0\<in>?P. \<forall>A. closedin_on ?P ?TP A \<and> p0 \<notin> A \<longrightarrow>
       (\<exists>f. top1_continuous_map_on ?P ?TP ?I ?TI f \<and> f p0 = 1 \<and> (\<forall>p\<in>A. f p = 0))"
    proof (intro ballI allI impI)
      fix p0 A
      assume hp0: "p0 \<in> ?P"
      assume hA0: "closedin_on ?P ?TP A \<and> p0 \<notin> A"
      have hAcl: "closedin_on ?P ?TP A"
        by (rule conjunct1[OF hA0])
      have hp0A: "p0 \<notin> A"
        by (rule conjunct2[OF hA0])

      have hAsubP: "A \<subseteq> ?P"
        by (rule closedin_sub[OF hAcl])

      have hWopen: "?P - A \<in> ?TP"
        using hAcl unfolding closedin_on_def by blast
      have hp0W: "p0 \<in> ?P - A"
        using hp0 hp0A by blast

      have hWcov:
        "\<forall>p\<in>?P - A. \<exists>b\<in>top1_product_basis_on I X T. p \<in> b \<and> b \<subseteq> ?P - A"
        using hWopen
        unfolding top1_product_topology_on_def topology_generated_by_basis_def
        by blast

      obtain b where hbasis: "b \<in> top1_product_basis_on I X T"
        and hp0b: "p0 \<in> b"
        and hbsubW: "b \<subseteq> ?P - A"
        using hWcov hp0W by blast

      obtain U where hbEq: "b = top1_PiE I U"
        and hU: "(\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i)"
        and hUfin: "finite {i \<in> I. U i \<noteq> X i}"
        using hbasis unfolding top1_product_basis_on_def by blast

      define S where "S = {i \<in> I. U i \<noteq> X i}"
      have hSfin: "finite S"
        unfolding S_def using hUfin by simp

      have hSsubI: "S \<subseteq> I"
        unfolding S_def by blast

      have hp0X: "\<forall>i\<in>I. p0 i \<in> X i"
        using hp0 unfolding top1_PiE_iff by blast
      have hp0U: "\<forall>i\<in>I. p0 i \<in> U i"
        using hp0b unfolding hbEq top1_PiE_iff by blast

      have hb_disj_A: "b \<inter> A = {}"
      proof (rule equalityI)
        show "b \<inter> A \<subseteq> {}"
	        proof (rule subsetI)
	          fix p assume hp: "p \<in> b \<inter> A"
	          have hpA: "p \<in> A" by (rule IntD2[OF hp])
	          have hpW: "p \<in> ?P - A"
	            using hbsubW IntD1[OF hp] by blast
	          have "p \<notin> A"
	            using hpW by simp
	          thus "p \<in> {}"
	            using hpA by blast
	        qed
        show "{} \<subseteq> b \<inter> A"
          by (rule empty_subsetI)
      qed

      have hexF:
        "\<exists>F. top1_continuous_map_on ?P ?TP ?I ?TI F \<and> F p0 = 1
             \<and> (\<forall>p\<in>?P. (\<exists>i\<in>S. p i \<in> X i - U i) \<longrightarrow> F p = 0)"
      proof -
        obtain xs where hxs: "set xs = S" and hdist: "distinct xs"
          using finite_distinct_list_of_set[OF hSfin] by blast

        have hxsI: "set xs \<subseteq> I"
          using hxs hSsubI by simp

        have hexF_list:
          "set xs \<subseteq> I \<Longrightarrow>
             (\<exists>F. top1_continuous_map_on ?P ?TP ?I ?TI F \<and> F p0 = 1
                  \<and> (\<forall>p\<in>?P. (\<exists>i\<in>set xs. p i \<in> X i - U i) \<longrightarrow> F p = 0))"
        proof (induct xs)
          case Nil
          assume hset: "set [] \<subseteq> I"
          have h1mem: "1 \<in> ?I"
            unfolding top1_closed_interval_def by simp
          have hconst: "top1_continuous_map_on ?P ?TP ?I ?TI (\<lambda>p. (1::real))"
            by (rule top1_continuous_map_on_const[OF hTopP hTopI h1mem])
          show ?case
            apply (rule exI[where x="(\<lambda>p. (1::real))"])
            apply (intro conjI)
              apply (rule hconst)
             apply simp
            apply (intro ballI impI)
            apply simp
            done
        next
          case (Cons i xs)
          assume hset: "set (i # xs) \<subseteq> I"
          have hiI: "i \<in> I"
            using hset by simp
          have htail: "set xs \<subseteq> I"
            using hset by simp

          obtain F0 where hF0cont: "top1_continuous_map_on ?P ?TP ?I ?TI F0"
            and hF0p0: "F0 p0 = 1"
            and hF0zero: "\<forall>p\<in>?P. (\<exists>j\<in>set xs. p j \<in> X j - U j) \<longrightarrow> F0 p = 0"
            using Cons.hyps[OF htail] by blast

          have hTopi: "is_topology_on (X i) (T i)"
            using hTop hiI by blast
          have hUi: "U i \<in> T i"
            using hU hiI by blast
          have hXi_open: "X i \<in> T i"
            using hTopi unfolding is_topology_on_def by (rule conjunct1[OF conjunct2])
          have hXU_open: "X i \<inter> U i \<in> T i"
            by (rule topology_inter2[OF hTopi hXi_open hUi])

          have hAi_cl: "closedin_on (X i) (T i) (X i - U i)"
            apply (rule closedin_intro)
             apply (rule Diff_subset)
            apply (simp only: Diff_Diff_Int)
            apply (rule hXU_open)
            done

          have hp0Xi: "p0 i \<in> X i"
            by (rule bspec[OF hp0X hiI])
          have hp0Ui: "p0 i \<in> U i"
            by (rule bspec[OF hp0U hiI])
          have hp0Ai: "p0 i \<notin> X i - U i"
            using hp0Ui by blast

          have hCRi: "top1_completely_regular_on (X i) (T i)"
            using hCR hiI by blast
	          have hSepi:
	            "\<forall>x0\<in>X i. \<forall>A0. closedin_on (X i) (T i) A0 \<and> x0 \<notin> A0 \<longrightarrow>
	               (\<exists>f.
	                   top1_continuous_map_on (X i) (T i) ?I ?TI f \<and> f x0 = 1 \<and> (\<forall>x\<in>A0. f x = 0))"
	            using hCRi unfolding top1_completely_regular_on_def by (rule conjunct2)

	          have hexfi:
	            "\<exists>f.
	              top1_continuous_map_on (X i) (T i) ?I ?TI f \<and> f (p0 i) = 1 \<and> (\<forall>x\<in>X i - U i. f x = 0)"
          proof -
	            have hImp:
	              "closedin_on (X i) (T i) (X i - U i) \<and> p0 i \<notin> (X i - U i)
	               \<longrightarrow>
	                 (\<exists>f.
	                    top1_continuous_map_on (X i) (T i) ?I ?TI f \<and> f (p0 i) = 1 \<and> (\<forall>x\<in>X i - U i. f x = 0))"
	              by (rule spec[OF bspec[OF hSepi hp0Xi], where x="X i - U i"])
            show ?thesis
              apply (rule mp[OF hImp])
              apply (intro conjI)
               apply (rule hAi_cl)
              apply (rule hp0Ai)
              done
          qed

          obtain fi where hficont: "top1_continuous_map_on (X i) (T i) ?I ?TI fi"
            and hfip0: "fi (p0 i) = 1"
            and hfi0: "\<forall>x\<in>X i - U i. fi x = 0"
            using hexfi by blast

          have hproj: "top1_continuous_map_on ?P ?TP (X i) (T i) (\<lambda>p. p i)"
            by (rule top1_continuous_map_on_product_projection[OF hTop hiI])

          have hgi: "top1_continuous_map_on ?P ?TP ?I ?TI (\<lambda>p. fi (p i))"
          proof -
            have hEq: "(\<lambda>p. fi (p i)) = fi \<circ> (\<lambda>p. p i)"
              by (rule ext, simp add: o_def)
            show ?thesis
              unfolding hEq by (rule top1_continuous_map_on_comp[OF hproj hficont])
          qed

          define F1 where "F1 = (\<lambda>p. min (fi (p i)) (F0 p))"
          have hF1cont: "top1_continuous_map_on ?P ?TP ?I ?TI F1"
            unfolding F1_def
            by (rule top1_continuous_min2_unit_interval[OF hTopP hgi hF0cont])
          have hF1p0: "F1 p0 = 1"
            unfolding F1_def using hF0p0 hfip0 by simp

          have hF1zero:
            "\<forall>p\<in>?P. (\<exists>j\<in>set (i # xs). p j \<in> X j - U j) \<longrightarrow> F1 p = 0"
          proof (intro ballI impI)
            fix p assume hpP: "p \<in> ?P"
            assume hex: "\<exists>j\<in>set (i # xs). p j \<in> X j - U j"
            have hcases: "p i \<in> X i - U i \<or> (\<exists>j\<in>set xs. p j \<in> X j - U j)"
              using hex by simp
            show "F1 p = 0"
            proof (rule disjE[OF hcases])
	              assume hpi: "p i \<in> X i - U i"
	              have "fi (p i) = 0"
	                using hfi0 hpi by blast
	              thus ?thesis
	              proof -
	                have "F1 p = min (fi (p i)) (F0 p)"
	                  unfolding F1_def by simp
		                also have "... = min 0 (F0 p)"
		                  using \<open>fi (p i) = 0\<close> by simp
		                also have "... = 0"
		                proof -
		                  have hmapF0: "F0 p \<in> ?I"
		                    using hF0cont hpP unfolding top1_continuous_map_on_def by blast
		                  have h0: "0 \<le> F0 p"
		                    using hmapF0 unfolding top1_closed_interval_def by blast
		                  show "min 0 (F0 p) = 0"
		                    by (simp add: min_def h0)
		                qed
		                finally show "F1 p = 0" .
		              qed
	            next
	              assume htail': "\<exists>j\<in>set xs. p j \<in> X j - U j"
	              have "F0 p = 0"
	                using hF0zero hpP htail' by blast
	              thus ?thesis
	              proof -
	                have "F1 p = min (fi (p i)) (F0 p)"
	                  unfolding F1_def by simp
	                also have "... = min (fi (p i)) 0"
	                  using \<open>F0 p = 0\<close> by simp
	                also have "... = 0"
	                proof -
	                  have hmapfi: "fi (p i) \<in> ?I"
	                  proof -
	                    have hpXi: "p i \<in> X i"
	                      using hpP hiI unfolding top1_PiE_iff by blast
	                    have hfi_map: "\<forall>x\<in>X i. fi x \<in> ?I"
	                      using hficont unfolding top1_continuous_map_on_def by blast
	                    show ?thesis
	                      using hfi_map hpXi by blast
	                  qed
		                  have h0: "0 \<le> fi (p i)"
		                    using hmapfi unfolding top1_closed_interval_def by blast
		                  show "min (fi (p i)) 0 = 0"
		                  proof (cases "fi (p i) \<le> 0")
		                    case True
		                    have "fi (p i) = 0"
		                      using h0 True by linarith
		                    thus ?thesis
		                      using True by (simp add: min_def)
		                  next
		                    case False
		                    thus ?thesis
		                      by (simp add: min_def)
		                  qed
		                qed
		                finally show "F1 p = 0" .
		              qed
	            qed
	          qed

          show ?case
            apply (rule exI[where x=F1])
            apply (intro conjI)
              apply (rule hF1cont)
             apply (rule hF1p0)
            apply (rule hF1zero)
            done
        qed

        have "\<exists>F. top1_continuous_map_on ?P ?TP ?I ?TI F \<and> F p0 = 1
              \<and> (\<forall>p\<in>?P. (\<exists>i\<in>set xs. p i \<in> X i - U i) \<longrightarrow> F p = 0)"
          by (rule hexF_list[OF hxsI])
        thus ?thesis
          unfolding hxs by simp
      qed

      obtain F where hFcont: "top1_continuous_map_on ?P ?TP ?I ?TI F"
        and hFp0: "F p0 = 1"
        and hFzero: "\<forall>p\<in>?P. (\<exists>i\<in>S. p i \<in> X i - U i) \<longrightarrow> F p = 0"
        using hexF by blast

      have hAcoord:
        "\<forall>p\<in>A. \<exists>i\<in>S. p i \<in> X i - U i"
      proof (intro ballI)
        fix p assume hpA: "p \<in> A"
        have hpP: "p \<in> ?P"
          using hAsubP hpA by blast
        have hpnotb: "p \<notin> b"
        proof
          assume hpb: "p \<in> b"
          have "p \<in> ?P - A"
            using hbsubW hpb by blast
          thus False
            using hpA by simp
        qed

        have hpExt: "\<forall>j. j \<notin> I \<longrightarrow> p j = undefined"
          using hpP unfolding top1_PiE_iff by blast
        have hpXi: "\<forall>j\<in>I. p j \<in> X j"
          using hpP unfolding top1_PiE_iff by blast

        have hpnotU: "\<exists>i\<in>I. p i \<notin> U i"
        proof -
          have hnot: "p \<notin> top1_PiE I U"
            using hpnotb unfolding hbEq by simp
          have hnot': "\<not> ((\<forall>i\<in>I. p i \<in> U i) \<and> (\<forall>j. j \<notin> I \<longrightarrow> p j = undefined))"
            using hnot unfolding top1_PiE_iff by simp
          have "\<not> (\<forall>i\<in>I. p i \<in> U i)"
            using hnot' hpExt by blast
          thus ?thesis
            by blast
        qed

        obtain i where hiI: "i \<in> I" and hpiU: "p i \<notin> U i"
          using hpnotU by blast

        have hpiX: "p i \<in> X i"
          using hpXi hiI by blast

        have hiS: "i \<in> S"
        proof (rule ccontr)
          assume hinot: "i \<notin> S"
          have hUiX: "U i = X i"
            using hinot hiI unfolding S_def by blast
          have "p i \<in> U i"
            using hpiX hUiX by simp
          thus False
            using hpiU by blast
        qed

        have "p i \<in> X i - U i"
          using hpiX hpiU by blast
        show "\<exists>i\<in>S. p i \<in> X i - U i"
          by (rule bexI[where x=i], rule \<open>p i \<in> X i - U i\<close>, rule hiS)
      qed

      have hF_A0: "\<forall>p\<in>A. F p = 0"
      proof (intro ballI)
        fix p assume hpA: "p \<in> A"
        have hpP: "p \<in> ?P"
          using hAsubP hpA by blast
        obtain i where hiS: "i \<in> S" and hpi: "p i \<in> X i - U i"
          using hAcoord hpA by blast
        have "(\<exists>i\<in>S. p i \<in> X i - U i)"
          by (rule bexI[where x=i], rule hpi, rule hiS)
        have "F p = 0"
          using hFzero hpP \<open>\<exists>i\<in>S. p i \<in> X i - U i\<close> by blast
        show "F p = 0"
          by (rule \<open>F p = 0\<close>)
      qed

      show "\<exists>f. top1_continuous_map_on ?P ?TP ?I ?TI f \<and> f p0 = 1 \<and> (\<forall>p\<in>A. f p = 0)"
        apply (rule exI[where x=F])
        apply (intro conjI)
          apply (rule hFcont)
         apply (rule hFp0)
        apply (rule hF_A0)
        done
    qed
  qed
qed

lemma top1_homeomorphism_on_imp_completely_regular_on:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
  assumes hCRY: "top1_completely_regular_on Y TY"
  shows "top1_completely_regular_on X TX"
proof -
  have hTopX: "is_topology_on X TX"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hbij: "bij_betw f X Y"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hcontf: "top1_continuous_map_on X TX Y TY f"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hcontinv: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hhomeo unfolding top1_homeomorphism_on_def by blast

  have hT1Y: "top1_T1_on Y TY"
    using hCRY unfolding top1_completely_regular_on_def by blast
  have hTopX': "is_topology_on X TX"
    using hTopX .

  have hT1X: "top1_T1_on X TX"
  proof (unfold top1_T1_on_def, intro conjI)
    show "is_topology_on X TX"
      by (rule hTopX')
    show "\<forall>x\<in>X. closedin_on X TX {x}"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have hyY: "f x \<in> Y"
        using hbij hxX unfolding bij_betw_def by blast
      have hsingY: "closedin_on Y TY {f x}"
        using hT1Y hyY unfolding top1_T1_on_def by blast

      have hprecl: "closedin_on X TX {u\<in>X. f u \<in> {f x}}"
        using Theorem_18_1(2)[OF hTopX hTopY, of f] hcontf hsingY by blast

      have hEq: "{u\<in>X. f u \<in> {f x}} = {x}"
      proof (rule equalityI)
        show "{u \<in> X. f u \<in> {f x}} \<subseteq> {x}"
	        proof (rule subsetI)
	          fix u assume hu: "u \<in> {u \<in> X. f u \<in> {f x}}"
	          have huX: "u \<in> X" and hfu: "f u = f x"
	          proof -
	            have hu_conj: "u \<in> X \<and> f u \<in> {f x}"
	              using hu by simp
	            have huX: "u \<in> X"
	              using hu_conj by (rule conjunct1)
	            have hfu_set: "f u \<in> {f x}"
	              using hu_conj by (rule conjunct2)
	            have hfu: "f u = f x"
	              using hfu_set by simp
	            show "u \<in> X" by (rule huX)
	            show "f u = f x" by (rule hfu)
	          qed
	          have hinj: "inj_on f X"
	            using hbij unfolding bij_betw_def by blast
	          have "u = x"
	            by (rule hinj[unfolded inj_on_def, rule_format, OF huX hxX hfu])
          thus "u \<in> {x}"
            by simp
        qed
        show "{x} \<subseteq> {u \<in> X. f u \<in> {f x}}"
          using hxX by simp
      qed

      show "closedin_on X TX {x}"
        using hprecl unfolding hEq by simp
    qed
  qed

  have hSepY:
    "\<forall>y0\<in>Y. \<forall>B. closedin_on Y TY B \<and> y0 \<notin> B \<longrightarrow>
       (\<exists>g::'b \<Rightarrow> real.
           top1_continuous_map_on Y TY (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) g
           \<and> g y0 = 1 \<and> (\<forall>y\<in>B. g y = 0))"
    using hCRY unfolding top1_completely_regular_on_def by blast

  show ?thesis
    unfolding top1_completely_regular_on_def
  proof (intro conjI)
    show "top1_T1_on X TX"
      by (rule hT1X)

    show "\<forall>x0\<in>X. \<forall>A. closedin_on X TX A \<and> x0 \<notin> A \<longrightarrow>
       (\<exists>h::'a \<Rightarrow> real.
           top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) h
           \<and> h x0 = 1 \<and> (\<forall>x\<in>A. h x = 0))"
    proof (intro ballI allI impI)
      fix x0 A
      assume hx0: "x0 \<in> X"
      assume hA: "closedin_on X TX A \<and> x0 \<notin> A"
      have hAcl: "closedin_on X TX A"
        using hA by blast
      have hx0A: "x0 \<notin> A"
        using hA by blast

      have hAsub: "A \<subseteq> X"
        by (rule closedin_sub[OF hAcl])

      have hImgClosed: "closedin_on Y TY (f ` A)"
      proof -
        define inv where "inv = inv_into X f"
        have hinj: "inj_on f X"
          using hbij unfolding bij_betw_def by blast
        have hsurj: "f ` X = Y"
          using hbij unfolding bij_betw_def by blast

        have hcontinv': "top1_continuous_map_on Y TY X TX inv"
          unfolding inv_def by (rule hcontinv)

        have hinv_closed_pre:
          "\<forall>B. closedin_on X TX B \<longrightarrow> closedin_on Y TY {y\<in>Y. inv y \<in> B}"
        proof -
          have hiff:
            "top1_continuous_map_on Y TY X TX inv \<longleftrightarrow>
              ((\<forall>y\<in>Y. inv y \<in> X) \<and>
               (\<forall>B. closedin_on X TX B \<longrightarrow> closedin_on Y TY {y\<in>Y. inv y \<in> B}))"
            using Theorem_18_1(2)[OF hTopY hTopX, of inv] .
          have hpre: "(\<forall>B. closedin_on X TX B \<longrightarrow> closedin_on Y TY {y\<in>Y. inv y \<in> B})"
            using iffD1[OF hiff] hcontinv' by blast
          show ?thesis
            using hpre .
        qed

        have hCclosed: "closedin_on Y TY {y\<in>Y. inv y \<in> A}"
          using hinv_closed_pre hAcl by blast

        have hEq: "{y\<in>Y. inv y \<in> A} = f ` A"
        proof (rule equalityI)
          show "{y \<in> Y. inv y \<in> A} \<subseteq> f ` A"
          proof (rule subsetI)
            fix y assume hy: "y \<in> {y \<in> Y. inv y \<in> A}"
            have hyY: "y \<in> Y" and hinvA: "inv y \<in> A"
              using hy by blast+
            have hyFX: "y \<in> f ` X"
              using hyY hsurj by simp
            have hyEq: "f (inv y) = y"
              unfolding inv_def by (rule f_inv_into_f[OF hyFX])
            have "y = f (inv y)"
              using hyEq by simp
            thus "y \<in> f ` A"
              apply (subst \<open>y = f (inv y)\<close>)
              apply (rule imageI)
              apply (rule hinvA)
              done
          qed
          show "f ` A \<subseteq> {y \<in> Y. inv y \<in> A}"
          proof (rule subsetI)
            fix y assume hy: "y \<in> f ` A"
            then obtain a where haA: "a \<in> A" and hyEq: "y = f a"
              by blast
            have haX: "a \<in> X"
              using hAsub haA by blast
            have hyY: "y \<in> Y"
              using hy hsurj hAsub by blast
            have hinv: "inv y = a"
            proof -
              have "inv (f a) = a"
                unfolding inv_def by (rule inv_into_f_f[OF hinj haX])
              thus ?thesis
                using hyEq by simp
            qed
            show "y \<in> {y \<in> Y. inv y \<in> A}"
              apply (rule CollectI)
              apply (intro conjI)
               apply (rule hyY)
              unfolding hinv
              apply (rule haA)
              done
          qed
        qed

        show "closedin_on Y TY (f ` A)"
          using hCclosed unfolding hEq by simp
      qed

      have hf_x0_notin: "f x0 \<notin> f ` A"
      proof
        assume hfx0: "f x0 \<in> f ` A"
        obtain a where haA: "a \<in> A" and hfa: "f x0 = f a"
          using hfx0 by blast
        have haX: "a \<in> X"
          using hAsub haA by blast
	        have hinj: "inj_on f X"
	          using hbij unfolding bij_betw_def by blast
	        have "x0 = a"
	        proof -
	          have hInj: "\<forall>u\<in>X. \<forall>v\<in>X. f u = f v \<longrightarrow> u = v"
	            using hinj unfolding inj_on_def by blast
	          have "f x0 = f a"
	            by (rule hfa)
	          thus "x0 = a"
	            using hInj hx0 haX by blast
	        qed
	        thus False
	          using hx0A haA by simp
	      qed

      have hexg:
        "\<exists>g::'b \<Rightarrow> real.
           top1_continuous_map_on Y TY (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) g
           \<and> g (f x0) = 1 \<and> (\<forall>y\<in>f ` A. g y = 0)"
      proof -
        have hfX: "f x0 \<in> Y"
          using hbij hx0 unfolding bij_betw_def by blast
        have hSep_fx0:
          "\<forall>B. closedin_on Y TY B \<and> f x0 \<notin> B \<longrightarrow>
             (\<exists>g::'b \<Rightarrow> real.
                top1_continuous_map_on Y TY (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) g
                \<and> g (f x0) = 1 \<and> (\<forall>y\<in>B. g y = 0))"
          by (rule bspec[OF hSepY hfX])
        have hImp:
          "closedin_on Y TY (f ` A) \<and> f x0 \<notin> (f ` A)
           \<longrightarrow>
           (\<exists>g::'b \<Rightarrow> real.
              top1_continuous_map_on Y TY (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) g
              \<and> g (f x0) = 1 \<and> (\<forall>y\<in>f ` A. g y = 0))"
          by (rule spec[OF hSep_fx0, where x="f ` A"])
        show ?thesis
          apply (rule mp[OF hImp])
          apply (intro conjI)
           apply (rule hImgClosed)
          apply (rule hf_x0_notin)
          done
      qed

      obtain g where hgcont: "top1_continuous_map_on Y TY (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) g"
        and hgf: "g (f x0) = 1"
        and hg0: "\<forall>y\<in>f ` A. g y = 0"
        using hexg by blast

      define h where "h = g \<circ> f"
      have hhcont:
        "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) h"
        unfolding h_def by (rule top1_continuous_map_on_comp[OF hcontf hgcont])

      have hhx0: "h x0 = 1"
        unfolding h_def using hgf by (simp add: o_def)

      have hhA0: "\<forall>x\<in>A. h x = 0"
      proof (intro ballI)
        fix x assume hxA: "x \<in> A"
        have "f x \<in> f ` A"
          by (rule imageI[OF hxA])
        have "g (f x) = 0"
          using hg0 \<open>f x \<in> f ` A\<close> by blast
        thus "h x = 0"
          unfolding h_def by (simp add: o_def)
      qed

      show "\<exists>h::'a \<Rightarrow> real.
           top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) h
           \<and> h x0 = 1 \<and> (\<forall>x\<in>A. h x = 0)"
        apply (rule exI[where x=h])
        apply (intro conjI)
          apply (rule hhcont)
         apply (rule hhx0)
        apply (rule hhA0)
        done
    qed
  qed
qed

(** from \S34 Theorem 34.3 (Completely regular spaces embed into a cube) [top1.tex:4765] **)
theorem Theorem_34_3_forward:
  assumes hCR: "top1_completely_regular_on X TX"
  shows "\<exists>J::('a \<Rightarrow> real) set. \<exists>F::'a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real).
    top1_embedding_on X TX
      (top1_PiE J (\<lambda>_. top1_closed_interval 0 1))
      (top1_product_topology_on J (\<lambda>_. top1_closed_interval 0 1) (\<lambda>_. top1_closed_interval_topology 0 1))
      F"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?TR = "(\<lambda>_. order_topology_on_UNIV)"

  have hT1: "top1_T1_on X TX"
    using hCR unfolding top1_completely_regular_on_def by blast
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by blast
  have hT1sing: "\<forall>x\<in>X. closedin_on X TX {x}"
    using hT1 unfolding top1_T1_on_def by blast

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    apply (rule subspace_topology_is_topology_on)
     apply (rule hTopR)
    apply simp
    done

  define J where "J = {f::'a \<Rightarrow> real. top1_continuous_map_on X TX ?I ?TI f}"
  define F where "F x = (\<lambda>f. if f \<in> J then f x else undefined)" for x

  have hfcontR: "\<forall>f\<in>J. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
  proof (intro ballI)
    fix f assume hfJ: "f \<in> J"
    have hfI: "top1_continuous_map_on X TX ?I ?TI f"
      using hfJ unfolding J_def by simp
    show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
    proof -
      have hTopUNIV: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
        by (rule hTopR)
      have hTI_eq: "?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I"
        unfolding top1_closed_interval_topology_def by simp
      have hexpand:
        "\<forall>W g. top1_continuous_map_on X TX ?I ?TI g \<and> ?I \<subseteq> W \<and> ?TI = subspace_topology W order_topology_on_UNIV ?I
          \<longrightarrow> top1_continuous_map_on X TX W order_topology_on_UNIV g"
        using Theorem_18_2(6)[OF hTopX hTopI hTopUNIV] .
      have hImp:
        "top1_continuous_map_on X TX ?I ?TI f \<and> ?I \<subseteq> (UNIV::real set) \<and> ?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I
          \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
        by (rule spec[OF spec[OF hexpand, where x="UNIV::real set"], where x=f])
      have hPre:
        "top1_continuous_map_on X TX ?I ?TI f \<and> ?I \<subseteq> (UNIV::real set) \<and> ?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I"
        using hfI hTI_eq by simp
      show ?thesis
        by (rule mp[OF hImp hPre])
    qed
  qed

  have hSep:
    "\<forall>x0\<in>X. \<forall>A. closedin_on X TX A \<and> x0 \<notin> A \<longrightarrow>
       (\<exists>f::'a \<Rightarrow> real.
          top1_continuous_map_on X TX ?I ?TI f \<and> f x0 = 1 \<and> (\<forall>x\<in>A. f x = 0))"
    using hCR unfolding top1_completely_regular_on_def by blast

  have hloc:
    "\<forall>x0\<in>X. \<forall>U. neighborhood_of x0 X TX U \<longrightarrow>
       (\<exists>f\<in>J. 0 < f x0 \<and> (\<forall>x\<in>X - U. f x = 0))"
  proof (intro ballI allI impI)
    fix x0 U
    assume hx0X: "x0 \<in> X"
    assume hnbd: "neighborhood_of x0 X TX U"
    have hUopen: "U \<in> TX" and hx0U: "x0 \<in> U"
      using hnbd unfolding neighborhood_of_def by blast+
    have hXopen: "X \<in> TX"
      using hTopX unfolding is_topology_on_def by blast
    let ?A = "X - U"
    have hAcl: "closedin_on X TX ?A"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?A \<subseteq> X"
        by simp
      have "X \<inter> U \<in> TX"
        by (rule topology_inter2[OF hTopX hXopen hUopen])
      moreover have "X - ?A = X \<inter> U"
        by blast
      ultimately show "X - ?A \<in> TX"
        by simp
    qed

    have hx0A: "x0 \<notin> ?A"
      using hx0U hx0X by blast

    obtain f where hfI: "top1_continuous_map_on X TX ?I ?TI f"
      and hfx0: "f x0 = 1" and hfA0: "\<forall>x\<in>?A. f x = 0"
      using hSep hx0X hAcl hx0A by blast

    have hfJ: "f \<in> J"
      unfolding J_def using hfI by simp

    have hpos: "0 < f x0"
      using hfx0 by simp

    have hfout: "\<forall>x\<in>X - U. f x = 0"
      using hfA0 by simp

    show "\<exists>f\<in>J. 0 < f x0 \<and> (\<forall>x\<in>X - U. f x = 0)"
      apply (rule bexI[where x=f])
       apply (intro conjI)
        apply (rule hpos)
       apply (rule hfout)
      apply (rule hfJ)
      done
  qed

  have hEmbR:
    "top1_embedding_on X TX
      (top1_PiE J ?XR)
      (top1_product_topology_on J ?XR ?TR)
      F"
  proof -
    have hEmb:
      "top1_embedding_on X TX
        (top1_PiE J ?XR)
        (top1_product_topology_on J ?XR ?TR)
        F"
      by (rule Theorem_34_2[where f="(\<lambda>g::('a \<Rightarrow> real). g)" and J=J, folded F_def],
          rule hTopX, rule hT1sing, rule hfcontR, rule hloc)
    show ?thesis
      by (rule hEmb)
  qed

  have hFimgI: "F ` X \<subseteq> top1_PiE J (\<lambda>_. ?I)"
  proof (rule subsetI)
    fix y assume hy: "y \<in> F ` X"
    then obtain x where hxX: "x \<in> X" and hyEq: "y = F x"
      by blast
    have hmem: "\<forall>f\<in>J. (F x) f \<in> ?I"
    proof (intro ballI)
      fix f assume hfJ: "f \<in> J"
      have hfI: "top1_continuous_map_on X TX ?I ?TI f"
        using hfJ unfolding J_def by simp
      have hmap: "\<forall>z\<in>X. f z \<in> ?I"
        using hfI unfolding top1_continuous_map_on_def by blast
      have "(F x) f = f x"
        unfolding F_def using hfJ by simp
      thus "(F x) f \<in> ?I"
        using hmap hxX by simp
    qed
    have hext: "\<forall>f. f \<notin> J \<longrightarrow> (F x) f = undefined"
      unfolding F_def by simp
    have "F x \<in> top1_PiE J (\<lambda>_. ?I)"
      unfolding top1_PiE_iff using hmem hext by blast
    thus "y \<in> top1_PiE J (\<lambda>_. ?I)"
      using hyEq by simp
  qed

  have hTopEq:
    "top1_product_topology_on J (\<lambda>_. ?I) (\<lambda>_. ?TI)
     =
     subspace_topology
       (top1_PiE J ?XR)
       (top1_product_topology_on J ?XR ?TR)
       (top1_PiE J (\<lambda>_. ?I))"
    by (rule top1_product_topology_on_unit_interval_eq_subspace)

  have hEmbI':
    "top1_embedding_on X TX
      (top1_PiE J (\<lambda>_. ?I))
      (subspace_topology
        (top1_PiE J ?XR)
        (top1_product_topology_on J ?XR ?TR)
        (top1_PiE J (\<lambda>_. ?I)))
      F"
  proof -
    have hYsub:
      "top1_PiE J (\<lambda>_. ?I) \<subseteq> top1_PiE J ?XR"
    proof -
      have "\<forall>i\<in>J. (\<lambda>_. ?I) i \<subseteq> ?XR i"
        by simp
      thus ?thesis
        by (rule top1_PiE_mono)
    qed
    show ?thesis
    proof -
	      have hEmbTmp:
	        "top1_embedding_on X TX (top1_PiE J (\<lambda>_. ?I))
	          (subspace_topology (top1_PiE J ?XR) (top1_product_topology_on J ?XR ?TR) (top1_PiE J (\<lambda>_. ?I))) F"
		      proof -
		        show ?thesis
		          apply (rule top1_embedding_on_restrict_codomain_subspace[OF hEmbR hYsub hFimgI])
		          done
		      qed
	      show ?thesis
	        by (rule hEmbTmp)
	    qed
	  qed

	  have hEmbI:
	    "top1_embedding_on X TX
	      (top1_PiE J (\<lambda>_. ?I))
	      (top1_product_topology_on J (\<lambda>_. ?I) (\<lambda>_. ?TI))
	      F"
	    unfolding hTopEq using hEmbI' by simp
	
		  show ?thesis
		  proof (rule exI[where x=J])
		    show "\<exists>F. top1_embedding_on X TX (top1_PiE J (\<lambda>_. ?I))
		      (top1_product_topology_on J (\<lambda>_. ?I) (\<lambda>_. ?TI)) F"
	    proof (rule exI[where x=F])
	      show "top1_embedding_on X TX (top1_PiE J (\<lambda>_. ?I))
	        (top1_product_topology_on J (\<lambda>_. ?I) (\<lambda>_. ?TI)) F"
	        by (rule hEmbI)
	    qed
	  qed
	qed

theorem Theorem_34_3:
  shows "top1_completely_regular_on X TX \<longleftrightarrow>
    (\<exists>J::('a \<Rightarrow> real) set. \<exists>F::'a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real).
      top1_embedding_on X TX
        (top1_PiE J (\<lambda>_. top1_closed_interval 0 1))
        (top1_product_topology_on J (\<lambda>_. top1_closed_interval 0 1) (\<lambda>_. top1_closed_interval_topology 0 1))
        F)"
proof (rule iffI)
  assume hCR: "top1_completely_regular_on X TX"
  show "\<exists>J::('a \<Rightarrow> real) set. \<exists>F::'a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real).
      top1_embedding_on X TX
        (top1_PiE J (\<lambda>_. top1_closed_interval 0 1))
        (top1_product_topology_on J (\<lambda>_. top1_closed_interval 0 1) (\<lambda>_. top1_closed_interval_topology 0 1))
        F"
    by (rule Theorem_34_3_forward[OF hCR])
next
  assume hEmb:
    "\<exists>J::('a \<Rightarrow> real) set. \<exists>F::'a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real).
      top1_embedding_on X TX
        (top1_PiE J (\<lambda>_. top1_closed_interval 0 1))
        (top1_product_topology_on J (\<lambda>_. top1_closed_interval 0 1) (\<lambda>_. top1_closed_interval_topology 0 1))
        F"
  show "top1_completely_regular_on X TX"
  proof -
    obtain J :: "('a \<Rightarrow> real) set" and F :: "'a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real)" where
      hEmbF:
        "top1_embedding_on X TX
          (top1_PiE J (\<lambda>_. top1_closed_interval 0 1))
          (top1_product_topology_on J (\<lambda>_. top1_closed_interval 0 1) (\<lambda>_. top1_closed_interval_topology 0 1))
          F"
      using hEmb by blast

    let ?I = "top1_closed_interval 0 1"
    let ?TI = "top1_closed_interval_topology 0 1"
    let ?Y = "top1_PiE J (\<lambda>_. ?I)"
    let ?TY = "top1_product_topology_on J (\<lambda>_. ?I) (\<lambda>_. ?TI)"
    let ?W = "F ` X"
    let ?TW = "subspace_topology ?Y ?TY ?W"

    have hCRcoord: "\<forall>i\<in>J. top1_completely_regular_on ?I ?TI"
      by (intro ballI, rule top1_closed_interval_completely_regular)

    have hCRcube: "top1_completely_regular_on ?Y ?TY"
      by (rule top1_completely_regular_on_product_topology_on[OF hCRcoord])

    have hWsub: "?W \<subseteq> ?Y"
      using hEmbF unfolding top1_embedding_on_def by blast

    have hCRW: "top1_completely_regular_on ?W ?TW"
      by (rule Theorem_33_2_subspace[OF hCRcube hWsub])

    have hhomeo: "top1_homeomorphism_on X TX ?W ?TW F"
      using hEmbF unfolding top1_embedding_on_def by blast

    show "top1_completely_regular_on X TX"
      by (rule top1_homeomorphism_on_imp_completely_regular_on[OF hhomeo hCRW])
  qed
qed

section \<open>*\<S>35 The Tietze Extension Theorem\<close>

text \<open>
  We begin with Step 1 of the proof in \<open>top1.tex\<close>: given a continuous map
  \<open>f : A \<rightarrow> [-r,r]\<close> on a closed subset \<open>A\<close> of a normal space \<open>X\<close>, we construct a continuous
  \<open>g : X \<rightarrow> [-r/3,r/3]\<close> that is uniformly small and approximates \<open>f\<close> on \<open>A\<close>.
\<close>

text \<open>
  The analytic part of the argument uses standard estimates for the geometric series with ratio
  \<open>2/3\<close>.  We record a couple of convenient lemmas in the form needed for bounding partial sums and
  tails of the Tietze approximants.
\<close>

lemma top1_geometric_partial_sum_2_3:
  fixes n :: nat
  shows "(\<Sum>i<n. (1/3::real) * (2/3) ^ i) = 1 - (2/3) ^ n"
proof -
  have hgeom:
    "(\<Sum>i<n. (2/3::real) ^ i) = ((2/3) ^ n - 1) / ((2/3::real) - 1)"
    by (rule geometric_sum) simp
  have "(\<Sum>i<n. (1/3::real) * (2/3) ^ i) = (1/3::real) * (\<Sum>i<n. (2/3) ^ i)"
    by (simp add: sum_distrib_left)
  also have "... = (1/3::real) * (((2/3) ^ n - 1) / ((2/3::real) - 1))"
    using hgeom by simp
  also have "... = 1 - (2/3) ^ n"
    by (simp add: field_simps)
  finally show ?thesis .
qed

lemma top1_geometric_partial_sum_shift_bound:
  fixes m n :: nat
  shows "(\<Sum>i<n. (1/3::real) * (2/3) ^ (m + i)) \<le> (2/3) ^ m"
proof -
  have hsum: "(\<Sum>i<n. (1/3::real) * (2/3) ^ i) = 1 - (2/3) ^ n"
    by (rule top1_geometric_partial_sum_2_3)

  have hrewrite:
    "(\<Sum>i<n. (1/3::real) * (2/3) ^ (m + i))
     = (2/3) ^ m * (\<Sum>i<n. (1/3::real) * (2/3) ^ i)"
  proof -
    have "(\<Sum>i<n. (1/3::real) * (2/3) ^ (m + i))
        = (\<Sum>i<n. (2/3) ^ m * ((1/3::real) * (2/3) ^ i))"
      by (simp add: power_add algebra_simps)
    also have "... = (2/3) ^ m * (\<Sum>i<n. (1/3::real) * (2/3) ^ i)"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed

  have hn: "0 \<le> (2/3::real) ^ n"
    by simp
  have "(\<Sum>i<n. (1/3::real) * (2/3) ^ (m + i)) = (2/3) ^ m * (1 - (2/3) ^ n)"
    unfolding hrewrite hsum by simp
  also have "... \<le> (2/3::real) ^ m * 1"
  proof (rule mult_left_mono)
    show "1 - (2/3::real) ^ n \<le> 1"
      using hn by simp
    show "0 \<le> (2/3::real) ^ m"
      by simp
  qed
  finally show ?thesis
    by simp
qed

lemma top1_tietze_tail_bound:
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> real" and x :: 'a
  assumes hsinc: "\<forall>n. \<forall>x\<in>X. abs (s (Suc n) x - s n x) \<le> (1/3) * (2/3) ^ n"
  assumes hx: "x \<in> X"
  shows "abs (s (n + k) x - s n x) \<le> (2/3) ^ n"
proof -
  have htel:
    "(\<Sum>i<k. s (n + Suc i) x - s (n + i) x) = s (n + k) x - s n x"
  proof -
    have "(\<Sum>i<k. (\<lambda>i. s (n + i) x) (Suc i) - (\<lambda>i. s (n + i) x) i)
        = (\<lambda>i. s (n + i) x) k - (\<lambda>i. s (n + i) x) 0"
      by (rule sum_lessThan_telescope)
    thus ?thesis
      by simp
  qed

  have habs_sum:
    "abs (s (n + k) x - s n x) \<le> (\<Sum>i<k. abs (s (n + Suc i) x - s (n + i) x))"
  proof -
    have "abs (s (n + k) x - s n x) = abs (\<Sum>i<k. s (n + Suc i) x - s (n + i) x)"
      using htel by simp
    also have "... \<le> (\<Sum>i<k. abs (s (n + Suc i) x - s (n + i) x))"
      by (rule sum_abs)
    finally show ?thesis .
  qed

  have hterm:
    "\<forall>i<k. abs (s (n + Suc i) x - s (n + i) x) \<le> (1/3) * (2/3) ^ (n + i)"
  proof (intro allI impI)
    fix i assume hi: "i < k"
    have "abs (s (Suc (n + i)) x - s (n + i) x) \<le> (1/3) * (2/3) ^ (n + i)"
      using hsinc hx by blast
    thus "abs (s (n + Suc i) x - s (n + i) x) \<le> (1/3) * (2/3) ^ (n + i)"
      by simp
  qed

  have hsum:
    "(\<Sum>i<k. abs (s (n + Suc i) x - s (n + i) x)) \<le> (\<Sum>i<k. (1/3) * (2/3) ^ (n + i))"
  proof (rule sum_mono)
    fix i assume hi: "i \<in> {..<k}"
    have hik: "i < k"
      using hi by simp
    show "abs (s (n + Suc i) x - s (n + i) x) \<le> (1/3) * (2/3) ^ (n + i)"
      using hterm hik by blast
  qed

  have hgeom: "(\<Sum>i<k. (1/3::real) * (2/3) ^ (n + i)) \<le> (2/3) ^ n"
    by (rule top1_geometric_partial_sum_shift_bound[where m=n and n=k])

  show ?thesis
    using order_trans[OF habs_sum order_trans[OF hsum hgeom]] .
qed

lemma top1_closed_interval_closedin_order_topology:
  fixes a b :: real
  shows "closedin_on (UNIV::real set) order_topology_on_UNIV (top1_closed_interval a b)"
proof -
  have hTop: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hray1: "open_ray_lt a \<in> order_topology_on_UNIV"
    by (rule open_ray_lt_in_order_topology)
  have hray2: "open_ray_gt b \<in> order_topology_on_UNIV"
    by (rule open_ray_gt_in_order_topology)

  have hcomp: "(UNIV::real set) - top1_closed_interval a b = open_ray_lt a \<union> open_ray_gt b"
  proof (rule set_eqI)
    fix x :: real
    show "x \<in> (UNIV::real set) - top1_closed_interval a b \<longleftrightarrow> x \<in> open_ray_lt a \<union> open_ray_gt b"
      by (simp add: top1_closed_interval_def open_ray_lt_def open_ray_gt_def not_le)
  qed

  have hopen: "open_ray_lt a \<union> open_ray_gt b \<in> order_topology_on_UNIV"
    by (rule topology_union2[OF hTop hray1 hray2])

  show ?thesis
    unfolding closedin_on_def
    apply (intro conjI)
     apply simp
    apply (simp add: hcomp hopen)
    done
qed

lemma abs_diff_le_of_bounds:
  fixes L U u v :: real
  assumes hLu: "L \<le> u" and huU: "u \<le> U"
  assumes hLv: "L \<le> v" and hvU: "v \<le> U"
  shows "abs (u - v) \<le> U - L"
proof -
  have h1: "u - v \<le> U - L"
    using huU hLv by linarith
  have h2: "- (u - v) \<le> U - L"
    using hvU hLu by linarith
  show ?thesis
    by (rule abs_leI[OF h1 h2])
qed

lemma top1_tietze_step1:
  fixes A :: "'a set" and f :: "'a \<Rightarrow> real" and r :: real
  defines "J \<equiv> top1_closed_interval (-r) r"
  defines "TJ \<equiv> top1_closed_interval_topology (-r) r"
  defines "I1 \<equiv> top1_closed_interval (-r) (-r/3)"
  defines "I3 \<equiv> top1_closed_interval (r/3) r"
  defines "B \<equiv> {a \<in> A. f a \<in> I1}"
  defines "C \<equiv> {a \<in> A. f a \<in> I3}"
  assumes hX: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hf: "top1_continuous_map_on A (subspace_topology X TX A) J TJ f"
  assumes hr: "0 < r"
  shows "\<exists>g. top1_continuous_map_on X TX (top1_closed_interval (-r/3) (r/3))
                  (top1_closed_interval_topology (-r/3) (r/3)) g
            \<and> (\<forall>x\<in>B. g x = -r/3)
            \<and> (\<forall>x\<in>C. g x = r/3)
            \<and> (\<forall>x\<in>X. abs (g x) \<le> r/3)
            \<and> (\<forall>a\<in>A. abs (g a - f a) \<le> 2*r/3)"
proof -
  have hT1: "top1_T1_on X TX"
    using hX unfolding top1_normal_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)
  have hAX: "A \<subseteq> X"
    by (rule closedin_sub[OF hA])

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopA: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF hTopX hAX])
  have hTopJ: "is_topology_on J TJ"
    unfolding TJ_def top1_closed_interval_topology_def J_def
    by (rule subspace_topology_is_topology_on[OF hTopR], simp)

  have hI1subJ: "I1 \<subseteq> J"
  proof (rule subsetI)
    fix t assume ht: "t \<in> I1"
    have ht1: "-r \<le> t" and ht2: "t \<le> -r/3"
      using ht unfolding I1_def top1_closed_interval_def by blast+
    have hle: "-r/3 \<le> r"
      using hr by linarith
    have "t \<le> r"
      using ht2 hle by linarith
    thus "t \<in> J"
      unfolding J_def top1_closed_interval_def using ht1 by blast
  qed
  have hI3subJ: "I3 \<subseteq> J"
  proof (rule subsetI)
    fix t assume ht: "t \<in> I3"
    have ht1: "r/3 \<le> t" and ht2: "t \<le> r"
      using ht unfolding I3_def top1_closed_interval_def by blast+
    have hle: "-r \<le> r/3"
      using hr by linarith
    have "-r \<le> t"
      using hle ht1 by linarith
    thus "t \<in> J"
      unfolding J_def top1_closed_interval_def using ht2 by blast
  qed

  have hI1_closed_J: "closedin_on J TJ I1"
  proof -
    have hI1_closed_UNIV: "closedin_on (UNIV::real set) order_topology_on_UNIV I1"
      unfolding I1_def by (rule top1_closed_interval_closedin_order_topology)
    show ?thesis
      unfolding J_def TJ_def top1_closed_interval_topology_def
      apply (rule iffD2)
       apply (rule Theorem_17_2[OF hTopR])
       apply simp
      apply (rule exI[where x=I1])
      apply (intro conjI)
       apply (rule hI1_closed_UNIV)
      apply (rule sym)
      apply (rule Int_absorb2)
      apply (simp only: J_def[symmetric])
      apply (rule hI1subJ)
  done
qed
  have hI3_closed_J: "closedin_on J TJ I3"
  proof -
    have hI3_closed_UNIV: "closedin_on (UNIV::real set) order_topology_on_UNIV I3"
      unfolding I3_def by (rule top1_closed_interval_closedin_order_topology)
    show ?thesis
      unfolding J_def TJ_def top1_closed_interval_topology_def
      apply (rule iffD2)
       apply (rule Theorem_17_2[OF hTopR])
       apply simp
      apply (rule exI[where x=I3])
      apply (intro conjI)
       apply (rule hI3_closed_UNIV)
      apply (rule sym)
      apply (rule Int_absorb2)
      apply (simp only: J_def[symmetric])
      apply (rule hI3subJ)
  done
qed
  have cont_closed_f:
    "top1_continuous_map_on A (subspace_topology X TX A) J TJ f \<longleftrightarrow>
       ((\<forall>x\<in>A. f x \<in> J) \<and>
        (\<forall>D. closedin_on J TJ D \<longrightarrow> closedin_on A (subspace_topology X TX A) {x\<in>A. f x \<in> D}))"
    by (rule Theorem_18_1(2)[OF hTopA hTopJ])

  have preimage_closed_f:
    "\<forall>D. closedin_on J TJ D \<longrightarrow> closedin_on A (subspace_topology X TX A) {x\<in>A. f x \<in> D}"
  proof -
    have hconj:
      "(\<forall>x\<in>A. f x \<in> J)
       \<and> (\<forall>D. closedin_on J TJ D \<longrightarrow> closedin_on A (subspace_topology X TX A) {x\<in>A. f x \<in> D})"
      using iffD1[OF cont_closed_f hf] .
    show ?thesis
      by (rule conjunct2[OF hconj])
  qed

  have hB_closed_A: "closedin_on A (subspace_topology X TX A) B"
    unfolding B_def by (rule preimage_closed_f[rule_format, OF hI1_closed_J])
  have hC_closed_A: "closedin_on A (subspace_topology X TX A) C"
    unfolding C_def by (rule preimage_closed_f[rule_format, OF hI3_closed_J])

  have hB_closed_X: "closedin_on X TX B"
    by (rule Theorem_17_3[OF hTopX hA hB_closed_A])
  have hC_closed_X: "closedin_on X TX C"
    by (rule Theorem_17_3[OF hTopX hA hC_closed_A])

  have hdisj: "B \<inter> C = {}"
  proof (rule ccontr)
    assume hne: "B \<inter> C \<noteq> {}"
    then obtain x where hx: "x \<in> B \<inter> C"
      by blast
    have hxB: "x \<in> B" and hxC: "x \<in> C"
      using hx by blast+
    have hxA: "x \<in> A"
      using hxB unfolding B_def by blast
    have hfxI1: "f x \<in> I1"
      using hxB unfolding B_def by blast
    have hfxI3: "f x \<in> I3"
      using hxC unfolding C_def by blast
    have hle1: "f x \<le> -r/3"
      using hfxI1 unfolding I1_def top1_closed_interval_def by blast
    have hge3: "r/3 \<le> f x"
      using hfxI3 unfolding I3_def top1_closed_interval_def by blast
    have "r \<le> 0"
      using hge3 hle1 by linarith
    thus False
      using hr by linarith
  qed

  have hab: "-r/3 \<le> r/3"
    using hr by linarith

  obtain g where hg:
    "top1_continuous_map_on X TX (top1_closed_interval (-r/3) (r/3))
        (top1_closed_interval_topology (-r/3) (r/3)) g
     \<and> (\<forall>x\<in>B. g x = -r/3)
     \<and> (\<forall>x\<in>C. g x = r/3)"
    using Theorem_33_1[of X TX B C "-r/3" "r/3"] hX hB_closed_X hC_closed_X hdisj hab
    by blast

  have hgcont:
    "top1_continuous_map_on X TX (top1_closed_interval (-r/3) (r/3))
        (top1_closed_interval_topology (-r/3) (r/3)) g"
    using hg by blast
  have hgonB: "\<forall>x\<in>B. g x = -r/3"
    using hg by blast
  have hgonC: "\<forall>x\<in>C. g x = r/3"
    using hg by blast

  have hg_range: "\<forall>x\<in>X. g x \<in> top1_closed_interval (-r/3) (r/3)"
    using hgcont unfolding top1_continuous_map_on_def by blast

  have hg_abs: "\<forall>x\<in>X. abs (g x) \<le> r/3"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hgb: "-r/3 \<le> g x \<and> g x \<le> r/3"
      using hg_range hxX unfolding top1_closed_interval_def by blast
    have "g x \<le> r/3"
      using hgb by blast
    moreover have "- (g x) \<le> r/3"
      using hgb by linarith
    ultimately show "abs (g x) \<le> r/3"
      by (rule abs_leI)
  qed

  have hf_range: "\<forall>a\<in>A. f a \<in> J"
    using hf unfolding top1_continuous_map_on_def by blast

  have hf_approx: "\<forall>a\<in>A. abs (g a - f a) \<le> 2*r/3"
  proof (intro ballI)
    fix a assume haA: "a \<in> A"
    have haX: "a \<in> X"
      using hAX haA by blast
    have hfb: "-r \<le> f a \<and> f a \<le> r"
      using hf_range haA unfolding J_def top1_closed_interval_def by blast
    have hgb: "-r/3 \<le> g a \<and> g a \<le> r/3"
      using hg_range haX unfolding top1_closed_interval_def by blast

    show "abs (g a - f a) \<le> 2*r/3"
    proof (cases "a \<in> B")
      case True
      have hga: "g a = -r/3"
        using hgonB True by blast
      have hfa: "f a \<in> I1"
        using True haA unfolding B_def by blast
      have hfa1: "-r \<le> f a" and hfa2: "f a \<le> -r/3"
        using hfa unfolding I1_def top1_closed_interval_def by blast+
      have habs: "abs (-r/3 - f a) \<le> 2*r/3"
      proof -
        have hnonneg: "0 \<le> -r/3 - f a"
          using hfa2 by linarith
        have hle: "-r/3 - f a \<le> 2*r/3"
          using hfa1 by linarith
        have habseq: "abs (-r/3 - f a) = -r/3 - f a"
        proof -
          have "abs (-r/3 - f a) = (-r/3 - f a)"
            apply (rule abs_of_nonneg)
            apply (rule hnonneg)
            done
          thus ?thesis by simp
        qed
        show ?thesis
          apply (simp only: habseq)
          apply (rule hle)
          done
      qed
      show ?thesis
        apply (simp only: hga)
        apply (rule habs)
        done
    next
      case FalseB: False
      show ?thesis
      proof (cases "a \<in> C")
        case True
        have hga: "g a = r/3"
          using hgonC True by blast
        have hfa: "f a \<in> I3"
          using True haA unfolding C_def by blast
        have hfa1: "r/3 \<le> f a" and hfa2: "f a \<le> r"
          using hfa unfolding I3_def top1_closed_interval_def by blast+
        have habs: "abs (r/3 - f a) \<le> 2*r/3"
        proof -
          have hnonneg: "0 \<le> f a - r/3"
            using hfa1 by linarith
          have hle: "f a - r/3 \<le> 2*r/3"
            using hfa2 by linarith
          have habseq: "abs (r/3 - f a) = f a - r/3"
          proof -
            have "abs (r/3 - f a) = abs (f a - r/3)"
              by (simp add: abs_minus_commute)
            also have "... = f a - r/3"
              apply (rule abs_of_nonneg)
              apply (rule hnonneg)
              done
            finally show ?thesis .
          qed
          show ?thesis
            apply (simp only: habseq)
            apply (rule hle)
            done
        qed
        show ?thesis
          apply (simp only: hga)
          apply (rule habs)
          done
      next
        case FalseC: False
        have hnotI1: "f a \<notin> I1"
          using haA FalseB unfolding B_def by blast
        have hnotI3: "f a \<notin> I3"
          using haA FalseC unfolding C_def by blast
        have hfaI2: "-r/3 \<le> f a \<and> f a \<le> r/3"
        proof -
          have hfL: "-r \<le> f a"
            using hfb by blast
          have hfU: "f a \<le> r"
            using hfb by blast
          have hnle: "\<not> f a \<le> -r/3"
          proof
            assume hle: "f a \<le> -r/3"
            have "f a \<in> I1"
              unfolding I1_def top1_closed_interval_def using hfL hle by simp
            thus False
              using hnotI1 by contradiction
          qed
          have hnge: "\<not> r/3 \<le> f a"
          proof
            assume hge: "r/3 \<le> f a"
            have "f a \<in> I3"
              unfolding I3_def top1_closed_interval_def using hfU hge by simp
            thus False
              using hnotI3 by contradiction
          qed
          have "-r/3 < f a"
            using hfL hnle by linarith
          moreover have "f a < r/3"
            using hfU hnge by linarith
          ultimately show ?thesis
            by linarith
        qed
        have hgaI2: "-r/3 \<le> g a \<and> g a \<le> r/3"
          using hgb by blast
        have "abs (g a - f a) \<le> r/3 - (-r/3)"
          by (rule abs_diff_le_of_bounds[OF conjunct1[OF hgaI2] conjunct2[OF hgaI2]
                                          conjunct1[OF hfaI2] conjunct2[OF hfaI2]])
        thus ?thesis
          by simp
      qed
    qed
  qed

  show ?thesis
    apply (rule exI[where x=g])
    apply (intro conjI)
    apply (rule hgcont)
    apply (rule hgonB)
    apply (rule hgonC)
    apply (rule hg_abs)
    apply (rule hf_approx)
    done
qed

lemma top1_continuous_add_order_topology:
  shows "top1_continuous_map_on
      ((UNIV::real set) \<times> (UNIV::real set))
      (product_topology_on order_topology_on_UNIV order_topology_on_UNIV)
      (UNIV::real set) order_topology_on_UNIV
      (\<lambda>p::real \<times> real. pi1 p + pi2 p)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?X = "?R \<times> ?R"
  let ?plus = "(\<lambda>p::real \<times> real. pi1 p + pi2 p)"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopX: "is_topology_on ?X ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopR hTopR])

  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    by (rule basis_for_order_topology_on_UNIV)

  show ?thesis
  proof (rule top1_continuous_map_on_generated_by_basis)
    show "is_topology_on ?X ?TP"
      by (rule hTopX)
    show "basis_for ?R (basis_order_topology::real set set) ?TR"
      by (rule hBasisR)
    show "\<forall>p\<in>?X. ?plus p \<in> ?R"
      by simp
    show "\<forall>b\<in>(basis_order_topology::real set set). {p \<in> ?X. ?plus p \<in> b} \<in> ?TP"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      define P where "P = {p \<in> ?X. ?plus p \<in> b}"
      have hPsub: "P \<subseteq> ?X"
        unfolding P_def by simp

      have hlocal: "\<forall>p\<in>P. \<exists>W\<in>?TP. p \<in> W \<and> W \<subseteq> P"
	      proof (intro ballI)
	        fix p assume hpP: "p \<in> P"
	        have hpX: "p \<in> ?X" and hpb: "?plus p \<in> b"
	        proof -
	          have hp_conj: "p \<in> ?X \<and> ?plus p \<in> b"
	            using hpP unfolding P_def by simp
	          show "p \<in> ?X"
	            using hp_conj by (rule conjunct1)
	          show "?plus p \<in> b"
	            using hp_conj by (rule conjunct2)
	        qed

        obtain e where he: "0 < e"
          and hI_sub: "open_interval (?plus p - e) (?plus p + e) \<subseteq> b"
          using basis_order_topology_contains_open_interval[OF hb hpb] by blast
        have he2: "0 < e/2"
          using he by linarith

        define U where "U = open_interval (pi1 p - e/2) (pi1 p + e/2)"
        define V where "V = open_interval (pi2 p - e/2) (pi2 p + e/2)"
        define W where "W = U \<times> V"

        have hU_TR: "U \<in> ?TR"
        proof -
          have "pi1 p - e/2 < pi1 p + e/2"
            using he2 by linarith
          thus ?thesis
            unfolding U_def by (rule open_interval_in_order_topology)
        qed
        have hV_TR: "V \<in> ?TR"
        proof -
          have "pi2 p - e/2 < pi2 p + e/2"
            using he2 by linarith
          thus ?thesis
            unfolding V_def by (rule open_interval_in_order_topology)
        qed
        have hW_TP: "W \<in> ?TP"
          unfolding W_def by (rule product_rect_open[OF hU_TR hV_TR])

        have hpW: "p \<in> W"
        proof -
          have h1: "pi1 p - e/2 < pi1 p"
            using he2 by linarith
          have h2: "pi1 p < pi1 p + e/2"
            using he2 by linarith
          have h3: "pi2 p - e/2 < pi2 p"
            using he2 by linarith
          have h4: "pi2 p < pi2 p + e/2"
            using he2 by linarith
          have hpU: "pi1 p \<in> U"
            unfolding U_def open_interval_def using h1 h2 by simp
          have hpV: "pi2 p \<in> V"
            unfolding V_def open_interval_def using h3 h4 by simp
          have "(pi1 p, pi2 p) \<in> W"
            unfolding W_def using hpU hpV by simp
          thus ?thesis
            by (simp add: W_def pi1_def pi2_def)
        qed

        have hWsub: "W \<subseteq> P"
        proof (rule subsetI)
          fix q assume hqW: "q \<in> W"
          have hqU: "pi1 q \<in> U"
          proof (cases q)
            case (Pair u v)
            have "(u, v) \<in> U \<times> V"
              using hqW unfolding W_def Pair by simp
            hence "u \<in> U"
              by simp
            thus ?thesis
              unfolding pi1_def Pair by simp
          qed
          have hqV: "pi2 q \<in> V"
          proof (cases q)
            case (Pair u v)
            have "(u, v) \<in> U \<times> V"
              using hqW unfolding W_def Pair by simp
            hence "v \<in> V"
              by simp
            thus ?thesis
              unfolding pi2_def Pair by simp
	          qed
	          have hq1: "pi1 p - e/2 < pi1 q" and hq2: "pi1 q < pi1 p + e/2"
	          proof -
	            have hq_conj: "pi1 p - e/2 < pi1 q \<and> pi1 q < pi1 p + e/2"
	              using hqU unfolding U_def open_interval_def by simp
	            show "pi1 p - e/2 < pi1 q"
	              using hq_conj by (rule conjunct1)
	            show "pi1 q < pi1 p + e/2"
	              using hq_conj by (rule conjunct2)
	          qed
	          have hq3: "pi2 p - e/2 < pi2 q" and hq4: "pi2 q < pi2 p + e/2"
	          proof -
	            have hq_conj: "pi2 p - e/2 < pi2 q \<and> pi2 q < pi2 p + e/2"
	              using hqV unfolding V_def open_interval_def by simp
	            show "pi2 p - e/2 < pi2 q"
	              using hq_conj by (rule conjunct1)
	            show "pi2 q < pi2 p + e/2"
	              using hq_conj by (rule conjunct2)
	          qed

          have hsum1: "?plus p - e < ?plus q"
          proof -
            have htmp: "pi1 p + pi2 p - e < pi1 q + pi2 q"
              using hq1 hq3 by linarith
            show ?thesis
              using htmp by simp
          qed
          have hsum2: "?plus q < ?plus p + e"
          proof -
            have htmp: "pi1 q + pi2 q < pi1 p + pi2 p + e"
              using hq2 hq4 by linarith
            show ?thesis
              using htmp by simp
          qed
          have hqI: "?plus q \<in> open_interval (?plus p - e) (?plus p + e)"
            unfolding open_interval_def using hsum1 hsum2 by simp
          have hqB: "?plus q \<in> b"
            using hI_sub hqI by blast
          show "q \<in> P"
            unfolding P_def using hqB by simp
        qed

        show "\<exists>W\<in>?TP. p \<in> W \<and> W \<subseteq> P"
        proof (rule bexI[where x=W])
          show "W \<in> ?TP"
            by (rule hW_TP)
          show "p \<in> W \<and> W \<subseteq> P"
            by (intro conjI, rule hpW, rule hWsub)
        qed
      qed

      have "P \<in> ?TP"
        by (rule top1_open_set_from_local_opens[OF hTopX hPsub hlocal])
      thus "{p \<in> ?X. ?plus p \<in> b} \<in> ?TP"
        unfolding P_def .
    qed
  qed
qed

lemma top1_continuous_mul_order_topology:
  shows "top1_continuous_map_on
      ((UNIV::real set) \<times> (UNIV::real set))
      (product_topology_on order_topology_on_UNIV order_topology_on_UNIV)
      (UNIV::real set) order_topology_on_UNIV
      (\<lambda>p::real \<times> real. pi1 p * pi2 p)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?X = "?R \<times> ?R"
  let ?mul = "(\<lambda>p::real \<times> real. pi1 p * pi2 p)"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopX: "is_topology_on ?X ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopR hTopR])

  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    by (rule basis_for_order_topology_on_UNIV)

  show ?thesis
  proof (rule top1_continuous_map_on_generated_by_basis)
    show "is_topology_on ?X ?TP"
      by (rule hTopX)
    show "basis_for ?R (basis_order_topology::real set set) ?TR"
      by (rule hBasisR)
    show "\<forall>p\<in>?X. ?mul p \<in> ?R"
      by simp
    show "\<forall>b\<in>(basis_order_topology::real set set). {p \<in> ?X. ?mul p \<in> b} \<in> ?TP"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      define P where "P = {p \<in> ?X. ?mul p \<in> b}"
      have hPsub: "P \<subseteq> ?X"
        unfolding P_def by simp

      have hlocal: "\<forall>p\<in>P. \<exists>W\<in>?TP. p \<in> W \<and> W \<subseteq> P"
	      proof (intro ballI)
	        fix p assume hpP: "p \<in> P"
	        have hpX: "p \<in> ?X" and hpb: "?mul p \<in> b"
	        proof -
	          have hp_conj: "p \<in> ?X \<and> ?mul p \<in> b"
	            using hpP unfolding P_def by simp
	          show "p \<in> ?X"
	            using hp_conj by (rule conjunct1)
	          show "?mul p \<in> b"
	            using hp_conj by (rule conjunct2)
	        qed

        obtain e where he: "0 < e"
          and hI_sub: "open_interval (?mul p - e) (?mul p + e) \<subseteq> b"
          using basis_order_topology_contains_open_interval[OF hb hpb] by blast

        define K where "K = abs (pi2 p) + abs (pi1 p) + 1"
        have hKpos: "0 < K"
          unfolding K_def by linarith

        define d0 where "d0 = e / (2 * K)"
        define d where "d = min 1 d0"

        have hd0pos: "0 < d0"
          unfolding d0_def using he hKpos by (simp add: divide_pos_pos)
        have hdpos: "0 < d"
          unfolding d_def using hd0pos by simp
        have hd_le_1: "d \<le> 1"
          unfolding d_def by simp
        have hd_le_d0: "d \<le> d0"
          unfolding d_def by simp

        define U where "U = open_interval (pi1 p - d) (pi1 p + d)"
        define V where "V = open_interval (pi2 p - d) (pi2 p + d)"
        define W where "W = U \<times> V"

        have hU_TR: "U \<in> ?TR"
        proof -
          have "pi1 p - d < pi1 p + d"
            using hdpos by linarith
          thus ?thesis
            unfolding U_def by (rule open_interval_in_order_topology)
        qed
        have hV_TR: "V \<in> ?TR"
        proof -
          have "pi2 p - d < pi2 p + d"
            using hdpos by linarith
          thus ?thesis
            unfolding V_def by (rule open_interval_in_order_topology)
        qed
        have hW_TP: "W \<in> ?TP"
          unfolding W_def by (rule product_rect_open[OF hU_TR hV_TR])

        have hpW: "p \<in> W"
        proof -
          have h1: "pi1 p - d < pi1 p"
            using hdpos by linarith
          have h2: "pi1 p < pi1 p + d"
            using hdpos by linarith
          have h3: "pi2 p - d < pi2 p"
            using hdpos by linarith
          have h4: "pi2 p < pi2 p + d"
            using hdpos by linarith
          have hpU: "pi1 p \<in> U"
            unfolding U_def open_interval_def using h1 h2 by simp
          have hpV: "pi2 p \<in> V"
            unfolding V_def open_interval_def using h3 h4 by simp
          have "(pi1 p, pi2 p) \<in> W"
            unfolding W_def using hpU hpV by simp
          thus ?thesis
            by (simp add: W_def pi1_def pi2_def)
        qed

        have hWsub: "W \<subseteq> P"
        proof (rule subsetI)
          fix q assume hqW: "q \<in> W"
          have hqU: "pi1 q \<in> U"
          proof (cases q)
            case (Pair u v)
            have "(u, v) \<in> U \<times> V"
              using hqW unfolding W_def Pair by simp
            hence "u \<in> U"
              by simp
            thus ?thesis
              unfolding pi1_def Pair by simp
          qed
          have hqV: "pi2 q \<in> V"
          proof (cases q)
            case (Pair u v)
            have "(u, v) \<in> U \<times> V"
              using hqW unfolding W_def Pair by simp
            hence "v \<in> V"
              by simp
            thus ?thesis
              unfolding pi2_def Pair by simp
	          qed
	
	          have hq1: "pi1 p - d < pi1 q" and hq2: "pi1 q < pi1 p + d"
	          proof -
	            have hq_conj: "pi1 p - d < pi1 q \<and> pi1 q < pi1 p + d"
	              using hqU unfolding U_def open_interval_def by simp
	            show "pi1 p - d < pi1 q"
	              using hq_conj by (rule conjunct1)
	            show "pi1 q < pi1 p + d"
	              using hq_conj by (rule conjunct2)
	          qed
	          have hq3: "pi2 p - d < pi2 q" and hq4: "pi2 q < pi2 p + d"
	          proof -
	            have hq_conj: "pi2 p - d < pi2 q \<and> pi2 q < pi2 p + d"
	              using hqV unfolding V_def open_interval_def by simp
	            show "pi2 p - d < pi2 q"
	              using hq_conj by (rule conjunct1)
	            show "pi2 q < pi2 p + d"
	              using hq_conj by (rule conjunct2)
	          qed

          have habs1: "abs (pi1 q - pi1 p) \<le> d"
          proof -
            have habs: "abs (pi1 q - pi1 p) < d"
              using hq1 hq2 by (simp add: abs_less_iff)
            show ?thesis
              using habs by (rule less_imp_le)
          qed
          have habs2: "abs (pi2 q - pi2 p) \<le> d"
          proof -
            have habs: "abs (pi2 q - pi2 p) < d"
              using hq3 hq4 by (simp add: abs_less_iff)
            show ?thesis
              using habs by (rule less_imp_le)
          qed

          have habs2_1: "abs (pi2 q - pi2 p) \<le> 1"
            using habs2 hd_le_1 by linarith
          have hq2_bound: "abs (pi2 q) \<le> abs (pi2 p) + 1"
          proof -
            have htri: "abs (pi2 q) \<le> abs (pi2 p) + abs (pi2 q - pi2 p)"
            proof -
              have "pi2 q = pi2 p + (pi2 q - pi2 p)"
                by simp
              thus ?thesis
                using abs_triangle_ineq[of "pi2 p" "pi2 q - pi2 p"] by simp
            qed
            show ?thesis
              using htri habs2_1 by linarith
          qed

          have hdiff_le:
            "abs (?mul q - ?mul p)
              \<le> d * (abs (pi2 p) + 1) + abs (pi1 p) * d"
          proof -
            have hEq: "?mul q - ?mul p = (pi1 q - pi1 p) * (pi2 q) + (pi1 p) * (pi2 q - pi2 p)"
              by (simp add: algebra_simps pi1_def pi2_def)
            have htri: "abs (?mul q - ?mul p)
                \<le> abs ((pi1 q - pi1 p) * (pi2 q)) + abs ((pi1 p) * (pi2 q - pi2 p))"
              unfolding hEq by (rule abs_triangle_ineq)
            have hmul1: "abs ((pi1 q - pi1 p) * (pi2 q)) = abs (pi1 q - pi1 p) * abs (pi2 q)"
              by (simp add: abs_mult)
            have hmul2: "abs ((pi1 p) * (pi2 q - pi2 p)) = abs (pi1 p) * abs (pi2 q - pi2 p)"
              by (simp add: abs_mult)
            have hle1: "abs ((pi1 q - pi1 p) * (pi2 q)) \<le> d * (abs (pi2 p) + 1)"
            proof -
              have hnonneg: "0 \<le> d"
                using hdpos by linarith
              have hprod: "abs (pi1 q - pi1 p) * abs (pi2 q) \<le> d * (abs (pi2 p) + 1)"
              proof (rule mult_mono)
                show "abs (pi1 q - pi1 p) \<le> d"
                  by (rule habs1)
                show "abs (pi2 q) \<le> abs (pi2 p) + 1"
                  by (rule hq2_bound)
                show "0 \<le> abs (pi2 q)"
                  by simp
                show "0 \<le> d"
                  by (rule hnonneg)
              qed
              show ?thesis
                using hprod by (simp add: hmul1)
            qed
            have hle2: "abs ((pi1 p) * (pi2 q - pi2 p)) \<le> abs (pi1 p) * d"
            proof -
              have hle: "abs (pi1 p) * abs (pi2 q - pi2 p) \<le> abs (pi1 p) * d"
                by (rule mult_left_mono[OF habs2], simp)
              show ?thesis
                using hle by (simp add: hmul2)
            qed
            have "abs (?mul q - ?mul p)
                \<le> d * (abs (pi2 p) + 1) + abs (pi1 p) * d"
              using htri hle1 hle2 by linarith
            thus ?thesis .
          qed

          have hK: "d * (abs (pi2 p) + 1) + abs (pi1 p) * d = d * K"
            unfolding K_def by (simp add: algebra_simps)
          have hdiff_leK: "abs (?mul q - ?mul p) \<le> d * K"
            using hdiff_le unfolding hK .

          have hde_le: "d * K \<le> e / 2"
	          proof -
	            have hd_le: "d \<le> e / (2 * K)"
	              using hd_le_d0 unfolding d0_def by simp
	            have hKnonneg: "0 \<le> K"
	              by (rule less_imp_le[OF hKpos])
	            have hmult: "d * K \<le> (e / (2 * K)) * K"
	              by (rule mult_right_mono[OF hd_le hKnonneg])
	            have hEq: "(e / (2 * K)) * K = e / 2"
	              using hKpos by (simp add: field_simps)
	            show ?thesis
	              using hmult unfolding hEq .
	          qed
          have he2: "e / 2 < e"
            using he by linarith
          have hdiff_lt_e: "abs (?mul q - ?mul p) < e"
          proof -
            have hdiff_le_e2: "abs (?mul q - ?mul p) \<le> e / 2"
              by (rule order_trans[OF hdiff_leK hde_le])
            show ?thesis
              by (rule le_less_trans[OF hdiff_le_e2 he2])
          qed

          have hmul1': "?mul p - e < ?mul q"
          proof -
            have "-e < ?mul q - ?mul p"
              using hdiff_lt_e by (simp add: abs_less_iff)
            thus ?thesis
              by linarith
          qed
          have hmul2': "?mul q < ?mul p + e"
          proof -
            have "?mul q - ?mul p < e"
              using hdiff_lt_e by (simp add: abs_less_iff)
            thus ?thesis
              by linarith
          qed

          have hqI: "?mul q \<in> open_interval (?mul p - e) (?mul p + e)"
            unfolding open_interval_def using hmul1' hmul2' by simp
          have hqB: "?mul q \<in> b"
            using hI_sub hqI by blast
          show "q \<in> P"
            unfolding P_def using hqB by simp
        qed

        show "\<exists>W\<in>?TP. p \<in> W \<and> W \<subseteq> P"
        proof (rule bexI[where x=W])
          show "W \<in> ?TP"
            by (rule hW_TP)
          show "p \<in> W \<and> W \<subseteq> P"
            by (intro conjI, rule hpW, rule hWsub)
        qed
      qed

      have "P \<in> ?TP"
        by (rule top1_open_set_from_local_opens[OF hTopX hPsub hlocal])
      thus "{p \<in> ?X. ?mul p \<in> b} \<in> ?TP"
        unfolding P_def .
    qed
  qed
qed

(*
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?plus = "(\<lambda>p::real \<times> real. pi1 p + pi2 p)"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopRR: "is_topology_on (?R \<times> ?R) ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopR hTopR])
  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    by (rule basis_for_order_topology_on_UNIV)

  have hpre:
    "\<forall>b\<in>(basis_order_topology::real set set). {p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
  proof (intro ballI)
    fix b :: "real set"
    assume hb: "b \<in> (basis_order_topology::real set set)"

    have hcases:
      "(\<exists>a c. a < c \<and> b = open_interval a c)
       \<or> (\<exists>a. b = open_ray_gt a)
       \<or> (\<exists>a. b = open_ray_lt a)
       \<or> b = (UNIV::real set)"
      by (rule basis_order_topology_cases[OF hb])

    show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
    proof (rule disjE[OF hcases])
      assume hbint: "\<exists>a c. a < c \<and> b = open_interval a c"
      then obtain a c where hac: "a < c" and hbeq: "b = open_interval a c"
        by blast

      show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
        unfolding hbeq product_topology_on_def topology_generated_by_basis_def
      proof (rule CollectI, rule conjI)
        show "{p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c} \<subseteq> (UNIV::(real \<times> real) set)"
          by simp
        show "\<forall>p\<in>{p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}.
            \<exists>bb\<in>product_basis ?TR ?TR.
              p \<in> bb \<and> bb \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
        proof (intro ballI)
	          fix p assume hp: "p \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
	          have hs_in: "?plus p \<in> open_interval a c"
	            using hp by simp
	          have hs1: "a < ?plus p" and hs2: "?plus p < c"
	          proof -
	            have hs_conj: "a < ?plus p \<and> ?plus p < c"
	              using hs_in unfolding open_interval_def by simp
	            show "a < ?plus p"
	              using hs_conj by (rule conjunct1)
	            show "?plus p < c"
	              using hs_conj by (rule conjunct2)
	          qed

	          define s where "s = ?plus p"
	          have hs: "a < s" and hs': "s < c"
	          proof -
	            have hs_conj: "a < s \<and> s < c"
	              unfolding s_def using hs1 hs2 by simp
	            show "a < s"
	              using hs_conj by (rule conjunct1)
	            show "s < c"
	              using hs_conj by (rule conjunct2)
	          qed
          define e where "e = min (s - a) (c - s) / 4"
          have he_pos: "0 < e"
          proof -
            have "0 < s - a"
              using hs by linarith
            moreover have "0 < c - s"
              using hs' by linarith
            ultimately have "0 < min (s - a) (c - s)"
              by simp
            thus ?thesis
              unfolding e_def by (simp add: divide_pos_pos)
          qed

          let ?U = "open_interval (pi1 p - e) (pi1 p + e)"
          let ?V = "open_interval (pi2 p - e) (pi2 p + e)"

          have hU_open: "?U \<in> ?TR"
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith
          have hV_open: "?V \<in> ?TR"
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith

          have hUV_basis: "?U \<times> ?V \<in> product_basis ?TR ?TR"
            unfolding product_basis_def
            apply (rule CollectI)
            apply (rule exI[where x="?U"])
            apply (rule exI[where x="?V"])
            apply (intro conjI)
              apply (rule refl)
             apply (rule hU_open)
            apply (rule hV_open)
            done

          have hpUV: "p \<in> ?U \<times> ?V"
            using he_pos by (cases p, simp add: pi1_def pi2_def open_interval_def)

          have hUV_sub: "?U \<times> ?V \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
          proof (rule subsetI)
            fix q assume hq: "q \<in> ?U \<times> ?V"
            have hqUV: "pi1 q \<in> ?U \<and> pi2 q \<in> ?V"
              using hq by (cases q, simp add: pi1_def pi2_def)
            have hqU: "pi1 q \<in> ?U"
              by (rule conjunct1[OF hqUV])
            have hqV: "pi2 q \<in> ?V"
              by (rule conjunct2[OF hqUV])
	            have hqU1: "pi1 p - e < pi1 q" and hqU2: "pi1 q < pi1 p + e"
	            proof -
	              have hq_conj: "pi1 p - e < pi1 q \<and> pi1 q < pi1 p + e"
	                using hqU unfolding open_interval_def by simp
	              show "pi1 p - e < pi1 q"
	                using hq_conj by (rule conjunct1)
	              show "pi1 q < pi1 p + e"
	                using hq_conj by (rule conjunct2)
	            qed
	            have hqV1: "pi2 p - e < pi2 q" and hqV2: "pi2 q < pi2 p + e"
	            proof -
	              have hq_conj: "pi2 p - e < pi2 q \<and> pi2 q < pi2 p + e"
	                using hqV unfolding open_interval_def by simp
	              show "pi2 p - e < pi2 q"
	                using hq_conj by (rule conjunct1)
	              show "pi2 q < pi2 p + e"
	                using hq_conj by (rule conjunct2)
	            qed

            have hsum_gt: "s - 2*e < ?plus q"
            proof -
              have "(pi1 p - e) + (pi2 p - e) < (pi1 q) + (pi2 q)"
                using hqU1 hqV1 by linarith
              thus ?thesis
                unfolding s_def by simp
            qed
            have hsum_lt: "?plus q < s + 2*e"
            proof -
              have "(pi1 q) + (pi2 q) < (pi1 p + e) + (pi2 p + e)"
                using hqU2 hqV2 by linarith
              thus ?thesis
                unfolding s_def by simp
            qed

	            have he_le1: "e \<le> (s - a) / 4" and he_le2: "e \<le> (c - s) / 4"
	            have he_conj: "e \<le> (s - a) / 4 \<and> e \<le> (c - s) / 4"
	              unfolding e_def by simp
	            have he_le1: "e \<le> (s - a) / 4"
	              using he_conj by (rule conjunct1)
	            have he_le2: "e \<le> (c - s) / 4"
	              using he_conj by (rule conjunct2)
            have h2e_lt1: "2*e < s - a"
            proof -
              have "2*e \<le> 2*((s - a) / 4)"
                apply (rule mult_left_mono[OF he_le1])
                by simp
              also have "... = (s - a) / 2"
                by simp
              finally have hle: "2*e \<le> (s - a) / 2" .
              have hsma: "0 < s - a"
                using hs by linarith
              have hlt: "(s - a) / 2 < s - a"
              proof -
                have "((s - a) / 2 < s - a) \<longleftrightarrow> (s - a < (s - a) * (2::real))"
                  by (simp add: divide_less_eq)
                moreover have "s - a < (s - a) * (2::real)"
                proof -
                  have "(s - a) * (1::real) < (s - a) * (2::real)"
                    apply (rule mult_strict_left_mono)
                     apply simp
                    apply (rule hsma)
                    done
                  thus ?thesis
                    by simp
                qed
                ultimately show ?thesis
                  by simp
              qed
              show ?thesis
                using hle hlt by linarith
            qed
            have h2e_lt2: "2*e < c - s"
            proof -
              have "2*e \<le> 2*((c - s) / 4)"
                apply (rule mult_left_mono[OF he_le2])
                by simp
              also have "... = (c - s) / 2"
                by simp
              finally have hle: "2*e \<le> (c - s) / 2" .
              have hcs: "0 < c - s"
                using hs' by linarith
              have hlt: "(c - s) / 2 < c - s"
              proof -
                have "((c - s) / 2 < c - s) \<longleftrightarrow> (c - s < (c - s) * (2::real))"
                  by (simp add: divide_less_eq)
                moreover have "c - s < (c - s) * (2::real)"
                proof -
                  have "(c - s) * (1::real) < (c - s) * (2::real)"
                    apply (rule mult_strict_left_mono)
                     apply simp
                    apply (rule hcs)
                    done
                  thus ?thesis
                    by simp
                qed
                ultimately show ?thesis
                  by simp
              qed
              show ?thesis
                using hle hlt by linarith
            qed
            have ha_lt: "a < s - 2*e"
              using h2e_lt1 by linarith
            have hlt_c: "s + 2*e < c"
              using h2e_lt2 by linarith

            have hsum_in: "?plus q \<in> open_interval a c"
            proof -
              have haq: "a < ?plus q"
                by (rule less_trans[OF ha_lt hsum_gt])
              have hqc: "?plus q < c"
                by (rule less_trans[OF hsum_lt hlt_c])
              show ?thesis
                unfolding open_interval_def using haq hqc by simp
            qed

            show "q \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
              using hsum_in by simp
          qed

          show "\<exists>bb\<in>product_basis ?TR ?TR.
              p \<in> bb \<and> bb \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
            apply (rule bexI[where x="?U \<times> ?V"])
             apply (intro conjI)
              apply (rule hpUV)
             apply (rule hUV_sub)
            apply (rule hUV_basis)
            done
        qed
      qed
    next
      assume hbr1: "(\<exists>a. b = open_ray_gt a) \<or> (\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
      show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
      proof (rule disjE[OF hbr1])
        assume hbgt: "\<exists>a. b = open_ray_gt a"
        then obtain a where hbeq: "b = open_ray_gt a" by blast
        show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
          unfolding hbeq product_topology_on_def topology_generated_by_basis_def
        proof (rule CollectI, rule conjI)
          show "{p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a} \<subseteq> (UNIV::(real \<times> real) set)"
            by simp
          show "\<forall>p\<in>{p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}.
              \<exists>bb\<in>product_basis ?TR ?TR.
                p \<in> bb \<and> bb \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
          proof (intro ballI)
            fix p assume hp: "p \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
            have hs_in: "?plus p \<in> open_ray_gt a"
              using hp by simp
            have hs: "a < ?plus p"
              using hs_in unfolding open_ray_gt_def by simp
            define s where "s = ?plus p"
            define e where "e = (s - a) / 4"
            have he_pos: "0 < e"
              unfolding e_def using hs unfolding s_def by (simp add: divide_pos_pos)

            let ?U = "open_interval (pi1 p - e) (pi1 p + e)"
            let ?V = "open_interval (pi2 p - e) (pi2 p + e)"

            have hU_open: "?U \<in> ?TR"
              apply (rule open_interval_in_order_topology)
              using he_pos by linarith
            have hV_open: "?V \<in> ?TR"
              apply (rule open_interval_in_order_topology)
              using he_pos by linarith

            have hUV_basis: "?U \<times> ?V \<in> product_basis ?TR ?TR"
              unfolding product_basis_def
              apply (rule CollectI)
              apply (rule exI[where x="?U"])
              apply (rule exI[where x="?V"])
              apply (intro conjI)
                apply (rule refl)
               apply (rule hU_open)
              apply (rule hV_open)
              done

            have hpUV: "p \<in> ?U \<times> ?V"
              using he_pos by (cases p, simp add: pi1_def pi2_def open_interval_def)

            have hUV_sub: "?U \<times> ?V \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
            proof (rule subsetI)
              fix q assume hq: "q \<in> ?U \<times> ?V"
              have hqUV: "pi1 q \<in> ?U \<and> pi2 q \<in> ?V"
                using hq by (cases q, simp add: pi1_def pi2_def)
              have hqU: "pi1 q \<in> ?U"
                by (rule conjunct1[OF hqUV])
              have hqV: "pi2 q \<in> ?V"
                by (rule conjunct2[OF hqUV])
              have hqU1: "pi1 p - e < pi1 q"
                using hqU unfolding open_interval_def by simp
              have hqV1: "pi2 p - e < pi2 q"
                using hqV unfolding open_interval_def by simp
              have hsum_gt: "s - 2*e < ?plus q"
              proof -
                have "(pi1 p - e) + (pi2 p - e) < (pi1 q) + (pi2 q)"
                  using hqU1 hqV1 by linarith
                thus ?thesis
                  unfolding s_def by simp
              qed

              have ha_lt: "a < s - 2*e"
              proof -
                have has: "a < s"
                  unfolding s_def using hs by simp
                have ha_half: "a < (a + s) / 2"
                  by (rule field_less_half_sum[OF has])
                have ha_half': "a < (s + a) / 2"
                  using ha_half by (simp add: add.commute)
                have hEq: "s - 2*e = (s + a) / 2"
                  unfolding e_def by (simp add: field_simps)
                show ?thesis
                  unfolding hEq using ha_half' by simp
              qed
              have haq: "a < ?plus q"
                by (rule less_trans[OF ha_lt hsum_gt])
              have "?plus q \<in> open_ray_gt a"
                unfolding open_ray_gt_def using haq by simp
              thus "q \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
                by simp
            qed

            show "\<exists>bb\<in>product_basis ?TR ?TR.
                p \<in> bb \<and> bb \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
              apply (rule bexI[where x="?U \<times> ?V"])
               apply (intro conjI)
                apply (rule hpUV)
               apply (rule hUV_sub)
              apply (rule hUV_basis)
              done
          qed
        qed
      next
        assume hbr2: "(\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
        show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
        proof (rule disjE[OF hbr2])
          assume hblt: "\<exists>a. b = open_ray_lt a"
          then obtain a where hbeq: "b = open_ray_lt a" by blast
          show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
            unfolding hbeq product_topology_on_def topology_generated_by_basis_def
          proof (rule CollectI, rule conjI)
            show "{p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a} \<subseteq> (UNIV::(real \<times> real) set)"
              by simp
            show "\<forall>p\<in>{p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}.
                \<exists>bb\<in>product_basis ?TR ?TR.
                  p \<in> bb \<and> bb \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
            proof (intro ballI)
              fix p assume hp: "p \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
              have hs_in: "?plus p \<in> open_ray_lt a"
                using hp by simp
              have hs: "?plus p < a"
                using hs_in unfolding open_ray_lt_def by simp
              define s where "s = ?plus p"
              define e where "e = (a - s) / 4"
              have he_pos: "0 < e"
                unfolding e_def using hs unfolding s_def by (simp add: divide_pos_pos)

              let ?U = "open_interval (pi1 p - e) (pi1 p + e)"
              let ?V = "open_interval (pi2 p - e) (pi2 p + e)"

              have hU_open: "?U \<in> ?TR"
                apply (rule open_interval_in_order_topology)
                using he_pos by linarith
              have hV_open: "?V \<in> ?TR"
                apply (rule open_interval_in_order_topology)
                using he_pos by linarith

              have hUV_basis: "?U \<times> ?V \<in> product_basis ?TR ?TR"
                unfolding product_basis_def
                apply (rule CollectI)
                apply (rule exI[where x="?U"])
                apply (rule exI[where x="?V"])
                apply (intro conjI)
                  apply (rule refl)
                 apply (rule hU_open)
                apply (rule hV_open)
                done

              have hpUV: "p \<in> ?U \<times> ?V"
                using he_pos by (cases p, simp add: pi1_def pi2_def open_interval_def)

              have hUV_sub: "?U \<times> ?V \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
              proof (rule subsetI)
                fix q assume hq: "q \<in> ?U \<times> ?V"
                have hqUV: "pi1 q \<in> ?U \<and> pi2 q \<in> ?V"
                  using hq by (cases q, simp add: pi1_def pi2_def)
                have hqU: "pi1 q \<in> ?U"
                  by (rule conjunct1[OF hqUV])
                have hqV: "pi2 q \<in> ?V"
                  by (rule conjunct2[OF hqUV])
                have hqU2: "pi1 q < pi1 p + e"
                  using hqU unfolding open_interval_def by simp
                have hqV2: "pi2 q < pi2 p + e"
                  using hqV unfolding open_interval_def by simp
                have hsum_lt: "?plus q < s + 2*e"
                proof -
                  have "(pi1 q) + (pi2 q) < (pi1 p + e) + (pi2 p + e)"
                    using hqU2 hqV2 by linarith
                  thus ?thesis
                    unfolding s_def by simp
                qed

                have hlt_a: "s + 2*e < a"
                proof -
                  have hsa: "s < a"
                    unfolding s_def using hs by simp
                  have hsum: "s + a < a + a"
                    by (rule add_strict_right_mono[OF hsa])
                  have hhalf: "(s + a) / 2 < a"
                  proof -
                    have "((s + a) / 2 < a) \<longleftrightarrow> (s + a < a * (2::real))"
                      by (simp add: divide_less_eq)
                    moreover have "s + a < a * (2::real)"
                      using hsum by simp
                    ultimately show ?thesis
                      by simp
                  qed
                  have hEq: "s + 2*e = (s + a) / 2"
                    unfolding e_def by (simp add: field_simps)
                  show ?thesis
                    unfolding hEq using hhalf by simp
                qed
                have hqa: "?plus q < a"
                  by (rule less_trans[OF hsum_lt hlt_a])
                have "?plus q \<in> open_ray_lt a"
                  unfolding open_ray_lt_def using hqa by simp
                thus "q \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
                  by simp
              qed

              show "\<exists>bb\<in>product_basis ?TR ?TR.
                  p \<in> bb \<and> bb \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
                apply (rule bexI[where x="?U \<times> ?V"])
                 apply (intro conjI)
                  apply (rule hpUV)
                 apply (rule hUV_sub)
                apply (rule hUV_basis)
                done
            qed
          qed
        next
          assume hU: "b = (UNIV::real set)"
          have hTR_UNIV: "UNIV \<in> ?TR"
            using hTopR unfolding is_topology_on_def by blast
          have hTP_UNIV: "?R \<times> ?R \<in> ?TP"
            by (rule product_rect_open[OF hTR_UNIV hTR_UNIV])
          show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
            unfolding hU using hTP_UNIV by simp
        qed
      qed
    qed
  qed

  show ?thesis
    apply (rule top1_continuous_map_on_generated_by_basis)
       apply (rule hTopRR)
      apply (rule hBasisR)
     apply simp
    apply (rule hpre)
    done
qed
*)

(*
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?plus = "(\<lambda>p::real \<times> real. pi1 p + pi2 p)"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopRR: "is_topology_on (?R \<times> ?R) ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopR hTopR])

  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    by (rule basis_for_order_topology_on_UNIV)

  show ?thesis
  proof (rule top1_continuous_map_on_generated_by_basis)
    show "is_topology_on (?R \<times> ?R) ?TP"
      by (rule hTopRR)
    show "basis_for ?R (basis_order_topology::real set set) ?TR"
      by (rule hBasisR)
    show "\<forall>p\<in>(?R \<times> ?R). ?plus p \<in> ?R"
      by simp
    show "\<forall>b\<in>(basis_order_topology::real set set). {p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      have hcases:
        "(\<exists>a c. a < c \<and> b = open_interval a c)
         \<or> (\<exists>a. b = open_ray_gt a)
         \<or> (\<exists>a. b = open_ray_lt a)
         \<or> b = (UNIV::real set)"
        by (rule basis_order_topology_cases[OF hb])

      show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
      proof (rule disjE[OF hcases])
        assume hbint: "\<exists>a c. a < c \<and> b = open_interval a c"
        then obtain a c where hac: "a < c" and hbeq: "b = open_interval a c"
          by blast
        define P where "P = {p \<in> ?R \<times> ?R. ?plus p \<in> b}"

        have hP_open: "P \<in> ?TP"
          unfolding P_def hbeq product_topology_on_def topology_generated_by_basis_def
        proof (intro CollectI conjI ballI)
          show "{p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c} \<subseteq> (UNIV::(real \<times> real) set)"
            by simp
	          fix p assume hp: "p \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
	          have hps: "a < ?plus p" and hsp: "?plus p < c"
	          proof -
	            have hs_conj: "a < ?plus p \<and> ?plus p < c"
	              using hp unfolding open_interval_def by simp
	            show "a < ?plus p"
	              using hs_conj by (rule conjunct1)
	            show "?plus p < c"
	              using hs_conj by (rule conjunct2)
	          qed
	          define s where "s = ?plus p"
	          have hs: "a < s" and hs': "s < c"
	          proof -
	            have hs_conj: "a < s \<and> s < c"
	              unfolding s_def using hps hsp by simp
	            show "a < s"
	              using hs_conj by (rule conjunct1)
	            show "s < c"
	              using hs_conj by (rule conjunct2)
	          qed

          define e where "e = min (s - a) (c - s) / 4"
          have he_pos: "0 < e"
          proof -
            have "0 < s - a"
              using hs by linarith
            moreover have "0 < c - s"
              using hs' by linarith
            ultimately have "0 < min (s - a) (c - s)"
              by simp
            thus ?thesis
              unfolding e_def by (simp add: divide_pos_pos)
          qed

          define U where "U = open_interval (pi1 p - e) (pi1 p + e)"
          define V where "V = open_interval (pi2 p - e) (pi2 p + e)"

          have hU_open: "U \<in> ?TR"
            unfolding U_def
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith
          have hV_open: "V \<in> ?TR"
            unfolding V_def
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith

          have hpUV: "p \<in> U \<times> V"
            unfolding U_def V_def open_interval_def
            using he_pos by (cases p, simp add: pi1_def pi2_def)

          have hUV_basis: "U \<times> V \<in> product_basis ?TR ?TR"
            unfolding product_basis_def using hU_open hV_open by blast

          have hUV_sub: "U \<times> V \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
          proof (rule subsetI)
            fix q assume hq: "q \<in> U \<times> V"
            have hqU: "pi1 q \<in> U"
              using hq by (cases q, simp add: pi1_def)
            have hqV: "pi2 q \<in> V"
              using hq by (cases q, simp add: pi2_def)
	            have hqU': "pi1 p - e < pi1 q" and hqU'': "pi1 q < pi1 p + e"
	            proof -
	              have hq_conj: "pi1 p - e < pi1 q \<and> pi1 q < pi1 p + e"
	                using hqU unfolding U_def open_interval_def by simp
	              show "pi1 p - e < pi1 q"
	                using hq_conj by (rule conjunct1)
	              show "pi1 q < pi1 p + e"
	                using hq_conj by (rule conjunct2)
	            qed
	            have hqV': "pi2 p - e < pi2 q" and hqV'': "pi2 q < pi2 p + e"
	            proof -
	              have hq_conj: "pi2 p - e < pi2 q \<and> pi2 q < pi2 p + e"
	                using hqV unfolding V_def open_interval_def by simp
	              show "pi2 p - e < pi2 q"
	                using hq_conj by (rule conjunct1)
	              show "pi2 q < pi2 p + e"
	                using hq_conj by (rule conjunct2)
	            qed

            have hsum_gt: "s - 2*e < ?plus q"
            proof -
              have "(pi1 p - e) + (pi2 p - e) < (pi1 q) + (pi2 q)"
                using hqU' hqV' by linarith
              thus ?thesis
                unfolding s_def by simp
            qed
            have hsum_lt: "?plus q < s + 2*e"
            proof -
              have "(pi1 q) + (pi2 q) < (pi1 p + e) + (pi2 p + e)"
                using hqU'' hqV'' by linarith
              thus ?thesis
                unfolding s_def by simp
            qed

            have h2e_le1: "2*e \<le> (s - a) / 2"
              unfolding e_def by (simp add: min_def)
            have h2e_le2: "2*e \<le> (c - s) / 2"
              unfolding e_def by (simp add: min_def)

            have hs_a: "0 < s - a"
              using hs by linarith
            have hc_s: "0 < c - s"
              using hs' by linarith
            have hhalf1: "(s - a) / 2 < s - a"
            proof -
              have "((s - a) / 2 < s - a) \<longleftrightarrow> (s - a < (s - a) * (2::real))"
                by (simp add: divide_less_eq)
              also have "... "
              proof -
                have "(s - a) * (1::real) < (s - a) * (2::real)"
                  apply (rule mult_strict_left_mono)
                   apply simp
                  apply (rule hs_a)
                  done
                thus ?thesis
                  by simp
              qed
              finally show ?thesis .
            qed
            have hhalf2: "(c - s) / 2 < c - s"
            proof -
              have "((c - s) / 2 < c - s) \<longleftrightarrow> (c - s < (c - s) * (2::real))"
                by (simp add: divide_less_eq)
              also have "... "
              proof -
                have "(c - s) * (1::real) < (c - s) * (2::real)"
                  apply (rule mult_strict_left_mono)
                   apply simp
                  apply (rule hc_s)
                  done
                thus ?thesis
                  by simp
              qed
              finally show ?thesis .
            qed
            have h2e_lt1: "2*e < s - a"
              using h2e_le1 hhalf1 by linarith
            have h2e_lt2: "2*e < c - s"
              using h2e_le2 hhalf2 by linarith
            have ha_lt: "a < s - 2*e"
              using h2e_lt1 by linarith
            have hlt_c: "s + 2*e < c"
              using h2e_lt2 by linarith

            have "a < ?plus q"
              using ha_lt hsum_gt by linarith
            moreover have "?plus q < c"
              using hsum_lt hlt_c by linarith
            ultimately have "?plus q \<in> open_interval a c"
              unfolding open_interval_def by simp
            moreover have "q \<in> ?R \<times> ?R"
              by simp
            ultimately show "q \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
              by simp
          qed

          show "\<exists>b'\<in>product_basis ?TR ?TR. p \<in> b' \<and> b' \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_interval a c}"
            apply (rule bexI[where x="U \<times> V"])
             apply (intro conjI)
              apply (rule hpUV)
             apply (rule hUV_sub)
            apply (rule hUV_basis)
            done
        qed

        have hPre': "{p. ?plus p \<in> b} \<in> ?TP"
          using hP_open unfolding P_def by simp
        have hEq: "{p \<in> ?R \<times> ?R. ?plus p \<in> b} = {p. ?plus p \<in> b}"
          by simp
        show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
          using hPre' by (simp add: hEq[symmetric])
      next
        assume hbr: "\<exists>a. b = open_ray_gt a"
        then obtain a where hbeq: "b = open_ray_gt a"
          by blast
        define P where "P = {p \<in> ?R \<times> ?R. ?plus p \<in> b}"

        have hP_open: "P \<in> ?TP"
          unfolding P_def hbeq product_topology_on_def topology_generated_by_basis_def
        proof (intro CollectI conjI ballI)
          show "{p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a} \<subseteq> (UNIV::(real \<times> real) set)"
            by simp
	          fix p assume hp: "p \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
	          have hs: "a < ?plus p"
	          using hp unfolding open_ray_gt_def by simp
          define s where "s = ?plus p"
          have hs': "a < s"
            unfolding s_def using hs by simp
          define e where "e = (s - a) / 4"
          have he_pos: "0 < e"
          proof -
            have "0 < s - a"
              using hs' by linarith
            thus ?thesis
              unfolding e_def by (simp add: divide_pos_pos)
          qed

          define U where "U = open_interval (pi1 p - e) (pi1 p + e)"
          define V where "V = open_interval (pi2 p - e) (pi2 p + e)"

          have hU_open: "U \<in> ?TR"
            unfolding U_def
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith
          have hV_open: "V \<in> ?TR"
            unfolding V_def
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith

          have hpUV: "p \<in> U \<times> V"
            unfolding U_def V_def open_interval_def
            using he_pos by (cases p, simp add: pi1_def pi2_def)

          have hUV_basis: "U \<times> V \<in> product_basis ?TR ?TR"
            unfolding product_basis_def using hU_open hV_open by blast

          have hUV_sub: "U \<times> V \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
          proof (rule subsetI)
            fix q assume hq: "q \<in> U \<times> V"
            have hqU: "pi1 q \<in> U"
              using hq by (cases q, simp add: pi1_def)
            have hqV: "pi2 q \<in> V"
              using hq by (cases q, simp add: pi2_def)
            have hqU': "pi1 p - e < pi1 q"
              using hqU unfolding U_def open_interval_def by simp
            have hqV': "pi2 p - e < pi2 q"
              using hqV unfolding V_def open_interval_def by simp
            have hsum_gt: "s - 2*e < ?plus q"
            proof -
              have "(pi1 p - e) + (pi2 p - e) < (pi1 q) + (pi2 q)"
                using hqU' hqV' by linarith
              thus ?thesis
                unfolding s_def by simp
            qed
            have ha_lt: "a < s - 2*e"
            proof -
              have hEq: "s - 2*e = (s + a) / 2"
                unfolding e_def
                by (simp add: field_simps)
              have "a < (s + a) / 2"
              proof -
                have "a < (s + a) / 2 \<longleftrightarrow> a * (2::real) < s + a"
                  by (simp add: divide_less_eq)
                moreover have "a * (2::real) < s + a"
                  using hs' by linarith
                ultimately show ?thesis
                  by simp
              qed
              thus ?thesis
                unfolding hEq by simp
            qed
            have "a < ?plus q"
              using ha_lt hsum_gt by linarith
            hence "?plus q \<in> open_ray_gt a"
              unfolding open_ray_gt_def by simp
            moreover have "q \<in> ?R \<times> ?R"
              by simp
            ultimately show "q \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
              by simp
          qed

          show "\<exists>b'\<in>product_basis ?TR ?TR. p \<in> b' \<and> b' \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_gt a}"
            apply (rule bexI[where x="U \<times> V"])
             apply (intro conjI)
              apply (rule hpUV)
             apply (rule hUV_sub)
            apply (rule hUV_basis)
            done
        qed

        have hPre': "{p. ?plus p \<in> b} \<in> ?TP"
          using hP_open unfolding P_def by simp
        have hEq: "{p \<in> ?R \<times> ?R. ?plus p \<in> b} = {p. ?plus p \<in> b}"
          by simp
        show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
          using hPre' by (simp add: hEq[symmetric])
      next
        assume hbl: "\<exists>a. b = open_ray_lt a"
        then obtain a where hbeq: "b = open_ray_lt a"
          by blast
        define P where "P = {p \<in> ?R \<times> ?R. ?plus p \<in> b}"

        have hP_open: "P \<in> ?TP"
          unfolding P_def hbeq product_topology_on_def topology_generated_by_basis_def
        proof (intro CollectI conjI ballI)
          show "{p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a} \<subseteq> (UNIV::(real \<times> real) set)"
            by simp
	          fix p assume hp: "p \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
	          have hs: "?plus p < a"
	          using hp unfolding open_ray_lt_def by simp
          define s where "s = ?plus p"
          have hs': "s < a"
            unfolding s_def using hs by simp
          define e where "e = (a - s) / 4"
          have he_pos: "0 < e"
          proof -
            have "0 < a - s"
              using hs' by linarith
            thus ?thesis
              unfolding e_def by (simp add: divide_pos_pos)
          qed

          define U where "U = open_interval (pi1 p - e) (pi1 p + e)"
          define V where "V = open_interval (pi2 p - e) (pi2 p + e)"

          have hU_open: "U \<in> ?TR"
            unfolding U_def
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith
          have hV_open: "V \<in> ?TR"
            unfolding V_def
            apply (rule open_interval_in_order_topology)
            using he_pos by linarith

          have hpUV: "p \<in> U \<times> V"
            unfolding U_def V_def open_interval_def
            using he_pos by (cases p, simp add: pi1_def pi2_def)

          have hUV_basis: "U \<times> V \<in> product_basis ?TR ?TR"
            unfolding product_basis_def using hU_open hV_open by blast

          have hUV_sub: "U \<times> V \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
          proof (rule subsetI)
            fix q assume hq: "q \<in> U \<times> V"
            have hqU: "pi1 q \<in> U"
              using hq by (cases q, simp add: pi1_def)
            have hqV: "pi2 q \<in> V"
              using hq by (cases q, simp add: pi2_def)
            have hqU'': "pi1 q < pi1 p + e"
              using hqU unfolding U_def open_interval_def by simp
            have hqV'': "pi2 q < pi2 p + e"
              using hqV unfolding V_def open_interval_def by simp
            have hsum_lt: "?plus q < s + 2*e"
            proof -
              have "(pi1 q) + (pi2 q) < (pi1 p + e) + (pi2 p + e)"
                using hqU'' hqV'' by linarith
              thus ?thesis
                unfolding s_def by simp
            qed
            have hlt_a: "s + 2*e < a"
            proof -
              have hEq: "s + 2*e = (s + a) / 2"
                unfolding e_def
                by (simp add: field_simps)
              have "(s + a) / 2 < a"
              proof -
                have "(s + a) / 2 < a \<longleftrightarrow> s + a < a * (2::real)"
                  by (simp add: divide_less_eq)
                moreover have "s + a < a * (2::real)"
                  using hs' by linarith
                ultimately show ?thesis
                  by simp
              qed
              thus ?thesis
                unfolding hEq by simp
            qed
            have "?plus q < a"
              using hsum_lt hlt_a by linarith
            hence "?plus q \<in> open_ray_lt a"
              unfolding open_ray_lt_def by simp
            moreover have "q \<in> ?R \<times> ?R"
              by simp
            ultimately show "q \<in> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
              by simp
          qed

          show "\<exists>b'\<in>product_basis ?TR ?TR. p \<in> b' \<and> b' \<subseteq> {p \<in> ?R \<times> ?R. ?plus p \<in> open_ray_lt a}"
            apply (rule bexI[where x="U \<times> V"])
             apply (intro conjI)
              apply (rule hpUV)
             apply (rule hUV_sub)
            apply (rule hUV_basis)
            done
        qed

        have hPre': "{p. ?plus p \<in> b} \<in> ?TP"
          using hP_open unfolding P_def by simp
        have hEq: "{p \<in> ?R \<times> ?R. ?plus p \<in> b} = {p. ?plus p \<in> b}"
          by simp
        show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
          using hPre' by (simp add: hEq[symmetric])
      next
        assume hU: "b = (UNIV::real set)"
        have hRR_open: "?R \<times> ?R \<in> ?TP"
          using hTopRR unfolding is_topology_on_def by blast
        show "{p \<in> ?R \<times> ?R. ?plus p \<in> b} \<in> ?TP"
          unfolding hU using hRR_open by simp
      qed
    qed
  qed
qed
*)

(** Continuity of unary negation on \<open>\<real>\<close> in the order topology. **)
lemma top1_continuous_uminus_order_topology:
  shows "top1_continuous_map_on
      (UNIV::real set) order_topology_on_UNIV
      (UNIV::real set) order_topology_on_UNIV
      (\<lambda>x::real. -x)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?neg = "(\<lambda>x::real. -x)"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    by (rule basis_for_order_topology_on_UNIV)

  show ?thesis
  proof (rule top1_continuous_map_on_generated_by_basis)
    show "is_topology_on ?R ?TR"
      by (rule hTopR)
    show "basis_for ?R (basis_order_topology::real set set) ?TR"
      by (rule hBasisR)
    show "\<forall>x\<in>?R. ?neg x \<in> ?R"
      by simp
    show "\<forall>b\<in>(basis_order_topology::real set set). {x \<in> ?R. ?neg x \<in> b} \<in> ?TR"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      have hcases:
        "(\<exists>a c. a < c \<and> b = open_interval a c)
         \<or> (\<exists>a. b = open_ray_gt a)
         \<or> (\<exists>a. b = open_ray_lt a)
         \<or> b = (UNIV::real set)"
        by (rule basis_order_topology_cases[OF hb])
      show "{x \<in> ?R. -x \<in> b} \<in> ?TR"
      proof (rule disjE[OF hcases])
	        assume hbint: "\<exists>a c. a < c \<and> b = open_interval a c"
	        then obtain a c where hac: "a < c" and hbeq: "b = open_interval a c"
	          by blast
	        have hEq: "{x \<in> ?R. -x \<in> b} = open_interval (-c) (-a)"
	        proof (rule equalityI)
	          show "{x \<in> ?R. -x \<in> b} \<subseteq> open_interval (-c) (-a)"
	          proof (rule subsetI)
	            fix x
	            assume hx: "x \<in> {x \<in> ?R. -x \<in> b}"
	            have hxb: "-x \<in> b"
	              using hx by simp
	            have "a < -x \<and> -x < c"
	              using hxb unfolding hbeq open_interval_def by simp
	            hence "-c < x \<and> x < -a"
	              by linarith
	            thus "x \<in> open_interval (-c) (-a)"
	              unfolding open_interval_def by simp
	          qed
	          show "open_interval (-c) (-a) \<subseteq> {x \<in> ?R. -x \<in> b}"
	          proof (rule subsetI)
	            fix x
	            assume hx: "x \<in> open_interval (-c) (-a)"
	            have "-c < x \<and> x < -a"
	              using hx unfolding open_interval_def by simp
	            hence "a < -x \<and> -x < c"
	              by linarith
	            hence "-x \<in> b"
	              unfolding hbeq open_interval_def by simp
	            thus "x \<in> {x \<in> ?R. -x \<in> b}"
	              by simp
	          qed
	        qed
        have hEq': "{x. -x \<in> b} = open_interval (-c) (-a)"
          using hEq by simp
        have hOpen: "open_interval (-c) (-a) \<in> ?TR"
        proof -
          have "-c < -a"
            using hac by linarith
          thus ?thesis
            by (rule open_interval_in_order_topology)
        qed
        show ?thesis
          using hOpen by (simp add: hEq')
      next
        assume hrest: "(\<exists>a. b = open_ray_gt a) \<or> (\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
        show ?thesis
        proof (rule disjE[OF hrest])
          assume hbr: "\<exists>a. b = open_ray_gt a"
	          then obtain a where hbeq: "b = open_ray_gt a"
	            by blast
	          have hEq: "{x \<in> ?R. -x \<in> b} = open_ray_lt (-a)"
	          proof (rule equalityI)
	            show "{x \<in> ?R. -x \<in> b} \<subseteq> open_ray_lt (-a)"
	            proof (rule subsetI)
	              fix x
	              assume hx: "x \<in> {x \<in> ?R. -x \<in> b}"
	              have "-x \<in> b"
	                using hx by simp
	              have "a < -x"
	                using \<open>-x \<in> b\<close> unfolding hbeq open_ray_gt_def by simp
	              hence "x < -a"
	                by linarith
	              thus "x \<in> open_ray_lt (-a)"
	                unfolding open_ray_lt_def by simp
	            qed
	            show "open_ray_lt (-a) \<subseteq> {x \<in> ?R. -x \<in> b}"
	            proof (rule subsetI)
	              fix x
	              assume hx: "x \<in> open_ray_lt (-a)"
	              have "x < -a"
	                using hx unfolding open_ray_lt_def by simp
	              hence "a < -x"
	                by linarith
	              hence "-x \<in> b"
	                unfolding hbeq open_ray_gt_def by simp
	              thus "x \<in> {x \<in> ?R. -x \<in> b}"
	                by simp
	            qed
	          qed
          have hEq': "{x. -x \<in> b} = open_ray_lt (-a)"
            using hEq by simp
          have hOpen: "open_ray_lt (-a) \<in> ?TR"
            by (rule open_ray_lt_in_order_topology)
          show ?thesis
            using hOpen by (simp add: hEq')
        next
          assume hrest2: "(\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
          show ?thesis
          proof (rule disjE[OF hrest2])
	            assume hbl: "\<exists>a. b = open_ray_lt a"
	            then obtain a where hbeq: "b = open_ray_lt a"
	              by blast
	            have hEq: "{x \<in> ?R. -x \<in> b} = open_ray_gt (-a)"
	            proof (rule equalityI)
	              show "{x \<in> ?R. -x \<in> b} \<subseteq> open_ray_gt (-a)"
	              proof (rule subsetI)
	                fix x
	                assume hx: "x \<in> {x \<in> ?R. -x \<in> b}"
	                have "-x \<in> b"
	                  using hx by simp
	                have "-x < a"
	                  using \<open>-x \<in> b\<close> unfolding hbeq open_ray_lt_def by simp
	                hence "-a < x"
	                  by linarith
	                thus "x \<in> open_ray_gt (-a)"
	                  unfolding open_ray_gt_def by simp
	              qed
	              show "open_ray_gt (-a) \<subseteq> {x \<in> ?R. -x \<in> b}"
	              proof (rule subsetI)
	                fix x
	                assume hx: "x \<in> open_ray_gt (-a)"
	                have "-a < x"
	                  using hx unfolding open_ray_gt_def by simp
	                hence "-x < a"
	                  by linarith
	                hence "-x \<in> b"
	                  unfolding hbeq open_ray_lt_def by simp
	                thus "x \<in> {x \<in> ?R. -x \<in> b}"
	                  by simp
	              qed
	            qed
            have hEq': "{x. -x \<in> b} = open_ray_gt (-a)"
              using hEq by simp
            have hOpen: "open_ray_gt (-a) \<in> ?TR"
              by (rule open_ray_gt_in_order_topology)
            show ?thesis
              using hOpen by (simp add: hEq')
          next
            assume hU: "b = (UNIV::real set)"
            have hR_open: "?R \<in> ?TR"
              using hTopR unfolding is_topology_on_def by blast
            show ?thesis
              unfolding hU using hR_open by simp
          qed
        qed
      qed
    qed
  qed
qed

(** Continuity of multiplicative inversion on the positive reals in the order topology. **)
lemma top1_continuous_inv_order_topology_pos:
  shows "top1_continuous_map_on
      (open_ray_gt (0::real))
      (subspace_topology (UNIV::real set) order_topology_on_UNIV (open_ray_gt (0::real)))
      (UNIV::real set) order_topology_on_UNIV
      (\<lambda>t::real. inverse t)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?Pos = "open_ray_gt (0::real)"
  let ?TPos = "subspace_topology ?R ?TR ?Pos"
  let ?inv = "(\<lambda>t::real. inverse t)"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopPos: "is_topology_on ?Pos ?TPos"
    by (rule subspace_topology_is_topology_on[OF hTopR], simp)

  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    by (rule basis_for_order_topology_on_UNIV)

  show ?thesis
  proof (rule top1_continuous_map_on_generated_by_basis)
    show "is_topology_on ?Pos ?TPos"
      by (rule hTopPos)
    show "basis_for ?R (basis_order_topology::real set set) ?TR"
      by (rule hBasisR)
    show "\<forall>t\<in>?Pos. ?inv t \<in> ?R"
      by simp
    show "\<forall>b\<in>(basis_order_topology::real set set). {t \<in> ?Pos. ?inv t \<in> b} \<in> ?TPos"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      define P where "P = {t \<in> ?Pos. ?inv t \<in> b}"
      have hPsub: "P \<subseteq> ?Pos"
        unfolding P_def by simp

	      have hlocal: "\<forall>p\<in>P. \<exists>U\<in>?TPos. p \<in> U \<and> U \<subseteq> P"
	      proof (intro ballI)
	        fix p assume hpP: "p \<in> P"
	        have hpPos: "p \<in> ?Pos" and hpb: "?inv p \<in> b"
	        proof -
	          have hp_conj: "p \<in> ?Pos \<and> ?inv p \<in> b"
	            using hpP unfolding P_def by simp
	          show "p \<in> ?Pos"
	            using hp_conj by (rule conjunct1)
	          show "?inv p \<in> b"
	            using hp_conj by (rule conjunct2)
	        qed
        have hpgt: "0 < p"
          using hpPos unfolding open_ray_gt_def by simp

        obtain e where he: "0 < e"
          and hI_sub: "open_interval (?inv p - e) (?inv p + e) \<subseteq> b"
          using basis_order_topology_contains_open_interval[OF hb hpb] by blast

        define d1 where "d1 = p / 2"
        define d2 where "d2 = e * p\<^sup>2 / 4"
        define d where "d = min d1 d2"

        have hd1: "0 < d1"
          unfolding d1_def using hpgt by linarith
        have hd2: "0 < d2"
          unfolding d2_def using he hpgt by (simp add: divide_pos_pos)
        have hd: "0 < d"
          unfolding d_def using hd1 hd2 by simp
        have hd_le_d1: "d \<le> d1"
          unfolding d_def by simp
        have hd_le_d2: "d \<le> d2"
          unfolding d_def by simp

        define U where "U = open_interval (p - d) (p + d)"
        have hU_TR: "U \<in> ?TR"
        proof -
          have "p - d < p + d"
            using hd by linarith
          thus ?thesis
            unfolding U_def by (rule open_interval_in_order_topology)
        qed

        have hUsubPos: "U \<subseteq> ?Pos"
        proof (rule subsetI)
          fix t assume htU: "t \<in> U"
          have hlt: "p - d < t"
            using htU unfolding U_def open_interval_def by simp
          have "p / 2 \<le> p - d"
            using hd_le_d1 unfolding d1_def by linarith
          hence "p / 2 < t"
            using hlt by linarith
          hence "0 < t"
            using hpgt by linarith
          thus "t \<in> ?Pos"
            unfolding open_ray_gt_def by simp
        qed

        have hU_TPos: "U \<in> ?TPos"
        proof -
          have "U = ?Pos \<inter> U"
            using hUsubPos by blast
          thus ?thesis
            unfolding subspace_topology_def using hU_TR by blast
        qed

        have hpU: "p \<in> U"
        proof -
          have "p - d < p"
            using hd by linarith
          have "p < p + d"
            using hd by linarith
          thus ?thesis
            unfolding U_def open_interval_def using \<open>p - d < p\<close> by simp
        qed

        have hUsubP: "U \<subseteq> P"
        proof (rule subsetI)
          fix t assume htU: "t \<in> U"
          have htPos: "t \<in> ?Pos"
            using hUsubPos htU by blast
	          have htgt: "0 < t"
	            using htPos unfolding open_ray_gt_def by simp
	
	          have ht1: "p - d < t" and ht2: "t < p + d"
	          proof -
	            have ht_conj: "p - d < t \<and> t < p + d"
	              using htU unfolding U_def open_interval_def by simp
	            show "p - d < t"
	              using ht_conj by (rule conjunct1)
	            show "t < p + d"
	              using ht_conj by (rule conjunct2)
	          qed
          have habs_lt: "abs (t - p) < d"
            using ht1 ht2 by (simp add: abs_less_iff)
          have habs_le: "abs (t - p) \<le> d"
            using habs_lt by (rule less_imp_le)

          have ht_ge_p2: "p / 2 \<le> t"
          proof -
            have "p / 2 \<le> p - d"
              using hd_le_d1 unfolding d1_def by linarith
            thus ?thesis
              using ht1 by linarith
          qed
          have ht_lower: "p * (p / 2) \<le> p * t"
            using ht_ge_p2 by (simp add: mult_left_mono hpgt less_imp_le)

          have hinv_diff:
            "abs (?inv t - ?inv p) = abs (t - p) / (p * t)"
          proof -
            have hp0: "p \<noteq> 0"
              using hpgt by simp
            have ht0: "t \<noteq> 0"
              using htgt by simp
            have "?inv t - ?inv p = (p - t) / (p * t)"
              using hp0 ht0 by (simp add: field_simps)
            hence "abs (?inv t - ?inv p) = abs (p - t) / abs (p * t)"
              by (simp add: abs_divide)
            also have "abs (p - t) = abs (t - p)"
              by simp
            also have "abs (p * t) = p * t"
              using hpgt htgt by simp
            finally show ?thesis
              by simp
          qed

          have hden_pos: "0 < p * (p / 2)"
            using hpgt by (simp add: mult_pos_pos)
          have hden_le: "p * (p / 2) \<le> p * t"
            by (rule ht_lower)
          have hle_inv: "inverse (p * t) \<le> inverse (p * (p / 2))"
            using hden_le hden_pos by (rule le_imp_inverse_le)

          have hdiff_le:
            "abs (?inv t - ?inv p) \<le> abs (t - p) / (p * (p / 2))"
          proof -
            have hnonneg: "0 \<le> abs (t - p)"
              by simp
            have "abs (?inv t - ?inv p) = abs (t - p) * inverse (p * t)"
              unfolding hinv_diff by (simp only: divide_inverse)
            also have "... \<le> abs (t - p) * inverse (p * (p / 2))"
              using hle_inv hnonneg by (rule mult_left_mono)
            also have "... = abs (t - p) / (p * (p / 2))"
              by (simp only: divide_inverse)
            finally show ?thesis .
          qed

          have hdiff_le2: "abs (?inv t - ?inv p) \<le> 2 * d / p\<^sup>2"
          proof -
            have hp0: "p \<noteq> 0"
              using hpgt by simp
            have hEq: "abs (t - p) / (p * (p / 2)) = 2 * abs (t - p) / p\<^sup>2"
              using hp0 by (simp add: field_simps power2_eq_square)
            have "abs (?inv t - ?inv p) \<le> 2 * abs (t - p) / p\<^sup>2"
              using hdiff_le unfolding hEq .
            also have "... \<le> 2 * d / p\<^sup>2"
	            proof -
	              have hp2pos: "0 < p\<^sup>2"
	                using hpgt by simp
	              have hp2nonneg: "0 \<le> p\<^sup>2"
	                by (rule less_imp_le[OF hp2pos])
	              have "2 * abs (t - p) \<le> 2 * d"
	                using habs_le by (rule mult_left_mono, simp)
	              have "2 * abs (t - p) / p\<^sup>2 \<le> 2 * d / p\<^sup>2"
	              proof (rule divide_right_mono)
	                show "2 * abs (t - p) \<le> 2 * d"
	                  by (rule \<open>2 * abs (t - p) \<le> 2 * d\<close>)
	                show "0 \<le> p\<^sup>2"
	                  by (rule hp2nonneg)
	              qed
	              thus ?thesis .
	            qed
	            finally show ?thesis .
	          qed

          have hbound: "2 * d / p\<^sup>2 \<le> e / 2"
	          proof -
	            have hp2pos: "0 < p\<^sup>2"
	              using hpgt by simp
	            have hp2nonneg: "0 \<le> p\<^sup>2"
	              by (rule less_imp_le[OF hp2pos])
	            have hd_le: "d \<le> e * p\<^sup>2 / 4"
	              using hd_le_d2 unfolding d2_def by simp
	            have hnum_le: "2 * d \<le> 2 * (e * p\<^sup>2 / 4)"
	              using hd_le by (rule mult_left_mono, simp)
	            have "2 * d / p\<^sup>2 \<le> (2 * (e * p\<^sup>2 / 4)) / p\<^sup>2"
	            proof (rule divide_right_mono)
	              show "2 * d \<le> 2 * (e * p\<^sup>2 / 4)"
	                by (rule hnum_le)
	              show "0 \<le> p\<^sup>2"
	                by (rule hp2nonneg)
	            qed
	            hence "2 * d / p\<^sup>2 \<le> (2 * (e * p\<^sup>2 / 4)) / p\<^sup>2" .
	            also have "... = e / 2"
	              using hpgt by (simp add: field_simps)
	            finally show ?thesis .
	          qed

          have he2: "e / 2 < e"
            using he by linarith
          have hdiff_lt: "abs (?inv t - ?inv p) < e"
          proof -
            have hdiff_le_e2: "abs (?inv t - ?inv p) \<le> e / 2"
              by (rule order_trans[OF hdiff_le2 hbound])
            show ?thesis
              by (rule le_less_trans[OF hdiff_le_e2 he2])
          qed

          have hlt1: "?inv p - e < ?inv t"
          proof -
            have "-e < ?inv t - ?inv p"
              using hdiff_lt by (simp add: abs_less_iff)
            thus ?thesis
              by linarith
          qed
          have hlt2: "?inv t < ?inv p + e"
          proof -
            have "?inv t - ?inv p < e"
              using hdiff_lt by (simp add: abs_less_iff)
            thus ?thesis
              by linarith
          qed
          have htI: "?inv t \<in> open_interval (?inv p - e) (?inv p + e)"
            unfolding open_interval_def using hlt1 hlt2 by simp
          have htB: "?inv t \<in> b"
            using hI_sub htI by blast

          show "t \<in> P"
            unfolding P_def using htPos htB by simp
        qed

        show "\<exists>U\<in>?TPos. p \<in> U \<and> U \<subseteq> P"
        proof (rule bexI[where x=U])
          show "U \<in> ?TPos"
            by (rule hU_TPos)
          show "p \<in> U \<and> U \<subseteq> P"
            by (intro conjI, rule hpU, rule hUsubP)
        qed
      qed

      have "P \<in> ?TPos"
        by (rule top1_open_set_from_local_opens[OF hTopPos hPsub hlocal])
      thus "{t \<in> ?Pos. ?inv t \<in> b} \<in> ?TPos"
        unfolding P_def .
    qed
  qed
qed

(** Convenience: sums and differences of continuous real-valued maps in the order topology. **)
lemma top1_continuous_add_real:
  fixes f g :: "'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hf: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
  assumes hg: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV g"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. f x + g x)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?pair = "(\<lambda>x. (f x, g x))"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hpi1: "top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> ?pair)"
  proof -
    have hEq: "(pi1 \<circ> ?pair) = f"
      by (rule ext, simp add: o_def pi1_def)
    show ?thesis
      unfolding hEq by (rule hf)
  qed
  have hpi2: "top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> ?pair)"
  proof -
    have hEq: "(pi2 \<circ> ?pair) = g"
      by (rule ext, simp add: o_def pi2_def)
    show ?thesis
      unfolding hEq by (rule hg)
  qed

  have hpair: "top1_continuous_map_on X TX (?R \<times> ?R) ?TP ?pair"
  proof -
    have hiff:
      "top1_continuous_map_on X TX (?R \<times> ?R) ?TP ?pair
       \<longleftrightarrow>
         (top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> ?pair)
          \<and> top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> ?pair))"
      by (rule Theorem_18_4[OF hTopX hTopR hTopR])
    show ?thesis
      apply (rule iffD2[OF hiff])
      apply (intro conjI)
       apply (rule hpi1)
      apply (rule hpi2)
      done
  qed

  have hplus: "top1_continuous_map_on (?R \<times> ?R) ?TP ?R ?TR (\<lambda>p::real \<times> real. pi1 p + pi2 p)"
    by (rule top1_continuous_add_order_topology)

  have hEq: "(\<lambda>x. f x + g x) = (\<lambda>p::real \<times> real. pi1 p + pi2 p) \<circ> ?pair"
    by (rule ext, simp add: o_def pi1_def pi2_def)

  show ?thesis
    unfolding hEq
    by (rule top1_continuous_map_on_comp[OF hpair hplus])
qed

(*
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?pair = "(\<lambda>x. (f x, g x))"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopRR: "is_topology_on (?R \<times> ?R) ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopR hTopR])

  have hpi1: "top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> ?pair)"
  proof -
    have hEq: "(pi1 \<circ> ?pair) = f"
      by (rule ext, simp add: o_def pi1_def)
    show ?thesis
      unfolding hEq
      by (rule hf)
  qed
  have hpi2: "top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> ?pair)"
  proof -
    have hEq: "(pi2 \<circ> ?pair) = g"
      by (rule ext, simp add: o_def pi2_def)
    show ?thesis
      unfolding hEq
      by (rule hg)
  qed

  have hpair: "top1_continuous_map_on X TX (?R \<times> ?R) ?TP ?pair"
  proof -
    have hiff:
      "top1_continuous_map_on X TX (?R \<times> ?R) ?TP ?pair
       \<longleftrightarrow>
         (top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> ?pair)
          \<and> top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> ?pair))"
      by (rule Theorem_18_4[OF hTopX hTopR hTopR])
    show ?thesis
      by (rule iffD2[OF hiff], intro conjI, rule hpi1, rule hpi2)
  qed

  have hplus: "top1_continuous_map_on (?R \<times> ?R) ?TP ?R ?TR (\<lambda>p::real \<times> real. pi1 p + pi2 p)"
    by (rule top1_continuous_add_order_topology)

  show ?thesis
  proof -
    have hEq: "(\<lambda>x. f x + g x) = (\<lambda>p::real \<times> real. pi1 p + pi2 p) \<circ> ?pair"
      by (rule ext, simp add: o_def pi1_def pi2_def)
    show ?thesis
      unfolding hEq
      by (rule top1_continuous_map_on_comp[OF hpair hplus])
  qed
qed
*)

lemma top1_continuous_uminus_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes hf: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. - f x)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  have hneg: "top1_continuous_map_on ?R ?TR ?R ?TR (\<lambda>t::real. -t)"
    by (rule top1_continuous_uminus_order_topology)
  have hEq: "(\<lambda>x. - f x) = (\<lambda>t::real. -t) \<circ> f"
    by (rule ext, simp add: o_def)
  show ?thesis
    unfolding hEq
    by (rule top1_continuous_map_on_comp[OF hf hneg])
qed

lemma top1_continuous_diff_real:
  fixes f g :: "'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hf: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
  assumes hg: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV g"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. f x - g x)"
proof -
  have hneg: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. - g x)"
    by (rule top1_continuous_uminus_real[OF hg])
  have hadd: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. f x + (- g x))"
    by (rule top1_continuous_add_real[OF hTopX hf hneg])
  show ?thesis
    using hadd by simp
qed

(** Continuity of pointwise multiplication of continuous real-valued maps (order topology on \<open>\<real>\<close>). **)
lemma top1_continuous_mul_real:
  fixes f g :: "'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hf: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
  assumes hg: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV g"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. f x * g x)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?pair = "(\<lambda>x. (f x, g x))"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hpi1: "top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> ?pair)"
  proof -
    have hEq: "(pi1 \<circ> ?pair) = f"
      by (rule ext, simp add: o_def pi1_def)
    show ?thesis
      unfolding hEq by (rule hf)
  qed
  have hpi2: "top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> ?pair)"
  proof -
    have hEq: "(pi2 \<circ> ?pair) = g"
      by (rule ext, simp add: o_def pi2_def)
    show ?thesis
      unfolding hEq by (rule hg)
  qed

  have hpair: "top1_continuous_map_on X TX (?R \<times> ?R) ?TP ?pair"
  proof -
    have hiff:
      "top1_continuous_map_on X TX (?R \<times> ?R) ?TP ?pair
       \<longleftrightarrow>
         (top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> ?pair)
          \<and> top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> ?pair))"
      by (rule Theorem_18_4[OF hTopX hTopR hTopR])
    show ?thesis
      apply (rule iffD2[OF hiff])
      apply (intro conjI)
       apply (rule hpi1)
      apply (rule hpi2)
      done
  qed

  have hmul: "top1_continuous_map_on (?R \<times> ?R) ?TP ?R ?TR (\<lambda>p::real \<times> real. pi1 p * pi2 p)"
    by (rule top1_continuous_mul_order_topology)

  have hEq: "(\<lambda>x. f x * g x) = (\<lambda>p::real \<times> real. pi1 p * pi2 p) \<circ> ?pair"
    by (rule ext, simp add: o_def pi1_def pi2_def)

  show ?thesis
    unfolding hEq
    by (rule top1_continuous_map_on_comp[OF hpair hmul])
qed

(** Finite sums of continuous real-valued maps are continuous (order topology on \<open>\<real>\<close>). **)
lemma top1_continuous_sum_lessThan_real:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hf: "\<forall>i<n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i)"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<n. f i x))"
proof -
  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hConst: "\<forall>y0\<in>(UNIV::real set). top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. y0)"
    by (rule Theorem_18_2(1)[OF hTopX hTopR hTopR])
  have h0: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (0::real))"
    using hConst by simp

  have hInd:
    "\<forall>m. (\<forall>i<m. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i))
          \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<m. f i x))"
  proof (intro allI)
    fix m :: nat
    show "(\<forall>i<m. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i))
          \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<m. f i x))"
    proof (induction m)
      case 0
      show ?case
      proof (intro impI)
        assume "\<forall>i<0. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i)"
        have hEq: "(\<lambda>x. (\<Sum>i<0. f i x)) = (\<lambda>x. (0::real))"
          by (rule ext, simp)
        show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<0. f i x))"
          unfolding hEq by (rule h0)
      qed
    next
      case (Suc m)
      show ?case
      proof (intro impI)
        assume hfsuc: "\<forall>i<Suc m. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i)"

        have hpre: "\<forall>i<m. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i)"
        proof (intro allI impI)
          fix i assume hi: "i < m"
          have hi': "i < Suc m"
            using hi by simp
          have himp:
            "i < Suc m \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i)"
            using hfsuc by (rule spec)
          show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i)"
            by (rule mp[OF himp hi'])
        qed

        have hsn:
          "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<m. f i x))"
          by (rule mp[OF Suc.IH hpre])

        have hfn: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f m)"
        proof -
          have himp: "m < Suc m \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f m)"
            using hfsuc by (rule spec)
          have hm': "m < Suc m"
            by simp
          show ?thesis
            by (rule mp[OF himp hm'])
        qed

        have hadd: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<m. f i x) + f m x)"
          by (rule top1_continuous_add_real[OF hTopX hsn hfn])
        have hEq: "(\<lambda>x. (\<Sum>i<Suc m. f i x)) = (\<lambda>x. (\<Sum>i<m. f i x) + f m x)"
          by (rule ext, simp)
        show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<Suc m. f i x))"
          unfolding hEq by (rule hadd)
      qed
    qed
  qed

  have hImp:
    "(\<forall>i<n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (f i))
      \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (\<Sum>i<n. f i x))"
    using hInd by (rule spec)
  show ?thesis
    by (rule mp[OF hImp hf])
qed

(*
proof -
  have hneg: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. - g x)"
    by (rule top1_continuous_uminus_real[OF hg])
  have hadd: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. f x + (- g x))"
    by (rule top1_continuous_add_real[OF hTopX hf hneg])
  show ?thesis
    using hadd by simp
qed
*)

(** Uniform convergence on a set, specialized to real-valued maps. **)
definition top1_uniformly_convergent_on_real ::
  "'a set \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "top1_uniformly_convergent_on_real X s g \<longleftrightarrow>
     (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>X. abs (s n x - g x) < e)"

lemma top1_uniform_limit_continuous_real:
  fixes s :: "nat \<Rightarrow> 'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hscont: "\<forall>n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (s n)"
  assumes hunif: "top1_uniformly_convergent_on_real X s g"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV g"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"

  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> (\<Union>U) \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]]])

  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    by (rule basis_for_order_topology_on_UNIV)

  show ?thesis
  proof (rule top1_continuous_map_on_generated_by_basis)
    show "is_topology_on X TX"
      by (rule hTopX)
    show "basis_for ?R (basis_order_topology::real set set) ?TR"
      by (rule hBasisR)
    show "\<forall>x\<in>X. g x \<in> ?R"
      by simp
    show "\<forall>b\<in>(basis_order_topology::real set set). {x \<in> X. g x \<in> b} \<in> TX"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      define P where "P = {x\<in>X. g x \<in> b}"

	      have hlocal: "\<forall>x\<in>P. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> P"
	      proof (intro ballI)
	        fix x assume hxP: "x \<in> P"
	        have hxX: "x \<in> X" and hgxb: "g x \<in> b"
	        proof -
	          have hx_conj: "x \<in> X \<and> g x \<in> b"
	            using hxP unfolding P_def by simp
	          show "x \<in> X"
	            using hx_conj by (rule conjunct1)
	          show "g x \<in> b"
	            using hx_conj by (rule conjunct2)
	        qed

        obtain e where he: "0 < e" and hI_sub: "open_interval (g x - e) (g x + e) \<subseteq> b"
          using basis_order_topology_contains_open_interval[OF hb hgxb] by blast
        have he2: "0 < e/2"
          using he by linarith

        obtain N where hN: "\<forall>n\<ge>N. \<forall>y\<in>X. abs (s n y - g y) < e/2"
          using hunif unfolding top1_uniformly_convergent_on_real_def using he2 by blast
        have hNx: "abs (s N x - g x) < e/2"
          using hN hxX by simp

        have hW_open: "open_interval (g x - e/2) (g x + e/2) \<in> ?TR"
        proof -
          have "g x - e/2 < g x + e/2"
            using he2 by linarith
          thus ?thesis
            by (rule open_interval_in_order_topology)
        qed

        define W where "W = open_interval (g x - e/2) (g x + e/2)"
        define U where "U = {y\<in>X. s N y \<in> W}"

        have hsN_cont: "top1_continuous_map_on X TX ?R ?TR (s N)"
          using hscont by simp

        have hU_TX: "U \<in> TX"
        proof -
          have hpre: "\<forall>V\<in>?TR. {y\<in>X. s N y \<in> V} \<in> TX"
            using hsN_cont unfolding top1_continuous_map_on_def by blast
          show ?thesis
            unfolding U_def using hpre hW_open unfolding W_def by blast
        qed

        have hsNxW: "s N x \<in> W"
        proof -
          have hboth: "s N x - g x < e/2 \<and> - (s N x - g x) < e/2"
            using hNx by (rule iffD1[OF abs_less_iff])
          have hupper: "s N x - g x < e/2"
            by (rule conjunct1[OF hboth])
          have hneg: "- (s N x - g x) < e/2"
            by (rule conjunct2[OF hboth])
          have hlower: "-e/2 < (s N x - g x)"
            using hneg by linarith
          have h1: "g x - e/2 < s N x"
            using hlower by linarith
          have h2: "s N x < g x + e/2"
            using hupper by linarith
          show ?thesis
            unfolding W_def open_interval_def using h1 h2 by simp
        qed

        have hxU: "x \<in> U"
          unfolding U_def using hxX hsNxW by simp

        have hUsubP: "U \<subseteq> P"
	        proof (rule subsetI)
	          fix u assume huU: "u \<in> U"
	          have huX: "u \<in> X" and hsNuW: "s N u \<in> W"
	          proof -
	            have hu_conj: "u \<in> X \<and> s N u \<in> W"
	              using huU unfolding U_def by simp
	            show "u \<in> X"
	              using hu_conj by (rule conjunct1)
	            show "s N u \<in> W"
	              using hu_conj by (rule conjunct2)
	          qed
	          have hNu: "abs (s N u - g u) < e/2"
	            using hN huX by simp
	
	          have hsNu1: "g x - e/2 < s N u" and hsNu2: "s N u < g x + e/2"
	          proof -
	            have hs_conj: "g x - e/2 < s N u \<and> s N u < g x + e/2"
	              using hsNuW unfolding W_def open_interval_def by simp
	            show "g x - e/2 < s N u"
	              using hs_conj by (rule conjunct1)
	            show "s N u < g x + e/2"
	              using hs_conj by (rule conjunct2)
	          qed

          have hboth: "s N u - g u < e/2 \<and> - (s N u - g u) < e/2"
            using hNu by (rule iffD1[OF abs_less_iff])
          have hupper: "s N u - g u < e/2"
            by (rule conjunct1[OF hboth])
          have hneg: "- (s N u - g u) < e/2"
            by (rule conjunct2[OF hboth])
          have hlower: "-e/2 < (s N u - g u)"
            using hneg by linarith

          have hgu1: "g x - e < g u"
            using hsNu1 hupper by linarith
          have hgu2: "g u < g x + e"
            using hsNu2 hlower by linarith

          have hguI: "g u \<in> open_interval (g x - e) (g x + e)"
            unfolding open_interval_def using hgu1 hgu2 by simp
          have "g u \<in> b"
            using hI_sub hguI by blast
          thus "u \<in> P"
            unfolding P_def using huX by simp
        qed

        show "\<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> P"
        proof (rule bexI[where x=U])
          show "U \<in> TX"
            by (rule hU_TX)
          show "x \<in> U \<and> U \<subseteq> P"
            by (intro conjI, rule hxU, rule hUsubP)
        qed
      qed

      define UP where "UP = {U. U \<in> TX \<and> U \<subseteq> P}"
      have hUP_sub: "UP \<subseteq> TX"
      proof (rule subsetI)
        fix U assume hU: "U \<in> UP"
        thus "U \<in> TX"
          unfolding UP_def by simp
      qed
      have hUnion_UP: "\<Union>UP \<in> TX"
        using union_TX hUP_sub by blast

      have hEq: "P = \<Union>UP"
      proof (rule set_eqI)
        fix x
        show "x \<in> P \<longleftrightarrow> x \<in> \<Union>UP"
        proof (rule iffI)
          assume hxP: "x \<in> P"
          obtain U where hU_TX: "U \<in> TX" and hxU: "x \<in> U" and hUsub: "U \<subseteq> P"
            using hlocal hxP by blast
          have hU_UP: "U \<in> UP"
            unfolding UP_def using hU_TX hUsub by blast
          show "x \<in> \<Union>UP"
            by (rule UnionI[OF hU_UP hxU])
        next
          assume hx: "x \<in> \<Union>UP"
          then obtain U where hU_UP: "U \<in> UP" and hxU: "x \<in> U"
            by blast
          have hUsub: "U \<subseteq> P"
            using hU_UP unfolding UP_def by blast
          show "x \<in> P"
            using hUsub hxU by blast
        qed
      qed

      show "{x \<in> X. g x \<in> b} \<in> TX"
        unfolding P_def[symmetric] hEq
        using hUnion_UP .
    qed
  qed
qed

(*
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"

  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hnbhd_g:
    "\<forall>x\<in>X. \<forall>V. neighborhood_of (g x) ?R ?TR V \<longrightarrow>
      (\<exists>U. neighborhood_of x X TX U \<and> g ` U \<subseteq> V)"
  proof (intro ballI allI impI)
    fix x V
    assume hxX: "x \<in> X"
    assume hV: "neighborhood_of (g x) ?R ?TR V"
    have hVT: "V \<in> ?TR" and hgxV: "g x \<in> V"
      using hV unfolding neighborhood_of_def by blast+

    obtain b where hbB: "b \<in> (basis_order_topology::real set set)"
        and hgb: "g x \<in> b" and hbV: "b \<subseteq> V"
      using hVT hgxV unfolding order_topology_on_UNIV_def topology_generated_by_basis_def
      by blast

    obtain e where he: "0 < e" and hI_sub: "open_interval (g x - e) (g x + e) \<subseteq> b"
      using basis_order_topology_contains_open_interval[OF hbB hgb] by blast

    have he2: "0 < e/2"
      using he by linarith

    obtain N where hN:
      "\<forall>n\<ge>N. \<forall>y\<in>X. abs (s n y - g y) < e/2"
      using hunif unfolding top1_uniformly_convergent_on_real_def using he2 by blast

    have hNx: "abs (s N x - g x) < e/2"
      using hN hxX by simp

    have hW_open: "open_interval (g x - e/2) (g x + e/2) \<in> ?TR"
    proof -
      have "g x - e/2 < g x + e/2"
        using he2 by linarith
      thus ?thesis
        by (rule open_interval_in_order_topology)
    qed

    have hsN_cont: "top1_continuous_map_on X TX ?R ?TR (s N)"
      using hscont by simp

    have hsN_nbhd:
      "\<forall>y\<in>X. \<forall>W. neighborhood_of ((s N) y) ?R ?TR W \<longrightarrow>
        (\<exists>U. neighborhood_of y X TX U \<and> (s N) ` U \<subseteq> W)"
    proof -
      have hiff:
        "top1_continuous_map_on X TX ?R ?TR (s N) \<longleftrightarrow>
         ((\<forall>y\<in>X. (s N) y \<in> ?R) \<and>
          (\<forall>y\<in>X. \<forall>W. neighborhood_of ((s N) y) ?R ?TR W \<longrightarrow>
              (\<exists>U. neighborhood_of y X TX U \<and> (s N) ` U \<subseteq> W)))"
        by (rule Theorem_18_1(3)[OF hTopX hTopR])
      show ?thesis
        using hsN_cont hiff by blast
    qed

    have hsNxW: "neighborhood_of ((s N) x) ?R ?TR (open_interval (g x - e/2) (g x + e/2))"
    proof -
      have hboth: "s N x - g x < e/2 \<and> - (s N x - g x) < e/2"
        using hNx by (rule iffD1[OF abs_less_iff])
      have hupper: "s N x - g x < e/2"
        by (rule conjunct1[OF hboth])
      have hneg: "- (s N x - g x) < e/2"
        by (rule conjunct2[OF hboth])
      have hlower: "-e/2 < (s N x - g x)"
        using hneg by linarith
      have hdiff: "-e/2 < (s N x - g x) \<and> (s N x - g x) < e/2"
        using hlower hupper by blast
      have h1: "g x - e/2 < (s N x)"
        using hdiff by linarith
      have h2: "(s N x) < g x + e/2"
        using hdiff by linarith
      have hmem: "(s N) x \<in> open_interval (g x - e/2) (g x + e/2)"
        unfolding open_interval_def using h1 h2 by simp
      show ?thesis
        unfolding neighborhood_of_def
        using hW_open hmem by blast
    qed

    obtain U where hUx: "neighborhood_of x X TX U" and hUmap:
      "(s N) ` U \<subseteq> open_interval (g x - e/2) (g x + e/2)"
      using hsN_nbhd hxX hsNxW by blast

    have hUsubX: "U \<subseteq> X"
    proof -
      have hUT: "U \<in> TX"
        using hUx unfolding neighborhood_of_def by blast
      have hallsub: "\<forall>W\<in>TX. W \<subseteq> X"
        using hTopX unfolding is_topology_on_def by blast
      show ?thesis
        by (rule ballE[OF hallsub hUT], simp)
    qed

    have hgmapped: "g ` U \<subseteq> V"
    proof (rule subsetI)
      fix y assume hy: "y \<in> g ` U"
      then obtain u where huU: "u \<in> U" and hyEq: "y = g u"
        by blast
      have huX: "u \<in> X"
        using hUsubX huU by blast
	      have hNu: "abs (s N u - g u) < e/2"
	        using hN huX by simp
	      have hsNu: "s N u \<in> open_interval (g x - e/2) (g x + e/2)"
	        using hUmap huU by blast
	      have hsNu1: "g x - e/2 < s N u" and hsNu2: "s N u < g x + e/2"
	      proof -
	        have hs_conj: "g x - e/2 < s N u \<and> s N u < g x + e/2"
	          using hsNu unfolding open_interval_def by simp
	        show "g x - e/2 < s N u"
	          using hs_conj by (rule conjunct1)
	        show "s N u < g x + e/2"
	          using hs_conj by (rule conjunct2)
	      qed

      have hboth: "s N u - g u < e/2 \<and> - (s N u - g u) < e/2"
        using hNu by (rule iffD1[OF abs_less_iff])
      have hupper: "s N u - g u < e/2"
        by (rule conjunct1[OF hboth])
      have hneg: "- (s N u - g u) < e/2"
        by (rule conjunct2[OF hboth])
      have hlower: "-e/2 < (s N u - g u)"
        using hneg by linarith
      have hdiff: "-e/2 < (s N u - g u) \<and> (s N u - g u) < e/2"
        using hlower hupper by blast

      have hgu1: "g x - e < g u"
        using hsNu1 hdiff by linarith
      have hgu2: "g u < g x + e"
        using hsNu2 hdiff by linarith
      have hguI: "g u \<in> open_interval (g x - e) (g x + e)"
        unfolding open_interval_def using hgu1 hgu2 by simp

      have "g u \<in> b"
        using hI_sub hguI by blast
      hence "g u \<in> V"
        using hbV by blast
      thus "y \<in> V"
        unfolding hyEq by simp
    qed

    show "\<exists>U. neighborhood_of x X TX U \<and> g ` U \<subseteq> V"
      by (rule exI[where x=U], intro conjI, rule hUx, rule hgmapped)
  qed

  have hiff:
    "top1_continuous_map_on X TX ?R ?TR g \<longleftrightarrow>
     ((\<forall>x\<in>X. g x \<in> ?R) \<and>
      (\<forall>x\<in>X. \<forall>V. neighborhood_of (g x) ?R ?TR V \<longrightarrow>
          (\<exists>U. neighborhood_of x X TX U \<and> g ` U \<subseteq> V)))"
    by (rule Theorem_18_1(3)[OF hTopX hTopR])

  show ?thesis
    apply (rule iffD2[OF hiff])
    apply (intro conjI)
     apply simp
    apply (rule hnbhd_g)
    done
qed
*)

(** Step 2 of the Tietze construction (top1.tex): existence of a uniformly Cauchy sequence of
    continuous approximants on \<open>X\<close> whose restriction to \<open>A\<close> converges to \<open>f\<close>.  This is the
    core iterative content; the remaining analytic part is turning the uniform Cauchy property into a
    continuous limit map. **)
lemma top1_tietze_step2_approximants:
  fixes f :: "'a \<Rightarrow> real"
  defines "I \<equiv> top1_closed_interval (-1) 1"
  defines "TI \<equiv> top1_closed_interval_topology (-1) 1"
  assumes hX: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hf: "top1_continuous_map_on A (subspace_topology X TX A) I TI f"
  shows "\<exists>s::nat \<Rightarrow> 'a \<Rightarrow> real.
      s 0 = (\<lambda>_. 0)
      \<and> (\<forall>n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (s n))
      \<and> (\<forall>n. \<forall>x\<in>X. abs (s (Suc n) x - s n x) \<le> (1/3) * (2/3) ^ n)
      \<and> (\<forall>n. \<forall>a\<in>A. abs (f a - s n a) \<le> (2/3) ^ n)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "order_topology_on_UNIV"
  let ?TA = "subspace_topology X TX A"

  define r where "r = (\<lambda>n::nat. (2/3::real) ^ n)"

  have hT1: "top1_T1_on X TX"
    using hX unfolding top1_normal_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)
  have hAX: "A \<subseteq> X"
    by (rule closedin_sub[OF hA])
  have hTopR: "is_topology_on ?R ?TR"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopA: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTopX hAX])

  have hTopI: "is_topology_on I TI"
    unfolding TI_def top1_closed_interval_topology_def I_def
    by (rule subspace_topology_is_topology_on[OF hTopR], simp)
  have hTI_eq: "TI = subspace_topology ?R ?TR I"
    unfolding TI_def top1_closed_interval_topology_def I_def by simp
  have hI_sub: "I \<subseteq> ?R"
    by simp

  have f_cont_UNIV: "top1_continuous_map_on A ?TA ?R ?TR f"
    using Theorem_18_2(6)[OF hTopA hTopI hTopR]
          hf hI_sub hTI_eq
    by blast

  define Inv where
    "Inv n sn \<longleftrightarrow>
        top1_continuous_map_on X TX ?R ?TR sn
        \<and> (\<forall>a\<in>A. abs (f a - sn a) \<le> r n)"
    for n :: nat and sn :: "'a \<Rightarrow> real"

  define Step where
    "Step n sn g \<longleftrightarrow>
        top1_continuous_map_on X TX ?R ?TR g
        \<and> (\<forall>x\<in>X. abs (g x) \<le> (1/3) * r n)
        \<and> (\<forall>a\<in>A. abs (g a - (f a - sn a)) \<le> r (Suc n))"
    for n :: nat and sn :: "'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"

  define choose_g where
    "choose_g n sn = (SOME g. Step n sn g)"
    for n :: nat and sn :: "'a \<Rightarrow> real"
  
  define s where
    "s = rec_nat (\<lambda>_. 0) (\<lambda>n sn. (\<lambda>x. sn x + choose_g n sn x))"

  have s0: "s 0 = (\<lambda>_. 0)"
    unfolding s_def by simp
  have sSuc: "\<forall>n. s (Suc n) = (\<lambda>x. s n x + choose_g n (s n) x)"
    unfolding s_def by simp

  have Step_ex: "Inv n sn \<Longrightarrow> \<exists>g. Step n sn g" for n :: nat and sn :: "'a \<Rightarrow> real"
  proof -
    fix n :: nat
    fix sn :: "'a \<Rightarrow> real"
    assume hInv: "Inv n sn"

    have sn_cont: "top1_continuous_map_on X TX ?R ?TR sn"
      using hInv unfolding Inv_def by blast
    have herr: "\<forall>a\<in>A. abs (f a - sn a) \<le> r n"
      using hInv unfolding Inv_def by blast

    have sn_cont_A: "top1_continuous_map_on A ?TA ?R ?TR sn"
      using Theorem_18_2(4)[OF hTopX hTopR hTopR] sn_cont hAX by blast

    have h_cont_UNIV: "top1_continuous_map_on A ?TA ?R ?TR (\<lambda>a. f a - sn a)"
      by (rule top1_continuous_diff_real[OF hTopA f_cont_UNIV sn_cont_A])

    have h_img: "(\<lambda>a. f a - sn a) ` A \<subseteq> top1_closed_interval (- r n) (r n)"
    proof (rule subsetI)
      fix y assume hy: "y \<in> (\<lambda>a. f a - sn a) ` A"
      obtain a where haA: "a \<in> A" and hyEq: "y = f a - sn a"
        using hy by blast
      have habs: "abs (f a - sn a) \<le> r n"
        using herr haA by blast
      show "y \<in> top1_closed_interval (- r n) (r n)"
        unfolding hyEq top1_closed_interval_def
        using habs by (simp add: abs_le_iff)
    qed

    have h_cont_J: "top1_continuous_map_on A ?TA (top1_closed_interval (- r n) (r n))
        (top1_closed_interval_topology (- r n) (r n)) (\<lambda>a. f a - sn a)"
    proof -
      have hJsub: "top1_closed_interval (- r n) (r n) \<subseteq> ?R"
        by simp
      have hTJ_eq: "top1_closed_interval_topology (- r n) (r n) =
          subspace_topology ?R ?TR (top1_closed_interval (- r n) (r n))"
        unfolding top1_closed_interval_topology_def by simp
      have h_cont_J': "top1_continuous_map_on A ?TA (top1_closed_interval (- r n) (r n))
          (subspace_topology ?R ?TR (top1_closed_interval (- r n) (r n))) (\<lambda>a. f a - sn a)"
        using Theorem_18_2(5)[OF hTopA hTopR hTopR] h_cont_UNIV hJsub h_img by blast
      show ?thesis
        unfolding hTJ_eq using h_cont_J' .
    qed

    have hrpos: "0 < r n"
      unfolding r_def by simp

    obtain g where
      g_contI: "top1_continuous_map_on X TX (top1_closed_interval (- r n / 3) (r n / 3))
          (top1_closed_interval_topology (- r n / 3) (r n / 3)) g" and
      g_bound: "\<forall>x\<in>X. abs (g x) \<le> r n / 3" and
      g_appr: "\<forall>a\<in>A. abs (g a - (f a - sn a)) \<le> 2 * r n / 3"
      using top1_tietze_step1[where A=A and f="(\<lambda>a. f a - sn a)" and r="r n", OF hX hA h_cont_J hrpos]
      by blast

    have hTopI_n: "is_topology_on (top1_closed_interval (- r n / 3) (r n / 3))
        (top1_closed_interval_topology (- r n / 3) (r n / 3))"
      unfolding top1_closed_interval_topology_def
      by (rule subspace_topology_is_topology_on[OF hTopR], simp)

    have g_cont: "top1_continuous_map_on X TX ?R ?TR g"
    proof -
      have hI_sub: "top1_closed_interval (- r n / 3) (r n / 3) \<subseteq> ?R"
        by simp
      have hTI_eq: "top1_closed_interval_topology (- r n / 3) (r n / 3) =
          subspace_topology ?R ?TR (top1_closed_interval (- r n / 3) (r n / 3))"
        unfolding top1_closed_interval_topology_def by simp
      show ?thesis
        using Theorem_18_2(6)[OF hTopX hTopI_n hTopR] g_contI hI_sub hTI_eq
        by blast
    qed

    have g_bound': "\<forall>x\<in>X. abs (g x) \<le> (1/3) * r n"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have habs: "abs (g x) \<le> r n / 3"
        using g_bound hxX by blast
      show "abs (g x) \<le> (1/3) * r n"
        using habs by (simp add: field_simps)
    qed

    have g_appr': "\<forall>a\<in>A. abs (g a - (f a - sn a)) \<le> r (Suc n)"
    proof (intro ballI)
      fix a assume haA: "a \<in> A"
      have habs: "abs (g a - (f a - sn a)) \<le> 2 * r n / 3"
        using g_appr haA by blast
      have hEq: "2 * r n / 3 = r (Suc n)"
        unfolding r_def by (simp add: field_simps)
      show "abs (g a - (f a - sn a)) \<le> r (Suc n)"
        using habs unfolding hEq .
    qed

    show "\<exists>g. Step n sn g"
    proof (rule exI[where x=g])
      show "Step n sn g"
        unfolding Step_def
        apply (intro conjI)
          apply (rule g_cont)
         apply (rule g_bound')
        apply (rule g_appr')
        done
    qed
  qed

  have Inv_all: "\<forall>n. Inv n (s n)"
  proof
    fix n
    show "Inv n (s n)"
    proof (induction n)
      case 0
      have hconst: "top1_continuous_map_on X TX ?R ?TR (\<lambda>x. (0::real))"
        using Theorem_18_2(1)[OF hTopX hTopR hTopR, rule_format, of 0] by simp
      have herr0: "\<forall>a\<in>A. abs (f a - (s 0) a) \<le> r 0"
      proof (intro ballI)
        fix a assume haA: "a \<in> A"
        have hfaI: "f a \<in> I"
          using hf haA unfolding top1_continuous_map_on_def by blast
        have hbounds: "-1 \<le> f a \<and> f a \<le> 1"
          using hfaI unfolding I_def top1_closed_interval_def by blast
        have habs: "abs (f a) \<le> 1"
        proof (rule abs_leI)
          show "f a \<le> 1"
            using hbounds by simp
          show "- f a \<le> 1"
            using hbounds by linarith
        qed
        show "abs (f a - s 0 a) \<le> r 0"
          unfolding s0 r_def using habs by simp
      qed
	      show ?case
	        unfolding Inv_def s0
		      proof (intro conjI)
		        show "top1_continuous_map_on X TX ?R ?TR (\<lambda>_. (0::real))"
		          by (rule hconst)
		        show "\<forall>a\<in>A. abs (f a - (\<lambda>_. (0::real)) a) \<le> r 0"
		          using herr0 unfolding s0 by simp
		      qed
	    next
	      case (Suc n)
	      have hInvn: "Inv n (s n)"
	        using Suc by simp
	      have hex: "\<exists>g. Step n (s n) g"
	        using Step_ex[OF hInvn] .
	      have hStep: "Step n (s n) (choose_g n (s n))"
	        unfolding choose_g_def
	        by (rule someI_ex[OF hex])
      have sn_cont: "top1_continuous_map_on X TX ?R ?TR (s n)"
        using hInvn unfolding Inv_def by blast
      have gn_cont: "top1_continuous_map_on X TX ?R ?TR (choose_g n (s n))"
        using hStep unfolding Step_def by blast
      have sn1_cont: "top1_continuous_map_on X TX ?R ?TR (\<lambda>x. s n x + choose_g n (s n) x)"
        by (rule top1_continuous_add_real[OF hTopX sn_cont gn_cont])
      have herr1: "\<forall>a\<in>A. abs (f a - (\<lambda>x. s n x + choose_g n (s n) x) a) \<le> r (Suc n)"
      proof (intro ballI)
        fix a assume haA: "a \<in> A"
        have habs: "abs (choose_g n (s n) a - (f a - s n a)) \<le> r (Suc n)"
          using hStep haA unfolding Step_def by blast
        have hEq:
          "f a - (s n a + choose_g n (s n) a) = (f a - s n a) - choose_g n (s n) a"
          by simp
        have "abs (f a - (s n a + choose_g n (s n) a)) = abs (choose_g n (s n) a - (f a - s n a))"
          unfolding hEq by (simp add: abs_minus_commute)
        thus "abs (f a - (\<lambda>x. s n x + choose_g n (s n) x) a) \<le> r (Suc n)"
          using habs by simp
      qed
      show ?case
        unfolding Inv_def
	      proof (intro conjI)
	        show "top1_continuous_map_on X TX ?R ?TR (s (Suc n))"
	          unfolding sSuc[rule_format, of n] by (rule sn1_cont)
	        show "\<forall>a\<in>A. abs (f a - s (Suc n) a) \<le> r (Suc n)"
	          unfolding sSuc[rule_format, of n] by (rule herr1)
	      qed
    qed
  qed

  have inc_all: "\<forall>n. \<forall>x\<in>X. abs (s (Suc n) x - s n x) \<le> (1/3) * r n"
	  proof (intro allI ballI)
	    fix n x assume hxX: "x \<in> X"
	    have hInvn: "Inv n (s n)"
	      using Inv_all by blast
	    have hex: "\<exists>g. Step n (s n) g"
	      using Step_ex[OF hInvn] .
	    have hStep: "Step n (s n) (choose_g n (s n))"
	      unfolding choose_g_def
	      by (rule someI_ex[OF hex])
	    have habs: "abs (choose_g n (s n) x) \<le> (1/3) * r n"
      using hStep hxX unfolding Step_def by blast
    have hEq: "s (Suc n) x - s n x = choose_g n (s n) x"
      using sSuc[rule_format, of n] by simp
    show "abs (s (Suc n) x - s n x) \<le> (1/3) * r n"
      unfolding hEq using habs by simp
  qed
  
	  show ?thesis
	  proof (rule exI[where x=s])
	    show "s 0 = (\<lambda>_. 0)
	        \<and> (\<forall>n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (s n))
	        \<and> (\<forall>n. \<forall>x\<in>X. abs (s (Suc n) x - s n x) \<le> (1/3) * (2/3) ^ n)
	        \<and> (\<forall>n. \<forall>a\<in>A. abs (f a - s n a) \<le> (2/3) ^ n)"
	    proof (intro conjI)
	      show "s 0 = (\<lambda>_. 0)"
	        by (rule s0)
	      show "\<forall>n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (s n)"
	        using Inv_all unfolding Inv_def by blast
	      show "\<forall>n. \<forall>x\<in>X. abs (s (Suc n) x - s n x) \<le> (1/3) * (2/3) ^ n"
	        using inc_all unfolding r_def by (simp add: field_simps)
	      show "\<forall>n. \<forall>a\<in>A. abs (f a - s n a) \<le> (2/3) ^ n"
	        using Inv_all unfolding Inv_def r_def by simp
	    qed
	  qed
	qed

(** from *\S35 Theorem 35.1 (Tietze extension theorem) [top1.tex:~4771] **)
theorem Theorem_35_1:
  fixes f :: "'a \<Rightarrow> real"
  defines "I \<equiv> top1_closed_interval (-1) 1"
  defines "TI \<equiv> top1_closed_interval_topology (-1) 1"
  assumes hX: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hf: "top1_continuous_map_on A (subspace_topology X TX A) I TI f"
  shows "\<exists>F. top1_continuous_map_on X TX I TI F \<and> (\<forall>x\<in>A. F x = f x)"
proof -
  have hTopX: "is_topology_on X TX"
    using hX unfolding top1_normal_on_def top1_T1_on_def by blast
  have hAX: "A \<subseteq> X"
    by (rule closedin_sub[OF hA])

  have hf': "top1_continuous_map_on A (subspace_topology X TX A)
      (top1_closed_interval (-1) 1) (top1_closed_interval_topology (-1) 1) f"
    using hf unfolding I_def TI_def .

  obtain s :: "nat \<Rightarrow> 'a \<Rightarrow> real" where
    hs0: "s 0 = (\<lambda>_. 0)"
    and hscont: "\<forall>n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (s n)"
    and hsinc: "\<forall>n. \<forall>x\<in>X. abs (s (Suc n) x - s n x) \<le> (1/3) * (2/3) ^ n"
    and hserr: "\<forall>n. \<forall>a\<in>A. abs (f a - s n a) \<le> (2/3) ^ n"
    using top1_tietze_step2_approximants[OF hX hA hf'] by blast

  define F where "F = (\<lambda>x. lim (\<lambda>n. s n x))"

  have cauchy_sx: "\<forall>x\<in>X. Cauchy (\<lambda>n. s n x)"
  proof (intro ballI)
    fix x assume hx: "x \<in> X"
    show "Cauchy (\<lambda>n. s n x)"
    proof (rule metric_CauchyI)
      fix e :: real
      assume he: "0 < e"
      have h23: "(2/3::real) < 1"
        by simp
      obtain N where hN: "(2/3::real) ^ N < e"
        using real_arch_pow_inv[OF he h23] by blast
      show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (s m x) (s n x) < e"
      proof (rule exI[where x=N], intro allI impI)
        fix m assume hm: "N \<le> m"
        fix n assume hn: "N \<le> n"
        have hdist: "dist (s m x) (s n x) = abs (s m x - s n x)"
          by (simp add: dist_real_def)
        show "dist (s m x) (s n x) < e"
        proof (cases "n \<le> m")
          case True
          define k where "k = m - n"
          have hmk: "m = n + k"
            unfolding k_def using True by simp
          have htail: "abs (s (n + k) x - s n x) \<le> (2/3::real) ^ n"
            by (rule top1_tietze_tail_bound[OF hsinc hx])
          have hpow: "(2/3::real) ^ n \<le> (2/3::real) ^ N"
	          proof -
	            have "N \<le> n"
	              using hn by simp
	            thus ?thesis
	            proof -
	              have h0: "0 \<le> (2/3::real)"
	                by simp
	              have h1: "(2/3::real) \<le> 1"
	                by simp
	              show "(2/3::real) ^ n \<le> (2/3::real) ^ N"
	                by (rule power_decreasing[OF \<open>N \<le> n\<close> h0 h1])
	            qed
	          qed
          have habs: "abs (s m x - s n x) \<le> (2/3::real) ^ N"
            unfolding hmk using order_trans[OF htail hpow] by simp
          show ?thesis
            unfolding hdist using le_less_trans[OF habs hN] by simp
        next
          case False
          define k where "k = n - m"
          have hnk: "n = m + k"
            unfolding k_def using False by simp
          have htail: "abs (s (m + k) x - s m x) \<le> (2/3::real) ^ m"
            by (rule top1_tietze_tail_bound[OF hsinc hx])
          have hpow: "(2/3::real) ^ m \<le> (2/3::real) ^ N"
	          proof -
	            have "N \<le> m"
	              using hm by simp
	            thus ?thesis
	            proof -
	              have h0: "0 \<le> (2/3::real)"
	                by simp
	              have h1: "(2/3::real) \<le> 1"
	                by simp
	              show "(2/3::real) ^ m \<le> (2/3::real) ^ N"
	                by (rule power_decreasing[OF \<open>N \<le> m\<close> h0 h1])
	            qed
	          qed
          have habs: "abs (s n x - s m x) \<le> (2/3::real) ^ N"
            unfolding hnk using order_trans[OF htail hpow] by simp
          have habs': "abs (s m x - s n x) \<le> (2/3::real) ^ N"
            using habs by (simp add: abs_minus_commute)
          show ?thesis
            unfolding hdist using le_less_trans[OF habs' hN] by simp
        qed
      qed
    qed
  qed

  have conv_sx: "\<forall>x\<in>X. convergent (\<lambda>n. s n x)"
  proof (intro ballI)
    fix x assume hx: "x \<in> X"
    have "Cauchy (\<lambda>n. s n x)"
      using cauchy_sx hx by blast
    thus "convergent (\<lambda>n. s n x)"
      by (rule real_Cauchy_convergent)
  qed

  have lim_sx: "\<forall>x\<in>X. (\<lambda>n. s n x) \<longlonglongrightarrow> F x"
  proof (intro ballI)
    fix x assume hx: "x \<in> X"
    have hconv: "convergent (\<lambda>n. s n x)"
      using conv_sx hx by blast
    show "(\<lambda>n. s n x) \<longlonglongrightarrow> F x"
      unfolding F_def using hconv by (simp add: convergent_LIMSEQ_iff)
  qed

  have F_minus_sn_bound: "\<forall>n. \<forall>x\<in>X. abs (F x - s n x) \<le> (2/3) ^ n"
  proof (intro allI ballI)
    fix n x assume hx: "x \<in> X"
    have hLIM: "(\<lambda>m. s m x) \<longlonglongrightarrow> F x"
      using lim_sx hx by blast
    have hshift: "(\<lambda>k. s (k + n) x) \<longlonglongrightarrow> F x"
      by (rule LIMSEQ_ignore_initial_segment[OF hLIM])
    have hdiff: "(\<lambda>k. s (k + n) x - s n x) \<longlonglongrightarrow> F x - s n x"
      using hshift by (intro tendsto_diff tendsto_const)
    have hnorm_lim: "(\<lambda>k. norm (s (k + n) x - s n x)) \<longlonglongrightarrow> norm (F x - s n x)"
      by (rule tendsto_norm[OF hdiff])
    have habs_lim: "(\<lambda>k. abs (s (k + n) x - s n x)) \<longlonglongrightarrow> abs (F x - s n x)"
      using hnorm_lim by simp
    have hbound: "\<exists>N. \<forall>k\<ge>N. abs (s (k + n) x - s n x) \<le> (2/3) ^ n"
    proof (rule exI[where x=0], intro allI impI)
      fix k :: nat
      assume hk: "0 \<le> k"
      have "abs (s (n + k) x - s n x) \<le> (2/3) ^ n"
        by (rule top1_tietze_tail_bound[OF hsinc hx])
      thus "abs (s (k + n) x - s n x) \<le> (2/3) ^ n"
        by (simp add: add.commute)
    qed
    show "abs (F x - s n x) \<le> (2/3) ^ n"
      using LIMSEQ_le_const2[OF habs_lim hbound] by simp
  qed

  have hunif: "top1_uniformly_convergent_on_real X s F"
  proof (unfold top1_uniformly_convergent_on_real_def, intro allI impI)
    fix e :: real
    assume he: "0 < e"
    have h23: "(2/3::real) < 1"
      by simp
    obtain N where hN: "(2/3::real) ^ N < e"
      using real_arch_pow_inv[OF he h23] by blast
    show "\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>X. abs (s n x - F x) < e"
    proof (rule exI[where x=N], intro allI impI ballI)
      fix n assume hn: "N \<le> n"
      fix x assume hx: "x \<in> X"
      have hbound: "abs (F x - s n x) \<le> (2/3::real) ^ n"
        using F_minus_sn_bound hx by blast
      have hpow: "(2/3::real) ^ n \<le> (2/3::real) ^ N"
      proof -
        have h0: "0 \<le> (2/3::real)"
          by simp
        have h1: "(2/3::real) \<le> 1"
          by simp
        show "(2/3::real) ^ n \<le> (2/3::real) ^ N"
          by (rule power_decreasing[OF hn h0 h1])
      qed
      have habs1: "abs (s n x - F x) \<le> (2/3::real) ^ n"
        using hbound by (simp add: abs_minus_commute)
      have habs: "abs (s n x - F x) \<le> (2/3::real) ^ N"
        by (rule order_trans[OF habs1 hpow])
      show "abs (s n x - F x) < e"
        using le_less_trans[OF habs hN] by simp
    qed
  qed

  have F_cont_UNIV: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV F"
    by (rule top1_uniform_limit_continuous_real[OF hTopX hscont hunif])

  have F_in_I: "\<forall>x\<in>X. F x \<in> I"
  proof (intro ballI)
    fix x assume hx: "x \<in> X"
    have hLIM: "(\<lambda>n. s n x) \<longlonglongrightarrow> F x"
      using lim_sx hx by blast

    have abs_sn: "\<forall>n. abs (s n x) \<le> 1"
    proof (intro allI)
      fix n
      have htail: "abs (s (0 + n) x - s 0 x) \<le> (2/3::real) ^ 0"
        by (rule top1_tietze_tail_bound[OF hsinc hx])
      have hs0x: "s 0 x = 0"
        using hs0 by simp
      show "abs (s n x) \<le> 1"
        using htail unfolding hs0x by simp
    qed

    have sn_le1: "\<exists>N. \<forall>n\<ge>N. s n x \<le> 1"
    proof (rule exI[where x=0], intro allI impI)
      fix n :: nat
      assume hn: "0 \<le> n"
      have "abs (s n x) \<le> 1"
        using abs_sn by blast
      thus "s n x \<le> 1"
        by (simp add: abs_le_iff)
    qed
    have sn_ge_m1: "\<exists>N. \<forall>n\<ge>N. (-1::real) \<le> s n x"
    proof (rule exI[where x=0], intro allI impI)
      fix n :: nat
      assume hn: "0 \<le> n"
      have "abs (s n x) \<le> 1"
        using abs_sn by blast
      thus "(-1::real) \<le> s n x"
        by (simp add: abs_le_iff)
    qed

    have hFx_le1: "F x \<le> 1"
      using LIMSEQ_le_const2[OF hLIM sn_le1] by simp
    have hFx_ge: "(-1::real) \<le> F x"
      using LIMSEQ_le_const[OF hLIM sn_ge_m1] by simp

    show "F x \<in> I"
      unfolding I_def top1_closed_interval_def
      using hFx_ge hFx_le1 by blast
  qed

  have F_range: "F ` X \<subseteq> I"
  proof (rule image_subsetI)
    fix x assume hx: "x \<in> X"
    show "F x \<in> I"
      using F_in_I hx by blast
  qed

  have F_cont_I: "top1_continuous_map_on X TX I TI F"
  proof -
    have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
      by (rule order_topology_on_UNIV_is_topology_on)
    have hTI_eq: "TI = subspace_topology UNIV order_topology_on_UNIV I"
      unfolding TI_def top1_closed_interval_topology_def I_def by simp
    have hsub: "I \<subseteq> (UNIV::real set)"
      by simp
    have hcont_sub:
      "top1_continuous_map_on X TX I (subspace_topology UNIV order_topology_on_UNIV I) F"
    proof -
      have hrestrict_all:
        "\<forall>W f.
          top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f
          \<and> W \<subseteq> (UNIV::real set)
          \<and> f ` X \<subseteq> W
          \<longrightarrow> top1_continuous_map_on X TX W (subspace_topology UNIV order_topology_on_UNIV W) f"
        using Theorem_18_2(5)[OF hTopX hTopR hTopR] .
      have hrestrict_I:
        "\<forall>f.
          top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f
          \<and> I \<subseteq> (UNIV::real set)
          \<and> f ` X \<subseteq> I
          \<longrightarrow> top1_continuous_map_on X TX I (subspace_topology UNIV order_topology_on_UNIV I) f"
        using hrestrict_all by (rule spec[where x=I])
      have hrestrict_IF:
        "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV F
         \<and> I \<subseteq> (UNIV::real set)
         \<and> F ` X \<subseteq> I
         \<longrightarrow> top1_continuous_map_on X TX I (subspace_topology UNIV order_topology_on_UNIV I) F"
        using hrestrict_I by (rule spec[where x=F])
      have hpre: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV F
          \<and> I \<subseteq> (UNIV::real set) \<and> F ` X \<subseteq> I"
        by (intro conjI, rule F_cont_UNIV, rule hsub, rule F_range)
      show ?thesis
        by (rule mp[OF hrestrict_IF hpre])
    qed
    show ?thesis
      unfolding hTI_eq using hcont_sub .
  qed

  have F_eq_f_on_A: "\<forall>a\<in>A. F a = f a"
  proof (intro ballI)
    fix a assume ha: "a \<in> A"
    have haX: "a \<in> X"
      using hAX ha by blast
    have hLIM_F: "(\<lambda>n. s n a) \<longlonglongrightarrow> F a"
      using lim_sx haX by blast
    have hLIM_f: "(\<lambda>n. s n a) \<longlonglongrightarrow> f a"
    proof (subst lim_sequentially, intro allI impI)
      fix e :: real
      assume he: "0 < e"
      have h23: "(2/3::real) < 1"
        by simp
      obtain N where hN: "(2/3::real) ^ N < e"
        using real_arch_pow_inv[OF he h23] by blast
      show "\<exists>N. \<forall>n\<ge>N. dist (s n a) (f a) < e"
      proof (rule exI[where x=N], intro allI impI)
        fix n assume hn: "N \<le> n"
	        have herr: "abs (f a - s n a) \<le> (2/3::real) ^ n"
	          using hserr ha by blast
	        have hpow: "(2/3::real) ^ n \<le> (2/3::real) ^ N"
	        proof -
	          have h0: "0 \<le> (2/3::real)"
	            by simp
	          have h1: "(2/3::real) \<le> 1"
	            by simp
	          show "(2/3::real) ^ n \<le> (2/3::real) ^ N"
	            by (rule power_decreasing[OF hn h0 h1])
	        qed
	        have hdist: "dist (s n a) (f a) = abs (f a - s n a)"
	          by (simp add: dist_real_def abs_minus_commute)
	        have habs: "dist (s n a) (f a) \<le> (2/3::real) ^ N"
	          unfolding hdist using order_trans[OF herr hpow] by simp
        show "dist (s n a) (f a) < e"
          using le_less_trans[OF habs hN] by simp
      qed
    qed
    show "F a = f a"
      using LIMSEQ_unique[OF hLIM_F hLIM_f] by simp
  qed

  show ?thesis
    apply (rule exI[where x=F])
    apply (intro conjI)
     apply (rule F_cont_I)
    apply (rule F_eq_f_on_A)
    done
qed

section \<open>*\<S>36 Imbeddings of Manifolds\<close>

text \<open>
  The starred sections (*\<S>35–*\<S>36) of \<open>top1.tex\<close> develop stronger results based on the Urysohn lemma.
  We begin by formalizing the notion of a (finite) partition of unity dominated by a finite open cover,
  and we state the existence theorem (Theorem 36.1).

  The full proof will require additional analytic infrastructure about pointwise products (and possibly
  normalization) of real-valued continuous maps in the \<open>top1_continuous_map_on\<close> framework.
\<close>

definition top1_support_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> 'a set" where
  "top1_support_on X TX f = closure_on X TX {x \<in> X. f x \<noteq> 0}"

lemma top1_support_on_subset_imp_zero_on_complement:
  assumes hsupp: "top1_support_on X TX f \<subseteq> U"
  assumes hx: "x \<in> X - U"
  shows "f x = 0"
proof -
  have hsub: "{x \<in> X. f x \<noteq> 0} \<subseteq> top1_support_on X TX f"
    unfolding top1_support_on_def by (rule subset_closure_on)
  have hsubU: "{x \<in> X. f x \<noteq> 0} \<subseteq> U"
    using subset_trans[OF hsub hsupp] .
  have hxX: "x \<in> X" and hxU: "x \<notin> U"
    using hx by blast+
  have "x \<notin> {x \<in> X. f x \<noteq> 0}"
  proof
    assume hxNZ: "x \<in> {x \<in> X. f x \<noteq> 0}"
    have "x \<in> U"
      using hsubU hxNZ by blast
    thus False
      using hxU by contradiction
  qed
  thus ?thesis
    using hxX by simp
qed

(** Outside the support, the function value must be zero. **)
lemma top1_support_on_complement_imp_zero:
  assumes hxX: "x \<in> X"
  assumes hx: "x \<notin> top1_support_on X TX f"
  shows "f x = 0"
proof (rule ccontr)
  assume hne: "f x \<noteq> 0"
  have hxNZ: "x \<in> {y \<in> X. f y \<noteq> 0}"
    using hxX hne by simp
  have hsub: "{y \<in> X. f y \<noteq> 0} \<subseteq> top1_support_on X TX f"
    unfolding top1_support_on_def by (rule subset_closure_on)
  have "x \<in> top1_support_on X TX f"
    by (rule subsetD[OF hsub hxNZ])
  thus False
    using hx by contradiction
qed

(** If \<open>\<phi>\<close> is supported in an open set \<open>U\<close>, then the "zero extension" of \<open>\<phi> * h\<close> is continuous. **)
lemma top1_continuous_mul_supported_extend_zero:
  fixes \<phi> h :: "'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hUopen: "U \<in> TX"
  assumes hUsub: "U \<subseteq> X"
  assumes hphi: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV \<phi>"
  assumes hsupp: "top1_support_on X TX \<phi> \<subseteq> U"
  assumes hh: "top1_continuous_map_on U (subspace_topology X TX U) (UNIV::real set) order_topology_on_UNIV h"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. if x \<in> U then \<phi> x * h x else 0)"
proof -
  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hTopU: "is_topology_on U (subspace_topology X TX U)"
    by (rule subspace_topology_is_topology_on[OF hTopX hUsub])

  have hphiU: "top1_continuous_map_on U (subspace_topology X TX U) (UNIV::real set) order_topology_on_UNIV \<phi>"
  proof -
    have hRestrDom:
      "\<forall>A' f. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f \<and> A' \<subseteq> X
             \<longrightarrow> top1_continuous_map_on A' (subspace_topology X TX A') (UNIV::real set) order_topology_on_UNIV f"
      by (rule Theorem_18_2(4)[OF hTopX hTopR hTopR])
    show ?thesis
      using hRestrDom hphi hUsub by blast
  qed

  have hmulU:
    "top1_continuous_map_on U (subspace_topology X TX U) (UNIV::real set) order_topology_on_UNIV (\<lambda>x. \<phi> x * h x)"
    by (rule top1_continuous_mul_real[OF hTopU hphiU hh])

  have hSuppClosed: "closedin_on X TX (top1_support_on X TX \<phi>)"
  proof -
    have hAX: "{x \<in> X. \<phi> x \<noteq> (0::real)} \<subseteq> X"
      by blast
    have "closedin_on X TX (closure_on X TX {x \<in> X. \<phi> x \<noteq> (0::real)})"
      by (rule closure_on_closed[OF hTopX hAX])
    thus ?thesis
      unfolding top1_support_on_def by simp
  qed

  define A where "A = X - top1_support_on X TX \<phi>"
  have hAopen: "A \<in> TX"
    unfolding A_def by (rule closedin_diff_open[OF hSuppClosed])

  have hUA: "U \<union> A = X"
  proof (rule equalityI)
    show "U \<union> A \<subseteq> X"
      unfolding A_def using hUsub by blast
  next
    show "X \<subseteq> U \<union> A"
    proof (rule subsetI)
      fix x assume hxX: "x \<in> X"
      show "x \<in> U \<union> A"
      proof (cases "x \<in> top1_support_on X TX \<phi>")
        case True
        have "x \<in> U"
          using hsupp True by blast
        thus ?thesis
          by simp
      next
        case False
        thus ?thesis
          unfolding A_def using hxX by simp
      qed
    qed
  qed

  define f where "f x = (if x \<in> U then \<phi> x * h x else 0)" for x

  have hcont_U: "top1_continuous_map_on U (subspace_topology X TX U) (UNIV::real set) order_topology_on_UNIV f"
  proof -
    have heq: "\<forall>x\<in>U. f x = \<phi> x * h x"
      unfolding f_def by simp
    show ?thesis
      using top1_continuous_map_on_cong[OF heq] hmulU by blast
  qed

  have hzeroA: "\<forall>x\<in>A. f x = 0"
  proof (intro ballI)
    fix x assume hxA: "x \<in> A"
    have hxX: "x \<in> X"
      using hxA unfolding A_def by blast
    have hxns: "x \<notin> top1_support_on X TX \<phi>"
      using hxA unfolding A_def by blast
    have hphi0: "\<phi> x = 0"
      by (rule top1_support_on_complement_imp_zero[OF hxX hxns])
  show "f x = 0"
  proof (cases "x \<in> U")
    case True
    show ?thesis
      unfolding f_def using True hphi0 by simp
  next
    case False
    show ?thesis
      unfolding f_def using False by simp
  qed
  qed

  have hconstA: "top1_continuous_map_on A (subspace_topology X TX A) (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (0::real))"
  proof -
    have hTopA: "is_topology_on A (subspace_topology X TX A)"
      by (rule subspace_topology_is_topology_on[OF hTopX], simp add: A_def)
    have hConst:
      "\<forall>y0\<in>(UNIV::real set). top1_continuous_map_on A (subspace_topology X TX A) (UNIV::real set) order_topology_on_UNIV (\<lambda>x. y0)"
      by (rule Theorem_18_2(1)[OF hTopA hTopR hTopR])
    show ?thesis
      using hConst by simp
  qed

  have hcont_A: "top1_continuous_map_on A (subspace_topology X TX A) (UNIV::real set) order_topology_on_UNIV f"
    using top1_continuous_map_on_cong[OF hzeroA] hconstA by blast

  have hUc: "(\<Union>{U, A}) = X"
    using hUA by simp
  have hcond: "\<forall>W\<in>{U, A}. W \<in> TX \<and>
        top1_continuous_map_on W (subspace_topology X TX W) (UNIV::real set) order_topology_on_UNIV f"
  proof (intro ballI)
    fix W assume hW: "W \<in> {U, A}"
    show "W \<in> TX \<and>
        top1_continuous_map_on W (subspace_topology X TX W) (UNIV::real set) order_topology_on_UNIV f"
    proof (cases "W = U")
      case True
      show ?thesis
        unfolding True
        by (intro conjI, rule hUopen, rule hcont_U)
    next
      case False
      have "W = A"
        using hW False by simp
      show ?thesis
        unfolding \<open>W = A\<close>
        by (intro conjI, rule hAopen, rule hcont_A)
    qed
  qed

  have hlocal_form:
    "(\<Union>{U, A} = X) \<and>
     (\<forall>W\<in>{U, A}. W \<in> TX \<and>
        top1_continuous_map_on W (subspace_topology X TX W) (UNIV::real set) order_topology_on_UNIV f)
     \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
  proof -
    have hRules:
      "\<forall>Uc g.
        (\<Union>Uc = X) \<and>
        (\<forall>W\<in>Uc. W \<in> TX \<and> top1_continuous_map_on W (subspace_topology X TX W)
            (UNIV::real set) order_topology_on_UNIV g)
        \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV g"
      by (rule Theorem_18_2(7)[OF hTopX hTopR hTopR])

    have hspec:
      "(\<Union>{U, A} = X) \<and>
       (\<forall>W\<in>{U, A}. W \<in> TX \<and> top1_continuous_map_on W (subspace_topology X TX W)
          (UNIV::real set) order_topology_on_UNIV f)
       \<longrightarrow> top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
      using hRules by blast

    show ?thesis
      by (rule hspec)
  qed

  have "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
    by (rule mp[OF hlocal_form], intro conjI, rule hUc, rule hcond)

  thus ?thesis
    unfolding f_def by simp
qed

definition top1_partition_of_unity_dominated_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "top1_partition_of_unity_dominated_on X TX n U \<phi> \<longleftrightarrow>
     (\<forall>i<n.
        top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<phi> i)
        \<and> top1_support_on X TX (\<phi> i) \<subseteq> U i)
     \<and> (\<forall>x\<in>X. (\<Sum>i<n. \<phi> i x) = 1)"

lemma top1_support_on_mul_nonzero_factor:
  fixes f c :: "'a \<Rightarrow> real"
  assumes hfac: "\<forall>x\<in>X. c x \<noteq> 0"
  shows "top1_support_on X TX (\<lambda>x. f x * c x) = top1_support_on X TX f"
proof -
  have hEq: "{x \<in> X. f x * c x \<noteq> 0} = {x \<in> X. f x \<noteq> 0}"
  proof (rule set_eqI)
    fix x
    show "x \<in> {x \<in> X. f x * c x \<noteq> 0} \<longleftrightarrow> x \<in> {x \<in> X. f x \<noteq> 0}"
    proof (cases "x \<in> X")
      case False
      then show ?thesis
        by simp
    next
      case True
      have hc: "c x \<noteq> 0"
        using hfac True by blast
      have "(f x * c x \<noteq> 0) \<longleftrightarrow> (f x \<noteq> 0)"
      proof
        assume h: "f x * c x \<noteq> 0"
        show "f x \<noteq> 0"
        proof
          assume "f x = 0"
          then have "f x * c x = 0"
            by simp
          thus False
            using h by contradiction
        qed
      next
        assume h: "f x \<noteq> 0"
        show "f x * c x \<noteq> 0"
          using h hc by simp
      qed
      then show ?thesis
        using True by simp
    qed
  qed

  show ?thesis
    unfolding top1_support_on_def
    apply (subst hEq)
    apply simp
    done
qed

(** Step 1 of Theorem 36.1: "shrink" a finite open cover so that each shrunken set has closure
    contained in the corresponding original one. **)
lemma normal_shrink_finite_open_cover:
  fixes U :: "nat \<Rightarrow> 'a set"
  assumes hN: "top1_normal_on X TX"
  assumes hUopen: "\<forall>i<n. U i \<in> TX"
  assumes hUsub: "\<forall>i<n. U i \<subseteq> X"
  assumes hcov: "X \<subseteq> (\<Union>i<n. U i)"
  shows "\<exists>V. (\<forall>i<n. V i \<in> TX \<and> V i \<subseteq> X \<and> closure_on X TX (V i) \<subseteq> U i)
        \<and> X \<subseteq> (\<Union>i<n. V i)"
proof -
  have hT1: "top1_T1_on X TX"
    using hN unfolding top1_normal_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  have union_TX: "\<forall>K. K \<subseteq> TX \<longrightarrow> (\<Union>K) \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]]])

  define P where
    "P k V \<longleftrightarrow>
       (\<forall>i<k. V i \<in> TX \<and> V i \<subseteq> X \<and> closure_on X TX (V i) \<subseteq> U i)
       \<and> X \<subseteq> (\<Union>i<k. V i) \<union> (\<Union>i\<in>{k..<n}. U i)"
    for k :: nat and V :: "nat \<Rightarrow> 'a set"

  have P_ex: "\<forall>k\<le>n. \<exists>V. P k V"
  proof (intro allI impI)
    fix k assume hk: "k \<le> n"
    show "\<exists>V. P k V"
      using hk
    proof (induction k)
      case 0
      let ?V = "\<lambda>i. {}"
      show "\<exists>V. P 0 V"
      proof -
        have hcov': "X \<subseteq> (\<Union>(U ` {0..<n}))"
          using hcov by (simp add: atLeast0LessThan)
        show ?thesis
          unfolding P_def
          apply (rule exI[where x = ?V])
          apply (intro conjI)
           apply simp
          apply simp
          apply (rule hcov')
          done
      qed
    next
      case (Suc k)
      have hklt: "k < n"
        using Suc.prems by simp
      have hk_le_n: "k \<le> n"
        using Suc.prems by simp
      obtain V where hP: "P k V"
        using Suc.IH[OF hk_le_n] by blast

      define Prev where "Prev = (\<Union>i<k. V i)"
      define Rest where "Rest = (\<Union>i\<in>{Suc k..<n}. U i)"
      define A where "A = X - Prev - Rest"

      have in_succ: "i \<in> {k..<n} \<Longrightarrow> i \<noteq> k \<Longrightarrow> i \<in> {Suc k..<n}" for i :: nat
      proof -
        fix i :: nat
	        assume hi: "i \<in> {k..<n}"
	        assume hne: "i \<noteq> k"
	        have hk_le: "k \<le> i"
	          using hi by simp
	        have hi_lt: "i < n"
	          using hi by simp
        have hne': "k \<noteq> i"
          using hne by simp
        have hk_lt: "k < i"
          by (rule le_neq_trans[OF hk_le hne'])
        have hsuc_le: "Suc k \<le> i"
          by (rule Suc_leI[OF hk_lt])
        show "i \<in> {Suc k..<n}"
          using hsuc_le hi_lt by simp
      qed

      have hPrev_subX: "Prev \<subseteq> X"
      proof (rule subsetI)
        fix x assume hx: "x \<in> Prev"
        then obtain i where hi: "i < k" and hxVi: "x \<in> V i"
          unfolding Prev_def by blast
        have hVi_subX: "V i \<subseteq> X"
          using hP unfolding P_def using hi by blast
        show "x \<in> X"
          using hVi_subX hxVi by blast
      qed

      have hRest_subX: "Rest \<subseteq> X"
      proof (rule subsetI)
        fix x assume hx: "x \<in> Rest"
        then obtain i where hi: "i \<in> {Suc k..<n}" and hxUi: "x \<in> U i"
          unfolding Rest_def by blast
        have hUi_subX: "U i \<subseteq> X"
          using hUsub[rule_format, of i] hi by simp
        show "x \<in> X"
          using hUi_subX hxUi by blast
      qed

      have hPrev_open: "Prev \<in> TX"
      proof -
        have hPrev_img: "V ` {..<k} \<subseteq> TX"
        proof (rule subsetI)
          fix W assume hW: "W \<in> V ` {..<k}"
          then obtain i where hi: "i < k" and hWeq: "W = V i"
            by blast
          show "W \<in> TX"
            using hP unfolding P_def using hi hWeq by blast
        qed
        have "(\<Union>(V ` {..<k})) \<in> TX"
          using union_TX hPrev_img by blast
        moreover have "(\<Union>(V ` {..<k})) = Prev"
          unfolding Prev_def by blast
        ultimately show ?thesis
          by simp
      qed

      have hRest_open: "Rest \<in> TX"
      proof -
        have hRest_img: "U ` {Suc k..<n} \<subseteq> TX"
        proof (rule subsetI)
          fix W assume hW: "W \<in> U ` {Suc k..<n}"
          then obtain i where hi: "i \<in> {Suc k..<n}" and hWeq: "W = U i"
            by blast
          show "W \<in> TX"
            using hUopen[rule_format, of i] hi hWeq by simp
        qed
        have "(\<Union>(U ` {Suc k..<n})) \<in> TX"
          using union_TX hRest_img by blast
        moreover have "(\<Union>(U ` {Suc k..<n})) = Rest"
          unfolding Rest_def by blast
        ultimately show ?thesis
          by simp
      qed

      have hPrevRest_open: "Prev \<union> Rest \<in> TX"
        by (rule topology_union2[OF hTopX hPrev_open hRest_open])

      have hA_subX: "A \<subseteq> X"
        unfolding A_def by blast

      have hXdiffA: "X - A = Prev \<union> Rest"
      proof -
        have hSub: "Prev \<union> Rest \<subseteq> X"
          using hPrev_subX hRest_subX by blast
        have "X - A = X \<inter> (Prev \<union> Rest)"
          unfolding A_def by blast
        also have "... = Prev \<union> Rest"
          using hSub by blast
        finally show ?thesis .
      qed

      have hA_closed: "closedin_on X TX A"
        by (rule closedin_intro[OF hA_subX], simp add: hXdiffA hPrevRest_open)

      have hU_k_open: "U k \<in> TX"
        using hUopen hklt by blast
      have hU_k_subX: "U k \<subseteq> X"
        using hUsub hklt by blast

      have hA_sub_Uk: "A \<subseteq> U k"
      proof (rule subsetI)
        fix x assume hxA: "x \<in> A"
        have hxX: "x \<in> X"
          using hxA unfolding A_def by blast
        have hxnotPrev: "x \<notin> Prev"
          using hxA unfolding A_def by blast
        have hxnotRest: "x \<notin> Rest"
          using hxA unfolding A_def by blast
        have hxCov: "x \<in> Prev \<union> (\<Union>i\<in>{k..<n}. U i)"
          using hP hxX unfolding P_def Prev_def by blast
        have hxCov2: "x \<in> Prev \<or> x \<in> (\<Union>i\<in>{k..<n}. U i)"
          using hxCov by blast
        have hxInUset: "x \<in> (\<Union>i\<in>{k..<n}. U i)"
          using hxCov2 hxnotPrev by blast
        have hSplit: "(\<Union>i\<in>{k..<n}. U i) = U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
        proof (rule set_eqI)
          fix y
          show "y \<in> (\<Union>i\<in>{k..<n}. U i) \<longleftrightarrow> y \<in> U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
          proof
            assume hy: "y \<in> (\<Union>i\<in>{k..<n}. U i)"
            then obtain i where hi: "i \<in> {k..<n}" and hyUi: "y \<in> U i"
              by blast
            show "y \<in> U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
            proof (cases "i = k")
              case True
              show ?thesis
                using hyUi unfolding True by blast
	            next
	              case False
	              have hi2: "i \<in> {Suc k..<n}"
	                by (rule in_succ[OF hi False])
	              have "y \<in> (\<Union>j\<in>{Suc k..<n}. U j)"
	                using hi2 hyUi by blast
	              thus ?thesis
	                by blast
            qed
          next
            assume hy: "y \<in> U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
            show "y \<in> (\<Union>i\<in>{k..<n}. U i)"
            proof -
              have hy': "y \<in> U k \<or> y \<in> (\<Union>i\<in>{Suc k..<n}. U i)"
                using hy by simp
              show ?thesis
              proof (rule disjE[OF hy'])
              assume hyk: "y \<in> U k"
              have hk': "k \<in> {k..<n}"
                using hklt by simp
              show ?thesis
                using hk' hyk by blast
            next
              assume hyL: "y \<in> (\<Union>i\<in>{Suc k..<n}. U i)"
	              then obtain i where hi: "i \<in> {Suc k..<n}" and hyUi: "y \<in> U i"
	                by blast
	              have hi': "i \<in> {k..<n}"
	                using hi by simp
	              show ?thesis
	                using hi' hyUi by blast
              qed
            qed
          qed
        qed
        have hxInSplit: "x \<in> U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
          using hxInUset unfolding hSplit by simp
        have hxRest2: "x \<in> (\<Union>i\<in>{Suc k..<n}. U i) \<Longrightarrow> x \<in> Rest"
          unfolding Rest_def by blast
        show "x \<in> U k"
        proof -
          have hxInSplit': "x \<in> U k \<or> x \<in> (\<Union>i\<in>{Suc k..<n}. U i)"
            using hxInSplit by simp
          show ?thesis
          proof (rule disjE[OF hxInSplit'])
          assume "x \<in> U k"
          thus ?thesis .
        next
          assume hxInLater: "x \<in> (\<Union>i\<in>{Suc k..<n}. U i)"
          have "x \<in> Rest"
            using hxRest2 hxInLater .
          thus ?thesis
            using hxnotRest by contradiction
          qed
        qed
      qed

      obtain Vk where hVk: "Vk \<in> TX \<and> Vk \<subseteq> X \<and> A \<subseteq> Vk \<and> closure_on X TX Vk \<subseteq> U k"
        using normal_refine_closed_into_open[OF hN hA_closed hU_k_open hU_k_subX hA_sub_Uk] by blast

      define V' where "V' = (\<lambda>i. if i = k then Vk else V i)"

      have hP': "P (Suc k) V'"
        unfolding P_def
      proof (intro conjI)
        show "\<forall>i<Suc k. V' i \<in> TX \<and> V' i \<subseteq> X \<and> closure_on X TX (V' i) \<subseteq> U i"
        proof (intro allI impI)
          fix i assume hi: "i < Suc k"
          show "V' i \<in> TX \<and> V' i \<subseteq> X \<and> closure_on X TX (V' i) \<subseteq> U i"
          proof (cases "i = k")
            case True
            show ?thesis
              unfolding V'_def True using hVk by simp
          next
            case False
	            have hi': "i < k"
	              using hi False by simp
	            show ?thesis
	              unfolding V'_def using hP hi' False unfolding P_def by simp
	          qed
	        qed

        have hCover_k: "X \<subseteq> Prev \<union> (\<Union>i\<in>{k..<n}. U i)"
          using hP unfolding P_def Prev_def by blast

        have hCover_k': "X \<subseteq> (Prev \<union> Vk) \<union> Rest"
        proof (rule subsetI)
          fix x assume hxX: "x \<in> X"
          have hx: "x \<in> Prev \<union> (\<Union>i\<in>{k..<n}. U i)"
            using hCover_k hxX by blast
          have hSplit: "(\<Union>i\<in>{k..<n}. U i) = U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
          proof (rule set_eqI)
            fix y
            show "y \<in> (\<Union>i\<in>{k..<n}. U i) \<longleftrightarrow> y \<in> U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
            proof
              assume hy: "y \<in> (\<Union>i\<in>{k..<n}. U i)"
              then obtain i where hi: "i \<in> {k..<n}" and hyUi: "y \<in> U i"
                by blast
              show "y \<in> U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
              proof (cases "i = k")
                case True
                show ?thesis
                  using hyUi unfolding True by blast
	              next
	                case False
	                have hi2: "i \<in> {Suc k..<n}"
	                  by (rule in_succ[OF hi False])
	                have "y \<in> (\<Union>j\<in>{Suc k..<n}. U j)"
	                  using hi2 hyUi by blast
	                thus ?thesis
	                  by blast
              qed
            next
              assume hy: "y \<in> U k \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
              show "y \<in> (\<Union>i\<in>{k..<n}. U i)"
              proof -
                have hy': "y \<in> U k \<or> y \<in> (\<Union>i\<in>{Suc k..<n}. U i)"
                  using hy by simp
                show ?thesis
                proof (rule disjE[OF hy'])
                assume hyk: "y \<in> U k"
                have hk': "k \<in> {k..<n}"
                  using hklt by simp
                show ?thesis
                  using hk' hyk by blast
              next
                assume hyL: "y \<in> (\<Union>i\<in>{Suc k..<n}. U i)"
	                then obtain i where hi: "i \<in> {Suc k..<n}" and hyUi: "y \<in> U i"
	                  by blast
	                have hi': "i \<in> {k..<n}"
	                  using hi by simp
	                show ?thesis
	                  using hi' hyUi by blast
                qed
              qed
            qed
          qed
          have hx2: "x \<in> Prev \<or> x \<in> U k \<or> x \<in> (\<Union>i\<in>{Suc k..<n}. U i)"
            using hx unfolding hSplit by blast
          show "x \<in> (Prev \<union> Vk) \<union> Rest"
          proof (cases "x \<in> Prev \<union> Rest")
            case True
            thus ?thesis
              by blast
          next
            case False
            have hxnotPrev: "x \<notin> Prev" and hxnotRest: "x \<notin> Rest"
              using False by blast+
            have hxA: "x \<in> A"
              unfolding A_def using hxX hxnotPrev hxnotRest by blast
            have "x \<in> Vk"
              using hVk hxA by blast
            thus ?thesis
              by blast
          qed
        qed

        have hEq1: "(\<Union>i<Suc k. V' i) = Prev \<union> Vk"
        proof (rule set_eqI)
          fix x
          show "x \<in> (\<Union>i<Suc k. V' i) \<longleftrightarrow> x \<in> Prev \<union> Vk"
          proof
            assume hx: "x \<in> (\<Union>i<Suc k. V' i)"
            then obtain i where hi: "i < Suc k" and hxVi: "x \<in> V' i"
              by blast
            show "x \<in> Prev \<union> Vk"
            proof (cases "i = k")
              case True
              show ?thesis
                using hxVi unfolding V'_def True by simp
            next
              case False
              have hi': "i < k"
                using hi False by simp
              have "x \<in> V i"
                using hxVi unfolding V'_def using False by simp
              hence "x \<in> Prev"
                unfolding Prev_def using hi' by blast
              thus ?thesis
                by blast
            qed
          next
            assume hx: "x \<in> Prev \<union> Vk"
            show "x \<in> (\<Union>i<Suc k. V' i)"
            proof -
              have hx': "x \<in> Prev \<or> x \<in> Vk"
                using hx by simp
              show ?thesis
              proof (rule disjE[OF hx'])
                assume hxPrev: "x \<in> Prev"
                then obtain i where hi: "i < k" and hxVi: "x \<in> V i"
                  unfolding Prev_def by blast
                have hi2: "i < Suc k"
                  using hi by simp
                have hik: "i \<noteq> k"
                  using hi by simp
                have hxV'i: "x \<in> V' i"
                  unfolding V'_def using hik hxVi by simp
                show ?thesis
                  apply simp
                  apply (rule bexI[where x=i])
                   apply (rule hxV'i)
                  apply (simp add: hi2)
                  done
              next
                assume hxVk: "x \<in> Vk"
                have hk2: "k < Suc k"
                  by simp
                have hxV'k: "x \<in> V' k"
                  unfolding V'_def by simp (rule hxVk)
                show ?thesis
                  apply simp
                  apply (rule bexI[where x=k])
                   apply (rule hxV'k)
                  apply (simp add: hk2)
                  done
              qed
            qed
          qed
        qed

        have hEq2: "(\<Union>i\<in>{Suc k..<n}. U i) = Rest"
          unfolding Rest_def by blast

        show "X \<subseteq> (\<Union>i<Suc k. V' i) \<union> (\<Union>i\<in>{Suc k..<n}. U i)"
          unfolding hEq1 hEq2 using hCover_k' by blast
      qed

      show "\<exists>V0. P (Suc k) V0"
        by (rule exI[where x=V'], rule hP')
    qed
  qed

  obtain V where hPn: "P n V"
    using P_ex by blast

  have hVprops: "\<forall>i<n. V i \<in> TX \<and> V i \<subseteq> X \<and> closure_on X TX (V i) \<subseteq> U i"
    using hPn unfolding P_def by blast
  have hVcov: "X \<subseteq> (\<Union>i<n. V i)"
    using hPn unfolding P_def by simp

  show ?thesis
    apply (rule exI[where x=V])
    apply (intro conjI)
     apply (rule hVprops)
    apply (rule hVcov)
    done
qed

(** Bump function from the Urysohn lemma: if a closed set \<open>A\<close> sits inside an open set \<open>V\<close>,
    then we can find a continuous map \<open>\<psi> : X \<rightarrow> [0,1]\<close> that is 1 on \<open>A\<close>, vanishes on \<open>X - V\<close>,
    and whose support is contained in the closure of \<open>V\<close>. **)
lemma normal_urysohn_bump_support:
  assumes hN: "top1_normal_on X TX"
  assumes hV: "V \<in> TX"
  assumes hVX: "V \<subseteq> X"
  assumes hA: "closedin_on X TX A"
  assumes hAV: "A \<subseteq> V"
  shows "\<exists>\<psi>. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) \<psi>
            \<and> (\<forall>x\<in>A. \<psi> x = 1)
            \<and> (\<forall>x\<in>X - V. \<psi> x = 0)
            \<and> top1_support_on X TX \<psi> \<subseteq> closure_on X TX V"
proof -
  have hT1: "top1_T1_on X TX"
    using hN unfolding top1_normal_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  have hXV_closed: "closedin_on X TX (X - V)"
    apply (rule closedin_intro)
     apply (rule Diff_subset)
    apply (simp only: Diff_Diff_Int)
    apply (simp only: Int_absorb1[OF hVX])
    apply (rule hV)
    done

  have hdisj: "(X - V) \<inter> A = {}"
  proof (rule equalityI)
    show "(X - V) \<inter> A \<subseteq> {}"
    proof (rule subsetI)
      fix x assume hx: "x \<in> (X - V) \<inter> A"
      have hxA: "x \<in> A" and hxnotV: "x \<notin> V"
        using hx by blast+
      have hxV: "x \<in> V"
        using hAV hxA by blast
      show "x \<in> {}"
        using hxV hxnotV by blast
    qed
    show "{} \<subseteq> (X - V) \<inter> A"
      by (rule empty_subsetI)
  qed

  obtain \<psi> where hpsi:
    "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) \<psi>
     \<and> (\<forall>x\<in>X - V. \<psi> x = 0)
     \<and> (\<forall>x\<in>A. \<psi> x = 1)"
    using Theorem_33_1[OF hN hXV_closed hA hdisj, of 0 1] by simp blast

  have hnz_sub: "{x \<in> X. \<psi> x \<noteq> 0} \<subseteq> V"
	  proof (rule subsetI)
	    fix x assume hx: "x \<in> {x \<in> X. \<psi> x \<noteq> 0}"
	    have hxX: "x \<in> X" and hx0: "\<psi> x \<noteq> 0"
	    proof -
	      have hx_conj: "x \<in> X \<and> \<psi> x \<noteq> 0"
	        using hx by simp
	      show "x \<in> X"
	        using hx_conj by (rule conjunct1)
	      show "\<psi> x \<noteq> 0"
	        using hx_conj by (rule conjunct2)
	    qed
    show "x \<in> V"
    proof (rule ccontr)
      assume hxnotV: "x \<notin> V"
      have hxXmV: "x \<in> X - V"
        using hxX hxnotV by blast
      have "\<psi> x = 0"
        using hpsi hxXmV by blast
      thus False
        using hx0 by contradiction
    qed
  qed

  have hsupp: "top1_support_on X TX \<psi> \<subseteq> closure_on X TX V"
    unfolding top1_support_on_def
    by (rule closure_on_mono[OF hnz_sub])

  show ?thesis
    apply (rule exI[where x=\<psi>])
    apply (intro conjI)
       apply (rule conjunct1[OF hpsi])
      apply (rule conjunct2[OF conjunct2[OF hpsi]])
     apply (rule conjunct1[OF conjunct2[OF hpsi]])
    apply (rule hsupp)
    done
qed

(** Step 2 of the construction in Theorem 36.1: from a finite open cover of a normal space,
    produce a family of Urysohn bump functions whose supports are contained in the original cover,
    and such that at every point at least one bump function is 1. **)
lemma normal_finite_cover_bump_family:
  fixes U :: "nat \<Rightarrow> 'a set"
  assumes hN: "top1_normal_on X TX"
  assumes hUopen: "\<forall>i<n. U i \<in> TX"
  assumes hUsub: "\<forall>i<n. U i \<subseteq> X"
  assumes hcov: "X \<subseteq> (\<Union>i<n. U i)"
  shows "\<exists>\<psi>. (\<forall>i<n. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<psi> i)
                \<and> top1_support_on X TX (\<psi> i) \<subseteq> U i)
            \<and> (\<forall>x\<in>X. \<exists>i<n. \<psi> i x = 1)"
proof -
  have hT1: "top1_T1_on X TX"
    using hN unfolding top1_normal_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  obtain V where hV:
    "(\<forall>i<n. V i \<in> TX \<and> V i \<subseteq> X \<and> closure_on X TX (V i) \<subseteq> U i)
     \<and> X \<subseteq> (\<Union>i<n. V i)"
    using normal_shrink_finite_open_cover[OF hN hUopen hUsub hcov] by blast
  have hVopen: "\<forall>i<n. V i \<in> TX"
    using hV by blast
  have hVsub: "\<forall>i<n. V i \<subseteq> X"
    using hV by blast
  have hVclsubU: "\<forall>i<n. closure_on X TX (V i) \<subseteq> U i"
    using hV by blast
  have hVcov: "X \<subseteq> (\<Union>i<n. V i)"
    using hV by blast

  obtain W where hW:
    "(\<forall>i<n. W i \<in> TX \<and> W i \<subseteq> X \<and> closure_on X TX (W i) \<subseteq> V i)
     \<and> X \<subseteq> (\<Union>i<n. W i)"
    using normal_shrink_finite_open_cover[OF hN hVopen hVsub hVcov] by blast
  have hWopen: "\<forall>i<n. W i \<in> TX"
    using hW by blast
  have hWsub: "\<forall>i<n. W i \<subseteq> X"
    using hW by blast
  have hWclsubV: "\<forall>i<n. closure_on X TX (W i) \<subseteq> V i"
    using hW by blast
  have hWcov: "X \<subseteq> (\<Union>i<n. W i)"
    using hW by blast

  define P where
    "P i psi \<longleftrightarrow>
        top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) psi
        \<and> top1_support_on X TX psi \<subseteq> U i
        \<and> (\<forall>x\<in>closure_on X TX (W i). psi x = 1)"
    for i :: nat and psi :: "'a \<Rightarrow> real"

  have hex: "\<forall>i<n. \<exists>\<psi>. P i \<psi>"
  proof (intro allI impI)
    fix i assume hi: "i < n"
    have hWiX: "W i \<subseteq> X"
      using hWsub hi by blast
    have hAi_closed: "closedin_on X TX (closure_on X TX (W i))"
      by (rule closure_on_closed[OF hTopX hWiX])
    have hAi_sub_Vi: "closure_on X TX (W i) \<subseteq> V i"
      using hWclsubV hi by blast

    obtain psi0 where hpsi:
      "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) psi0
       \<and> (\<forall>x\<in>closure_on X TX (W i). psi0 x = 1)
       \<and> (\<forall>x\<in>X - V i. psi0 x = 0)
       \<and> top1_support_on X TX psi0 \<subseteq> closure_on X TX (V i)"
      using normal_urysohn_bump_support[OF hN, of "V i" "closure_on X TX (W i)"]
      using hVopen[rule_format, OF hi] hVsub[rule_format, OF hi] hAi_closed hAi_sub_Vi
      by blast

    have hsuppUi: "top1_support_on X TX psi0 \<subseteq> U i"
    proof -
      have hsuppcl: "top1_support_on X TX psi0 \<subseteq> closure_on X TX (V i)"
        using hpsi by blast
      have hclsub: "closure_on X TX (V i) \<subseteq> U i"
        using hVclsubU hi by blast
      show ?thesis
        using subset_trans[OF hsuppcl hclsub] .
    qed

    show "\<exists>\<psi>. P i \<psi>"
      unfolding P_def
      apply (rule exI[where x=psi0])
      apply (intro conjI)
        apply (rule conjunct1[OF hpsi])
       apply (rule hsuppUi)
      apply (rule conjunct1[OF conjunct2[OF hpsi]])
      done
  qed

  let ?psi = "(\<lambda>i. if i < n then (SOME \<psi>. P i \<psi>) else (\<lambda>x. (0::real)))"

  have hpsi_all: "\<forall>i<n. P i (?psi i)"
  proof (intro allI impI)
    fix i assume hi: "i < n"
    have exPi: "\<exists>\<psi>. P i \<psi>"
      using hex hi by blast
    have "P i (SOME \<psi>. P i \<psi>)"
      by (rule someI_ex[OF exPi])
    thus "P i (?psi i)"
      using hi by simp
  qed

  have hP1: "\<forall>i<n. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (?psi i)
                \<and> top1_support_on X TX (?psi i) \<subseteq> U i"
  proof (intro allI impI)
    fix i assume hi: "i < n"
    have hPi: "P i (?psi i)"
      using hpsi_all hi by blast
    have hPi': "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (?psi i)
        \<and> top1_support_on X TX (?psi i) \<subseteq> U i
        \<and> (\<forall>x\<in>closure_on X TX (W i). ?psi i x = 1)"
      using hPi unfolding P_def by simp
    show "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (?psi i)
        \<and> top1_support_on X TX (?psi i) \<subseteq> U i"
      using hPi' by simp
  qed

  have hP2: "\<forall>x\<in>X. \<exists>i<n. ?psi i x = 1"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hx: "x \<in> (\<Union>i<n. W i)"
      using hWcov hxX by blast
    then obtain i where hi: "i < n" and hxWi: "x \<in> W i"
      by blast
    have hxcl: "x \<in> closure_on X TX (W i)"
      by (rule subsetD[OF subset_closure_on hxWi])
    have hPi: "P i (?psi i)"
      using hpsi_all hi by blast
    have hones: "\<forall>y\<in>closure_on X TX (W i). ?psi i y = 1"
      using hPi unfolding P_def by simp
    have "?psi i x = 1"
      using hones hxcl by blast
    show "\<exists>i<n. ?psi i x = 1"
    proof (rule exI[where x=i], intro conjI)
      show "i < n"
        by (rule hi)
      show "?psi i x = 1"
        by (rule \<open>?psi i x = 1\<close>)
    qed
  qed

  show ?thesis
    apply (rule exI[where x = ?psi])
    apply (intro conjI)
     apply (rule hP1)
    apply (rule hP2)
    done
qed

(** from *\S36 Theorem 36.1 (Existence of finite partitions of unity) [top1.tex:~5009] **)
theorem Theorem_36_1:
  assumes hN: "top1_normal_on X TX"
  assumes hUopen: "\<forall>i<n. U i \<in> TX"
  assumes hUsub: "\<forall>i<n. U i \<subseteq> X"
  assumes hcov: "X \<subseteq> (\<Union>i<n. U i)"
  shows "\<exists>\<phi>. top1_partition_of_unity_dominated_on X TX n U \<phi>"
proof -
  obtain \<psi> where hpsi_dom:
      "\<forall>i<n. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<psi> i)
            \<and> top1_support_on X TX (\<psi> i) \<subseteq> U i"
    and hpsi_one: "\<forall>x\<in>X. \<exists>i<n. \<psi> i x = 1"
    using normal_finite_cover_bump_family[OF hN hUopen hUsub hcov] by blast

  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"

  have hT1: "top1_T1_on X TX"
    using hN unfolding top1_normal_on_def by (rule conjunct1)
  have hTopX: "is_topology_on X TX"
    using hT1 unfolding top1_T1_on_def by (rule conjunct1)

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF hTopR], simp add: top1_closed_interval_def)

  have hTI_eq: "?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I"
    unfolding top1_closed_interval_topology_def by simp

  have hpsi_contI: "\<forall>i<n. top1_continuous_map_on X TX ?I ?TI (\<psi> i)"
    using hpsi_dom by blast
  have hpsi_suppU: "\<forall>i<n. top1_support_on X TX (\<psi> i) \<subseteq> U i"
    using hpsi_dom by blast

	  have hpsi_mapI: "\<forall>i<n. \<forall>x\<in>X. \<psi> i x \<in> ?I"
	  proof (intro allI impI)
	    fix i assume hi: "i < n"
	    have hcont: "top1_continuous_map_on X TX ?I ?TI (\<psi> i)"
	      using hpsi_contI hi by blast
	    have hmap: "\<forall>x\<in>X. \<psi> i x \<in> ?I"
	      using hcont unfolding top1_continuous_map_on_def by (rule conjunct1)
	    show "\<forall>x\<in>X. \<psi> i x \<in> ?I"
	      by (rule hmap)
	  qed

  have hpsi_ge0: "\<forall>i<n. \<forall>x\<in>X. 0 \<le> \<psi> i x"
  proof (intro allI impI ballI)
    fix i assume hi: "i < n"
    fix x assume hx: "x \<in> X"
    have "\<psi> i x \<in> ?I"
      using hpsi_mapI hi hx by blast
    thus "0 \<le> \<psi> i x"
      unfolding top1_closed_interval_def by simp
  qed
  have hpsi_le1: "\<forall>i<n. \<forall>x\<in>X. \<psi> i x \<le> 1"
  proof (intro allI impI ballI)
    fix i assume hi: "i < n"
    fix x assume hx: "x \<in> X"
    have "\<psi> i x \<in> ?I"
      using hpsi_mapI hi hx by blast
    thus "\<psi> i x \<le> 1"
      unfolding top1_closed_interval_def by simp
  qed

  define \<Psi> where "\<Psi> x = (\<Sum>i<n. \<psi> i x)" for x

  have hpsi_contR: "\<forall>i<n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<psi> i)"
  proof (intro allI impI)
    fix i assume hi: "i < n"
    have hcontI: "top1_continuous_map_on X TX ?I ?TI (\<psi> i)"
      using hpsi_contI hi by blast
    have hexpand:
      "\<forall>W f.
        top1_continuous_map_on X TX ?I ?TI f
        \<and> ?I \<subseteq> W
        \<and> ?TI = subspace_topology W order_topology_on_UNIV ?I
        \<longrightarrow> top1_continuous_map_on X TX W order_topology_on_UNIV f"
      using Theorem_18_2(6)[OF hTopX hTopI hTopR] .
    have hW: "?I \<subseteq> (UNIV::real set)"
      by simp
    have hpre:
      "top1_continuous_map_on X TX ?I ?TI (\<psi> i)
       \<and> ?I \<subseteq> (UNIV::real set)
       \<and> ?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I"
      by (intro conjI, rule hcontI, rule hW, rule hTI_eq)
    have "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<psi> i)"
      using mp[OF spec[OF spec[OF hexpand, where x="(UNIV::real set)"], where x="(\<psi> i)"] hpre] .
    thus "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<psi> i)" .
  qed

  have hPsi_contR: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV \<Psi>"
    unfolding \<Psi>_def
    by (rule top1_continuous_sum_lessThan_real[OF hTopX hpsi_contR])

	  have hPsi_ge1: "\<forall>x\<in>X. 1 \<le> \<Psi> x"
	  proof (intro ballI)
	    fix x assume hxX: "x \<in> X"
	    obtain i where hi: "i < n" and hpsi1: "\<psi> i x = 1"
	      using hpsi_one hxX by blast

    have hnonneg: "\<And>j. j \<in> {..<n} \<Longrightarrow> 0 \<le> (\<lambda>j. \<psi> j x) j"
    proof -
      fix j assume hj: "j \<in> {..<n}"
      have hj': "j < n"
        using hj by simp
      show "0 \<le> (\<psi> j x)"
        using hpsi_ge0 hj' hxX by blast
    qed

	    have hterm_le: "\<psi> i x \<le> (\<Sum>j<n. \<psi> j x)"
	    proof -
	      have fin: "finite ({..<n}::nat set)"
	        by simp
	      have hi_in: "i \<in> {..<n}"
	        using hi by simp
	      have hsplit: "(\<Sum>j\<in>{..<n}. \<psi> j x) = \<psi> i x + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
	        by (rule sum.remove[OF fin hi_in])
	      have hrest_nonneg: "0 \<le> (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
	      proof -
	        have "\<And>j. j \<in> {..<n} - {i} \<Longrightarrow> 0 \<le> \<psi> j x"
	        proof -
	          fix j assume hj: "j \<in> {..<n} - {i}"
	          have hj': "j < n"
	            using hj by simp
	          have himp: "j < n \<longrightarrow> (\<forall>y\<in>X. 0 \<le> \<psi> j y)"
	            using hpsi_ge0 by (rule spec)
	          have hAll: "\<forall>y\<in>X. 0 \<le> \<psi> j y"
	            by (rule mp[OF himp hj'])
	          show "0 \<le> \<psi> j x"
	            by (rule bspec[OF hAll hxX])
	        qed
		        show ?thesis
		        proof (rule sum_nonneg)
		          fix xa assume hxa: "xa \<in> {..<n} - {i}"
		          show "0 \<le> \<psi> xa x"
		            by (rule \<open>\<And>j. j \<in> {..<n} - {i} \<Longrightarrow> 0 \<le> \<psi> j x\<close>[OF hxa])
		        qed
		      qed

		      have hle: "\<psi> i x \<le> \<psi> i x + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
		      proof -
		        have "(\<psi> i x) + 0 \<le> (\<psi> i x) + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
		          using hrest_nonneg by (rule add_left_mono)
		        thus ?thesis
		          by simp
		      qed
	      have hEq: "\<psi> i x + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x) = (\<Sum>j\<in>{..<n}. \<psi> j x)"
	        by (rule sym[OF hsplit])
	      have "\<psi> i x \<le> (\<Sum>j\<in>{..<n}. \<psi> j x)"
	        using hle by (simp add: hEq)
	      thus ?thesis
	        by simp
	    qed
	    show "1 \<le> \<Psi> x"
	      unfolding \<Psi>_def using hterm_le hpsi1 by simp
	  qed

  have hPsi_pos: "\<forall>x\<in>X. 0 < \<Psi> x"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have "1 \<le> \<Psi> x"
      using hPsi_ge1 hxX by blast
    thus "0 < \<Psi> x"
      by linarith
  qed

  have hPsi_img_pos: "\<Psi> ` X \<subseteq> open_ray_gt (0::real)"
  proof (rule subsetI)
    fix y assume hy: "y \<in> \<Psi> ` X"
    then obtain x where hxX: "x \<in> X" and hyEq: "y = \<Psi> x"
      by blast
    have "0 < \<Psi> x"
      using hPsi_pos hxX by blast
    thus "y \<in> open_ray_gt (0::real)"
      unfolding open_ray_gt_def using hyEq by simp
  qed

  have hPsi_contPos:
    "top1_continuous_map_on X TX (open_ray_gt (0::real))
        (subspace_topology (UNIV::real set) order_topology_on_UNIV (open_ray_gt (0::real))) \<Psi>"
  proof -
    have hrestrict_all:
      "\<forall>W f.
        top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f
        \<and> W \<subseteq> (UNIV::real set)
        \<and> f ` X \<subseteq> W
        \<longrightarrow> top1_continuous_map_on X TX W (subspace_topology (UNIV::real set) order_topology_on_UNIV W) f"
      using Theorem_18_2(5)[OF hTopX hTopR hTopR] .
    have hWsub: "open_ray_gt (0::real) \<subseteq> (UNIV::real set)"
      by simp
    have hpre:
      "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV \<Psi>
       \<and> open_ray_gt (0::real) \<subseteq> (UNIV::real set)
       \<and> \<Psi> ` X \<subseteq> open_ray_gt (0::real)"
      by (intro conjI, rule hPsi_contR, rule hWsub, rule hPsi_img_pos)
    show ?thesis
      using mp[OF spec[OF spec[OF hrestrict_all, where x="open_ray_gt (0::real)"], where x=\<Psi>] hpre] .
  qed

  have hInvPsi_contR: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV ((\<lambda>t::real. inverse t) \<circ> \<Psi>)"
    by (rule top1_continuous_map_on_comp[OF hPsi_contPos top1_continuous_inv_order_topology_pos])

  define \<phi> where "\<phi> i x = \<psi> i x * inverse (\<Psi> x)" for i x

  have hphi_contI_supp: "\<forall>i<n. top1_continuous_map_on X TX ?I ?TI (\<phi> i) \<and> top1_support_on X TX (\<phi> i) \<subseteq> U i"
  proof (intro allI impI)
    fix i assume hi: "i < n"

    have hpsi_i_R: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<psi> i)"
      using hpsi_contR hi by blast
    have hphi_i_R: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<phi> i)"
    proof -
      have hEq: "(\<phi> i) = (\<lambda>x. \<psi> i x * ((\<lambda>t::real. inverse t) \<circ> \<Psi>) x)"
        unfolding \<phi>_def by (rule ext, simp add: o_def)
      show ?thesis
        unfolding hEq
        by (rule top1_continuous_mul_real[OF hTopX hpsi_i_R hInvPsi_contR])
    qed

    have hphi_range: "(\<forall>x\<in>X. \<phi> i x \<in> ?I)"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have hPsi_posx: "0 < \<Psi> x"
        using hPsi_pos hxX by blast
      have hPsi_ne0: "\<Psi> x \<noteq> 0"
        using hPsi_posx by simp
      have hInv_pos: "0 < inverse (\<Psi> x)"
        using hPsi_posx by (rule positive_imp_inverse_positive)

      have hpsix_ge0: "0 \<le> \<psi> i x"
        using hpsi_ge0 hi hxX by blast
      have hpsix_le1: "\<psi> i x \<le> 1"
        using hpsi_le1 hi hxX by blast

	      have hpsix_le_sum: "\<psi> i x \<le> (\<Sum>j<n. \<psi> j x)"
	      proof -
	        have fin: "finite ({..<n}::nat set)"
	          by simp
	        have hi_in: "i \<in> {..<n}"
	          using hi by simp
	        have hsplit: "(\<Sum>j\<in>{..<n}. \<psi> j x) = \<psi> i x + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
	          by (rule sum.remove[OF fin hi_in])
		        have hrest_nonneg: "0 \<le> (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
		        proof -
		          have "\<And>j. j \<in> {..<n} - {i} \<Longrightarrow> 0 \<le> \<psi> j x"
		          proof -
		            fix j assume hj: "j \<in> {..<n} - {i}"
		            have hj': "j < n"
		              using hj by simp
		            have himp: "j < n \<longrightarrow> (\<forall>y\<in>X. 0 \<le> \<psi> j y)"
		              using hpsi_ge0 by (rule spec)
		            have hAll: "\<forall>y\<in>X. 0 \<le> \<psi> j y"
		              by (rule mp[OF himp hj'])
		            show "0 \<le> \<psi> j x"
		              by (rule bspec[OF hAll hxX])
		          qed
		          show ?thesis
		          proof (rule sum_nonneg)
		            fix xa assume hxa: "xa \<in> {..<n} - {i}"
		            show "0 \<le> \<psi> xa x"
		              by (rule \<open>\<And>j. j \<in> {..<n} - {i} \<Longrightarrow> 0 \<le> \<psi> j x\<close>[OF hxa])
		          qed
		        qed

		        have hle: "\<psi> i x \<le> \<psi> i x + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
		        proof -
		          have "(\<psi> i x) + 0 \<le> (\<psi> i x) + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x)"
		            using hrest_nonneg by (rule add_left_mono)
		          thus ?thesis
		            by simp
		        qed
	        have hEq: "\<psi> i x + (\<Sum>j\<in>{..<n} - {i}. \<psi> j x) = (\<Sum>j\<in>{..<n}. \<psi> j x)"
	          by (rule sym[OF hsplit])
	        have "\<psi> i x \<le> (\<Sum>j\<in>{..<n}. \<psi> j x)"
	          using hle by (simp add: hEq)
	        thus ?thesis
	          by simp
	      qed
      have hpsix_le_Psi: "\<psi> i x \<le> \<Psi> x"
        unfolding \<Psi>_def using hpsix_le_sum by simp

      have hphi_ge0: "0 \<le> \<phi> i x"
      proof -
        have "0 \<le> \<psi> i x * inverse (\<Psi> x)"
          using hpsix_ge0 less_imp_le[OF hInv_pos] by (rule mult_nonneg_nonneg)
        thus ?thesis
          unfolding \<phi>_def by simp
      qed

      have hphi_le1: "\<phi> i x \<le> 1"
      proof -
        have hmul_le: "\<psi> i x * inverse (\<Psi> x) \<le> \<Psi> x * inverse (\<Psi> x)"
          using hpsix_le_Psi less_imp_le[OF hInv_pos] by (rule mult_right_mono)
        have hPsi_cancel: "\<Psi> x * inverse (\<Psi> x) = 1"
          using hPsi_ne0 by simp
        have "\<psi> i x * inverse (\<Psi> x) \<le> 1"
          using hmul_le unfolding hPsi_cancel .
        thus ?thesis
          unfolding \<phi>_def by simp
      qed

	      have "\<phi> i x \<in> {t. 0 \<le> t \<and> t \<le> 1}"
	        using hphi_ge0 hphi_le1 unfolding top1_closed_interval_def by simp
	      thus "\<phi> i x \<in> ?I"
	        unfolding top1_closed_interval_def by simp
	    qed

    have hphi_contI: "top1_continuous_map_on X TX ?I ?TI (\<phi> i)"
    proof -
      have hrestrict_all:
        "\<forall>W f.
          top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f
          \<and> W \<subseteq> (UNIV::real set)
          \<and> f ` X \<subseteq> W
          \<longrightarrow> top1_continuous_map_on X TX W (subspace_topology (UNIV::real set) order_topology_on_UNIV W) f"
        using Theorem_18_2(5)[OF hTopX hTopR hTopR] .
      have hWsub: "?I \<subseteq> (UNIV::real set)"
        by simp
      have hImg: "(\<phi> i) ` X \<subseteq> ?I"
      proof (rule subsetI)
        fix y assume hy: "y \<in> (\<phi> i) ` X"
        then obtain x where hxX: "x \<in> X" and hyEq: "y = \<phi> i x"
          by blast
        have "\<phi> i x \<in> ?I"
          using hphi_range hxX by blast
        thus "y \<in> ?I"
          using hyEq by simp
      qed
      have hpre:
        "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<phi> i)
         \<and> ?I \<subseteq> (UNIV::real set)
         \<and> (\<phi> i) ` X \<subseteq> ?I"
        by (intro conjI, rule hphi_i_R, rule hWsub, rule hImg)
      have "top1_continuous_map_on X TX ?I (subspace_topology (UNIV::real set) order_topology_on_UNIV ?I) (\<phi> i)"
        using mp[OF spec[OF spec[OF hrestrict_all, where x="?I"], where x="(\<phi> i)"] hpre] .
      thus ?thesis
        unfolding hTI_eq .
    qed

    have hInvPsi_nonzero: "\<forall>x\<in>X. inverse (\<Psi> x) \<noteq> 0"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have "0 < \<Psi> x"
        using hPsi_pos hxX by blast
      hence "\<Psi> x \<noteq> 0"
        by simp
      thus "inverse (\<Psi> x) \<noteq> 0"
        by simp
    qed

    have hsupp_eq: "top1_support_on X TX (\<phi> i) = top1_support_on X TX (\<psi> i)"
    proof -
      have hEq: "(\<phi> i) = (\<lambda>x. \<psi> i x * inverse (\<Psi> x))"
        unfolding \<phi>_def by (rule ext, simp)
      show ?thesis
        unfolding hEq
        by (rule top1_support_on_mul_nonzero_factor[OF hInvPsi_nonzero])
    qed

    have hsuppU: "top1_support_on X TX (\<phi> i) \<subseteq> U i"
      unfolding hsupp_eq using hpsi_suppU hi by blast

    show "top1_continuous_map_on X TX ?I ?TI (\<phi> i) \<and> top1_support_on X TX (\<phi> i) \<subseteq> U i"
      by (intro conjI, rule hphi_contI, rule hsuppU)
  qed

  have hsum1: "\<forall>x\<in>X. (\<Sum>i<n. \<phi> i x) = 1"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hPsi_ne0: "\<Psi> x \<noteq> 0"
    proof -
      have "0 < \<Psi> x"
        using hPsi_pos hxX by blast
      thus ?thesis
        by simp
    qed
    have hsum:
      "(\<Sum>i<n. \<phi> i x) = (\<Sum>i<n. \<psi> i x) * inverse (\<Psi> x)"
    proof -
      have hEq1: "(\<Sum>i<n. \<phi> i x) = (\<Sum>i<n. \<psi> i x * inverse (\<Psi> x))"
        unfolding \<phi>_def by simp
      have hEq2: "(\<Sum>i<n. \<psi> i x * inverse (\<Psi> x)) = (\<Sum>i<n. \<psi> i x) * inverse (\<Psi> x)"
        by (simp add: sum_distrib_right[symmetric])
      show ?thesis
        using hEq1 hEq2 by simp
    qed
    have hPsiEq: "(\<Sum>i<n. \<psi> i x) = \<Psi> x"
      unfolding \<Psi>_def by simp
    have "(\<Sum>i<n. \<phi> i x) = \<Psi> x * inverse (\<Psi> x)"
      using hsum unfolding hPsiEq by simp
    also have "... = 1"
      using hPsi_ne0 by simp
    finally show "(\<Sum>i<n. \<phi> i x) = 1" .
  qed

  show ?thesis
    apply (rule exI[where x=\<phi>])
    unfolding top1_partition_of_unity_dominated_on_def
    apply (intro conjI)
     apply (rule hphi_contI_supp)
    apply (rule hsum1)
    done
qed

(** A concrete model of finite-dimensional Euclidean space \<open>\<real>^n\<close> using extensional function spaces. **)
definition top1_Rpow_set :: "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "top1_Rpow_set n = top1_PiE {0..<n} (\<lambda>_. (UNIV::real set))"

definition top1_Rpow_topology :: "nat \<Rightarrow> (nat \<Rightarrow> real) set set" where
  "top1_Rpow_topology n =
     top1_product_topology_on {0..<n} (\<lambda>_. (UNIV::real set)) (\<lambda>_. order_topology_on_UNIV)"

lemma top1_Rpow_is_hausdorff_on:
  shows "is_hausdorff_on (top1_Rpow_set n) (top1_Rpow_topology n)"
proof -
  have hHreal: "is_hausdorff_on (UNIV::real set) order_topology_on_UNIV"
    using conjunct1[OF Theorem_17_11] .
  have hHall: "\<forall>i\<in>{0..<n}. is_hausdorff_on (UNIV::real set) order_topology_on_UNIV"
    using hHreal by blast
  show ?thesis
    unfolding top1_Rpow_set_def top1_Rpow_topology_def
    by (rule Theorem_19_4_product[OF hHall])
qed

definition top1_m_manifold_on :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_m_manifold_on m X TX \<longleftrightarrow>
     is_hausdorff_on X TX
     \<and> top1_second_countable_on X TX
     \<and> (\<forall>x\<in>X. \<exists>U g. neighborhood_of x X TX U
              \<and> top1_embedding_on U (subspace_topology X TX U) (top1_Rpow_set m) (top1_Rpow_topology m) g)"

(** Embeddings are in particular injective on the carrier. **)
lemma top1_embedding_on_imp_inj_on:
  assumes hE: "top1_embedding_on A TA Y TY f"
  shows "inj_on f A"
proof -
  have hHomeo: "top1_homeomorphism_on A TA (f ` A) (subspace_topology Y TY (f ` A)) f"
    using hE unfolding top1_embedding_on_def by blast
  have hbij: "bij_betw f A (f ` A)"
    using hHomeo unfolding top1_homeomorphism_on_def by blast
  show ?thesis
    using hbij unfolding bij_betw_def by blast
qed

(** Embeddings are continuous into the ambient space (not just into the image-subspace). **)
lemma top1_embedding_on_imp_continuous:
  assumes hE: "top1_embedding_on A TA Y TY f"
  shows "top1_continuous_map_on A TA Y TY f"
proof -
  have hHomeo: "top1_homeomorphism_on A TA (f ` A) (subspace_topology Y TY (f ` A)) f"
    using hE unfolding top1_embedding_on_def by blast
  have hcontImg: "top1_continuous_map_on A TA (f ` A) (subspace_topology Y TY (f ` A)) f"
    using hHomeo unfolding top1_homeomorphism_on_def by blast
  have hmapImg: "\<forall>x\<in>A. f x \<in> f ` A"
    by blast
  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>A. f x \<in> Y"
      using hE unfolding top1_embedding_on_def top1_homeomorphism_on_def top1_continuous_map_on_def
      by blast
    show "\<forall>V\<in>TY. {x \<in> A. f x \<in> V} \<in> TA"
    proof (intro ballI)
      fix V assume hV: "V \<in> TY"
      have hVsub: "(f ` A) \<inter> V \<in> subspace_topology Y TY (f ` A)"
        unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x=V])
        apply (intro conjI)
         apply simp
        apply (rule hV)
        done
      have hpre: "{x \<in> A. f x \<in> (f ` A) \<inter> V} \<in> TA"
        using hcontImg hVsub unfolding top1_continuous_map_on_def by blast
      have hEq: "{x \<in> A. f x \<in> (f ` A) \<inter> V} = {x \<in> A. f x \<in> V}"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x \<in> A. f x \<in> (f ` A) \<inter> V} \<longleftrightarrow> x \<in> {x \<in> A. f x \<in> V}"
        proof
          assume hx: "x \<in> {x \<in> A. f x \<in> (f ` A) \<inter> V}"
          then show "x \<in> {x \<in> A. f x \<in> V}"
            by simp
	        next
	          assume hx: "x \<in> {x \<in> A. f x \<in> V}"
	          have hxA: "x \<in> A" and hfxV: "f x \<in> V"
	          proof -
	            have hx_conj: "x \<in> A \<and> f x \<in> V"
	              using hx by simp
	            show "x \<in> A"
	              using hx_conj by (rule conjunct1)
	            show "f x \<in> V"
	              using hx_conj by (rule conjunct2)
	          qed
	          have hfxImg: "f x \<in> f ` A"
	            using hmapImg hxA by blast
	          show "x \<in> {x \<in> A. f x \<in> (f ` A) \<inter> V}"
	            using hxA hfxImg hfxV by blast
        qed
      qed
      show "{x \<in> A. f x \<in> V} \<in> TA"
        using hpre unfolding hEq by simp
    qed
  qed
qed

(** Restricting the domain of a continuous map (directly from the definition). **)
lemma top1_continuous_map_on_restrict_domain_simple:
  assumes hf: "top1_continuous_map_on X0 TX0 Y0 TY0 f"
  assumes hA0: "A0 \<subseteq> X0"
  shows "top1_continuous_map_on A0 (subspace_topology X0 TX0 A0) Y0 TY0 f"
proof -
  have hmap: "\<forall>x\<in>X0. f x \<in> Y0"
    using hf unfolding top1_continuous_map_on_def by blast
  have hopen: "\<forall>V\<in>TY0. {x\<in>X0. f x \<in> V} \<in> TX0"
    using hf unfolding top1_continuous_map_on_def by blast
  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>A0. f x \<in> Y0"
      using hmap hA0 by blast
    show "\<forall>V\<in>TY0. {x \<in> A0. f x \<in> V} \<in> subspace_topology X0 TX0 A0"
    proof (intro ballI)
      fix V assume hV: "V \<in> TY0"
      have hpreim: "{x\<in>X0. f x \<in> V} \<in> TX0"
        using hopen hV by blast
      have hEq: "{x \<in> A0. f x \<in> V} = A0 \<inter> {x\<in>X0. f x \<in> V}"
        using hA0 by blast
      show "{x \<in> A0. f x \<in> V} \<in> subspace_topology X0 TX0 A0"
        unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x="{x\<in>X0. f x \<in> V}"])
        apply (intro conjI)
         apply (simp only: hEq Int_assoc Int_commute Int_left_commute)
        apply (rule hpreim)
        done
    qed
  qed
qed

(** If a point is nonzero, it lies in the support (support is a closure of the nonzero set). **)
lemma top1_support_on_contains_nonzero:
  assumes hxX: "x \<in> X"
  assumes hfx: "f x \<noteq> (0::real)"
  shows "x \<in> top1_support_on X TX f"
proof -
  have hxNZ: "x \<in> {y \<in> X. f y \<noteq> 0}"
    using hxX hfx by simp
  have hsub: "{y \<in> X. f y \<noteq> 0} \<subseteq> top1_support_on X TX f"
    unfolding top1_support_on_def by (rule subset_closure_on)
  show ?thesis
    by (rule subsetD[OF hsub hxNZ])
qed

(** Every manifold point has a chart on an open subset of the carrier, with continuous and injective chart map. **)
lemma top1_m_manifold_on_local_chart_inj_cont:
  fixes m :: nat
  assumes hM: "top1_m_manifold_on m X TX"
  assumes hxX: "x \<in> X"
  shows "\<exists>U g.
    U \<in> TX \<and> U \<subseteq> X \<and> x \<in> U
    \<and> top1_continuous_map_on U (subspace_topology X TX U) (top1_Rpow_set m) (top1_Rpow_topology m) g
    \<and> inj_on g U"
proof -
  have hLocal:
    "\<forall>x\<in>X. \<exists>U g. neighborhood_of x X TX U
      \<and> top1_embedding_on U (subspace_topology X TX U) (top1_Rpow_set m) (top1_Rpow_topology m) g"
    using hM unfolding top1_m_manifold_on_def by blast

  obtain U0 g0 where hnbhd: "neighborhood_of x X TX U0"
    and hEmb: "top1_embedding_on U0 (subspace_topology X TX U0) (top1_Rpow_set m) (top1_Rpow_topology m) g0"
    using hLocal hxX by blast

  define U where "U = X \<inter> U0"

  have hTopX: "is_topology_on X TX"
    using hM unfolding top1_m_manifold_on_def is_hausdorff_on_def by blast

  have hXopen: "X \<in> TX"
    using hTopX unfolding is_topology_on_def by blast
  have hU0open: "U0 \<in> TX"
    using hnbhd unfolding neighborhood_of_def by blast
  have hUopen: "U \<in> TX"
    unfolding U_def by (rule topology_inter2[OF hTopX hXopen hU0open])
  have hUsubX: "U \<subseteq> X"
    unfolding U_def by blast
  have hxU: "x \<in> U"
    unfolding U_def using hxX hnbhd unfolding neighborhood_of_def by blast

  have hCont0: "top1_continuous_map_on U0 (subspace_topology X TX U0) (top1_Rpow_set m) (top1_Rpow_topology m) g0"
    by (rule top1_embedding_on_imp_continuous[OF hEmb])
  have hInj0: "inj_on g0 U0"
    by (rule top1_embedding_on_imp_inj_on[OF hEmb])

  have hUsubU0: "U \<subseteq> U0"
    unfolding U_def by blast

  have hContU':
    "top1_continuous_map_on U
      (subspace_topology U0 (subspace_topology X TX U0) U)
      (top1_Rpow_set m) (top1_Rpow_topology m) g0"
    by (rule top1_continuous_map_on_restrict_domain_simple[OF hCont0 hUsubU0])

  have hTopEq:
    "subspace_topology U0 (subspace_topology X TX U0) U = subspace_topology X TX U"
    by (rule subspace_topology_trans[OF hUsubU0])

  have hContU:
    "top1_continuous_map_on U (subspace_topology X TX U) (top1_Rpow_set m) (top1_Rpow_topology m) g0"
    using hContU' unfolding hTopEq .

  have hInjU: "inj_on g0 U"
    by (rule inj_on_subset[OF hInj0 hUsubU0])

  show ?thesis
    apply (rule exI[where x=U])
    apply (rule exI[where x=g0])
    using hUopen hUsubX hxU hContU hInjU by blast
qed

(** Compactness helper: extract a finite subcover from a cover presented as an image \<open>V ` X\<close>. **)
lemma top1_compact_on_finite_subcover_image:
  assumes hcomp: "top1_compact_on X TX"
  assumes hVopen: "\<forall>x\<in>X. V x \<in> TX"
  assumes hVcov: "X \<subseteq> \<Union>(V ` X)"
  shows "\<exists>I. finite I \<and> I \<subseteq> X \<and> X \<subseteq> \<Union>(V ` I)"
proof -
  have hCover:
    "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  have hUc_sub: "V ` X \<subseteq> TX"
  proof (rule subsetI)
    fix U assume hU: "U \<in> V ` X"
    then obtain x where hxX: "x \<in> X" and hUeq: "U = V x"
      by blast
    show "U \<in> TX"
      using hVopen hxX hUeq by simp
  qed

  have hex: "\<exists>F. finite F \<and> F \<subseteq> V ` X \<and> X \<subseteq> \<Union>F"
  proof -
    have hspec:
      "V ` X \<subseteq> TX \<and> X \<subseteq> \<Union>(V ` X) \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> V ` X \<and> X \<subseteq> \<Union>F)"
      by (rule spec[OF hCover, where x="V ` X"])
    have hpre: "V ` X \<subseteq> TX \<and> X \<subseteq> \<Union>(V ` X)"
      by (intro conjI, rule hUc_sub, rule hVcov)
    show ?thesis
      by (rule mp[OF hspec hpre])
  qed

  obtain F where hF: "finite F \<and> F \<subseteq> V ` X \<and> X \<subseteq> \<Union>F"
    using hex by blast

  have hpre: "\<forall>U\<in>F. \<exists>x\<in>X. V x = U"
  proof (intro ballI)
    fix U assume hUF: "U \<in> F"
    have hUimg: "U \<in> V ` X"
      using hF hUF by blast
    then obtain x where hxX: "x \<in> X" and hUeq: "U = V x"
      by blast
    show "\<exists>x\<in>X. V x = U"
      apply (rule bexI[where x=x])
       apply (simp only: hUeq)
      apply (rule hxX)
      done
  qed

  have hpre': "\<forall>U\<in>F. \<exists>x. x \<in> X \<and> V x = U"
  proof (intro ballI)
    fix U assume hUF: "U \<in> F"
    obtain x where hxX: "x \<in> X" and hVU: "V x = U"
      using hpre hUF by blast
    show "\<exists>x. x \<in> X \<and> V x = U"
      by (rule exI[where x=x], intro conjI, rule hxX, rule hVU)
  qed

  obtain s where hs: "\<forall>U\<in>F. s U \<in> X \<and> V (s U) = U"
    using bchoice[OF hpre'] by blast

  define I where "I = s ` F"
  have hIfin: "finite I"
    unfolding I_def using hF by simp
  have hIsub: "I \<subseteq> X"
  proof (rule subsetI)
    fix x assume hx: "x \<in> I"
    then obtain U where hUF: "U \<in> F" and hxeq: "x = s U"
      unfolding I_def by blast
    show "x \<in> X"
      using hs hUF hxeq by blast
  qed

  have hFsub: "F \<subseteq> V ` I"
  proof (rule subsetI)
    fix U assume hUF: "U \<in> F"
    have hsUI: "s U \<in> I"
      unfolding I_def using hUF by blast
    have hVU: "V (s U) = U"
      using hs hUF by blast
    show "U \<in> V ` I"
    proof -
      have "V (s U) \<in> V ` I"
        by (rule imageI[OF hsUI])
      thus ?thesis
        using hVU by simp
    qed
  qed

  have hcovI: "X \<subseteq> \<Union>(V ` I)"
  proof -
    have "X \<subseteq> \<Union>F"
      using hF by blast
    moreover have "\<Union>F \<subseteq> \<Union>(V ` I)"
      using hFsub by blast
    ultimately show ?thesis
      by blast
  qed

  show ?thesis
    apply (rule exI[where x=I])
    using hIfin hIsub hcovI by blast
qed

(** A partition of unity has a nonzero coordinate at every point (since the sum is 1). **)
lemma top1_partition_of_unity_dominated_on_exists_ne0:
  assumes hPU: "top1_partition_of_unity_dominated_on X TX n U \<phi>"
  assumes hxX: "x \<in> X"
  shows "\<exists>i<n. \<phi> i x \<noteq> 0"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>i<n. \<phi> i x \<noteq> 0)"
  have hall0: "\<forall>i<n. \<phi> i x = 0"
    using hno by blast
  have hsum0: "(\<Sum>i<n. \<phi> i x) = 0"
    using hall0 by simp
  have hsum1: "(\<Sum>i<n. \<phi> i x) = 1"
    using hPU hxX unfolding top1_partition_of_unity_dominated_on_def by blast
  show False
    using hsum0 hsum1 by simp
qed

(** A continuous map into the closed interval is continuous as a real-valued map. **)
lemma top1_continuous_map_on_closed_interval_to_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes hTopX: "is_topology_on X TX"
  assumes hf: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
proof -
  let ?I = "top1_closed_interval 0 1"
  let ?TI = "top1_closed_interval_topology 0 1"

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hTopI: "is_topology_on ?I ?TI"
    unfolding top1_closed_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF hTopR], simp add: top1_closed_interval_def)

  have hTI_eq: "?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I"
    unfolding top1_closed_interval_topology_def by simp

  have hexpand:
    "\<forall>W g.
      top1_continuous_map_on X TX ?I ?TI g
      \<and> ?I \<subseteq> W
      \<and> ?TI = subspace_topology W order_topology_on_UNIV ?I
      \<longrightarrow> top1_continuous_map_on X TX W order_topology_on_UNIV g"
    using Theorem_18_2(6)[OF hTopX hTopI hTopR] .

  have hpre:
    "top1_continuous_map_on X TX ?I ?TI f
     \<and> ?I \<subseteq> (UNIV::real set)
     \<and> ?TI = subspace_topology (UNIV::real set) order_topology_on_UNIV ?I"
    by (intro conjI, rule hf, simp, rule hTI_eq)

  show ?thesis
    using mp[OF spec[OF spec[OF hexpand, where x="(UNIV::real set)"], where x=f] hpre] .
qed

(** The standard product topology is a topology on our model of \<open>\<real>^n\<close>. **)
lemma top1_Rpow_is_topology_on:
  shows "is_topology_on (top1_Rpow_set n) (top1_Rpow_topology n)"
proof -
  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hAll: "\<forall>i\<in>{0..<n}. is_topology_on (UNIV::real set) order_topology_on_UNIV"
    using hTopR by blast
  show ?thesis
    unfolding top1_Rpow_set_def top1_Rpow_topology_def
    by (rule top1_product_topology_on_is_topology_on[OF hAll])
qed

(** Extensionality of elements of \<open>top1_Rpow_set m\<close>. **)
lemma top1_Rpow_set_ext:
  fixes f g :: "nat \<Rightarrow> real"
  assumes hf: "f \<in> top1_Rpow_set m"
  assumes hg: "g \<in> top1_Rpow_set m"
  assumes hEq: "\<forall>k<m. f k = g k"
  shows "f = g"
proof (rule ext)
  fix k :: nat
  show "f k = g k"
  proof (cases "k < m")
    case True
    show ?thesis
      using hEq True by blast
  next
    case False
    have hk: "k \<notin> {0..<m}"
      using False by simp
    have hfext: "\<forall>i. i \<notin> {0..<m} \<longrightarrow> f i = undefined"
      using hf unfolding top1_Rpow_set_def top1_PiE_iff by blast
    have hgext: "\<forall>i. i \<notin> {0..<m} \<longrightarrow> g i = undefined"
      using hg unfolding top1_Rpow_set_def top1_PiE_iff by blast
    have "f k = undefined"
      using hfext hk by blast
    moreover have "g k = undefined"
      using hgext hk by blast
    ultimately show ?thesis
      by simp
  qed
qed

(** Coordinate projections of a continuous map into \<open>\<real>^n\<close> are continuous. **)
lemma top1_continuous_map_on_Rpow_coord:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> real"
  assumes hTopA: "is_topology_on A TA"
  assumes hf: "top1_continuous_map_on A TA (top1_Rpow_set n) (top1_Rpow_topology n) f"
  assumes hk: "k < n"
  shows "top1_continuous_map_on A TA (UNIV::real set) order_topology_on_UNIV (\<lambda>a. (f a) k)"
proof -
  let ?I = "{0..<n}"
  let ?X = "\<lambda>_. (UNIV::real set)"
  let ?T = "\<lambda>_. order_topology_on_UNIV"

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have hTop: "\<forall>i\<in>?I. is_topology_on (?X i) (?T i)"
    using hTopR by blast

  have hfmap: "\<forall>a\<in>A. f a \<in> top1_PiE ?I ?X"
  proof (intro ballI)
    fix a assume ha: "a \<in> A"
    have "f a \<in> top1_Rpow_set n"
      using hf ha unfolding top1_continuous_map_on_def by blast
    thus "f a \<in> top1_PiE ?I ?X"
      unfolding top1_Rpow_set_def by simp
  qed

  have hf_prod:
    "top1_continuous_map_on A TA (top1_PiE ?I ?X) (top1_product_topology_on ?I ?X ?T) f"
    using hf unfolding top1_Rpow_set_def top1_Rpow_topology_def by simp

  have hcoords:
    "\<forall>i\<in>?I. top1_continuous_map_on A TA (?X i) (?T i) (\<lambda>a. (f a) i)"
    by (rule iffD1[OF Theorem_19_6[OF hTopA hTop hfmap] hf_prod])

  have hkI: "k \<in> ?I"
    using hk by simp

  show ?thesis
    by (rule bspec[OF hcoords hkI])
qed

(** Compact manifolds admit a finite atlas by continuous injective charts into \<open>\<real>^m\<close>. **)
lemma top1_compact_m_manifold_finite_chart_cover:
  fixes m :: nat
  assumes hcomp: "top1_compact_on X TX"
  assumes hM: "top1_m_manifold_on m X TX"
  shows "\<exists>(n::nat) (U::nat \<Rightarrow> 'a set) (g::nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> real).
    (\<forall>i<n.
        U i \<in> TX \<and> U i \<subseteq> X
        \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
              (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
        \<and> inj_on (g i) (U i))
    \<and> X \<subseteq> (\<Union>i<n. U i)"
proof -
  have hLocal:
    "\<forall>x\<in>X. \<exists>U g.
      U \<in> TX \<and> U \<subseteq> X \<and> x \<in> U
      \<and> top1_continuous_map_on U (subspace_topology X TX U)
            (top1_Rpow_set m) (top1_Rpow_topology m) g
      \<and> inj_on g U"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    obtain U g where hU:
      "U \<in> TX \<and> U \<subseteq> X \<and> x \<in> U
       \<and> top1_continuous_map_on U (subspace_topology X TX U)
             (top1_Rpow_set m) (top1_Rpow_topology m) g
       \<and> inj_on g U"
      using top1_m_manifold_on_local_chart_inj_cont[OF hM hxX] by blast
    show "\<exists>U g.
      U \<in> TX \<and> U \<subseteq> X \<and> x \<in> U
      \<and> top1_continuous_map_on U (subspace_topology X TX U)
            (top1_Rpow_set m) (top1_Rpow_topology m) g
      \<and> inj_on g U"
      using hU by blast
  qed

  have hLocalPair:
    "\<forall>x\<in>X. \<exists>p.
      fst p \<in> TX \<and> fst p \<subseteq> X \<and> x \<in> fst p
      \<and> top1_continuous_map_on (fst p) (subspace_topology X TX (fst p))
            (top1_Rpow_set m) (top1_Rpow_topology m) (snd p)
      \<and> inj_on (snd p) (fst p)"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    obtain U g where hU:
      "U \<in> TX \<and> U \<subseteq> X \<and> x \<in> U
       \<and> top1_continuous_map_on U (subspace_topology X TX U)
             (top1_Rpow_set m) (top1_Rpow_topology m) g
       \<and> inj_on g U"
      using hLocal hxX by blast
    show "\<exists>p.
      fst p \<in> TX \<and> fst p \<subseteq> X \<and> x \<in> fst p
      \<and> top1_continuous_map_on (fst p) (subspace_topology X TX (fst p))
            (top1_Rpow_set m) (top1_Rpow_topology m) (snd p)
      \<and> inj_on (snd p) (fst p)"
      apply (rule exI[where x="(U,g)"])
      using hU by simp
  qed

  obtain p where hp:
    "\<forall>x\<in>X.
      fst (p x) \<in> TX \<and> fst (p x) \<subseteq> X \<and> x \<in> fst (p x)
      \<and> top1_continuous_map_on (fst (p x)) (subspace_topology X TX (fst (p x)))
            (top1_Rpow_set m) (top1_Rpow_topology m) (snd (p x))
      \<and> inj_on (snd (p x)) (fst (p x))"
    using bchoice[OF hLocalPair] by blast

  define U0 where "U0 = (\<lambda>x. fst (p x))"
  define g0 where "g0 = (\<lambda>x. snd (p x))"

  have hU0:
    "\<forall>x\<in>X.
      U0 x \<in> TX \<and> U0 x \<subseteq> X \<and> x \<in> U0 x
      \<and> top1_continuous_map_on (U0 x) (subspace_topology X TX (U0 x))
            (top1_Rpow_set m) (top1_Rpow_topology m) (g0 x)
      \<and> inj_on (g0 x) (U0 x)"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hpx:
      "fst (p x) \<in> TX \<and> fst (p x) \<subseteq> X \<and> x \<in> fst (p x)
       \<and> top1_continuous_map_on (fst (p x)) (subspace_topology X TX (fst (p x)))
             (top1_Rpow_set m) (top1_Rpow_topology m) (snd (p x))
       \<and> inj_on (snd (p x)) (fst (p x))"
      using hp hxX by blast
    show "U0 x \<in> TX \<and> U0 x \<subseteq> X \<and> x \<in> U0 x
      \<and> top1_continuous_map_on (U0 x) (subspace_topology X TX (U0 x))
            (top1_Rpow_set m) (top1_Rpow_topology m) (g0 x)
      \<and> inj_on (g0 x) (U0 x)"
      unfolding U0_def g0_def using hpx by simp
  qed

  have hVopen: "\<forall>x\<in>X. U0 x \<in> TX"
    using hU0 by blast
  have hVcov: "X \<subseteq> \<Union>(U0 ` X)"
  proof (rule subsetI)
    fix x assume hxX: "x \<in> X"
    have hxUx: "x \<in> U0 x"
      using hU0 hxX by blast
    show "x \<in> \<Union>(U0 ` X)"
    proof -
      have hUxImg: "U0 x \<in> U0 ` X"
        by (rule imageI[OF hxX])
      show ?thesis
        by (rule UnionI[OF hUxImg hxUx])
    qed
  qed

  obtain I where hI:
    "finite I \<and> I \<subseteq> X \<and> X \<subseteq> \<Union>(U0 ` I)"
    using top1_compact_on_finite_subcover_image[OF hcomp hVopen hVcov] by blast

  have hIfin: "finite I"
    using hI by blast
  have hIsub: "I \<subseteq> X"
    using hI by blast
  have hIcov: "X \<subseteq> \<Union>(U0 ` I)"
    using hI by blast

  obtain xs where hxs: "set xs = I \<and> distinct xs"
    using finite_distinct_list_of_set[OF hIfin] by blast

  define n where "n = length xs"
  define U where "U = (\<lambda>i. U0 (xs ! i))"
  define g where "g = (\<lambda>i. g0 (xs ! i))"

  have hprops:
    "\<forall>i<n.
      U i \<in> TX \<and> U i \<subseteq> X
      \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
            (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
      \<and> inj_on (g i) (U i)"
  proof (intro allI impI)
    fix i assume hi: "i < n"
    have hi': "i < length xs"
      using hi unfolding n_def by simp
    have hmem: "xs ! i \<in> set xs"
      using nth_mem hi' by blast
    have hxI: "xs ! i \<in> I"
      using hxs hmem by simp
    have hxX: "xs ! i \<in> X"
      using hIsub hxI by blast
    have hchart:
      "U0 (xs ! i) \<in> TX \<and> U0 (xs ! i) \<subseteq> X \<and> xs ! i \<in> U0 (xs ! i)
       \<and> top1_continuous_map_on (U0 (xs ! i)) (subspace_topology X TX (U0 (xs ! i)))
             (top1_Rpow_set m) (top1_Rpow_topology m) (g0 (xs ! i))
       \<and> inj_on (g0 (xs ! i)) (U0 (xs ! i))"
      using hU0 hxX by blast
    show "U i \<in> TX \<and> U i \<subseteq> X
      \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
            (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
      \<and> inj_on (g i) (U i)"
      unfolding U_def g_def using hchart by simp
  qed

  have hcov_n: "X \<subseteq> (\<Union>i<n. U i)"
  proof (rule subsetI)
    fix x assume hxX: "x \<in> X"
    have hxU: "x \<in> \<Union>(U0 ` I)"
      using hIcov hxX by blast
    obtain y where hyI: "y \<in> I" and hxy: "x \<in> U0 y"
      using hxU by blast
    have hyset: "y \<in> set xs"
      using hxs hyI by simp
    have hexj: "\<exists>j<length xs. xs ! j = y"
      using hyset by (simp add: in_set_conv_nth)
    obtain j where hjconj: "j < length xs \<and> xs ! j = y"
      using hexj by blast
    have hj: "j < length xs"
      using hjconj by (rule conjunct1)
    have hnth: "xs ! j = y"
      using hjconj by (rule conjunct2)
    have hjn: "j < n"
      unfolding n_def using hj by simp
    have hxUj: "x \<in> U j"
      unfolding U_def using hnth hxy by simp
    show "x \<in> (\<Union>i<n. U i)"
    proof -
      have hjmem: "j \<in> {..<n}"
        using hjn by simp
      have hUjmem: "U j \<in> U ` {..<n}"
        by (rule imageI[OF hjmem])
      show ?thesis
        by (rule UnionI[OF hUjmem hxUj])
    qed
  qed

  show ?thesis
    apply (rule exI[where x=n])
    apply (rule exI[where x=U])
    apply (rule exI[where x=g])
    using hprops hcov_n by blast
qed

(** from *\S36 Theorem 36.2 (Compact manifolds embed in some \<open>\<real>^N\<close>) [top1.tex:5055] **)
theorem Theorem_36_2:
  fixes m :: nat
  assumes hm: "0 < m"
  assumes hcomp: "top1_compact_on X TX"
  assumes hM: "top1_m_manifold_on m X TX"
  shows "\<exists>N F. top1_embedding_on X TX (top1_Rpow_set N) (top1_Rpow_topology N) F"
text \<open>
  The proof follows the construction in \<open>top1.tex\<close>:
  choose finitely many local embeddings into \<open>\<real>^m\<close>, build a finite partition of unity dominated
  by the corresponding cover (Theorem 36.1), and use it to assemble a continuous injective map into
  some finite product of copies of \<open>\<real>\<close>.

  In this formalization we model \<open>\<real>^n\<close> as an extensional function space
  \<open>{0..<n} \<rightarrow> UNIV\<close>. The final embedding lives in a suitable finite-dimensional instance of
  this product.
\<close>
text \<open>
  The full Isabelle proof (continuity of the assembled map and injectivity via the partition of unity)
  follows the standard argument: from a finite chart cover we obtain a finite partition of unity (Theorem 36.1),
  and then assemble a global continuous injective map by multiplying each chart with the corresponding partition
  function and adding the partition coordinate itself.
\<close>
proof -
  have hTopX: "is_topology_on X TX"
    using hcomp unfolding top1_compact_on_def by blast

  have hHausX: "is_hausdorff_on X TX"
    using hM unfolding top1_m_manifold_on_def by blast

  have hNormal: "top1_normal_on X TX"
    by (rule Theorem_32_3[OF hcomp hHausX])

  have hexCharts:
    "\<exists>(n::nat) (U::nat \<Rightarrow> 'a set) (g::nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> real).
      (\<forall>i<n.
          U i \<in> TX \<and> U i \<subseteq> X
          \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
                (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
          \<and> inj_on (g i) (U i))
      \<and> X \<subseteq> (\<Union>i<n. U i)"
    by (rule top1_compact_m_manifold_finite_chart_cover[OF hcomp hM])

  obtain n where hn:
    "\<exists>(U::nat \<Rightarrow> 'a set) (g::nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> real).
      (\<forall>i<n.
          U i \<in> TX \<and> U i \<subseteq> X
          \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
                (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
          \<and> inj_on (g i) (U i))
      \<and> X \<subseteq> (\<Union>i<n. U i)"
    using hexCharts by blast

  obtain U where hU:
    "\<exists>(g::nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> real).
      (\<forall>i<n.
          U i \<in> TX \<and> U i \<subseteq> X
          \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
                (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
          \<and> inj_on (g i) (U i))
      \<and> X \<subseteq> (\<Union>i<n. U i)"
    using hn by blast

  obtain g where hCharts:
    "(\<forall>i<n.
        U i \<in> TX \<and> U i \<subseteq> X
        \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
              (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
        \<and> inj_on (g i) (U i))
     \<and> X \<subseteq> (\<Union>i<n. U i)"
    using hU by blast

  have hUcontinj:
    "\<forall>i<n.
      U i \<in> TX \<and> U i \<subseteq> X
      \<and> top1_continuous_map_on (U i) (subspace_topology X TX (U i))
            (top1_Rpow_set m) (top1_Rpow_topology m) (g i)
      \<and> inj_on (g i) (U i)"
    by (rule conjunct1[OF hCharts])

  have hcov: "X \<subseteq> (\<Union>i<n. U i)"
    by (rule conjunct2[OF hCharts])

  have hUopen: "\<forall>i<n. U i \<in> TX"
    using hUcontinj by blast
  have hUsub: "\<forall>i<n. U i \<subseteq> X"
    using hUcontinj by blast
  obtain \<phi> where hPU: "top1_partition_of_unity_dominated_on X TX n U \<phi>"
    using Theorem_36_1[OF hNormal hUopen hUsub hcov] by blast

  have hTopR: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hphi_contR: "\<forall>i<n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<phi> i)"
  proof (intro allI impI)
    fix i assume hi: "i < n"
    have hcontI:
      "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<phi> i)"
      using hPU unfolding top1_partition_of_unity_dominated_on_def using hi by blast
    show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<phi> i)"
      by (rule top1_continuous_map_on_closed_interval_to_real[OF hTopX hcontI])
  qed

  have hphi_supp: "\<forall>i<n. top1_support_on X TX (\<phi> i) \<subseteq> U i"
    using hPU unfolding top1_partition_of_unity_dominated_on_def by blast

  define q where "q = Suc m"
  define N where "N = n * q"

  define F where
    "F x =
      (\<lambda>j.
        if j < N then
          (let i = j div q; r = j mod q in
            if r < m then (if x \<in> U i then \<phi> i x * (g i x r) else 0) else \<phi> i x)
        else undefined)"
    for x

  have hFmap: "\<forall>x\<in>X. F x \<in> top1_Rpow_set N"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have "\<forall>j\<in>{0..<N}. F x j \<in> (UNIV::real set)"
      by simp
    moreover have "\<forall>j. j \<notin> {0..<N} \<longrightarrow> F x j = undefined"
      unfolding F_def by auto
    ultimately show "F x \<in> top1_Rpow_set N"
      unfolding top1_Rpow_set_def top1_PiE_iff by blast
  qed

  have hFcoords:
    "\<forall>j\<in>{0..<N}. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (F x) j)"
  proof (intro ballI)
    fix j assume hj: "j \<in> {0..<N}"
    have hjN: "j < N"
      using hj by simp
    have hqpos: "q > 0"
      unfolding q_def by simp
    define i where "i = j div q"
    define r where "r = j mod q"
    have hi: "i < n"
    proof -
      have hj': "j < n * q"
        using hjN unfolding N_def by simp
      have "j div q < n"
        using hj' hqpos by (simp add: div_less_iff_less_mult)
      thus ?thesis
        unfolding i_def by simp
    qed
    have hr_ltq: "r < q"
      unfolding r_def using hqpos by (rule mod_less_divisor)
    have hr_le_m: "r \<le> m"
      unfolding q_def r_def using hr_ltq by simp
    have hcases: "r < m \<or> r = m"
      using hr_le_m by arith

    show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (F x) j)"
    proof (cases "r < m")
      case True
      have hcont:
        "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV
           (\<lambda>x. if x \<in> U i then \<phi> i x * (g i x r) else 0)"
      proof -
        have hUi_open: "U i \<in> TX"
          using hUopen hi by blast
        have hUi_sub: "U i \<subseteq> X"
          using hUsub hi by blast
        have hphi_i: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<phi> i)"
          using hphi_contR hi by blast
        have hsupp_i: "top1_support_on X TX (\<phi> i) \<subseteq> U i"
          using hphi_supp hi by blast
        have hg_i_r:
          "top1_continuous_map_on (U i) (subspace_topology X TX (U i))
             (UNIV::real set) order_topology_on_UNIV (\<lambda>x. (g i x) r)"
        proof -
          have hgi: "top1_continuous_map_on (U i) (subspace_topology X TX (U i))
              (top1_Rpow_set m) (top1_Rpow_topology m) (g i)"
            using hUcontinj hi by blast
          have hTopUi: "is_topology_on (U i) (subspace_topology X TX (U i))"
            by (rule subspace_topology_is_topology_on[OF hTopX], rule hUsub[rule_format, OF hi])
          show ?thesis
            by (rule top1_continuous_map_on_Rpow_coord[OF hTopUi hgi True])
        qed
        show ?thesis
          by (rule top1_continuous_mul_supported_extend_zero[OF hTopX hUi_open hUi_sub hphi_i hsupp_i hg_i_r])
      qed

      have hEq: "\<forall>x\<in>X. (F x) j = (if x \<in> U i then \<phi> i x * (g i x r) else 0)"
      proof (intro ballI)
        fix x assume hxX: "x \<in> X"
        have hIf: "j < N"
          using hjN by simp
        show "(F x) j = (if x \<in> U i then \<phi> i x * (g i x r) else 0)"
          unfolding F_def using hIf True
          by (simp add: q_def Let_def i_def r_def)
      qed

      show ?thesis
        using top1_continuous_map_on_cong[OF hEq] hcont by blast
    next
      case False
      have hEq: "\<forall>x\<in>X. (F x) j = \<phi> i x"
      proof (intro ballI)
        fix x assume hxX: "x \<in> X"
        have hIf: "j < N"
          using hjN by simp
        show "(F x) j = \<phi> i x"
          unfolding F_def using hIf False
          by (simp add: q_def Let_def i_def r_def)
      qed
      have hcont: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<phi> i)"
        using hphi_contR hi by blast
      show ?thesis
        using top1_continuous_map_on_cong[OF hEq] hcont by blast
    qed
  qed

  have hFcont: "top1_continuous_map_on X TX (top1_Rpow_set N) (top1_Rpow_topology N) F"
  proof -
    let ?I = "{0..<N}"
    let ?X = "\<lambda>_. (UNIV::real set)"
    let ?T = "\<lambda>_. order_topology_on_UNIV"

    have hTop: "\<forall>i\<in>?I. is_topology_on (?X i) (?T i)"
      using hTopR by blast
    have hfmap: "\<forall>x\<in>X. F x \<in> top1_PiE ?I ?X"
      using hFmap unfolding top1_Rpow_set_def by simp
    have hcoords:
      "\<forall>i\<in>?I. top1_continuous_map_on X TX (?X i) (?T i) (\<lambda>x. (F x) i)"
      by (rule hFcoords)
    have hcont_prod:
      "top1_continuous_map_on X TX (top1_PiE ?I ?X) (top1_product_topology_on ?I ?X ?T) F"
      by (rule iffD2[OF Theorem_19_6[OF hTopX hTop hfmap] hcoords])
    show ?thesis
      unfolding top1_Rpow_set_def top1_Rpow_topology_def by (rule hcont_prod)
  qed

  have hFinj: "inj_on F X"
  proof (rule inj_onI)
    fix x y assume hxX: "x \<in> X" and hyX: "y \<in> X" and hEq: "F x = F y"

    obtain i where hi: "i < n" and hphix: "\<phi> i x \<noteq> 0"
      using top1_partition_of_unity_dominated_on_exists_ne0[OF hPU hxX] by blast

    have hsupp_i: "top1_support_on X TX (\<phi> i) \<subseteq> U i"
      using hphi_supp hi by blast

    have hxUi: "x \<in> U i"
    proof (rule ccontr)
      assume hxnot: "x \<notin> U i"
      have hx: "x \<in> X - U i"
        using hxX hxnot by blast
      have "\<phi> i x = 0"
        by (rule top1_support_on_subset_imp_zero_on_complement[OF hsupp_i hx])
      thus False
        using hphix by contradiction
    qed

    have hphiEq: "\<phi> i x = \<phi> i y"
    proof -
      have hidx: "i * q + m < N"
      proof -
        have hmq: "m < q"
          unfolding q_def by simp
        have hsuc: "Suc i \<le> n"
          using hi by simp
        have h1: "i * q + m < i * q + q"
          using hmq by simp
        have h2: "i * q + q = Suc i * q"
          by simp
        have h3: "i * q + m < Suc i * q"
          using h1 by (simp add: h2)
        have h4: "Suc i * q \<le> n * q"
          by (rule mult_le_mono1[OF hsuc])
        have "i * q + m < n * q"
          by (rule less_le_trans[OF h3 h4])
        thus ?thesis
          unfolding N_def by simp
      qed
      have hFx: "(F x) (i * q + m) = \<phi> i x"
      proof -
        have hIf: "i * q + m < N"
          by (rule hidx)
        have hm_lt: "m < q"
          unfolding q_def by simp
        have hm0: "m div q = 0"
          using hm_lt by (simp add: div_eq_0_iff)
        have hq0: "q \<noteq> 0"
          unfolding q_def by simp
        have hdiv: "(i * q + m) div q = i"
        proof -
          have "(i * q + m) div q = (m + q * i) div q"
            by (simp add: add.assoc add.commute add.left_commute mult.commute)
          also have "... = i + m div q"
            by (simp add: div_mult_self2[OF hq0])
          also have "... = i"
            using hm0 by simp
          finally show ?thesis .
        qed
        have hmod: "(i * q + m) mod q = m"
        proof -
          have "(i * q + m) mod q = (m + q * i) mod q"
            by (simp add: add.assoc add.commute add.left_commute mult.commute)
          also have "... = m mod q"
            by simp
          also have "... = m"
            using hm_lt by simp
          finally show ?thesis .
        qed
        have hnotlt: "\<not> ((i * q + m) mod q < m)"
          using hmod by simp
        show ?thesis
          unfolding F_def Let_def
          using hIf hdiv hmod hnotlt by simp
      qed
      have hFy: "(F y) (i * q + m) = \<phi> i y"
      proof -
        have hIf: "i * q + m < N"
          by (rule hidx)
        have hm_lt: "m < q"
          unfolding q_def by simp
        have hm0: "m div q = 0"
          using hm_lt by (simp add: div_eq_0_iff)
        have hq0: "q \<noteq> 0"
          unfolding q_def by simp
        have hdiv: "(i * q + m) div q = i"
        proof -
          have "(i * q + m) div q = (m + q * i) div q"
            by (simp add: add.assoc add.commute add.left_commute mult.commute)
          also have "... = i + m div q"
            by (simp add: div_mult_self2[OF hq0])
          also have "... = i"
            using hm0 by simp
          finally show ?thesis .
        qed
        have hmod: "(i * q + m) mod q = m"
        proof -
          have "(i * q + m) mod q = (m + q * i) mod q"
            by (simp add: add.assoc add.commute add.left_commute mult.commute)
          also have "... = m mod q"
            by simp
          also have "... = m"
            using hm_lt by simp
          finally show ?thesis .
        qed
        have hnotlt: "\<not> ((i * q + m) mod q < m)"
          using hmod by simp
        show ?thesis
          unfolding F_def Let_def
          using hIf hdiv hmod hnotlt by simp
      qed
      have "(F x) (i * q + m) = (F y) (i * q + m)"
        using hEq by simp
      thus ?thesis
        using hFx hFy by simp
    qed

    have hphiy: "\<phi> i y \<noteq> 0"
      using hphiEq hphix by simp

    have hyUi: "y \<in> U i"
    proof (rule ccontr)
      assume hynot: "y \<notin> U i"
      have hy: "y \<in> X - U i"
        using hyX hynot by blast
      have "\<phi> i y = 0"
        by (rule top1_support_on_subset_imp_zero_on_complement[OF hsupp_i hy])
      thus False
        using hphiy by contradiction
    qed

    have hgi_mem: "\<forall>z\<in>U i. g i z \<in> top1_Rpow_set m"
    proof (intro ballI)
      fix z assume hz: "z \<in> U i"
      have hgi: "top1_continuous_map_on (U i) (subspace_topology X TX (U i))
          (top1_Rpow_set m) (top1_Rpow_topology m) (g i)"
        using hUcontinj hi by blast
      show "g i z \<in> top1_Rpow_set m"
        using hgi hz unfolding top1_continuous_map_on_def by blast
    qed

    have hgi_inj: "inj_on (g i) (U i)"
      using hUcontinj hi by blast

    have hcoords_eq: "\<forall>k<m. (g i x) k = (g i y) k"
    proof (intro allI impI)
      fix k assume hk: "k < m"
      have hidx: "i * q + k < N"
      proof -
        have hkq: "k < q"
          using hk by (simp add: q_def)
        have hSuc_le: "Suc i \<le> n"
          using hi by simp
        have hlt: "i * q + k < Suc i * q"
        proof -
          have "i * q + k < i * q + q"
            using hkq by simp
          thus ?thesis
            by simp
        qed
        have hle: "Suc i * q \<le> n * q"
          using hSuc_le by (rule mult_le_mono1)
        have "i * q + k < n * q"
          by (rule less_le_trans[OF hlt hle])
        thus ?thesis
          by (simp add: N_def)
      qed
      have hFx: "(F x) (i * q + k) = \<phi> i x * (g i x k)"
      proof -
        have hIf: "i * q + k < N"
          by (rule hidx)
        have hq0: "q > 0"
          by (simp add: q_def)
        have hkq: "k < q"
          using hk by (simp add: q_def)
        have hdiv0: "k div q = 0"
          using hkq hq0 by (simp add: div_eq_0_iff)
        have hdiv: "(i * q + k) div q = i"
        proof -
          have "(i * q + k) div q = (k + i * q) div q"
            by (simp add: add.commute)
          also have "... = i + k div q"
            using hq0 by simp
          also have "... = i"
            using hdiv0 by simp
          finally show ?thesis .
        qed
        have hmod: "(i * q + k) mod q = k"
        proof -
          have "(i * q + k) mod q = (k + i * q) mod q"
            by (simp add: add.commute)
          also have "... = k mod q"
            by simp
          also have "... = k"
            using hkq by simp
          finally show ?thesis .
        qed
        have hlt: "(i * q + k) mod q < m"
          using hk hmod by simp
        have hxUi': "x \<in> U ((i * q + k) div q)"
          using hxUi hdiv by simp
        show ?thesis
          unfolding F_def Let_def
          using hIf hdiv hmod hlt hxUi' by simp
      qed
      have hFy: "(F y) (i * q + k) = \<phi> i y * (g i y k)"
      proof -
        have hIf: "i * q + k < N"
          by (rule hidx)
        have hq0: "q > 0"
          by (simp add: q_def)
        have hkq: "k < q"
          using hk by (simp add: q_def)
        have hdiv0: "k div q = 0"
          using hkq hq0 by (simp add: div_eq_0_iff)
        have hdiv: "(i * q + k) div q = i"
        proof -
          have "(i * q + k) div q = (k + i * q) div q"
            by (simp add: add.commute)
          also have "... = i + k div q"
            using hq0 by simp
          also have "... = i"
            using hdiv0 by simp
          finally show ?thesis .
        qed
        have hmod: "(i * q + k) mod q = k"
        proof -
          have "(i * q + k) mod q = (k + i * q) mod q"
            by (simp add: add.commute)
          also have "... = k mod q"
            by simp
          also have "... = k"
            using hkq by simp
          finally show ?thesis .
        qed
        have hlt: "(i * q + k) mod q < m"
          using hk hmod by simp
        have hyUi': "y \<in> U ((i * q + k) div q)"
          using hyUi hdiv by simp
        show ?thesis
          unfolding F_def Let_def
          using hIf hdiv hmod hlt hyUi' by simp
      qed
      have hEqk: "(F x) (i * q + k) = (F y) (i * q + k)"
        using hEq by simp
      have hmult: "\<phi> i x * (g i x k) = \<phi> i y * (g i y k)"
        using hEqk hFx hFy by simp
      have hmult': "\<phi> i x * (g i x k) = \<phi> i x * (g i y k)"
        using hmult hphiEq by simp
      have hne: "\<phi> i x \<noteq> 0"
        by (rule hphix)
      have "inverse (\<phi> i x) * (\<phi> i x * (g i x k)) =
            inverse (\<phi> i x) * (\<phi> i x * (g i y k))"
        using hmult' by simp
      thus "(g i x) k = (g i y) k"
        using hne by (simp add: field_simps)
    qed

    have hgEq: "g i x = g i y"
    proof -
      have hxmem: "g i x \<in> top1_Rpow_set m"
        using hgi_mem hxUi by blast
      have hymem: "g i y \<in> top1_Rpow_set m"
        using hgi_mem hyUi by blast
      show ?thesis
        by (rule top1_Rpow_set_ext[OF hxmem hymem hcoords_eq])
    qed

    show "x = y"
      by (rule hgi_inj[unfolded inj_on_def, rule_format, OF hxUi hyUi], rule hgEq)
  qed

  have hTopN: "is_topology_on (top1_Rpow_set N) (top1_Rpow_topology N)"
    by (rule top1_Rpow_is_topology_on)
  have hHausN: "is_hausdorff_on (top1_Rpow_set N) (top1_Rpow_topology N)"
    by (rule top1_Rpow_is_hausdorff_on)

  have hEmbed: "top1_embedding_on X TX (top1_Rpow_set N) (top1_Rpow_topology N) F"
    by (rule top1_embedding_on_compact_inj[OF hTopX hTopN hcomp hHausN hFcont hFinj])

  show ?thesis
    apply (rule exI[where x=N])
    apply (rule exI[where x=F])
    apply (rule hEmbed)
    done
qed

text \<open>Auxiliary lemma for \<open>\<S>41\<close> (paracompact normality): closure avoidance step.
  Placed here (in Ch4) to avoid timeout in the larger Ch5\_8 theory.\<close>
lemma paracompact_closure_avoidance_step:
  assumes hTop: "is_topology_on X TX"
  assumes hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
  assumes hAX: "A \<subseteq> X"
  assumes hDCC: "D \<in> \<CC>"
  assumes hDinterB: "D \<inter> B \<noteq> {}"
  assumes hCC_ref: "\<forall>C\<in>\<CC>. \<exists>A\<in>insert (X - B) (Ub ` B). C \<subseteq> A"
  assumes hUbT: "\<forall>b\<in>B. Ub b \<in> TX"
  assumes hUb_sep: "\<forall>b\<in>B. \<exists>W. W \<in> TX \<and> A \<subseteq> W \<and> Ub b \<inter> W = {}"
  assumes hxA: "x \<in> A"
  shows "x \<notin> closure_on X TX D"
proof
  assume hxcl: "x \<in> closure_on X TX D"
  obtain E where hE1: "E \<in> insert (X - B) (Ub ` B)" and hDE: "D \<subseteq> E"
    using hCC_ref hDCC by blast
  have "E \<noteq> X - B" using hDE hDinterB by blast
  then obtain b where hbB: "b \<in> B" and hEeq: "E = Ub b" using hE1 by blast
  have hDUb: "D \<subseteq> Ub b" using hDE hEeq by simp
  obtain W where hWT: "W \<in> TX" and hAW: "A \<subseteq> W" and hUbW: "Ub b \<inter> W = {}"
    using hUb_sep hbB by blast
  have hUbX: "Ub b \<subseteq> X" using hTsub hUbT hbB by blast
  have hWX: "W \<subseteq> X" using hTsub hWT by blast
  have hXmW_sub: "X - W \<subseteq> X" by blast
  have hXmXmW: "X - (X - W) = W" using hWX by blast
  have hXmW_closed: "closedin_on X TX (X - W)"
    by (rule closedin_intro[OF hXmW_sub]) (simp only: hXmXmW, rule hWT)
  have hD_sub_XmW: "D \<subseteq> X - W" using hDUb hUbX hUbW by blast
  have hcl_D_sub: "closure_on X TX D \<subseteq> X - W"
    by (rule closure_on_subset_of_closed[OF hXmW_closed hD_sub_XmW])
  have "x \<in> W" using hAW hxA by blast
  have "x \<in> X - W" by (rule subsetD[OF hcl_D_sub hxcl])
  then show False using \<open>x \<in> W\<close> by blast
qed

end
