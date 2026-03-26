theory Top1_Ch2
  imports Complex_Main
begin


(*
  Formalization stubs (statements only, no proofs) for /mnt/data/top1.tex

  Notes:
  - This file is intended to mirror the mathematical content of top1.tex
    (Munkres, Chapter 2, §§12–17) at the level of definitions and stated results.
  - Proofs are omitted using placeholders (no axioms).
*)

section \<open>\<S>12 Topological Spaces\<close>

(** from \S12 Definition (Topology on a set) [top1.tex:49] **)
(** LATEX VERSION: "A topology on a set X is a collection T of subsets of X ..." **)
definition is_topology_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_topology_on X T \<longleftrightarrow>
     {} \<in> T \<and> X \<in> T \<and>
     (\<forall>U. U \<subseteq> T \<longrightarrow> (\<Union>U) \<in> T) \<and>
     (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> (\<Inter>F) \<in> T)"

(** Basic derived closure properties for a topology. **)
lemma topology_inter2:
  assumes hT: "is_topology_on X T"
  assumes hU: "U \<in> T"
  assumes hV: "V \<in> T"
  shows "U \<inter> V \<in> T"
proof -
  have inter_T: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have hfin: "finite {U, V}" by simp
  have hne: "{U, V} \<noteq> {}" by (rule insert_not_empty)
  have hsub: "{U, V} \<subseteq> T" using hU hV by blast
  have hInter: "\<Inter>{U, V} \<in> T"
    using inter_T hfin hne hsub by blast
  show ?thesis using hInter by simp
qed

lemma top1_open_of_local_subsets:
  assumes hTopX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hLoc: "\<forall>x\<in>A. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> A"
  shows "A \<in> TX"
proof -
  let ?G = "{U\<in>TX. U \<subseteq> A}"

  have hGsub: "?G \<subseteq> TX"
    by blast

  have hUnionT: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    using hTopX unfolding is_topology_on_def by blast

  have hUnionG: "\<Union>?G \<in> TX"
    using hUnionT hGsub by blast

  have hUnionG_sub: "\<Union>?G \<subseteq> A"
    by blast

  have hA_sub_UnionG: "A \<subseteq> \<Union>?G"
  proof (rule subsetI)
    fix x assume hx: "x \<in> A"
    obtain U where hU: "U \<in> TX" and hxU: "x \<in> U" and hUsub: "U \<subseteq> A"
      using hLoc hx by blast
    have hUinG: "U \<in> ?G"
      using hU hUsub by simp
    show "x \<in> \<Union>?G"
      using hxU hUinG by blast
  qed

  have hEq: "\<Union>?G = A"
    by (rule subset_antisym[OF hUnionG_sub hA_sub_UnionG])

  show ?thesis
    using hUnionG unfolding hEq by simp
qed

(*
  DRAFT: The following two §30 product-countability theorems were accidentally placed
  here (in §12). They are kept commented out as a reference draft; the actual
  statements (and eventual proofs) are provided later in §30.

(** from \S30 Theorem 30.2 (Countable products of first-countable spaces) [top1.tex:~3934] **)
theorem Theorem_30_2_first_countable_product:
  assumes hIcnt: "top1_countable I"
  assumes hfac: "\<forall>i\<in>I. top1_first_countable_on (X i) (T i)"
  shows "top1_first_countable_on (top1_PiE I X) (top1_product_topology_on I X T)"
proof -
  let ?Y = "top1_PiE I X"
  let ?B = "top1_product_basis_on I X T"
  let ?TP = "top1_product_topology_on I X T"

  have hIcount: "countable I"
    using hIcnt by (simp add: top1_countable_iff_countable)

  show ?thesis
    unfolding top1_first_countable_on_def top1_countable_neighborhood_basis_at_def neighborhood_of_def
  proof (intro ballI)
    fix x assume hxY: "x \<in> ?Y"
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
        using hnone by blast
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
      have hXopen: "\<forall>i\<in>I. i \<notin> {i \<in> I. A0 i \<noteq> X i} \<longrightarrow> X i \<in> T i"
      proof (intro ballI impI)
        fix i
        assume hiI: "i \<in> I"
        assume hi: "i \<notin> {i \<in> I. A0 i \<noteq> X i}"
        have hEq: "A0 i = X i"
          using hiI hi by blast
        show "X i \<in> T i"
          using hA0 hiI unfolding hEq by blast
      qed

      have hexB:
        "\<forall>i\<in>I. \<exists>Bi. top1_countable Bi
              \<and> (\<forall>U\<in>Bi. neighborhood_of (x i) (X i) (T i) U)
              \<and> (\<forall>V. neighborhood_of (x i) (X i) (T i) V \<longrightarrow> (\<exists>U\<in>Bi. U \<subseteq> V))"
      proof (intro ballI)
        fix i assume hiI: "i \<in> I"
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
      have hCcnt: "\<forall>i\<in>I. countable (C i)"
      proof (intro ballI)
        fix i assume hiI: "i \<in> I"
        have "top1_countable (B0 i)"
          using hB0 hiI by blast
        hence "top1_countable (C i)"
          unfolding C_def
          apply (rule top1_countable_subset)
          apply blast
          done
        thus "countable (C i)"
          by (simp add: top1_countable_iff_countable)
      qed
      have hSigma_cnt: "countable (SIGMA i:I. C i)"
        apply (rule countable_SIGMA[OF hIcount])
        apply (rule hCcnt)
        done
      have hLists_cnt: "countable (lists (SIGMA i:I. C i))"
        by (simp add: hSigma_cnt)

      define mkF where "mkF l = fold (λp f. f (fst p := snd p)) l A0" for l
      define mkU where "mkU l = top1_PiE I (mkF l)" for l
      define BB where "BB = mkU ` lists (SIGMA i:I. C i)"

      have hBBcnt: "top1_countable BB"
      proof -
        have "countable BB"
          unfolding BB_def by (rule countable_image) (rule hLists_cnt)
        thus ?thesis
          by (simp add: top1_countable_iff_countable)
      qed

      have hmkF_props:
        "\<forall>l\<in>lists (SIGMA i:I. C i).
            (\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i)
            \<and> finite {i \<in> I. mkF l i \<noteq> X i}"
      proof (intro ballI)
        fix l assume hl: "l \<in> lists (SIGMA i:I. C i)"

        have hP0: "\<forall>i\<in>I. A0 i \<in> T i \<and> A0 i \<subseteq> X i \<and> x i \<in> A0 i"
        proof (intro ballI)
          fix i assume hiI: "i \<in> I"
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
          obtain j U where hp: "p = (j,U)"
            by (cases p) simp
          have hps: "ps \<in> lists (SIGMA i:I. C i)"
            using Cons.prems by simp
          have hpSigma: "p \<in> (SIGMA i:I. C i)"
            using Cons.prems by simp
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
            unfolding mkF_def
            apply simp
            unfolding hp
            apply (intro ballI)
            fix i assume hiI: "i \<in> I"
            show "(mkF ps)(j := U) i \<in> T i \<and> (mkF ps)(j := U) i \<subseteq> X i \<and> x i \<in> (mkF ps)(j := U) i"
            proof (cases "i = j")
              case True
              show ?thesis
                unfolding True using hU_T hU_subX hxjU by simp
            next
              case False
              have "mkF ps i \<in> T i \<and> mkF ps i \<subseteq> X i \<and> x i \<in> mkF ps i"
                using hIH hiI by blast
              thus ?thesis
                unfolding False by simp
            qed
            done
        qed

        have hSub:
          "{i \<in> I. mkF l i \<noteq> X i} \<subseteq> {i \<in> I. A0 i \<noteq> X i} \<union> set (map fst l)"
        proof (rule subsetI)
          fix i assume hi: "i \<in> {i \<in> I. mkF l i \<noteq> X i}"
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
        fix U assume hU: "U \<in> BB"
        obtain l where hl: "l \<in> lists (SIGMA i:I. C i)" and hUeq: "U = mkU l"
          using hU unfolding BB_def by blast
        have hProps:
          "(\<forall>i\<in>I. mkF l i \<in> T i \<and> mkF l i \<subseteq> X i \<and> x i \<in> mkF l i) \<and> finite {i \<in> I. mkF l i \<noteq> X i}"
          using hmkF_props hl by blast

		        have hBasis: "mkU l \<in> ?B"
		          unfolding top1_product_basis_on_def
		          apply (rule CollectI)
		          apply (rule exI[where x="mkF l"])
		          apply (rule conjI)
		           apply (simp add: mkU_def)
		          apply (rule conjI)
		           apply (use hProps in blast)
		          apply (use hProps in blast)
		          done

        have hSubY: "mkU l \<subseteq> ?Y"
        proof -
          have hsub: "\<forall>i\<in>I. mkF l i \<subseteq> X i"
            using hProps by blast
          show ?thesis
            unfolding mkU_def
            by (rule top1_PiE_mono[OF hsub])
        qed

        have hOpen: "mkU l \<in> ?TP"
          unfolding top1_product_topology_on_def topology_generated_by_basis_def
          apply (rule CollectI)
          apply (intro conjI)
           apply (rule hSubY)
          apply (intro ballI)
          fix y assume hy: "y \<in> mkU l"
          show "\<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> mkU l"
            apply (rule bexI[where x="mkU l"])
             apply (intro conjI)
              apply (rule hy)
             apply (rule subset_refl)
            apply (rule hBasis)
            done
          done

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
        fix V assume hV: "V \<in> ?TP \<and> x \<in> V"
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
          fix i assume hiJ: "i \<in> J"
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

        define S where "S = (λi. (i, sel i)) ` J"
        have hSfin: "finite S"
          unfolding S_def by (rule finite_imageI[OF hJfin])
        have hSsub: "S \<subseteq> (SIGMA i:I. C i)"
        proof (rule subsetI)
          fix p assume hp: "p \<in> S"
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
          fix i assume hiI: "i \<in> I"
          show "mkF l i \<subseteq> U1 i"
          proof (cases "i \<in> J")
            case True
            have hpair: "(i, sel i) \<in> set l"
              using True hl unfolding S_def by blast
            have "mkF l i = sel i"
            proof (induct l)
              case Nil
              then show ?case using hpair by simp
            next
              case (Cons p ps)
              obtain j U where hp: "p = (j,U)"
                by (cases p) simp
              show ?case
              proof (cases "j = i")
                case True
                have "U = sel i"
                proof -
                  have "(i, sel i) = (j, U)"
                    using True hp hpair by simp
                  thus ?thesis by simp
                qed
                show ?thesis
                  unfolding mkF_def hp True \<open>U = sel i\<close> by simp
              next
                case False
                have hpair_ps: "(i, sel i) \<in> set ps"
                  using hpair False hp by auto
                have "mkF ps i = sel i"
                  using Cons.IH hpair_ps by blast
                thus ?thesis
                  unfolding mkF_def hp False by simp
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

  have hIcount: "countable I"
    using hIcnt by (simp add: top1_countable_iff_countable)

  have hexB: "\<forall>i\<in>I. \<exists>Bi. top1_countable Bi \<and> basis_for (X i) Bi (T i)"
    using hfac unfolding top1_second_countable_on_def by blast
  obtain B0 where hB0: "\<forall>i\<in>I. top1_countable (B0 i) \<and> basis_for (X i) (B0 i) (T i)"
    using bchoice[OF hexB] by blast

  define Sigma where "Sigma = (SIGMA i:I. B0 i)"
  have hSigma_cnt: "countable Sigma"
  proof -
    have hB0cnt: "\<forall>i\<in>I. countable (B0 i)"
      using hB0 by (simp add: top1_countable_iff_countable)
    show ?thesis
      unfolding Sigma_def
      apply (rule countable_SIGMA[OF hIcount])
      apply (rule hB0cnt)
      done
  qed

  have hTopI: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  proof (intro ballI)
    fix i
    assume hiI: "i \<in> I"
    have "basis_for (X i) (B0 i) (T i)"
      using hB0 hiI by blast
    thus "is_topology_on (X i) (T i)"
      by (rule basis_for_is_topology_on)
  qed
  have hXiTi: "\<forall>i\<in>I. X i \<in> T i"
    using hTopI unfolding is_topology_on_def by blast

  define mkF where "mkF l = fold (λp f. f (fst p := snd p)) l X" for l
  define mkU where "mkU l = top1_PiE I (mkF l)" for l
  define Cc where "Cc = mkU ` lists Sigma"

  have hCc_cnt: "top1_countable Cc"
  proof -
    have "countable (lists Sigma)"
      by (simp add: hSigma_cnt)
    hence "countable Cc"
      unfolding Cc_def by (rule countable_image)
    thus ?thesis
      by (simp add: top1_countable_iff_countable)
  qed

  have hCc_sub_TP: "Cc \<subseteq> ?TP"
  proof (rule subsetI)
    fix U assume hU: "U \<in> Cc"
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
      obtain j V where hp: "p = (j, V)"
        by (cases p) simp
      have hpSigma: "p \<in> Sigma"
        using Cons.prems by simp
      have hjI: "j \<in> I" and hV: "V \<in> B0 j"
        using hpSigma unfolding Sigma_def hp by blast+
      have hBasis: "basis_for (X j) (B0 j) (T j)"
        using hB0 hjI by blast
      have hVsub: "V \<subseteq> X j"
        using hBasis hV unfolding basis_for_def is_basis_on_def by blast
      have hVopen: "V \<in> T j"
        by (rule basis_elem_open_if_basis_for[OF hBasis hV])
      have hIH: "\<forall>i\<in>I. mkF ps i \<in> T i \<and> mkF ps i \<subseteq> X i"
        using Cons.IH Cons.prems by simp
      show ?case
        unfolding mkF_def
        apply simp
        unfolding hp
        apply (intro ballI)
        fix i assume hiI: "i \<in> I"
        show "(mkF ps)(j := V) i \<in> T i \<and> (mkF ps)(j := V) i \<subseteq> X i"
        proof (cases "i = j")
          case True
          show ?thesis
            unfolding True using hVopen hVsub by simp
        next
          case False
          show ?thesis
            using hIH hiI unfolding False by simp
        qed
        done
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
		        have hij: "i \<noteq> j" and hnotps: "i \<notin> set (map fst ps)"
		          using hnot unfolding hp by simp

	        have hrec: "mkF (p # ps) = (mkF ps)(j := V)"
	          unfolding mkF_def hp by (simp add: mkF_def[symmetric])

	        have "mkF (p # ps) i = (mkF ps)(j := V) i"
	          using hrec by simp
	        also have "\<dots> = mkF ps i"
	          using hij by simp
	        also have "\<dots> = X i"
	          using Cons.IH[OF hnotps] .
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
	      apply (intro conjI)
	       apply (simp add: mkU_def)
	      apply (rule conjI)
	       apply (rule hProps)
	      apply (rule hFin_mkF)
	      done

    have hOpen: "mkU l \<in> ?TP"
      unfolding top1_product_topology_on_def topology_generated_by_basis_def
      apply (rule CollectI)
      apply (intro conjI)
       apply (rule hSubY)
      apply (intro ballI)
      fix y assume hy: "y \<in> mkU l"
      show "\<exists>b\<in>top1_product_basis_on I X T. y \<in> b \<and> b \<subseteq> mkU l"
        apply (rule bexI[where x="mkU l"])
         apply (intro conjI)
          apply (rule hy)
         apply (rule subset_refl)
        apply (rule hBasisU)
        done
      done

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
      fix i assume hiJ: "i \<in> J"
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
    obtain sel where hsel: "\<forall>i\<in>J. sel i \<in> B0 i \<and> x i \<in> sel i \<and> sel i \<subseteq> W i"
      using bchoice[OF hexSel] by blast

    define S where "S = (λi. (i, sel i)) ` J"
    have hSfin: "finite S"
      unfolding S_def by (rule finite_imageI[OF hJfin])
    have hSsub: "S \<subseteq> Sigma"
      unfolding Sigma_def S_def by (use hsel in blast)
    obtain l where hl: "set l = S"
      using finite_list[OF hSfin] by blast
    have hlists: "l \<in> lists Sigma"
      using hl hSsub by (simp add: lists_eq_set)

    have hC: "mkU l \<in> Cc"
      unfolding Cc_def using hlists by blast

    have hsubW': "\<forall>i\<in>I. mkF l i \<subseteq> W i"
    proof (intro ballI)
      fix i assume hiI: "i \<in> I"
      show "mkF l i \<subseteq> W i"
      proof (cases "i \<in> J")
        case True
        have hpair: "(i, sel i) \<in> set l"
          using True hl unfolding S_def by blast

        have hsame: "\<forall>p\<in>set l. fst p = i \<longrightarrow> snd p = sel i"
        proof (intro ballI impI)
          fix p
          assume hp: "p \<in> set l"
          assume hfst: "fst p = i"
          have hpS: "p \<in> S"
            using hp hl by simp
          obtain j where hjJ: "j \<in> J" and hp': "p = (j, sel j)"
            using hpS unfolding S_def by blast
          have "j = i"
            using hfst unfolding hp' by simp
          thus "snd p = sel i"
            unfolding hp' by simp
        qed

        have "mkF l i = sel i"
          using hpair hsame
        proof (induct l)
          case Nil
          then show ?case by simp
        next
          case (Cons p ps)
          obtain j V where hp: "p = (j, V)"
            by (cases p) simp
          have hmem: "(i, sel i) = p \<or> (i, sel i) \<in> set ps"
            using Cons.prems(1) by simp
          have hsame_ps: "\<forall>p\<in>set ps. fst p = i \<longrightarrow> snd p = sel i"
            using Cons.prems(2) by simp
          show ?case
          proof (cases "j = i")
            case True
            have "V = sel i"
              using Cons.prems(2) True hp by simp
            thus ?thesis
              unfolding mkF_def hp True by simp
          next
            case False
            have htail: "(i, sel i) \<in> set ps"
              using hmem False hp by auto
            have "mkF ps i = sel i"
              by (rule Cons.IH[OF htail hsame_ps])
            thus ?thesis
              unfolding mkF_def hp False by simp
          qed
        qed
        moreover have "sel i \<subseteq> W i"
          using hsel True by blast
        ultimately show ?thesis
          by simp
      next
        case False
        have hnot: "i \<notin> set (map fst l)"
        proof
          assume hi: "i \<in> set (map fst l)"
          then obtain p where hp: "p \<in> set l" and hfst: "fst p = i"
            by auto
          have hpS: "p \<in> S"
            using hp hl by simp
          obtain j where hjJ: "j \<in> J" and hp': "p = (j, sel j)"
            using hpS unfolding S_def by blast
          have "i = j"
            using hfst unfolding hp' by simp
          hence "i \<in> J"
            using hjJ by simp
          thus False
            using False by contradiction
        qed

        have hmkF: "mkF l i = X i"
          using hnot
        proof (induct l)
          case Nil
          then show ?case
            by (simp add: mkF_def)
		        next
		          case (Cons p ps)
		          obtain j V where hp: "p = (j, V)"
		            by (cases p) simp
		          have hij_hnotps: "i \<noteq> j \<and> i \<notin> set (map fst ps)"
		            using Cons.prems unfolding hp by simp
		          have hij: "i \<noteq> j"
		            using hij_hnotps by (rule conjunct1)
		          have hnotps: "i \<notin> set (map fst ps)"
		            using hij_hnotps by (rule conjunct2)

          have "mkF (p # ps) i = mkF ps i"
            unfolding mkF_def hp using hij by simp
          also have "\<dots> = X i"
            using Cons.hyps[OF hnotps] .
          finally show ?case .
        qed

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
        fix i assume hiI: "i \<in> I"
        show "x i \<in> mkF l i"
        proof (cases "i \<in> J")
          case True
          have hpair: "(i, sel i) \<in> set l"
            using True hl unfolding S_def by blast
	        have "mkF l i = sel i"
	        proof (induct l)
	          case Nil
	          have False
	            using hpair by simp
	          thus ?case
	            by (rule FalseE)
	        next
	          case (Cons p ps)
	          obtain j V where hp: "p = (j, V)"
	            by (cases p) simp
            show ?case
            proof (cases "j = i")
              case True
              have "V = sel i"
              proof -
                have "(i, sel i) = (j, V)"
                  using True hp hpair by simp
                thus ?thesis by simp
              qed
              show ?thesis
                unfolding mkF_def hp True \<open>V = sel i\<close> by simp
            next
              case False
              have hpair_ps: "(i, sel i) \<in> set ps"
                using hpair False hp by auto
              have "mkF ps i = sel i"
                using Cons.IH hpair_ps by blast
              thus ?thesis
                unfolding mkF_def hp False by simp
            qed
          qed
          show ?thesis
            using hsel True unfolding \<open>mkF l i = sel i\<close> by blast
        next
          case False
          have "mkF l i = X i"
            using False hl hiI unfolding mkF_def S_def J_def by simp
          thus ?thesis
            using hxb unfolding hbdef top1_PiE_iff hiI by simp
        qed
      qed
	      show ?thesis
	        unfolding mkU_def top1_PiE_iff using hxC' by blast
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
	          by (rule subset_trans[OF subset_trans[OF hmk_sub hbU] subset_refl])
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

*)

(** Union of two open sets is open. **)
lemma topology_union2:
  assumes hT: "is_topology_on X T"
  assumes hU: "U \<in> T"
  assumes hV: "V \<in> T"
  shows "U \<union> V \<in> T"
proof -
  have union_T: "\<forall>K. K \<subseteq> T \<longrightarrow> (\<Union>K) \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have hSub: "{U, V} \<subseteq> T"
    using hU hV by simp
  have "(\<Union>{U, V}) \<in> T"
    by (rule union_T[rule_format, OF hSub])
  thus ?thesis
    by simp
qed

(** from \S12 (Open set terminology) [top1.tex:~55] **)
(** LATEX VERSION: "U is open in X iff U \<in> T." **)
definition openin_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "openin_on X T U \<longleftrightarrow> U \<in> T"

(** from \S12 Definition (Finer/coarser/comparable) [top1.tex:96] **)
(** LATEX VERSION: "T' is finer than T iff T \<subseteq> T' ..." **)
definition finer_than :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "finer_than T T' \<longleftrightarrow> T \<subseteq> T'"

definition strictly_finer_than :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "strictly_finer_than T T' \<longleftrightarrow> T \<subseteq> T' \<and> T \<noteq> T'"

definition comparable_topologies :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "comparable_topologies T T' \<longleftrightarrow> (T \<subseteq> T' \<or> T' \<subseteq> T)"


section \<open>\<S>13 Basis for a Topology\<close>

(** from \S13 Definition (Basis for a topology) [top1.tex:109] **)
(** LATEX VERSION: "B is a basis on X if (1) covers X and (2) intersection condition..." **)
definition is_basis_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_basis_on X B \<longleftrightarrow>
     (\<forall>b\<in>B. b \<subseteq> X) \<and>
     (\<forall>x\<in>X. \<exists>b\<in>B. x \<in> b) \<and>
     (\<forall>b1\<in>B. \<forall>b2\<in>B. \<forall>x\<in>(b1 \<inter> b2).
         \<exists>b3\<in>B. x \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2))"

(** from \S13 Definition (Topology generated by a basis) [top1.tex:109] **)
(** LATEX VERSION: "U is open iff for each x\<in>U there is basis element B with x\<in>B\<subseteq>U." **)
definition topology_generated_by_basis :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "topology_generated_by_basis X B =
     {U. U \<subseteq> X \<and> (\<forall>x\<in>U. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U)}"

(** Convenience: "B is a basis for T on X" [implicit throughout \S13] **)
definition basis_for :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "basis_for X B T \<longleftrightarrow> is_basis_on X B \<and> T = topology_generated_by_basis X B"

(** If B is a basis on X, then the topology it generates is a topology on X. **)
lemma topology_generated_by_basis_is_topology_on:
  assumes hB: "is_basis_on X B"
  shows "is_topology_on X (topology_generated_by_basis X B)"
proof (unfold is_topology_on_def, intro conjI)
  have hBsub: "\<forall>b\<in>B. b \<subseteq> X"
    by (rule conjunct1[OF hB[unfolded is_basis_on_def]])
  have hBcov: "\<forall>x\<in>X. \<exists>b\<in>B. x \<in> b"
    by (rule conjunct1[OF conjunct2[OF hB[unfolded is_basis_on_def]]])

  show "{} \<in> topology_generated_by_basis X B"
    unfolding topology_generated_by_basis_def
    apply (rule CollectI)
    apply (intro conjI)
     apply simp
    apply simp
    done
  show "X \<in> topology_generated_by_basis X B"
    unfolding topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "X \<subseteq> X" by simp
    show "\<forall>x\<in>X. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> X"
    proof (rule ballI)
      fix x assume hxX: "x \<in> X"
      obtain b where hbB: "b \<in> B" and hxb: "x \<in> b"
        using hBcov[rule_format, OF hxX] by blast
      have hbX: "b \<subseteq> X" using hBsub hbB by blast
      show "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> X"
        apply (rule bexI[where x=b])
         apply (intro conjI hxb hbX)
        apply (rule hbB)
        done
    qed
  qed
  show "\<forall>U. U \<subseteq> topology_generated_by_basis X B \<longrightarrow> \<Union>U \<in> topology_generated_by_basis X B"
  proof (intro allI impI)
    fix U assume hU: "U \<subseteq> topology_generated_by_basis X B"
    show "\<Union>U \<in> topology_generated_by_basis X B"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, rule conjI)
      show "\<Union>U \<subseteq> X"
        using hU unfolding topology_generated_by_basis_def by blast
      show "\<forall>x\<in>\<Union>U. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> \<Union>U"
      proof (rule ballI)
        fix x assume hx: "x \<in> \<Union>U"
        obtain V where hVU: "V \<in> U" and hxV: "x \<in> V" using hx by blast
        have hVopen: "V \<in> topology_generated_by_basis X B" using hU hVU by blast
        have hVcov: "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> V"
          using hVopen hxV unfolding topology_generated_by_basis_def by blast
        obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbV: "b \<subseteq> V"
          using hVcov by blast
        have hbU: "b \<subseteq> \<Union>U" using hbV Union_upper hVU by blast
        show "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> \<Union>U"
          apply (rule bexI[where x=b])
           apply (intro conjI hxb hbU)
          apply (rule hbB)
          done
		    qed
		  qed
		qed


  show "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> topology_generated_by_basis X B \<longrightarrow> \<Inter>F \<in> topology_generated_by_basis X B"
  proof (intro allI impI)
    fix F assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> topology_generated_by_basis X B"
    have hFin: "finite F" and hNe: "F \<noteq> {}" and hFsub: "F \<subseteq> topology_generated_by_basis X B"
      using hF by blast+

    have hBInt: "\<forall>b1\<in>B. \<forall>b2\<in>B. \<forall>x\<in>(b1 \<inter> b2).
        \<exists>b3\<in>B. x \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2)"
      using hB unfolding is_basis_on_def by blast

    have hBinInt: "\<forall>U\<in>topology_generated_by_basis X B. \<forall>V\<in>topology_generated_by_basis X B.
        (U \<inter> V) \<in> topology_generated_by_basis X B"
    proof (intro ballI)
      fix U V assume hU: "U \<in> topology_generated_by_basis X B" and hV: "V \<in> topology_generated_by_basis X B"
      show "U \<inter> V \<in> topology_generated_by_basis X B"
        unfolding topology_generated_by_basis_def
      proof (rule CollectI, rule conjI)
        show "U \<inter> V \<subseteq> X"
          using hU hV unfolding topology_generated_by_basis_def by blast
        show "\<forall>x\<in>U \<inter> V. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U \<inter> V"
        proof (rule ballI)
          fix x assume hx: "x \<in> U \<inter> V"
          have hxU: "x \<in> U" and hxV: "x \<in> V" using hx by blast+
          obtain b1 where hb1B: "b1 \<in> B" and hxb1: "x \<in> b1" and hb1U: "b1 \<subseteq> U"
            using hU hxU unfolding topology_generated_by_basis_def by blast
          obtain b2 where hb2B: "b2 \<in> B" and hxb2: "x \<in> b2" and hb2V: "b2 \<subseteq> V"
            using hV hxV unfolding topology_generated_by_basis_def by blast
          have hx12: "x \<in> b1 \<inter> b2" using hxb1 hxb2 by blast
          obtain b3 where hb3B: "b3 \<in> B" and hxb3: "x \<in> b3" and hb3sub12: "b3 \<subseteq> b1 \<inter> b2"
            using hBInt[rule_format, OF hb1B hb2B hx12] by blast
          have hb3UV: "b3 \<subseteq> U \<inter> V"
            using hb3sub12 hb1U hb2V by blast
          show "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U \<inter> V"
            apply (rule bexI[where x=b3])
             apply (intro conjI hxb3 hb3UV)
            apply (rule hb3B)
            done
        qed
      qed
    qed

    show "\<Inter>F \<in> topology_generated_by_basis X B"
      using hFin hNe hFsub
    proof (induct F rule: finite_ne_induct)
      case (singleton U)
      then show ?case by simp
    next
      case (insert U F)
      have hU: "U \<in> topology_generated_by_basis X B" using insert by blast
      have hIF: "\<Inter>F \<in> topology_generated_by_basis X B" using insert by blast
      have "U \<inter> \<Inter>F \<in> topology_generated_by_basis X B"
        using hBinInt[rule_format, OF hU hIF] by blast
      thus ?case by simp
    qed
  qed
qed

(** from \S13 Lemma 13.1 [top1.tex:168] **)
(** LATEX VERSION: "T equals the collection of all unions of elements of B." **)
theorem Lemma_13_1:
  assumes hB: "basis_for X B T"
  shows "T = { \<Union>U | U. U \<subseteq> B }"
proof -
  have hBasis: "is_basis_on X B"
    by (rule conjunct1[OF hB[unfolded basis_for_def]])
  have hBX: "\<forall>b\<in>B. b \<subseteq> X"
    by (rule conjunct1[OF hBasis[unfolded is_basis_on_def]])
  have hT_def: "T = topology_generated_by_basis X B"
    by (rule conjunct2[OF hB[unfolded basis_for_def]])
  show "T = { \<Union>U | U. U \<subseteq> B }"
  proof (rule set_eqI)
    fix W
    show "W \<in> T \<longleftrightarrow> W \<in> { \<Union>U | U. U \<subseteq> B }"
    proof (rule iffI)
      assume hW: "W \<in> T"
      have hWgen: "W \<in> topology_generated_by_basis X B"
        using hW hT_def by simp
      have hWcov: "\<forall>x\<in>W. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> W"
        using hWgen unfolding topology_generated_by_basis_def by blast
      have hUnion: "W = \<Union>{b \<in> B. b \<subseteq> W}"
      proof (rule set_eqI)
        fix x
        show "x \<in> W \<longleftrightarrow> x \<in> \<Union>{b \<in> B. b \<subseteq> W}"
        proof (rule iffI)
          assume hxW: "x \<in> W"
          obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
            using hWcov[rule_format, OF hxW] by blast
          show "x \<in> \<Union>{b \<in> B. b \<subseteq> W}"
            using hbB hbW hxb by blast
        next
          assume hx: "x \<in> \<Union>{b \<in> B. b \<subseteq> W}"
          then show "x \<in> W" by blast
        qed
      qed
      show "W \<in> { \<Union>U | U. U \<subseteq> B }"
        using hUnion by blast
    next
      assume hW: "W \<in> { \<Union>U | U. U \<subseteq> B }"
      obtain U where hWU: "W = \<Union>U" and hUB: "U \<subseteq> B" using hW by blast
      have hWgen: "W \<in> topology_generated_by_basis X B"
        unfolding topology_generated_by_basis_def
      proof (rule CollectI, rule conjI)
        show "W \<subseteq> X"
          using hUB hBX hWU by blast
        show "\<forall>x\<in>W. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> W"
        proof (rule ballI)
          fix x assume hxW: "x \<in> W"
          obtain b where hbU: "b \<in> U" and hxb: "x \<in> b"
            using hxW hWU by blast
          have hbB: "b \<in> B" using hbU hUB by blast
          have hbW: "b \<subseteq> W" using hbU hWU by blast
          show "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> W"
            apply (rule bexI[where x=b])
             apply (rule conjI[OF hxb hbW])
            apply (rule hbB)
            done
        qed
      qed
      show "W \<in> T" using hWgen hT_def by simp
    qed
  qed
qed

(** Minimality: if a topology contains the basis, it contains the topology generated by the basis. **)
lemma topology_generated_by_basis_subset:
  assumes hTop: "is_topology_on X T"
  assumes hBsub: "B \<subseteq> T"
  shows "topology_generated_by_basis X B \<subseteq> T"
proof (rule subsetI)
  fix U assume hU: "U \<in> topology_generated_by_basis X B"

  have union_T: "\<forall>K. K \<subseteq> T \<longrightarrow> (\<Union>K) \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])

  define K where "K = {b \<in> B. b \<subseteq> U}"
  have hKsubT: "K \<subseteq> T"
    unfolding K_def using hBsub by blast

  have hUeq: "U = \<Union>K"
  proof (rule set_eqI)
    fix x
    show "x \<in> U \<longleftrightarrow> x \<in> \<Union>K"
    proof (rule iffI)
      assume hxU: "x \<in> U"
      obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
        using hU hxU unfolding topology_generated_by_basis_def by blast
      show "x \<in> \<Union>K"
        unfolding K_def using hbB hbU hxb by blast
    next
      assume hx: "x \<in> \<Union>K"
      then show "x \<in> U"
        unfolding K_def by blast
    qed
  qed

  have "(\<Union>K) \<in> T"
    using union_T hKsubT by blast
  thus "U \<in> T"
    using hUeq by simp
qed

(** from \S13 Lemma 13.2 [top1.tex:176] **)
(** LATEX VERSION: "If C is a collection of open sets with local refinement property, then C is a basis." **)
theorem Lemma_13_2:
  assumes hT: "is_topology_on X T"
  assumes hCcT: "Cc \<subseteq> T"
  assumes hTX: "\<forall>U\<in>T. U \<subseteq> X"
  assumes hrefine: "\<And>U x. U \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>C\<in>Cc. C \<in> T \<and> x \<in> C \<and> C \<subseteq> U"
  shows "basis_for X Cc T"
proof -
  have hXT: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
  have hunion: "\<forall>U. U \<subseteq> T \<longrightarrow> \<Union>U \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have hinter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have hbas: "is_basis_on X Cc"
  proof -
    have hc_sub: "\<forall>c\<in>Cc. c \<subseteq> X"
    proof (rule ballI)
      fix c assume hc: "c \<in> Cc"
      have hcT: "c \<in> T" using hCcT hc by blast
      show "c \<subseteq> X" using hTX hcT by blast
    qed
    have hcov: "\<forall>x\<in>X. \<exists>c\<in>Cc. x \<in> c"
    proof (rule ballI)
      fix x assume hxX: "x \<in> X"
      obtain C where hCCc: "C \<in> Cc" and hxC: "x \<in> C"
        using hrefine[OF hXT hxX] by blast
      show "\<exists>c\<in>Cc. x \<in> c" using hCCc hxC by blast
    qed
    have hinter_cond: "\<forall>c1\<in>Cc. \<forall>c2\<in>Cc. \<forall>y\<in>(c1 \<inter> c2). \<exists>c3\<in>Cc. y \<in> c3 \<and> c3 \<subseteq> (c1 \<inter> c2)"
    proof (intro ballI)
      fix c1 c2 assume hc1: "c1 \<in> Cc" and hc2: "c2 \<in> Cc"
      fix y assume hy: "y \<in> c1 \<inter> c2"
      have hc1T: "c1 \<in> T" using hCcT hc1 by blast
      have hc2T: "c2 \<in> T" using hCcT hc2 by blast
      have hc12T: "c1 \<inter> c2 \<in> T"
      proof -
        have hF: "{c1, c2} \<subseteq> T" using hc1T hc2T by blast
        have hIT: "\<Inter>{c1, c2} \<in> T"
          apply (rule hinter[rule_format])
          apply (intro conjI)
            apply simp
           apply (rule insert_not_empty)
          apply (rule hF)
          done
        show "c1 \<inter> c2 \<in> T" using hIT by simp
      qed
      obtain C where hCCc: "C \<in> Cc" and hyC: "y \<in> C" and hCsub: "C \<subseteq> c1 \<inter> c2"
        using hrefine[OF hc12T hy] by blast
      show "\<exists>c3\<in>Cc. y \<in> c3 \<and> c3 \<subseteq> c1 \<inter> c2" using hCCc hyC hCsub by blast
    qed
    show "is_basis_on X Cc"
      unfolding is_basis_on_def
      apply (intro conjI)
        apply (rule hc_sub)
       apply (rule hcov)
      apply (rule hinter_cond)
      done
  qed
  have hTeq: "T = topology_generated_by_basis X Cc"
  proof (rule set_eqI)
    fix W
    show "W \<in> T \<longleftrightarrow> W \<in> topology_generated_by_basis X Cc"
    proof (rule iffI)
      assume hWT: "W \<in> T"
      show "W \<in> topology_generated_by_basis X Cc"
        unfolding topology_generated_by_basis_def
      proof (rule CollectI, rule conjI)
        show "W \<subseteq> X" using hTX hWT by blast
      next
        show "\<forall>x\<in>W. \<exists>c\<in>Cc. x \<in> c \<and> c \<subseteq> W"
        proof (rule ballI)
          fix x assume hxW: "x \<in> W"
          obtain C where hCCc: "C \<in> Cc" and hxC: "x \<in> C" and hCW: "C \<subseteq> W"
            using hrefine[OF hWT hxW] by blast
          show "\<exists>c\<in>Cc. x \<in> c \<and> c \<subseteq> W" using hCCc hxC hCW by blast
        qed
      qed
    next
      assume hWtgb: "W \<in> topology_generated_by_basis X Cc"
      have hWcov: "\<forall>x\<in>W. \<exists>c\<in>Cc. x \<in> c \<and> c \<subseteq> W"
        using hWtgb unfolding topology_generated_by_basis_def by blast
      have hWeq: "W = \<Union>{C \<in> Cc. C \<subseteq> W}"
      proof (rule set_eqI)
        fix z
        show "z \<in> W \<longleftrightarrow> z \<in> \<Union>{C \<in> Cc. C \<subseteq> W}"
        proof (rule iffI)
          assume hzW: "z \<in> W"
          obtain C where hCCc: "C \<in> Cc" and hzC: "z \<in> C" and hCW: "C \<subseteq> W"
            using hWcov[rule_format, OF hzW] by blast
          show "z \<in> \<Union>{C \<in> Cc. C \<subseteq> W}" using hCCc hzC hCW by blast
        next
          assume hz: "z \<in> \<Union>{C \<in> Cc. C \<subseteq> W}"
          obtain C where hCmem: "C \<in> {C \<in> Cc. C \<subseteq> W}" and hzC: "z \<in> C" using hz by blast
          show "z \<in> W" using hzC hCmem by blast
        qed
      qed
      have hsubT: "{C \<in> Cc. C \<subseteq> W} \<subseteq> T" using hCcT by blast
      have hbigT: "\<Union>{C \<in> Cc. C \<subseteq> W} \<in> T" using hunion[rule_format, OF hsubT] by blast
      show "W \<in> T" using hWeq hbigT by simp
    qed
  qed
  show "basis_for X Cc T"
    unfolding basis_for_def
    apply (intro conjI)
     apply (rule hbas)
    apply (rule hTeq)
    done
qed

(** from \S13 Lemma 13.3 [top1.tex:184] **)
(** LATEX VERSION: "Criterion for T' finer than T in terms of bases." **)
theorem Lemma_13_3:
  assumes hB: "basis_for X B T"
  assumes hB': "basis_for X B' T'"
  shows "finer_than T T' \<longleftrightarrow>
    (\<forall>x\<in>X. \<forall>b\<in>B. x \<in> b \<longrightarrow> (\<exists>b'\<in>B'. x \<in> b' \<and> b' \<subseteq> b))"
proof -
  have hBasis: "is_basis_on X B"
    by (rule conjunct1[OF hB[unfolded basis_for_def]])
  have hBX: "\<forall>b\<in>B. b \<subseteq> X"
    by (rule conjunct1[OF hBasis[unfolded is_basis_on_def]])
  have hInter: "\<forall>b1\<in>B. \<forall>b2\<in>B. \<forall>y\<in>(b1 \<inter> b2). \<exists>b3\<in>B. y \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2)"
    by (rule conjunct2[OF conjunct2[OF hBasis[unfolded is_basis_on_def]]])
  have hT_def: "T = topology_generated_by_basis X B"
    by (rule conjunct2[OF hB[unfolded basis_for_def]])
  have hT'_def: "T' = topology_generated_by_basis X B'"
    by (rule conjunct2[OF hB'[unfolded basis_for_def]])
  (* Every basis element of B is open in T *)
  have basis_open: "\<forall>b\<in>B. b \<in> T"
  proof (rule ballI)
    fix b assume hbB: "b \<in> B"
    have hbX: "b \<subseteq> X" by (rule bspec[OF hBX, OF hbB])
    have hbT: "b \<in> topology_generated_by_basis X B"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule hbX)
      show "\<forall>y\<in>b. \<exists>b'\<in>B. y \<in> b' \<and> b' \<subseteq> b"
      proof (rule ballI)
        fix y assume hyb: "y \<in> b"
        obtain b3 where hb3B: "b3 \<in> B" and hyb3: "y \<in> b3" and hb3sub: "b3 \<subseteq> b \<inter> b"
          using hInter[rule_format, OF hbB, OF hbB] hyb by blast
        have hb3sub': "b3 \<subseteq> b" using hb3sub by (simp only: Int_absorb)
        show "\<exists>b'\<in>B. y \<in> b' \<and> b' \<subseteq> b"
          apply (rule bexI[where x=b3])
           apply (rule conjI[OF hyb3 hb3sub'])
          apply (rule hb3B)
          done
      qed
    qed
    show "b \<in> T" using hbT hT_def by simp
  qed
  show "finer_than T T' \<longleftrightarrow>
    (\<forall>x\<in>X. \<forall>b\<in>B. x \<in> b \<longrightarrow> (\<exists>b'\<in>B'. x \<in> b' \<and> b' \<subseteq> b))"
    unfolding finer_than_def
  proof (rule iffI)
    (* T \<subseteq> T' \<Longrightarrow> criterion *)
    assume hTT': "T \<subseteq> T'"
    show "\<forall>x\<in>X. \<forall>b\<in>B. x \<in> b \<longrightarrow> (\<exists>b'\<in>B'. x \<in> b' \<and> b' \<subseteq> b)"
    proof (intro ballI impI)
      fix x b assume hxX: "x \<in> X" and hbB: "b \<in> B" and hxb: "x \<in> b"
      have hbT: "b \<in> T" by (rule bspec[OF basis_open, OF hbB])
      have hbT': "b \<in> T'" by (rule subsetD[OF hTT', OF hbT])
      have hbcov: "\<forall>y\<in>b. \<exists>b'\<in>B'. y \<in> b' \<and> b' \<subseteq> b"
        using hbT' hT'_def unfolding topology_generated_by_basis_def by blast
      show "\<exists>b'\<in>B'. x \<in> b' \<and> b' \<subseteq> b"
        by (rule hbcov[rule_format, OF hxb])
    qed
  next
    (* criterion \<Longrightarrow> T \<subseteq> T' *)
    assume hcrit: "\<forall>x\<in>X. \<forall>b\<in>B. x \<in> b \<longrightarrow> (\<exists>b'\<in>B'. x \<in> b' \<and> b' \<subseteq> b)"
    show "T \<subseteq> T'"
    proof (rule subsetI)
      fix W assume hW: "W \<in> T"
      have hWsub: "W \<subseteq> X" and hWcov: "\<forall>x\<in>W. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> W"
        using hW hT_def unfolding topology_generated_by_basis_def by blast+
      have hWgen: "W \<in> topology_generated_by_basis X B'"
        unfolding topology_generated_by_basis_def
      proof (rule CollectI, rule conjI, rule hWsub)
        show "\<forall>x\<in>W. \<exists>b'\<in>B'. x \<in> b' \<and> b' \<subseteq> W"
        proof (rule ballI)
          fix x assume hxW: "x \<in> W"
          have hxX: "x \<in> X" by (rule subsetD[OF hWsub, OF hxW])
          obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
            using hWcov[rule_format, OF hxW] by blast
          obtain b' where hb'B': "b' \<in> B'" and hxb': "x \<in> b'" and hb'b: "b' \<subseteq> b"
            using hcrit[rule_format, OF hxX, OF hbB, OF hxb] by blast
          show "\<exists>b'\<in>B'. x \<in> b' \<and> b' \<subseteq> W"
            apply (rule bexI[where x=b'])
             apply (rule conjI[OF hxb'])
             apply (rule subset_trans[OF hb'b, OF hbW])
            apply (rule hb'B')
            done
        qed
      qed
      show "W \<in> T'" using hWgen hT'_def by simp
    qed
  qed
qed


subsection \<open>Standard, lower limit, and K-topologies on \<real>\<close>

(** from \S13 Definition (standard, lower limit, K-topology) [top1.tex:205] **)
(** LATEX VERSION: "standard basis (a,b); lower limit basis [a,b); K basis (a,b) and (a,b)-K." **)

definition interval_open :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "interval_open a b = {x. a < x \<and> x < b}"

definition interval_half_open_left_closed :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "interval_half_open_left_closed a b = {x. a \<le> x \<and> x < b}"

definition K_set :: "real set" where
  "K_set = {x. \<exists>n::nat. n > 0 \<and> x = 1 / real n}"

definition basis_standard_R :: "real set set" where
  "basis_standard_R = { interval_open a b | a b. a < b }"

definition basis_lower_limit_R :: "real set set" where
  "basis_lower_limit_R = { interval_half_open_left_closed a b | a b. a < b }"

definition basis_K_topology_R :: "real set set" where
  "basis_K_topology_R =
     ({ interval_open a b | a b. a < b } \<union>
      { interval_open a b - K_set | a b. a < b })"

definition topology_standard_R :: "real set set" where
  "topology_standard_R = topology_generated_by_basis UNIV basis_standard_R"

definition topology_lower_limit_R :: "real set set" where
  "topology_lower_limit_R = topology_generated_by_basis UNIV basis_lower_limit_R"

definition topology_K_R :: "real set set" where
  "topology_K_R = topology_generated_by_basis UNIV basis_K_topology_R"

(** from \S13 Lemma 13.4 [top1.tex:221] **)
(** LATEX VERSION: "R_l and R_K are strictly finer than standard, but not comparable." **)
theorem Lemma_13_4:
  shows "strictly_finer_than topology_standard_R topology_lower_limit_R
       \<and> strictly_finer_than topology_standard_R topology_K_R
       \<and> \<not> comparable_topologies topology_lower_limit_R topology_K_R"
proof -
  define L where "L = interval_half_open_left_closed 0 1"
  define K0 where "K0 = interval_open (-1) 1 - K_set"

  have h_std_sub_ll: "topology_standard_R \<subseteq> topology_lower_limit_R"
    unfolding topology_standard_R_def topology_lower_limit_R_def
  proof (rule subsetI)
    fix W assume hW: "W \<in> topology_generated_by_basis UNIV basis_standard_R"
    have hWcov: "\<forall>x\<in>W. \<exists>b\<in>basis_standard_R. x \<in> b \<and> b \<subseteq> W"
      using hW unfolding topology_generated_by_basis_def by blast
    show "W \<in> topology_generated_by_basis UNIV basis_lower_limit_R"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule subset_UNIV)
      show "\<forall>x\<in>W. \<exists>b\<in>basis_lower_limit_R. x \<in> b \<and> b \<subseteq> W"
      proof (rule ballI)
        fix x assume hxW: "x \<in> W"
        obtain b where hbB: "b \<in> basis_standard_R" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
          using hWcov[rule_format, OF hxW] by blast
        obtain a c where hac: "a < c" and hbeq: "b = interval_open a c"
          using hbB unfolding basis_standard_R_def by blast
        have hxac: "a < x \<and> x < c"
          using hxb unfolding hbeq interval_open_def by simp
        have hax: "a < x" by (rule conjunct1[OF hxac])
        have hxc: "x < c" by (rule conjunct2[OF hxac])
        have hb'B: "interval_half_open_left_closed x c \<in> basis_lower_limit_R"
          unfolding basis_lower_limit_R_def
          apply (rule CollectI)
          apply (rule exI[where x=x], rule exI[where x=c])
          apply (intro conjI refl)
           apply (rule hxc)
          done
        have hxb': "x \<in> interval_half_open_left_closed x c"
          unfolding interval_half_open_left_closed_def using hxc by simp
        have hb'sub: "interval_half_open_left_closed x c \<subseteq> b"
        proof (rule subsetI)
          fix y assume hy: "y \<in> interval_half_open_left_closed x c"
          have hxy: "x \<le> y" and hyc: "y < c"
            using hy unfolding interval_half_open_left_closed_def by blast+
          have hay: "a < y" using hax hxy by linarith
          show "y \<in> b"
            unfolding hbeq interval_open_def using hay hyc by simp
        qed
        have hb'W: "interval_half_open_left_closed x c \<subseteq> W"
          by (rule subset_trans[OF hb'sub, OF hbW])
        show "\<exists>ba\<in>basis_lower_limit_R. x \<in> ba \<and> ba \<subseteq> W"
          apply (rule bexI[where x="interval_half_open_left_closed x c"])
           apply (intro conjI hxb' hb'W)
          apply (rule hb'B)
          done
      qed
    qed
  qed

  have h_std_sub_k: "topology_standard_R \<subseteq> topology_K_R"
    unfolding topology_standard_R_def topology_K_R_def
  proof (rule subsetI)
    fix W assume hW: "W \<in> topology_generated_by_basis UNIV basis_standard_R"
    have hWcov: "\<forall>x\<in>W. \<exists>b\<in>basis_standard_R. x \<in> b \<and> b \<subseteq> W"
      using hW unfolding topology_generated_by_basis_def by blast
    show "W \<in> topology_generated_by_basis UNIV basis_K_topology_R"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule subset_UNIV)
      show "\<forall>x\<in>W. \<exists>b\<in>basis_K_topology_R. x \<in> b \<and> b \<subseteq> W"
      proof (rule ballI)
        fix x assume hxW: "x \<in> W"
        obtain b where hbB: "b \<in> basis_standard_R" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
          using hWcov[rule_format, OF hxW] by blast
        obtain a c where hac: "a < c" and hbeq: "b = interval_open a c"
          using hbB unfolding basis_standard_R_def by blast
        have hbK: "b \<in> basis_K_topology_R"
          unfolding basis_K_topology_R_def
          apply (rule UnI1)
          unfolding basis_standard_R_def
          apply (rule CollectI)
          apply (rule exI[where x=a], rule exI[where x=c])
          apply (simp add: hbeq hac)
          done
        show "\<exists>ba\<in>basis_K_topology_R. x \<in> ba \<and> ba \<subseteq> W"
          apply (rule bexI[where x=b])
           apply (intro conjI hxb hbW)
          apply (rule hbK)
          done
      qed
    qed
  qed

  have hL_in_ll: "L \<in> topology_lower_limit_R"
    unfolding L_def topology_lower_limit_R_def topology_generated_by_basis_def
    apply (rule CollectI, rule conjI, rule subset_UNIV, rule ballI)
    apply (rule bexI[where x="interval_half_open_left_closed 0 1"])
     apply (intro conjI)
      apply assumption
     apply (rule subset_refl)
    unfolding basis_lower_limit_R_def
    apply (rule CollectI)
    apply (rule exI[where x=0], rule exI[where x=1])
    apply simp
    done

  have hL_not_std: "L \<notin> topology_standard_R"
  proof
    assume hL: "L \<in> topology_standard_R"
    have hLcov: "\<forall>x\<in>L. \<exists>b\<in>basis_standard_R. x \<in> b \<and> b \<subseteq> L"
      using hL unfolding topology_standard_R_def topology_generated_by_basis_def by blast
    have h0L: "0 \<in> L" unfolding L_def interval_half_open_left_closed_def by simp
    obtain b where hbB: "b \<in> basis_standard_R" and h0b: "0 \<in> b" and hbL: "b \<subseteq> L"
      using hLcov[rule_format, OF h0L] by blast
    obtain a c where hac: "a < c" and hbeq: "b = interval_open a c"
      using hbB unfolding basis_standard_R_def by blast
    have h0ac: "a < 0 \<and> 0 < c"
      using h0b unfolding hbeq interval_open_def by simp
    have ha0: "a < 0" by (rule conjunct1[OF h0ac])
    have h0c: "0 < c" by (rule conjunct2[OF h0ac])
    let ?y = "a / 2"
    have hay: "a < ?y" using ha0 by linarith
    have hy0: "?y < 0" using ha0 by linarith
    have hyc: "?y < c" using hy0 h0c by linarith
    have hyb: "?y \<in> b"
      unfolding hbeq interval_open_def using hay hyc by simp
    have hyL: "?y \<in> L" using hbL hyb by blast
    have hyL0: "0 \<le> ?y"
      using hyL unfolding L_def interval_half_open_left_closed_def by simp
    show False using hyL0 hy0 by linarith
  qed

  have hK0_in_k: "K0 \<in> topology_K_R"
    unfolding K0_def topology_K_R_def topology_generated_by_basis_def
    apply (rule CollectI, rule conjI, rule subset_UNIV, rule ballI)
    apply (rule bexI[where x="interval_open (-1) 1 - K_set"])
     apply (intro conjI)
      apply assumption
     apply (rule subset_refl)
    unfolding basis_K_topology_R_def
    apply (rule UnI2)
    apply (rule CollectI)
    apply (rule exI[where x="-1"], rule exI[where x=1])
    apply simp
    done

  have hK0_not_std: "K0 \<notin> topology_standard_R"
  proof
    assume hK0: "K0 \<in> topology_standard_R"
    have hcov: "\<forall>x\<in>K0. \<exists>b\<in>basis_standard_R. x \<in> b \<and> b \<subseteq> K0"
      using hK0 unfolding topology_standard_R_def topology_generated_by_basis_def by blast
    have h0K0: "0 \<in> K0"
      unfolding K0_def interval_open_def K_set_def by simp
    obtain b where hbB: "b \<in> basis_standard_R" and h0b: "0 \<in> b" and hbsub: "b \<subseteq> K0"
      using hcov[rule_format, OF h0K0] by blast
    obtain a c where hac: "a < c" and hbeq: "b = interval_open a c"
      using hbB unfolding basis_standard_R_def by blast
    have h0ac: "a < 0 \<and> 0 < c"
      using h0b unfolding hbeq interval_open_def by simp
    have ha0: "a < 0" by (rule conjunct1[OF h0ac])
    have h0c: "0 < c" by (rule conjunct2[OF h0ac])
    have hminpos: "0 < min c 1" using h0c by simp
    obtain n where hn0: "n > 0" and hninvc: "inverse (of_nat n) < min c 1"
      using ex_inverse_of_nat_less[OF hminpos] by blast
    have hninvc': "inverse (real n) < c"
      using hninvc by simp
    have hninvc_div: "1 / real n < c"
      using hninvc'
      apply (simp add: divide_inverse)
      done
    have hnpos: "0 < (1 / real n)"
      using hn0 by simp
    have ha_lt: "a < (1 / real n)" using ha0 hnpos by linarith
    have hx_in_b: "(1 / real n) \<in> b"
      unfolding hbeq interval_open_def using ha_lt hninvc_div by simp
    have hx_in_K0: "(1 / real n) \<in> K0" using hbsub hx_in_b by blast
    have hx_in_Kset: "(1 / real n) \<in> K_set"
      unfolding K_set_def using hn0 by blast
    show False using hx_in_K0 hx_in_Kset unfolding K0_def by blast
  qed

  have hL_not_k: "L \<notin> topology_K_R"
  proof
    assume hL: "L \<in> topology_K_R"
    have hcov: "\<forall>x\<in>L. \<exists>b\<in>basis_K_topology_R. x \<in> b \<and> b \<subseteq> L"
      using hL unfolding topology_K_R_def topology_generated_by_basis_def by blast
    have h0L: "0 \<in> L" unfolding L_def interval_half_open_left_closed_def by simp
    obtain b where hbB: "b \<in> basis_K_topology_R" and h0b: "0 \<in> b" and hbL: "b \<subseteq> L"
      using hcov[rule_format, OF h0L] by blast
    obtain a c where hac: "a < c" and hcase:
      "b = interval_open a c \<or> b = interval_open a c - K_set"
      using hbB unfolding basis_K_topology_R_def by blast
    have ha0: "a < 0"
      using h0b hcase unfolding interval_open_def by blast
    let ?y = "a / 2"
    have hy0: "?y < 0" using ha0 by linarith
    have hay: "a < ?y" using ha0 by linarith
    have h0c: "0 < c"
    proof (cases "b = interval_open a c")
      case True
      show ?thesis using h0b True unfolding interval_open_def by simp
    next
      case False
      have hb: "b = interval_open a c - K_set" using hcase False by blast
      have "0 \<in> interval_open a c"
        using h0b unfolding hb by simp
      thus ?thesis unfolding interval_open_def by simp
    qed
    have hyc: "?y < c" using hy0 h0c by linarith
    have hyb: "?y \<in> b"
    proof (cases "b = interval_open a c")
      case True
      show ?thesis
        unfolding True interval_open_def using hay hyc by simp
    next
      case False
      have "b = interval_open a c - K_set" using hcase False by blast
      show ?thesis
        unfolding \<open>b = interval_open a c - K_set\<close> interval_open_def K_set_def
        using hay hyc hy0 by auto
    qed
    have hyL: "?y \<in> L" using hbL hyb by blast
    have hyL0: "0 \<le> ?y"
      using hyL unfolding L_def interval_half_open_left_closed_def by simp
    show False using hyL0 hy0 by linarith
  qed

  have hK0_not_ll: "K0 \<notin> topology_lower_limit_R"
  proof
    assume hK0: "K0 \<in> topology_lower_limit_R"
    have hcov: "\<forall>x\<in>K0. \<exists>b\<in>basis_lower_limit_R. x \<in> b \<and> b \<subseteq> K0"
      using hK0 unfolding topology_lower_limit_R_def topology_generated_by_basis_def by blast
    have h0K0: "0 \<in> K0"
      unfolding K0_def interval_open_def K_set_def by simp
    obtain b where hbB: "b \<in> basis_lower_limit_R" and h0b: "0 \<in> b" and hbsub: "b \<subseteq> K0"
      using hcov[rule_format, OF h0K0] by blast
    obtain a c where hac: "a < c" and hbeq: "b = interval_half_open_left_closed a c"
      using hbB unfolding basis_lower_limit_R_def by blast
    have h0ac: "a \<le> 0 \<and> 0 < c"
      using h0b unfolding hbeq interval_half_open_left_closed_def by simp
    have ha0: "a \<le> 0" by (rule conjunct1[OF h0ac])
    have h0c: "0 < c" by (rule conjunct2[OF h0ac])
    have hminpos: "0 < min c 1" using h0c by simp
    obtain n where hn0: "n > 0" and hninvc: "inverse (of_nat n) < min c 1"
      using ex_inverse_of_nat_less[OF hminpos] by blast
    have hn_lt_c_inv: "inverse (real n) < c"
      using hninvc by simp
    have hn_lt_c: "1 / real n < c"
      using hn_lt_c_inv
      apply (simp add: divide_inverse)
      done
    have h0le: "0 \<le> (1 / real n)"
      using hn0 by simp
    have hn_ge_a: "a \<le> (1 / real n)"
      by (rule order_trans[OF ha0 h0le])
    have hx_in_b: "(1 / real n) \<in> b"
      unfolding hbeq interval_half_open_left_closed_def using hn_ge_a hn_lt_c by simp
    have hx_in_K0: "(1 / real n) \<in> K0" using hbsub hx_in_b by blast
    have hx_in_Kset: "(1 / real n) \<in> K_set"
      unfolding K_set_def using hn0 by blast
    show False using hx_in_K0 hx_in_Kset unfolding K0_def by blast
  qed

  have hstrict_ll: "strictly_finer_than topology_standard_R topology_lower_limit_R"
    unfolding strictly_finer_than_def
  proof (intro conjI)
    show "topology_standard_R \<subseteq> topology_lower_limit_R" by (rule h_std_sub_ll)
    show "topology_standard_R \<noteq> topology_lower_limit_R"
    proof
      assume hEq: "topology_standard_R = topology_lower_limit_R"
      have "L \<in> topology_standard_R" using hL_in_ll hEq by simp
      thus False using hL_not_std by contradiction
    qed
  qed

  have hstrict_k: "strictly_finer_than topology_standard_R topology_K_R"
    unfolding strictly_finer_than_def
  proof (intro conjI)
    show "topology_standard_R \<subseteq> topology_K_R" by (rule h_std_sub_k)
    show "topology_standard_R \<noteq> topology_K_R"
    proof
      assume hEq: "topology_standard_R = topology_K_R"
      have "K0 \<in> topology_standard_R" using hK0_in_k hEq by simp
      thus False using hK0_not_std by contradiction
    qed
  qed

  have hnotcomp: "\<not> comparable_topologies topology_lower_limit_R topology_K_R"
    unfolding comparable_topologies_def
  proof
    assume hcomp: "topology_lower_limit_R \<subseteq> topology_K_R \<or> topology_K_R \<subseteq> topology_lower_limit_R"
    have h1: "\<not> topology_lower_limit_R \<subseteq> topology_K_R"
    proof
      assume hsub: "topology_lower_limit_R \<subseteq> topology_K_R"
      have "L \<in> topology_K_R" using hsub hL_in_ll by blast
      thus False using hL_not_k by contradiction
    qed
    have h2: "\<not> topology_K_R \<subseteq> topology_lower_limit_R"
    proof
      assume hsub: "topology_K_R \<subseteq> topology_lower_limit_R"
      have "K0 \<in> topology_lower_limit_R" using hsub hK0_in_k by blast
      thus False using hK0_not_ll by contradiction
    qed
    show False using hcomp h1 h2 by blast
  qed

  show ?thesis using hstrict_ll hstrict_k hnotcomp by blast
qed

(** Any basis element is open in the topology generated by that basis. **)
lemma basis_elem_open_in_generated_topology:
  assumes hB: "is_basis_on X B"
  assumes hb: "b \<in> B"
  shows "b \<in> topology_generated_by_basis X B"
proof -
  have hBsub: "\<forall>c\<in>B. c \<subseteq> X"
    using hB unfolding is_basis_on_def by blast
  have hbX: "b \<subseteq> X"
    by (rule bspec[OF hBsub hb])
  show ?thesis
    unfolding topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "b \<subseteq> X" by (rule hbX)
    show "\<forall>x\<in>b. \<exists>c\<in>B. x \<in> c \<and> c \<subseteq> b"
    proof (intro ballI)
      fix x assume hx: "x \<in> b"
      show "\<exists>c\<in>B. x \<in> c \<and> c \<subseteq> b"
        apply (rule bexI[where x=b])
         apply (intro conjI)
          apply (rule hx)
         apply (rule subset_refl)
        apply (rule hb)
        done
    qed
  qed
qed

(** If \<open>B\<close> is a basis for \<open>T\<close> on \<open>X\<close>, then \<open>T\<close> is a topology on \<open>X\<close>. **)
lemma basis_for_is_topology_on:
  assumes hB: "basis_for X B T"
  shows "is_topology_on X T"
proof -
  have hBasis: "is_basis_on X B"
    using hB unfolding basis_for_def by blast
  have hTeq: "T = topology_generated_by_basis X B"
    using hB unfolding basis_for_def by blast
  show ?thesis
    unfolding hTeq
    by (rule topology_generated_by_basis_is_topology_on[OF hBasis])
qed

(** Any basis element is open in the topology for which it is a basis. **)
lemma basis_elem_open_if_basis_for:
  assumes hB: "basis_for X B T"
  assumes hb: "b \<in> B"
  shows "b \<in> T"
proof -
  have hBasis: "is_basis_on X B"
    using hB unfolding basis_for_def by blast
  have hTeq: "T = topology_generated_by_basis X B"
    using hB unfolding basis_for_def by blast
  have hbopen: "b \<in> topology_generated_by_basis X B"
    by (rule basis_elem_open_in_generated_topology[OF hBasis hb])
  show ?thesis
    unfolding hTeq using hbopen by simp
qed

(** Local refinement property for a basis: every open neighbourhood contains a basis element around the point. **)
lemma basis_for_refine:
  assumes hB: "basis_for X B T"
  assumes hU: "U \<in> T"
  assumes hx: "x \<in> U"
  shows "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U"
proof -
  have hTeq: "T = topology_generated_by_basis X B"
    using hB unfolding basis_for_def by blast
  have hUgen: "U \<in> topology_generated_by_basis X B"
    using hU unfolding hTeq by simp
  show ?thesis
    using hUgen hx unfolding topology_generated_by_basis_def by blast
qed


subsection \<open>Subbasis\<close>

(** from \S13 Definition (Subbasis and generated topology) [top1.tex:231] **)
(** LATEX VERSION: "S subbasis: \<Union>S = X; topology is unions of finite intersections of S." **)
definition is_subbasis_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_subbasis_on X S \<longleftrightarrow> (\<Union>S = X)"

definition finite_intersections :: "'a set set \<Rightarrow> 'a set set" where
  "finite_intersections S =
     { \<Inter>F | F. finite F \<and> F \<subseteq> S }"

definition topology_generated_by_subbasis :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "topology_generated_by_subbasis X S =
     { \<Union>U | U. U \<subseteq> finite_intersections S }"

lemma topology_generated_by_subbasis_contains:
  assumes hA: "A \<in> S"
  shows "A \<in> topology_generated_by_subbasis X S"
proof -
  have hAint: "A \<in> finite_intersections S"
  proof -
    have hsub: "{A} \<subseteq> S"
      using hA by simp
    show ?thesis
      unfolding finite_intersections_def
      apply (rule CollectI)
      apply (rule exI[where x="{A}"])
      apply (simp add: hA)
      done
  qed

  show ?thesis
    unfolding topology_generated_by_subbasis_def
    apply (rule CollectI)
    apply (rule exI[where x="{A}"])
    apply (intro conjI)
     apply simp
    apply (rule subsetI)
    apply (simp add: hAint)
    done
qed

(** The topology generated by a subbasis is indeed a topology, provided the subbasis covers
    the carrier.  (We only use the lightweight predicate \<open>is_subbasis_on\<close>.) **)
lemma topology_generated_by_subbasis_is_topology_on:
  assumes hS: "is_subbasis_on X S"
  shows "is_topology_on X (topology_generated_by_subbasis X S)"
proof -
  let ?T = "topology_generated_by_subbasis X S"

  have hEmpty: "{} \<in> ?T"
    unfolding topology_generated_by_subbasis_def
    apply (rule CollectI)
    apply (rule exI[where x="{}"])
    apply simp
    done

  have hSsubFI: "S \<subseteq> finite_intersections S"
  proof
    fix A
    assume hA: "A \<in> S"
    have "{A} \<subseteq> S"
      using hA by simp
    show "A \<in> finite_intersections S"
      unfolding finite_intersections_def
      apply (rule CollectI)
      apply (rule exI[where x="{A}"])
      using hA by simp
  qed

  have hX: "X \<in> ?T"
  proof -
    have hUX: "\<Union>S = X"
      using hS unfolding is_subbasis_on_def by simp
    have "X = \<Union>S"
      using hUX by simp
    also have "... \<in> ?T"
      unfolding topology_generated_by_subbasis_def
      apply (rule CollectI)
      apply (rule exI[where x=S])
      using hSsubFI by blast
    finally show ?thesis .
  qed

  have hUnion: "\<forall>Uc. Uc \<subseteq> ?T \<longrightarrow> (\<Union>Uc) \<in> ?T"
  proof (intro allI impI)
    fix Uc
    assume hUc: "Uc \<subseteq> ?T"

    define UU where
      "UU = {W. \<exists>U\<in>Uc. \<exists>U0. U0 \<subseteq> finite_intersections S \<and> U = \<Union>U0 \<and> W \<in> U0}"

    have hUUsub: "UU \<subseteq> finite_intersections S"
    proof
      fix W
      assume hW: "W \<in> UU"
      obtain U U0 where hU: "U \<in> Uc" and hU0: "U0 \<subseteq> finite_intersections S"
        and hUeq: "U = \<Union>U0" and hW0: "W \<in> U0"
        using hW unfolding UU_def by blast
      show "W \<in> finite_intersections S"
        using hU0 hW0 by blast
    qed

    have hEq: "\<Union>Uc = \<Union>UU"
    proof (rule set_eqI)
      fix x
      show "x \<in> \<Union>Uc \<longleftrightarrow> x \<in> \<Union>UU"
      proof
        assume hx: "x \<in> \<Union>Uc"
        obtain U where hU: "U \<in> Uc" and hxU: "x \<in> U"
          using hx by blast
        have hUT: "U \<in> ?T"
          using hUc hU by blast
        obtain U0 where hU0: "U0 \<subseteq> finite_intersections S" and hUeq: "U = \<Union>U0"
          using hUT unfolding topology_generated_by_subbasis_def by blast
        obtain W where hW: "W \<in> U0" and hxW: "x \<in> W"
          using hxU unfolding hUeq by blast
        have "W \<in> UU"
          unfolding UU_def using hU hU0 hUeq hW by blast
        thus "x \<in> \<Union>UU"
          using hxW by blast
      next
        assume hx: "x \<in> \<Union>UU"
        obtain W where hW: "W \<in> UU" and hxW: "x \<in> W"
          using hx by blast
        obtain U U0 where hU: "U \<in> Uc" and hU0: "U0 \<subseteq> finite_intersections S"
          and hUeq: "U = \<Union>U0" and hWU0: "W \<in> U0"
          using hW unfolding UU_def by blast
        have "W \<subseteq> U"
          using hWU0 unfolding hUeq by blast
        have "x \<in> U"
          using hxW \<open>W \<subseteq> U\<close> by blast
        thus "x \<in> \<Union>Uc"
          using hU by blast
      qed
    qed

    show "(\<Union>Uc) \<in> ?T"
      unfolding topology_generated_by_subbasis_def
      apply (rule CollectI)
      apply (rule exI[where x=UU])
      using hEq hUUsub by blast
  qed

  have hFinInt: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?T \<longrightarrow> (\<Inter>F) \<in> ?T"
  proof (intro allI impI)
    fix F
    assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?T"
    then have hfin: "finite F" and hne: "F \<noteq> {}" and hFsub: "F \<subseteq> ?T"
      by blast+
    from hfin hne hFsub show "(\<Inter>F) \<in> ?T"
    proof (induction F rule: finite_induct)
      case empty
      thus ?case by simp
    next
      case (insert U F)
      have hU: "U \<in> ?T"
        using insert.prems by blast
      show ?case
      proof (cases "F = {}")
        case True
        show ?thesis
          using hU True by simp
      next
        case False
        have hFsub': "F \<subseteq> ?T"
          using insert.prems by blast
        have hInterF: "(\<Inter>F) \<in> ?T"
        proof -
          have hneF: "F \<noteq> {}"
            using False by simp
          show ?thesis
            apply (rule insert.IH)
             apply (rule hneF)
            apply (rule hFsub')
            done
        qed

        obtain U0 where hU0: "U0 \<subseteq> finite_intersections S" and hUeq: "U = \<Union>U0"
          using hU unfolding topology_generated_by_subbasis_def by blast
        obtain V0 where hV0: "V0 \<subseteq> finite_intersections S" and hVeq: "(\<Inter>F) = \<Union>V0"
          using hInterF unfolding topology_generated_by_subbasis_def by blast

        define W0 where "W0 = {u \<inter> v | u v. u \<in> U0 \<and> v \<in> V0}"

        have hW0sub: "W0 \<subseteq> finite_intersections S"
        proof
          fix w
          assume hw: "w \<in> W0"
          obtain u v where hu: "u \<in> U0" and hv: "v \<in> V0" and hwuv: "w = u \<inter> v"
            using hw unfolding W0_def by blast
          have huFI: "u \<in> finite_intersections S"
            using hU0 hu by blast
          have hvFI: "v \<in> finite_intersections S"
            using hV0 hv by blast
          obtain Fu where hFu: "finite Fu" and hFusub: "Fu \<subseteq> S" and hueq: "u = \<Inter>Fu"
            using huFI unfolding finite_intersections_def by blast
          obtain Fv where hFv: "finite Fv" and hFvsub: "Fv \<subseteq> S" and hveq: "v = \<Inter>Fv"
            using hvFI unfolding finite_intersections_def by blast
          have hFin: "finite (Fu \<union> Fv)"
            using hFu hFv by simp
          have hSub: "Fu \<union> Fv \<subseteq> S"
            using hFusub hFvsub by blast
          have hInter: "(\<Inter>Fu) \<inter> (\<Inter>Fv) = \<Inter>(Fu \<union> Fv)"
          proof (rule set_eqI)
            fix x
            show "x \<in> (\<Inter>Fu) \<inter> (\<Inter>Fv) \<longleftrightarrow> x \<in> \<Inter>(Fu \<union> Fv)"
              by blast
          qed
          have hwInter: "w = \<Inter>(Fu \<union> Fv)"
            unfolding hwuv hueq hveq using hInter by simp
          have "w \<in> finite_intersections S"
            unfolding finite_intersections_def
            apply simp
            apply (rule exI[where x="Fu \<union> Fv"])
            using hFin hSub hwInter by simp
          thus "w \<in> finite_intersections S" .
        qed

        have hEq: "(\<Inter>(insert U F)) = \<Union>W0"
        proof (rule set_eqI)
          fix x
          show "x \<in> (\<Inter>(insert U F)) \<longleftrightarrow> x \<in> \<Union>W0"
          proof
            assume hx: "x \<in> (\<Inter>(insert U F))"
            have hxU: "x \<in> U"
              using hx by simp
            have hxF: "x \<in> (\<Inter>F)"
              using hx by simp
            obtain u where hu: "u \<in> U0" and hxu: "x \<in> u"
              using hxU unfolding hUeq by blast
            obtain v where hv: "v \<in> V0" and hxv: "x \<in> v"
              using hxF unfolding hVeq by blast
            have "x \<in> u \<inter> v"
              using hxu hxv by simp
            moreover have "u \<inter> v \<in> W0"
              unfolding W0_def using hu hv by blast
            ultimately show "x \<in> \<Union>W0"
              by blast
          next
            assume hx: "x \<in> \<Union>W0"
            obtain w where hw: "w \<in> W0" and hxw: "x \<in> w"
              using hx by blast
            obtain u v where hu: "u \<in> U0" and hv: "v \<in> V0" and hwuv: "w = u \<inter> v"
              using hw unfolding W0_def by blast
            have hxu: "x \<in> u" and hxv: "x \<in> v"
              using hxw unfolding hwuv by blast+
            have "u \<subseteq> U"
              using hu unfolding hUeq by blast
            have "v \<subseteq> (\<Inter>F)"
              using hv unfolding hVeq by blast
            have hxU: "x \<in> U"
              using hxu \<open>u \<subseteq> U\<close> by blast
            have hxF: "x \<in> (\<Inter>F)"
              using hxv \<open>v \<subseteq> (\<Inter>F)\<close> by blast
            show "x \<in> (\<Inter>(insert U F))"
              using hxU hxF by simp
          qed
        qed

        show "(\<Inter>(insert U F)) \<in> ?T"
          unfolding topology_generated_by_subbasis_def
          apply (rule CollectI)
          apply (rule exI[where x=W0])
          using hEq hW0sub by blast
      qed
    qed
  qed

  show ?thesis
    unfolding is_topology_on_def
    using hEmpty hX hUnion hFinInt by blast
qed


section \<open>\<S>14 The Order Topology\<close>

(** from \S14 Definition (Order topology on a simply ordered set) [top1.tex:314] **)
(** LATEX VERSION: "Order topology generated by open intervals and rays." **)

definition open_ray_gt :: "'a::linorder \<Rightarrow> 'a set" where
  "open_ray_gt a = {x. a < x}"

definition open_ray_lt :: "'a::linorder \<Rightarrow> 'a set" where
  "open_ray_lt a = {x. x < a}"

definition open_interval :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_interval a b = {x. a < x \<and> x < b}"

definition basis_order_topology :: "'a::linorder set set" where
  "basis_order_topology =
     ({ open_interval a b | a b. a < b } \<union>
      { open_ray_gt a | a. True } \<union>
      { open_ray_lt a | a. True } \<union>
      {UNIV})"

definition order_topology_on_UNIV :: "'a::linorder set set" where
  "order_topology_on_UNIV = topology_generated_by_basis UNIV basis_order_topology"

(** Order topology on an arbitrary carrier set X (ordered by the ambient order). **)

definition open_ray_gt_on :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_ray_gt_on X a = X \<inter> open_ray_gt a"

definition open_ray_lt_on :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_ray_lt_on X a = X \<inter> open_ray_lt a"

definition open_interval_on :: "'a::linorder set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "open_interval_on X a b = X \<inter> open_interval a b"

definition basis_order_topology_on :: "'a::linorder set \<Rightarrow> 'a set set" where
  "basis_order_topology_on X =
     ({ open_interval_on X a b | a b. a \<in> X \<and> b \<in> X \<and> a < b } \<union>
      { open_ray_gt_on X a | a. a \<in> X } \<union>
      { open_ray_lt_on X a | a. a \<in> X } \<union>
      {X})"

definition order_topology_on :: "'a::linorder set \<Rightarrow> 'a set set" where
  "order_topology_on X = topology_generated_by_basis X (basis_order_topology_on X)"

lemma basis_order_topology_on_UNIV:
  "basis_order_topology_on (UNIV::'a::linorder set) = basis_order_topology"
proof -
  have hInt:
      "{ open_interval_on (UNIV::'a set) a b | a b. a \<in> UNIV \<and> b \<in> UNIV \<and> a < b }
     = { open_interval a b | a b. a < b }"
  proof (rule set_eqI)
    fix s
    show "s \<in> { open_interval_on (UNIV::'a set) a b | a b. a \<in> UNIV \<and> b \<in> UNIV \<and> a < b }
      \<longleftrightarrow> s \<in> { open_interval a b | a b. a < b }"
    proof (rule iffI)
      assume hs: "s \<in> { open_interval_on (UNIV::'a set) a b | a b. a \<in> UNIV \<and> b \<in> UNIV \<and> a < b }"
      then obtain a b where hab: "a < b" and hseq: "s = open_interval_on UNIV a b"
        by blast
      have hseq': "s = open_interval a b"
        using hseq unfolding open_interval_on_def by simp
      show "s \<in> { open_interval a b | a b. a < b }"
        using hab hseq' by blast
    next
      assume hs: "s \<in> { open_interval a b | a b. a < b }"
      then obtain a b where hab: "a < b" and hseq: "s = open_interval a b"
        by blast
      have hseq': "s = open_interval_on (UNIV::'a set) a b"
        using hseq unfolding open_interval_on_def by simp
      show "s \<in> { open_interval_on (UNIV::'a set) a b | a b. a \<in> UNIV \<and> b \<in> UNIV \<and> a < b }"
        using hab hseq' by blast
    qed
  qed

  have hGt:
      "{ open_ray_gt_on (UNIV::'a set) a | a. a \<in> UNIV } = { open_ray_gt a | a. True }"
  proof (rule set_eqI)
    fix s
    show "s \<in> { open_ray_gt_on (UNIV::'a set) a | a. a \<in> UNIV }
      \<longleftrightarrow> s \<in> { open_ray_gt a | a. True }"
    proof (rule iffI)
      assume hs: "s \<in> { open_ray_gt_on (UNIV::'a set) a | a. a \<in> UNIV }"
      then obtain a where hseq: "s = open_ray_gt_on UNIV a"
        by blast
      have hseq': "s = open_ray_gt a"
        using hseq unfolding open_ray_gt_on_def by simp
      show "s \<in> { open_ray_gt a | a. True }"
        using hseq' by blast
    next
      assume hs: "s \<in> { open_ray_gt a | a. True }"
      then obtain a where hseq: "s = open_ray_gt a"
        by blast
      have hseq': "s = open_ray_gt_on (UNIV::'a set) a"
        using hseq unfolding open_ray_gt_on_def by simp
      show "s \<in> { open_ray_gt_on (UNIV::'a set) a | a. a \<in> UNIV }"
        using hseq' by blast
    qed
  qed

  have hLt:
      "{ open_ray_lt_on (UNIV::'a set) a | a. a \<in> UNIV } = { open_ray_lt a | a. True }"
  proof (rule set_eqI)
    fix s
    show "s \<in> { open_ray_lt_on (UNIV::'a set) a | a. a \<in> UNIV }
      \<longleftrightarrow> s \<in> { open_ray_lt a | a. True }"
    proof (rule iffI)
      assume hs: "s \<in> { open_ray_lt_on (UNIV::'a set) a | a. a \<in> UNIV }"
      then obtain a where hseq: "s = open_ray_lt_on UNIV a"
        by blast
      have hseq': "s = open_ray_lt a"
        using hseq unfolding open_ray_lt_on_def by simp
      show "s \<in> { open_ray_lt a | a. True }"
        using hseq' by blast
    next
      assume hs: "s \<in> { open_ray_lt a | a. True }"
      then obtain a where hseq: "s = open_ray_lt a"
        by blast
      have hseq': "s = open_ray_lt_on (UNIV::'a set) a"
        using hseq unfolding open_ray_lt_on_def by simp
      show "s \<in> { open_ray_lt_on (UNIV::'a set) a | a. a \<in> UNIV }"
        using hseq' by blast
    qed
  qed

  show ?thesis
    unfolding basis_order_topology_on_def basis_order_topology_def
    using hInt hGt hLt by simp
qed

lemma order_topology_on_UNIV_eq:
  "order_topology_on_UNIV = order_topology_on (UNIV::'a::linorder set)"
proof -
  show ?thesis
    unfolding order_topology_on_UNIV_def order_topology_on_def
    apply (subst basis_order_topology_on_UNIV)
    apply (rule refl)
    done
qed

(** The standard UNIV-order-topology basis is indeed a basis on UNIV. **)

lemma basis_order_topology_cases:
  assumes hb: "b \<in> basis_order_topology"
  shows "(\<exists>a c. a < c \<and> b = open_interval a c)
      \<or> (\<exists>a. b = open_ray_gt a)
      \<or> (\<exists>a. b = open_ray_lt a)
      \<or> b = (UNIV::'a::linorder set)"
  using hb unfolding basis_order_topology_def by blast

(** Any basic open set in the real order topology contains an open interval around each of its points.
    This helper is used repeatedly for continuity arguments. **)
lemma basis_order_topology_contains_open_interval:
  fixes b :: "real set" and x :: real
  assumes hb: "b \<in> (basis_order_topology::real set set)"
  assumes hx: "x \<in> b"
  shows "\<exists>e>0. open_interval (x - e) (x + e) \<subseteq> b"
proof -
  have hcases:
    "(\<exists>a c. a < c \<and> b = open_interval a c)
     \<or> (\<exists>a. b = open_ray_gt a)
     \<or> (\<exists>a. b = open_ray_lt a)
     \<or> b = (UNIV::real set)"
    by (rule basis_order_topology_cases[OF hb])

  show ?thesis
  proof (rule disjE[OF hcases])
    assume hbint: "\<exists>a c. a < c \<and> b = open_interval a c"
	    then obtain a c where hac: "a < c" and hbeq: "b = open_interval a c"
	      by blast
	    have hax_hxc: "a < x \<and> x < c"
	      using hx unfolding hbeq open_interval_def by simp
	    have ha: "a < x"
	      using hax_hxc by (rule conjunct1)
	    have hx': "x < c"
	      using hax_hxc by (rule conjunct2)
	    define e where "e = min (x - a) (c - x) / 2"
	    have he: "0 < e"
	    proof -
      have "0 < x - a"
        using ha by linarith
      moreover have "0 < c - x"
        using hx' by linarith
      ultimately have "0 < min (x - a) (c - x)"
        by simp
      thus ?thesis
        unfolding e_def by (simp add: divide_pos_pos)
    qed
    have he_lt1: "e < x - a"
    proof -
      have "e \<le> (x - a) / 2"
        unfolding e_def by simp
      also have "... < x - a"
      proof -
        have hxapos: "0 < x - a"
          using ha by linarith
        have hhalf: "(x - a) * (1 / 2 :: real) < (x - a) * 1"
          apply (rule mult_strict_left_mono)
           apply simp
          apply (rule hxapos)
          done
        show ?thesis
          using hhalf by simp
      qed
      finally show ?thesis
        by linarith
    qed
    have he_lt2: "e < c - x"
    proof -
      have "e \<le> (c - x) / 2"
        unfolding e_def by simp
      also have "... < c - x"
      proof -
        have hxpos: "0 < c - x"
          using hx' by linarith
        have hhalf: "(c - x) * (1 / 2 :: real) < (c - x) * 1"
          apply (rule mult_strict_left_mono)
           apply simp
          apply (rule hxpos)
          done
        show ?thesis
          using hhalf by simp
      qed
      finally show ?thesis
        by linarith
    qed

    have hsub: "open_interval (x - e) (x + e) \<subseteq> open_interval a c"
	    proof (rule subsetI)
	      fix y assume hy: "y \<in> open_interval (x - e) (x + e)"
	      have hy_conj: "x - e < y \<and> y < x + e"
	        using hy unfolding open_interval_def by simp
	      have hy1: "x - e < y"
	        using hy_conj by (rule conjunct1)
	      have hy2: "y < x + e"
	        using hy_conj by (rule conjunct2)
	      have "a < x - e"
	        using he_lt1 by linarith
	      hence "a < y"
        using hy1 by linarith
      moreover have "x + e < c"
        using he_lt2 by linarith
      hence "y < c"
        using hy2 by linarith
      ultimately show "y \<in> open_interval a c"
        unfolding open_interval_def by simp
    qed
    show ?thesis
      unfolding hbeq
      by (rule exI[where x=e], intro conjI, rule he, rule hsub)
  next
    assume hrest: "(\<exists>a. b = open_ray_gt a) \<or> (\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
    show ?thesis
    proof (rule disjE[OF hrest])
      assume hbr: "\<exists>a. b = open_ray_gt a"
      then obtain a where hbeq: "b = open_ray_gt a"
        by blast
      have ha: "a < x"
        using hx unfolding hbeq open_ray_gt_def by simp
      define e where "e = (x - a) / 2"
      have he: "0 < e"
      proof -
        have "0 < x - a"
          using ha by linarith
        thus ?thesis
          unfolding e_def by (simp add: divide_pos_pos)
      qed
      have hsub: "open_interval (x - e) (x + e) \<subseteq> open_ray_gt a"
      proof (rule subsetI)
        fix y assume hy: "y \<in> open_interval (x - e) (x + e)"
        have hy1: "x - e < y"
          using hy unfolding open_interval_def by simp
        have "a < x - e"
        proof -
          have hEq: "x - e = (x + a) / 2"
            unfolding e_def by (simp add: field_simps)
          have "a < (x + a) / 2"
          proof -
            have "a < (x + a) / 2 \<longleftrightarrow> a * (2::real) < x + a"
              by (simp add: divide_less_eq)
            moreover have "a * (2::real) < x + a"
              using ha by linarith
            ultimately show ?thesis
              by simp
          qed
          thus ?thesis
            unfolding hEq by simp
        qed
        hence "a < y"
          using hy1 by linarith
        thus "y \<in> open_ray_gt a"
          unfolding open_ray_gt_def by simp
      qed
      show ?thesis
        unfolding hbeq
        by (rule exI[where x=e], intro conjI, rule he, rule hsub)
    next
      assume hrest2: "(\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
      show ?thesis
      proof (rule disjE[OF hrest2])
        assume hbl: "\<exists>a. b = open_ray_lt a"
        then obtain a where hbeq: "b = open_ray_lt a"
          by blast
        have ha: "x < a"
          using hx unfolding hbeq open_ray_lt_def by simp
        define e where "e = (a - x) / 2"
        have he: "0 < e"
        proof -
          have "0 < a - x"
            using ha by linarith
          thus ?thesis
            unfolding e_def by (simp add: divide_pos_pos)
        qed
        have hsub: "open_interval (x - e) (x + e) \<subseteq> open_ray_lt a"
        proof (rule subsetI)
          fix y assume hy: "y \<in> open_interval (x - e) (x + e)"
          have hy2: "y < x + e"
            using hy unfolding open_interval_def by simp
          have "x + e < a"
          proof -
            have hEq: "x + e = (x + a) / 2"
              unfolding e_def by (simp add: field_simps)
            have hlt: "(x + a) / 2 < a"
            proof -
              have "((x + a) / 2 < a) \<longleftrightarrow> (x + a < a * (2::real))"
                by (simp add: divide_less_eq)
              also have "..."
                using ha by linarith
              finally show ?thesis .
            qed
            show ?thesis
              using hlt unfolding hEq .
          qed
          hence "y < a"
            using hy2 by linarith
          thus "y \<in> open_ray_lt a"
            unfolding open_ray_lt_def by simp
        qed
        show ?thesis
          unfolding hbeq
          by (rule exI[where x=e], intro conjI, rule he, rule hsub)
      next
        assume hU: "b = (UNIV::real set)"
        show ?thesis
          unfolding hU
          by (rule exI[where x="1::real"], simp)
      qed
    qed
  qed
qed

(** Open-set characterisation: a subset is open if every point has an open neighbourhood contained in it. **)
lemma top1_open_set_from_local_opens:
  assumes hTop: "is_topology_on X TX"
  assumes hPX: "P \<subseteq> X"
  assumes hlocal: "\<forall>x\<in>P. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> P"
  shows "P \<in> TX"
proof -
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> (\<Union>U) \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTop[unfolded is_topology_on_def]]]])

  define UP where "UP = {U. U \<in> TX \<and> U \<subseteq> P}"
  have hUP_sub: "UP \<subseteq> TX"
    unfolding UP_def by blast
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

  show "P \<in> TX"
    unfolding hEq using hUnion_UP .
qed

lemma basis_order_topology_refine_intersection:
  fixes b1 b2 :: "'a::linorder set" and x :: 'a
  assumes hb1: "b1 \<in> basis_order_topology"
  assumes hb2: "b2 \<in> basis_order_topology"
  assumes hx: "x \<in> b1 \<inter> b2"
  shows "\<exists>b3\<in>basis_order_topology. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
proof -
  have hb1c: "(\<exists>a c. a < c \<and> b1 = open_interval a c)
        \<or> (\<exists>a. b1 = open_ray_gt a)
        \<or> (\<exists>a. b1 = open_ray_lt a)
        \<or> b1 = (UNIV::'a set)"
    by (rule basis_order_topology_cases[OF hb1])
  have hb2c: "(\<exists>a c. a < c \<and> b2 = open_interval a c)
        \<or> (\<exists>a. b2 = open_ray_gt a)
        \<or> (\<exists>a. b2 = open_ray_lt a)
        \<or> b2 = (UNIV::'a set)"
    by (rule basis_order_topology_cases[OF hb2])

  from hb1c show ?thesis
  proof (elim disjE)
    assume hI1: "\<exists>a c. a < c \<and> b1 = open_interval a c"
    obtain a b where hab: "a < b" and hb1eq: "b1 = open_interval a b"
      using hI1 by blast
    from hb2c show ?thesis
    proof (elim disjE)
      assume hI2: "\<exists>a c. a < c \<and> b2 = open_interval a c"
      obtain c d where hcd: "c < d" and hb2eq: "b2 = open_interval c d"
        using hI2 by blast
      have hxa: "a < x" and hxb: "x < b" and hxc: "c < x" and hxd: "x < d"
        using hx unfolding hb1eq hb2eq open_interval_def by blast+
      define L where "L = max a c"
      define U where "U = min b d"
      have hLx: "L < x" using hxa hxc unfolding L_def by simp
      have hxU: "x < U" using hxb hxd unfolding U_def by simp
      have hLU: "L < U" using hLx hxU by (rule less_trans)
      have hb3B: "open_interval L U \<in> basis_order_topology"
        unfolding basis_order_topology_def using hLU by blast
      have hxin: "x \<in> open_interval L U"
        using hLx hxU unfolding open_interval_def by blast
      have hsub: "open_interval L U \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval L U"
        have hLt: "L < t" and htU: "t < U"
          using ht unfolding open_interval_def by blast+
        have haL: "a \<le> L" unfolding L_def by simp
        have hcL: "c \<le> L" unfolding L_def by simp
        have hat: "a < t" using haL hLt by (rule le_less_trans)
        have hct: "c < t" using hcL hLt by (rule le_less_trans)
        have htb: "t < b" using htU unfolding U_def by simp
        have htd: "t < d" using htU unfolding U_def by simp
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_interval_def
          using hat htb hct htd by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_interval L U"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hG2: "\<exists>a. b2 = open_ray_gt a"
      obtain c where hb2eq: "b2 = open_ray_gt c" using hG2 by blast
      have hxa: "a < x" and hxb: "x < b" and hxc: "c < x"
        using hx unfolding hb1eq hb2eq open_interval_def open_ray_gt_def by blast+
      define L where "L = max a c"
      have hLx: "L < x" using hxa hxc unfolding L_def by simp
      have hLU: "L < b" using hLx hxb by (rule less_trans)
      have hb3B: "open_interval L b \<in> basis_order_topology"
        unfolding basis_order_topology_def using hLU by blast
      have hxin: "x \<in> open_interval L b"
        using hLx hxb unfolding open_interval_def by blast
      have hsub: "open_interval L b \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval L b"
        have hLt: "L < t" and htb: "t < b"
          using ht unfolding open_interval_def by blast+
        have haL: "a \<le> L" unfolding L_def by simp
        have hcL: "c \<le> L" unfolding L_def by simp
        have hat: "a < t" using haL hLt by (rule le_less_trans)
        have hct: "c < t" using hcL hLt by (rule le_less_trans)
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_interval_def open_ray_gt_def
          using hat htb hct by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_interval L b"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hL2: "\<exists>a. b2 = open_ray_lt a"
      obtain d where hb2eq: "b2 = open_ray_lt d" using hL2 by blast
      have hxa: "a < x" and hxb: "x < b" and hxd: "x < d"
        using hx unfolding hb1eq hb2eq open_interval_def open_ray_lt_def by blast+
      define U where "U = min b d"
      have hxU: "x < U" using hxb hxd unfolding U_def by simp
      have hLU: "a < U" using hxa hxU by (rule less_trans)
      have hb3B: "open_interval a U \<in> basis_order_topology"
        unfolding basis_order_topology_def using hLU by blast
      have hxin: "x \<in> open_interval a U"
        using hxa hxU unfolding open_interval_def by blast
      have hsub: "open_interval a U \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval a U"
        have hat: "a < t" and htU: "t < U"
          using ht unfolding open_interval_def by blast+
        have htb: "t < b" using htU unfolding U_def by simp
        have htd: "t < d" using htU unfolding U_def by simp
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_interval_def open_ray_lt_def
          using hat htb htd by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_interval a U"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hb2U: "b2 = (UNIV::'a set)"
      have hxin: "x \<in> b1" using hx by blast
      have hsub: "b1 \<subseteq> b1 \<inter> b2" using hb2U by blast
      show ?thesis
        apply (rule bexI[where x=b1])
         apply (intro conjI hxin hsub)
        apply (rule hb1)
        done
    qed
  next
    assume hG1: "\<exists>a. b1 = open_ray_gt a"
    obtain a where hb1eq: "b1 = open_ray_gt a" using hG1 by blast
    from hb2c show ?thesis
    proof (elim disjE)
      assume hI2: "\<exists>a c. a < c \<and> b2 = open_interval a c"
      obtain c d where hcd: "c < d" and hb2eq: "b2 = open_interval c d"
        using hI2 by blast
      have hxa: "a < x" and hxc: "c < x" and hxd: "x < d"
        using hx unfolding hb1eq hb2eq open_interval_def open_ray_gt_def by blast+
      define L where "L = max a c"
      have hLx: "L < x" using hxa hxc unfolding L_def by simp
      have hLU: "L < d" using hLx hxd by (rule less_trans)
      have hb3B: "open_interval L d \<in> basis_order_topology"
        unfolding basis_order_topology_def using hLU by blast
      have hxin: "x \<in> open_interval L d"
        using hLx hxd unfolding open_interval_def by blast
      have hsub: "open_interval L d \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval L d"
        have hLt: "L < t" and htd: "t < d"
          using ht unfolding open_interval_def by blast+
        have haL: "a \<le> L" unfolding L_def by simp
        have hcL: "c \<le> L" unfolding L_def by simp
        have hat: "a < t" using haL hLt by (rule le_less_trans)
        have hct: "c < t" using hcL hLt by (rule le_less_trans)
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_ray_gt_def open_interval_def
          using hat hct htd by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_interval L d"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hG2: "\<exists>a. b2 = open_ray_gt a"
      obtain c where hb2eq: "b2 = open_ray_gt c" using hG2 by blast
      have hxa: "a < x" and hxc: "c < x"
        using hx unfolding hb1eq hb2eq open_ray_gt_def by blast+
      define L where "L = max a c"
      have hLx: "L < x" using hxa hxc unfolding L_def by simp
      have hb3B: "open_ray_gt L \<in> basis_order_topology"
        unfolding basis_order_topology_def by blast
      have hxin: "x \<in> open_ray_gt L"
        using hLx unfolding open_ray_gt_def by blast
      have hsub: "open_ray_gt L \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_ray_gt L"
        have hLt: "L < t" using ht unfolding open_ray_gt_def by blast
        have haL: "a \<le> L" unfolding L_def by simp
        have hcL: "c \<le> L" unfolding L_def by simp
        have hat: "a < t" using haL hLt by (rule le_less_trans)
        have hct: "c < t" using hcL hLt by (rule le_less_trans)
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_ray_gt_def
          using hat hct by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_ray_gt L"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hL2: "\<exists>a. b2 = open_ray_lt a"
      obtain d where hb2eq: "b2 = open_ray_lt d" using hL2 by blast
      have hxa: "a < x" and hxd: "x < d"
        using hx unfolding hb1eq hb2eq open_ray_gt_def open_ray_lt_def by blast+
      have had: "a < d" using hxa hxd by (rule less_trans)
      have hb3B: "open_interval a d \<in> basis_order_topology"
        unfolding basis_order_topology_def using had by blast
      have hxin: "x \<in> open_interval a d"
        using hxa hxd unfolding open_interval_def by blast
      have hsub: "open_interval a d \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval a d"
        have hat: "a < t" and htd: "t < d"
          using ht unfolding open_interval_def by blast+
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_interval_def open_ray_gt_def open_ray_lt_def
          using hat htd by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_interval a d"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hb2U: "b2 = (UNIV::'a set)"
      have hxin: "x \<in> b1" using hx by blast
      have hsub: "b1 \<subseteq> b1 \<inter> b2" using hb2U by blast
      show ?thesis
        apply (rule bexI[where x=b1])
         apply (intro conjI hxin hsub)
        apply (rule hb1)
        done
    qed
  next
    assume hL1: "\<exists>a. b1 = open_ray_lt a"
    obtain a where hb1eq: "b1 = open_ray_lt a" using hL1 by blast
    from hb2c show ?thesis
    proof (elim disjE)
      assume hI2: "\<exists>a c. a < c \<and> b2 = open_interval a c"
      obtain c d where hcd: "c < d" and hb2eq: "b2 = open_interval c d"
        using hI2 by blast
      have hxc: "c < x" and hxd: "x < d" and hxa: "x < a"
        using hx unfolding hb1eq hb2eq open_interval_def open_ray_lt_def by blast+
      define U where "U = min a d"
      have hxU: "x < U" using hxa hxd unfolding U_def by simp
      have hLU: "c < U" using hxc hxU by (rule less_trans)
      have hb3B: "open_interval c U \<in> basis_order_topology"
        unfolding basis_order_topology_def using hLU by blast
      have hxin: "x \<in> open_interval c U"
        using hxc hxU unfolding open_interval_def by blast
      have hsub: "open_interval c U \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval c U"
        have hct: "c < t" and htU: "t < U"
          using ht unfolding open_interval_def by blast+
        have hta: "t < a" using htU unfolding U_def by simp
        have htd: "t < d" using htU unfolding U_def by simp
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_interval_def open_ray_lt_def
          using hct hta htd by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_interval c U"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hG2: "\<exists>a. b2 = open_ray_gt a"
      obtain c where hb2eq: "b2 = open_ray_gt c" using hG2 by blast
      have hxc: "c < x" and hxa: "x < a"
        using hx unfolding hb1eq hb2eq open_ray_gt_def open_ray_lt_def by blast+
      have hca: "c < a" using hxc hxa by (rule less_trans)
      have hb3B: "open_interval c a \<in> basis_order_topology"
        unfolding basis_order_topology_def using hca by blast
      have hxin: "x \<in> open_interval c a"
        using hxc hxa unfolding open_interval_def by blast
      have hsub: "open_interval c a \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval c a"
        have hct: "c < t" and hta: "t < a"
          using ht unfolding open_interval_def by blast+
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_interval_def open_ray_gt_def open_ray_lt_def
          using hct hta by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_interval c a"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hL2: "\<exists>a. b2 = open_ray_lt a"
      obtain d where hb2eq: "b2 = open_ray_lt d" using hL2 by blast
      have hxa: "x < a" and hxd: "x < d"
        using hx unfolding hb1eq hb2eq open_ray_lt_def by blast+
      define U where "U = min a d"
      have hxU: "x < U" using hxa hxd unfolding U_def by simp
      have hb3B: "open_ray_lt U \<in> basis_order_topology"
        unfolding basis_order_topology_def by blast
      have hxin: "x \<in> open_ray_lt U"
        using hxU unfolding open_ray_lt_def by blast
      have hsub: "open_ray_lt U \<subseteq> b1 \<inter> b2"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_ray_lt U"
        have htU: "t < U" using ht unfolding open_ray_lt_def by blast
        have hta: "t < a" using htU unfolding U_def by simp
        have htd: "t < d" using htU unfolding U_def by simp
        show "t \<in> b1 \<inter> b2"
          unfolding hb1eq hb2eq open_ray_lt_def
          using hta htd by blast
      qed
      show ?thesis
        apply (rule bexI[where x="open_ray_lt U"])
         apply (intro conjI hxin hsub)
        apply (rule hb3B)
        done
    next
      assume hb2U: "b2 = (UNIV::'a set)"
      have hxin: "x \<in> b1" using hx by blast
      have hsub: "b1 \<subseteq> b1 \<inter> b2" using hb2U by blast
      show ?thesis
        apply (rule bexI[where x=b1])
         apply (intro conjI hxin hsub)
        apply (rule hb1)
        done
    qed
  next
    assume hb1U: "b1 = (UNIV::'a set)"
    have hxin: "x \<in> b2" using hx by blast
    have hsub: "b2 \<subseteq> b1 \<inter> b2" using hb1U by blast
    show ?thesis
      apply (rule bexI[where x=b2])
       apply (intro conjI hxin hsub)
      apply (rule hb2)
      done
  qed
qed

lemma basis_order_topology_is_basis_on_UNIV:
  "is_basis_on (UNIV::'a::linorder set) basis_order_topology"
proof -
  have hsub: "\<forall>b\<in>basis_order_topology. b \<subseteq> (UNIV::'a set)" by simp
  have hcov: "\<forall>x\<in>(UNIV::'a set). \<exists>b\<in>basis_order_topology. x \<in> b"
  proof (rule ballI)
    fix x :: 'a assume hx: "x \<in> (UNIV::'a set)"
    have hU: "(UNIV::'a set) \<in> basis_order_topology"
      unfolding basis_order_topology_def by blast
    show "\<exists>b\<in>basis_order_topology. x \<in> b"
      apply (rule bexI[where x="(UNIV::'a set)"])
       apply simp
      apply (rule hU)
      done
  qed
  have hint: "\<forall>b1\<in>basis_order_topology. \<forall>b2\<in>basis_order_topology. \<forall>x\<in>(b1 \<inter> b2).
      \<exists>b3\<in>basis_order_topology. x \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2)"
    by (intro ballI, rule basis_order_topology_refine_intersection)
  show ?thesis
    unfolding is_basis_on_def
    apply (intro conjI)
      apply (rule hsub)
     apply (rule hcov)
    apply (rule hint)
    done
qed

lemma basis_for_order_topology_on_UNIV:
  "basis_for (UNIV::'a::linorder set) basis_order_topology order_topology_on_UNIV"
  unfolding basis_for_def order_topology_on_UNIV_def
  apply (intro conjI)
   apply (rule basis_order_topology_is_basis_on_UNIV)
  apply (rule refl)
  done

lemma order_topology_on_UNIV_is_topology_on:
  "is_topology_on (UNIV::'a::linorder set) order_topology_on_UNIV"
  unfolding order_topology_on_UNIV_def
  apply (rule topology_generated_by_basis_is_topology_on)
  apply (rule basis_order_topology_is_basis_on_UNIV)
  done

(** from \S14 Definition (Four interval types determined by a and b) [top1.tex:345] **)
(** LATEX VERSION: "If X ordered and a element, there are four intervals ..." **)
definition interval_types_four :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a set list" where
  "interval_types_four a b =
     [ {x. a < x \<and> x < b},
       {x. a \<le> x \<and> x < b},
       {x. a < x \<and> x \<le> b},
       {x. a \<le> x \<and> x \<le> b} ]"


section \<open>\<S>15 The Product Topology on X \<times> Y\<close>

(** from \S15 Definition (Product topology) [top1.tex:365] **)
(** LATEX VERSION: "Product topology generated by basis {U\<times>V | U open in X, V open in Y}." **)

definition product_basis :: "'a set set \<Rightarrow> 'b set set \<Rightarrow> ('a \<times> 'b) set set" where
  "product_basis TX TY =
     { U \<times> V | U V. U \<in> TX \<and> V \<in> TY }"

definition product_topology_on :: "'a set set \<Rightarrow> 'b set set \<Rightarrow> ('a \<times> 'b) set set" where
  "product_topology_on TX TY =
     topology_generated_by_basis UNIV (product_basis TX TY)"

(** Basic fact: rectangles of open sets are open in the product topology. **)
lemma product_rect_open:
  assumes hU: "U \<in> TX"
  assumes hV: "V \<in> TY"
  shows "U \<times> V \<in> product_topology_on TX TY"
proof -
  show ?thesis
    unfolding product_topology_on_def topology_generated_by_basis_def product_basis_def
  proof (rule CollectI, rule conjI)
    show "U \<times> V \<subseteq> (UNIV::('a \<times> 'b) set)"
      by simp
    show "\<forall>p\<in>U \<times> V. \<exists>b\<in>{Ua \<times> Va |Ua Va. Ua \<in> TX \<and> Va \<in> TY}. p \<in> b \<and> b \<subseteq> U \<times> V"
    proof (intro ballI)
      fix p assume hp: "p \<in> U \<times> V"
      show "\<exists>b\<in>{Ua \<times> Va |Ua Va. Ua \<in> TX \<and> Va \<in> TY}. p \<in> b \<and> b \<subseteq> U \<times> V"
      proof (rule bexI[where x="U \<times> V"])
        show "p \<in> U \<times> V \<and> U \<times> V \<subseteq> U \<times> V"
          apply (rule conjI)
           apply (rule hp)
          apply simp
          done
        show "U \<times> V \<in> {Ua \<times> Va |Ua Va. Ua \<in> TX \<and> Va \<in> TY}"
          apply (rule CollectI)
          apply (rule exI[where x=U])
          apply (rule exI[where x=V])
          apply (intro conjI)
            apply (rule refl)
           apply (rule hU)
          apply (rule hV)
          done
      qed
    qed
  qed
qed

lemma product_topology_on_is_topology_on:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  shows "is_topology_on (X \<times> Y) (product_topology_on TX TY)"
proof -
  let ?TP = "product_topology_on TX TY"

  have hX: "X \<in> TX"
    using hTX unfolding is_topology_on_def by blast
  have hY: "Y \<in> TY"
    using hTY unfolding is_topology_on_def by blast

  have hinter2:
    "\<forall>W1\<in>?TP. \<forall>W2\<in>?TP. (W1 \<inter> W2) \<in> ?TP"
  proof (intro ballI)
    fix W1 W2 assume hW1: "W1 \<in> ?TP" and hW2: "W2 \<in> ?TP"

    have hW1cov: "\<forall>p\<in>W1. \<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> W1"
      using hW1 unfolding product_topology_on_def topology_generated_by_basis_def by blast
    have hW2cov: "\<forall>p\<in>W2. \<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> W2"
      using hW2 unfolding product_topology_on_def topology_generated_by_basis_def by blast

    show "W1 \<inter> W2 \<in> ?TP"
      unfolding product_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule subset_UNIV)
      show "\<forall>p\<in>W1 \<inter> W2. \<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> W1 \<inter> W2"
      proof (intro ballI)
        fix p assume hp: "p \<in> W1 \<inter> W2"
        have hp1: "p \<in> W1" and hp2: "p \<in> W2"
          using hp by blast+
        obtain b1 where hb1: "b1 \<in> product_basis TX TY" and hp_b1: "p \<in> b1" and hb1sub: "b1 \<subseteq> W1"
          using hW1cov[rule_format, OF hp1] by blast
        obtain b2 where hb2: "b2 \<in> product_basis TX TY" and hp_b2: "p \<in> b2" and hb2sub: "b2 \<subseteq> W2"
          using hW2cov[rule_format, OF hp2] by blast

        obtain U1 V1 where hU1: "U1 \<in> TX" and hV1: "V1 \<in> TY" and hb1eq: "b1 = U1 \<times> V1"
          using hb1 unfolding product_basis_def by blast
        obtain U2 V2 where hU2: "U2 \<in> TX" and hV2: "V2 \<in> TY" and hb2eq: "b2 = U2 \<times> V2"
          using hb2 unfolding product_basis_def by blast

        have hU12: "U1 \<inter> U2 \<in> TX"
          by (rule topology_inter2[OF hTX hU1 hU2])
        have hV12: "V1 \<inter> V2 \<in> TY"
          by (rule topology_inter2[OF hTY hV1 hV2])

        have hb3: "(U1 \<inter> U2) \<times> (V1 \<inter> V2) \<in> product_basis TX TY"
          unfolding product_basis_def
          apply (rule CollectI)
          apply (rule exI[where x="U1 \<inter> U2"])
          apply (rule exI[where x="V1 \<inter> V2"])
          apply (intro conjI)
            apply (rule refl)
           apply (rule hU12)
          apply (rule hV12)
          done
        have hp3: "p \<in> (U1 \<inter> U2) \<times> (V1 \<inter> V2)"
          using hp_b1 hp_b2 hb1eq hb2eq by blast
        have hsub3: "(U1 \<inter> U2) \<times> (V1 \<inter> V2) \<subseteq> W1 \<inter> W2"
          using hb1eq hb2eq hb1sub hb2sub by blast

        show "\<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> W1 \<inter> W2"
          apply (rule bexI[where x="(U1 \<inter> U2) \<times> (V1 \<inter> V2)"])
           apply (rule conjI[OF hp3 hsub3])
          apply (rule hb3)
          done
      qed
    qed
  qed

  have hinter:
    "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TP \<longrightarrow> \<Inter>F \<in> ?TP"
  proof (intro allI impI)
    fix F assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TP"
    have hFin: "finite F" and hNe: "F \<noteq> {}" and hSub: "F \<subseteq> ?TP"
      using hF by blast+
    show "\<Inter>F \<in> ?TP"
      using hFin hNe hSub
    proof (induct F rule: finite_ne_induct)
      case (singleton U)
      then show ?case by simp
    next
      case (insert U F)
      have hU: "U \<in> ?TP" using insert by blast
      have hIF: "\<Inter>F \<in> ?TP" using insert by blast
      have "U \<inter> \<Inter>F \<in> ?TP"
        using hinter2[rule_format, OF hU hIF] by blast
      then show ?case by simp
    qed
  qed

  have hunion:
    "\<forall>U. U \<subseteq> ?TP \<longrightarrow> (\<Union>U) \<in> ?TP"
  proof (intro allI impI)
    fix U assume hU: "U \<subseteq> ?TP"
    show "\<Union>U \<in> ?TP"
      unfolding product_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, rule conjI)
      show "\<Union>U \<subseteq> (UNIV::('a \<times> 'b) set)" by simp
      show "\<forall>p\<in>\<Union>U. \<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> \<Union>U"
      proof (intro ballI)
        fix p assume hp: "p \<in> \<Union>U"
        obtain W where hW: "W \<in> U" and hpW: "p \<in> W" using hp by blast
        have hWT: "W \<in> ?TP" using hU hW by blast
        have hWcov: "\<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> W"
          using hWT hpW unfolding product_topology_on_def topology_generated_by_basis_def by blast
        then obtain b where hb: "b \<in> product_basis TX TY" and hpb: "p \<in> b" and hbW: "b \<subseteq> W"
          by blast
        have hbU: "b \<subseteq> \<Union>U"
          using hbW hW by blast
        show "\<exists>b\<in>product_basis TX TY. p \<in> b \<and> b \<subseteq> \<Union>U"
          apply (rule bexI[where x=b])
           apply (intro conjI hpb hbU)
          apply (rule hb)
          done
      qed
    qed
  qed

  show ?thesis
    unfolding is_topology_on_def
  proof (intro conjI)
    show "{} \<in> ?TP"
      unfolding product_topology_on_def topology_generated_by_basis_def by simp
    show "X \<times> Y \<in> ?TP"
      by (rule product_rect_open[OF hX hY])
    show "\<forall>U. U \<subseteq> ?TP \<longrightarrow> \<Union>U \<in> ?TP"
      by (rule hunion)
    show "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TP \<longrightarrow> \<Inter>F \<in> ?TP"
      by (rule hinter)
  qed
qed

(** from \S15 Definition (Projections) [top1.tex:401] **)
(** LATEX VERSION: "\<pi>1(x,y)=x, \<pi>2(x,y)=y." **)
definition pi1 :: "'a \<times> 'b \<Rightarrow> 'a" where "pi1 p = fst p"
definition pi2 :: "'a \<times> 'b \<Rightarrow> 'b" where "pi2 p = snd p"

definition preimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set" where
  "preimage f U = {x. f x \<in> U}"

(** from \S15 Theorem 15.1 [top1.tex:379] **)
(** LATEX VERSION: "If B,C bases for X,Y then {B\<times>C} is a basis for X\<times>Y." **)
theorem Theorem_15_1:
  assumes hBX: "basis_for UNIV BX TX"
  assumes hBY: "basis_for UNIV BY TY"
  defines "D \<equiv> {B \<times> C | B C. B \<in> BX \<and> C \<in> BY}"
  shows "basis_for UNIV D (product_topology_on TX TY)"
proof -
  have hBX_basis: "is_basis_on UNIV BX" and hTX_eq: "TX = topology_generated_by_basis UNIV BX"
    using hBX unfolding basis_for_def by blast+
  have hBY_basis: "is_basis_on UNIV BY" and hTY_eq: "TY = topology_generated_by_basis UNIV BY"
    using hBY unfolding basis_for_def by blast+
  have hBX_cov: "\<forall>x\<in>UNIV. \<exists>b\<in>BX. x \<in> b"
    using hBX_basis unfolding is_basis_on_def by blast
  have hBY_cov: "\<forall>x\<in>UNIV. \<exists>b\<in>BY. x \<in> b"
    using hBY_basis unfolding is_basis_on_def by blast
  have hBX_int: "\<forall>b1\<in>BX. \<forall>b2\<in>BX. \<forall>x\<in>(b1 \<inter> b2). \<exists>b3\<in>BX. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
    using hBX_basis unfolding is_basis_on_def by blast
  have hBY_int: "\<forall>b1\<in>BY. \<forall>b2\<in>BY. \<forall>x\<in>(b1 \<inter> b2). \<exists>b3\<in>BY. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
    using hBY_basis unfolding is_basis_on_def by blast
  (* Basis elements are open *)
  have hBX_open: "\<forall>b\<in>BX. b \<in> TX"
  proof (rule ballI)
    fix b assume hb: "b \<in> BX"
    have "b \<in> topology_generated_by_basis UNIV BX"
      unfolding topology_generated_by_basis_def
      apply (rule CollectI, rule conjI, rule subset_UNIV, rule ballI)
      apply (rule bexI[where x=b], rule conjI[OF _ subset_refl], assumption)
      apply (rule hb)
      done
    thus "b \<in> TX" using hTX_eq by simp
  qed
  have hBY_open: "\<forall>b\<in>BY. b \<in> TY"
  proof (rule ballI)
    fix b assume hb: "b \<in> BY"
    have "b \<in> topology_generated_by_basis UNIV BY"
      unfolding topology_generated_by_basis_def
      apply (rule CollectI, rule conjI, rule subset_UNIV, rule ballI)
      apply (rule bexI[where x=b], rule conjI[OF _ subset_refl], assumption)
      apply (rule hb)
      done
    thus "b \<in> TY" using hTY_eq by simp
  qed
  (* is_basis_on UNIV D — unfold D_def to expose product structure and resolve types *)
  have hD_basis: "is_basis_on UNIV D"
    unfolding is_basis_on_def D_def
  proof (intro conjI)
    show "\<forall>b\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. b \<subseteq> UNIV" by blast
  next
    show "\<forall>x\<in>UNIV. \<exists>b\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. x \<in> b"
    proof -
      have aux: "\<forall>xa xb. \<exists>b\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. (xa, xb) \<in> b"
      proof (intro allI)
        fix xa xb
        obtain bx where hbxX: "bx \<in> BX" and hxa: "xa \<in> bx"
          using hBX_cov[rule_format, of xa] by blast
        obtain bb where hbbY: "bb \<in> BY" and hxb: "xb \<in> bb"
          using hBY_cov[rule_format, of xb] by blast
        show "\<exists>b\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. (xa, xb) \<in> b"
          apply (rule bexI[where x="bx \<times> bb"])
           apply (simp add: hxa hxb)
          apply (rule CollectI, rule exI[where x=bx], rule exI[where x=bb])
          apply (intro conjI refl hbxX hbbY)
          done
      qed
      show ?thesis
      proof (rule ballI)
        fix x
        show "\<exists>b\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. x \<in> b"
          using aux[rule_format, of "fst x" "snd x"] by (simp add: prod.collapse)
      qed
    qed
  next
    show "\<forall>b1\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. \<forall>b2\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}.
            \<forall>x\<in>(b1 \<inter> b2). \<exists>b3\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
    proof (intro ballI)
      fix b1 b2 x
      assume hb1D: "b1 \<in> {B \<times> C | B C. B \<in> BX \<and> C \<in> BY}"
      assume hb2D: "b2 \<in> {B \<times> C | B C. B \<in> BX \<and> C \<in> BY}"
      assume hxb12: "x \<in> b1 \<inter> b2"
      obtain B1 C1 where hB1X: "B1 \<in> BX" and hC1Y: "C1 \<in> BY" and hb1eq: "b1 = B1 \<times> C1"
        using hb1D by blast
      obtain B2 C2 where hB2X: "B2 \<in> BX" and hC2Y: "C2 \<in> BY" and hb2eq: "b2 = B2 \<times> C2"
        using hb2D by blast
      have hxb1: "x \<in> B1 \<times> C1" using hxb12 hb1eq by blast
      have hxb2: "x \<in> B2 \<times> C2" using hxb12 hb2eq by blast
      have ha1: "fst x \<in> B1" using hxb1[unfolded mem_Times_iff] by blast
      have hb1: "snd x \<in> C1" using hxb1[unfolded mem_Times_iff] by blast
      have ha2: "fst x \<in> B2" using hxb2[unfolded mem_Times_iff] by blast
      have hb2: "snd x \<in> C2" using hxb2[unfolded mem_Times_iff] by blast
      have haB12: "fst x \<in> B1 \<inter> B2" using ha1 ha2 by blast
      have hbC12: "snd x \<in> C1 \<inter> C2" using hb1 hb2 by blast
      obtain bx3 where hbx3: "bx3 \<in> BX" and ha3: "fst x \<in> bx3" and hbx3sub: "bx3 \<subseteq> B1 \<inter> B2"
        using hBX_int[rule_format, OF hB1X, rule_format, OF hB2X, rule_format, OF haB12]
        by blast
      obtain bb3 where hbb3: "bb3 \<in> BY" and hb3: "snd x \<in> bb3" and hbb3sub: "bb3 \<subseteq> C1 \<inter> C2"
        using hBY_int[rule_format, OF hC1Y, rule_format, OF hC2Y, rule_format, OF hbC12]
        by blast
      have hx_in3: "x \<in> bx3 \<times> bb3" using ha3 hb3 by (simp add: mem_Times_iff)
      have hsub3: "bx3 \<times> bb3 \<subseteq> b1 \<inter> b2"
        using hbx3sub hbb3sub hb1eq hb2eq by blast
      show "\<exists>b3\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
        apply (rule bexI[where x="bx3 \<times> bb3"])
         apply (rule conjI[OF hx_in3 hsub3])
        apply (rule CollectI, rule exI[where x=bx3], rule exI[where x=bb3])
        apply (intro conjI refl hbx3 hbb3)
        done
    qed
  qed
  (* topology_generated_by_basis UNIV D = product_topology_on TX TY *)
  have hDTP: "topology_generated_by_basis UNIV D = product_topology_on TX TY"
  proof (rule set_eqI)
    fix W
    show "W \<in> topology_generated_by_basis UNIV D \<longleftrightarrow> W \<in> product_topology_on TX TY"
    proof (rule iffI)
      assume hW: "W \<in> topology_generated_by_basis UNIV D"
      show "W \<in> product_topology_on TX TY"
        unfolding product_topology_on_def topology_generated_by_basis_def product_basis_def
      proof (rule CollectI, rule conjI, rule subset_UNIV, rule ballI)
        fix x assume hxW: "x \<in> W"
        obtain b where hbD: "b \<in> D" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
          using hW hxW unfolding topology_generated_by_basis_def by blast
        obtain B C where hBBX: "B \<in> BX" and hCBY: "C \<in> BY" and hbeq: "b = B \<times> C"
          using hbD unfolding D_def by blast
        have hBTX: "B \<in> TX" using hBX_open hBBX by blast
        have hCTY: "C \<in> TY" using hBY_open hCBY by blast
        show "\<exists>b\<in>{U \<times> V | U V. U \<in> TX \<and> V \<in> TY}. x \<in> b \<and> b \<subseteq> W"
          apply (rule bexI[where x="B \<times> C"])
           apply (rule conjI)
            using hxb hbeq apply simp
           using hbW hbeq apply simp
          apply (rule CollectI, rule exI[where x=B], rule exI[where x=C])
          apply (intro conjI refl hBTX hCTY)
          done
      qed
    next
      assume hW: "W \<in> product_topology_on TX TY"
      show "W \<in> topology_generated_by_basis UNIV D"
        unfolding topology_generated_by_basis_def D_def
      proof (rule CollectI, rule conjI, rule subset_UNIV, rule ballI)
        fix x assume hxW: "x \<in> W"
        obtain b where hbPB: "b \<in> product_basis TX TY" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
          using hW hxW unfolding product_topology_on_def topology_generated_by_basis_def by blast
        obtain U V where hUTX: "U \<in> TX" and hVTY: "V \<in> TY" and hbeq: "b = U \<times> V"
          using hbPB unfolding product_basis_def by blast
        have hxUV: "x \<in> U \<times> V" using hxb hbeq by simp
        have hfst: "fst x \<in> U" using hxUV[unfolded mem_Times_iff] by blast
        have hsnd: "snd x \<in> V" using hxUV[unfolded mem_Times_iff] by blast
        have hUcov: "\<forall>y\<in>U. \<exists>ba\<in>BX. y \<in> ba \<and> ba \<subseteq> U"
          using hUTX unfolding hTX_eq topology_generated_by_basis_def by blast
        have hVcov: "\<forall>y\<in>V. \<exists>bb\<in>BY. y \<in> bb \<and> bb \<subseteq> V"
          using hVTY unfolding hTY_eq topology_generated_by_basis_def by blast
        obtain ba where hbaX: "ba \<in> BX" and hxaba: "fst x \<in> ba" and hbaU: "ba \<subseteq> U"
          using hUcov[rule_format, OF hfst] by blast
        obtain bb where hbbY: "bb \<in> BY" and hxbbb: "snd x \<in> bb" and hbbV: "bb \<subseteq> V"
          using hVcov[rule_format, OF hsnd] by blast
        have hx_in: "x \<in> ba \<times> bb" using hxaba hxbbb by (simp add: mem_Times_iff)
        have hcovW: "ba \<times> bb \<subseteq> W"
          using hbaU hbbV hbeq hbW by blast
        show "\<exists>b\<in>{B \<times> C | B C. B \<in> BX \<and> C \<in> BY}. x \<in> b \<and> b \<subseteq> W"
          apply (rule bexI[where x="ba \<times> bb"])
           apply (rule conjI[OF hx_in hcovW])
          apply (rule CollectI, rule exI[where x=ba], rule exI[where x=bb])
          apply (intro conjI refl hbaX hbbY)
          done
      qed
    qed
  qed
  show "basis_for UNIV D (product_topology_on TX TY)"
    unfolding basis_for_def using hD_basis hDTP by simp
qed

(** from \S15 Theorem 15.2 [top1.tex:425] **)
(** LATEX VERSION: "Subbasis for product topology: preimages of opens under projections." **)
theorem Theorem_15_2:
  assumes "is_topology_on UNIV TX"
  assumes "is_topology_on UNIV TY"
  defines "S \<equiv> { preimage pi1 U | U. U \<in> TX } \<union> { preimage pi2 V | V. V \<in> TY }"
  shows "product_topology_on TX TY = topology_generated_by_subbasis UNIV S"
proof -
  let ?B = "product_basis TX TY"
  let ?P = "product_topology_on TX TY"

  have hUNIV_TX: "UNIV \<in> TX"
    using assms(1) unfolding is_topology_on_def by blast
  have hUNIV_TY: "UNIV \<in> TY"
    using assms(2) unfolding is_topology_on_def by blast

  have hInter_TX: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    using assms(1) unfolding is_topology_on_def by blast
  have hInter_TY: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY \<longrightarrow> \<Inter>F \<in> TY"
    using assms(2) unfolding is_topology_on_def by blast

  have hBasis: "is_basis_on UNIV ?B"
  proof -
    have hb_sub: "\<forall>b\<in>?B. b \<subseteq> UNIV"
      unfolding product_basis_def by blast
    have hb_cov: "\<forall>x\<in>UNIV. \<exists>b\<in>?B. x \<in> b"
    proof (rule ballI)
      fix x assume "x \<in> (UNIV::('a \<times> 'b) set)"
      show "\<exists>b\<in>?B. x \<in> b"
        unfolding product_basis_def
        apply (rule bexI[where x="UNIV \<times> UNIV"])
         apply simp
        apply (rule CollectI, rule exI[where x=UNIV], rule exI[where x=UNIV])
        apply (intro conjI refl hUNIV_TX hUNIV_TY)
        done
    qed
    have hb_int:
      "\<forall>b1\<in>?B. \<forall>b2\<in>?B. \<forall>x\<in>(b1 \<inter> b2). \<exists>b3\<in>?B. x \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2)"
    proof (intro ballI)
      fix b1 b2 assume hb1: "b1 \<in> ?B" and hb2: "b2 \<in> ?B"
      fix x assume hx: "x \<in> b1 \<inter> b2"
      obtain U1 V1 where hU1: "U1 \<in> TX" and hV1: "V1 \<in> TY" and hb1eq: "b1 = U1 \<times> V1"
        using hb1 unfolding product_basis_def by blast
      obtain U2 V2 where hU2: "U2 \<in> TX" and hV2: "V2 \<in> TY" and hb2eq: "b2 = U2 \<times> V2"
        using hb2 unfolding product_basis_def by blast
      have hU12: "U1 \<inter> U2 \<in> TX"
      proof -
        have "finite {U1,U2} \<and> {U1,U2} \<noteq> {} \<and> {U1,U2} \<subseteq> TX"
          using hU1 hU2 by auto
        hence "(\<Inter>{U1,U2}) \<in> TX"
          using hInter_TX[rule_format] by blast
        thus ?thesis by simp
      qed
      have hV12: "V1 \<inter> V2 \<in> TY"
      proof -
        have "finite {V1,V2} \<and> {V1,V2} \<noteq> {} \<and> {V1,V2} \<subseteq> TY"
          using hV1 hV2 by auto
        hence "(\<Inter>{V1,V2}) \<in> TY"
          using hInter_TY[rule_format] by blast
        thus ?thesis by simp
      qed
      have hb3: "(U1 \<inter> U2) \<times> (V1 \<inter> V2) \<in> ?B"
        unfolding product_basis_def
        apply (rule CollectI)
        apply (rule exI[where x="U1 \<inter> U2"])
        apply (rule exI[where x="V1 \<inter> V2"])
        apply (intro conjI refl hU12 hV12)
        done
      have hx3: "x \<in> (U1 \<inter> U2) \<times> (V1 \<inter> V2)"
        using hx hb1eq hb2eq by blast
      have hsub3: "(U1 \<inter> U2) \<times> (V1 \<inter> V2) \<subseteq> b1 \<inter> b2"
        using hb1eq hb2eq by blast
      show "\<exists>b3\<in>?B. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
        apply (rule bexI[where x="(U1 \<inter> U2) \<times> (V1 \<inter> V2)"])
         apply (intro conjI hx3 hsub3)
        apply (rule hb3)
        done
    qed
    show "is_basis_on UNIV ?B"
      unfolding is_basis_on_def
      apply (intro conjI)
        apply (rule hb_sub)
       apply (rule hb_cov)
      apply (rule hb_int)
      done
  qed

  have hBasis_for: "basis_for UNIV ?B ?P"
    unfolding basis_for_def product_topology_on_def using hBasis by simp

  have hP_union: "?P = { \<Union>U | U. U \<subseteq> ?B }"
    by (rule Lemma_13_1[OF hBasis_for])

  have hRect_in_finite_intersections: "?B \<subseteq> finite_intersections S"
  proof (rule subsetI)
    fix b assume hb: "b \<in> ?B"
    obtain U V where hU: "U \<in> TX" and hV: "V \<in> TY" and hbeq: "b = U \<times> V"
      using hb unfolding product_basis_def by blast
    have hUV_in: "{preimage pi1 U, preimage pi2 V} \<subseteq> S"
      unfolding S_def
    proof (rule subsetI)
      fix x assume hx: "x \<in> {preimage pi1 U, preimage pi2 V}"
      have hx_cases: "x = preimage pi1 U \<or> x = preimage pi2 V"
        using hx by simp
      show "x \<in> {preimage pi1 Ua |Ua. Ua \<in> TX} \<union> {preimage pi2 Va |Va. Va \<in> TY}"
      proof (rule disjE[OF hx_cases])
        assume "x = preimage pi1 U"
        show ?thesis
          apply (rule UnI1)
          apply (rule CollectI)
          apply (rule exI[where x=U])
          apply (intro conjI)
           apply (rule \<open>x = preimage pi1 U\<close>)
          apply (rule hU)
          done
      next
        assume "x = preimage pi2 V"
        show ?thesis
          apply (rule UnI2)
          apply (rule CollectI)
          apply (rule exI[where x=V])
          apply (intro conjI)
           apply (rule \<open>x = preimage pi2 V\<close>)
          apply (rule hV)
          done
      qed
    qed
    have hfin: "finite {preimage pi1 U, preimage pi2 V}"
      by simp
    have hb'': "preimage pi1 U \<inter> preimage pi2 V = U \<times> V"
      apply (rule set_eqI)
      apply (simp add: preimage_def pi1_def pi2_def mem_Times_iff)
      done
    have "b \<in> finite_intersections S"
      unfolding finite_intersections_def
      apply (rule CollectI)
      apply (rule exI[where x="{preimage pi1 U, preimage pi2 V}"])
      apply (intro conjI)
        apply (simp add: hbeq hb'')
       apply (rule hfin)
      apply (rule hUV_in)
      done
    thus "b \<in> finite_intersections S" .
  qed

  have hS_sub_P: "S \<subseteq> ?P"
  proof (rule subsetI)
    fix s assume hs: "s \<in> S"
    have "(\<exists>U. U \<in> TX \<and> s = preimage pi1 U) \<or> (\<exists>V. V \<in> TY \<and> s = preimage pi2 V)"
      using hs unfolding S_def by blast
    then show "s \<in> ?P"
    proof
      assume "\<exists>U. U \<in> TX \<and> s = preimage pi1 U"
      then obtain U where hU: "U \<in> TX" and hseq: "s = preimage pi1 U" by blast
      show "s \<in> ?P"
        unfolding product_topology_on_def topology_generated_by_basis_def product_basis_def
      proof (rule CollectI, rule conjI, rule subset_UNIV)
        show "\<forall>x\<in>s. \<exists>b\<in>{U \<times> V | U V. U \<in> TX \<and> V \<in> TY}. x \<in> b \<and> b \<subseteq> s"
        proof (rule ballI)
          fix x assume hx: "x \<in> s"
          have hxU: "fst x \<in> U"
            using hx unfolding hseq preimage_def pi1_def by simp
          have hxUV: "x \<in> U \<times> UNIV"
            using hxU by (simp add: mem_Times_iff)
          have hsub: "U \<times> UNIV \<subseteq> s"
            unfolding hseq preimage_def pi1_def by auto
          show "\<exists>b\<in>{U \<times> V | U V. U \<in> TX \<and> V \<in> TY}. x \<in> b \<and> b \<subseteq> s"
            apply (rule bexI[where x="U \<times> UNIV"])
             apply (intro conjI hxUV hsub)
            apply (rule CollectI)
            apply (rule exI[where x=U], rule exI[where x=UNIV])
            apply (intro conjI refl hU hUNIV_TY)
            done
        qed
      qed
    next
      assume "\<exists>V. V \<in> TY \<and> s = preimage pi2 V"
      then obtain V where hV: "V \<in> TY" and hseq: "s = preimage pi2 V" by blast
      show "s \<in> ?P"
        unfolding product_topology_on_def topology_generated_by_basis_def product_basis_def
      proof (rule CollectI, rule conjI, rule subset_UNIV)
        show "\<forall>x\<in>s. \<exists>b\<in>{U \<times> V | U V. U \<in> TX \<and> V \<in> TY}. x \<in> b \<and> b \<subseteq> s"
        proof (rule ballI)
          fix x assume hx: "x \<in> s"
          have hxV: "snd x \<in> V"
            using hx unfolding hseq preimage_def pi2_def by simp
          have hxUV: "x \<in> UNIV \<times> V"
            using hxV by (simp add: mem_Times_iff)
          have hsub: "UNIV \<times> V \<subseteq> s"
            unfolding hseq preimage_def pi2_def by auto
          show "\<exists>b\<in>{U \<times> V | U V. U \<in> TX \<and> V \<in> TY}. x \<in> b \<and> b \<subseteq> s"
            apply (rule bexI[where x="UNIV \<times> V"])
             apply (intro conjI hxUV hsub)
            apply (rule CollectI)
            apply (rule exI[where x=UNIV], rule exI[where x=V])
            apply (intro conjI refl hUNIV_TX hV)
            done
        qed
      qed
    qed
  qed

  have hBinInter: "\<forall>W1 W2. W1 \<in> ?P \<longrightarrow> W2 \<in> ?P \<longrightarrow> W1 \<inter> W2 \<in> ?P"
  proof (intro allI impI)
    fix W1 W2 assume hW1: "W1 \<in> ?P" and hW2: "W2 \<in> ?P"
    have hW1cov: "\<forall>x\<in>W1. \<exists>b\<in>?B. x \<in> b \<and> b \<subseteq> W1"
      using hW1 unfolding product_topology_on_def topology_generated_by_basis_def by blast
    have hW2cov: "\<forall>x\<in>W2. \<exists>b\<in>?B. x \<in> b \<and> b \<subseteq> W2"
      using hW2 unfolding product_topology_on_def topology_generated_by_basis_def by blast
    have hBint:
      "\<forall>b1\<in>?B. \<forall>b2\<in>?B. \<forall>x\<in>(b1 \<inter> b2). \<exists>b3\<in>?B. x \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2)"
      using hBasis unfolding is_basis_on_def by blast
    show "W1 \<inter> W2 \<in> ?P"
      unfolding product_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule subset_UNIV)
      show "\<forall>x\<in>W1 \<inter> W2. \<exists>b\<in>?B. x \<in> b \<and> b \<subseteq> W1 \<inter> W2"
      proof (rule ballI)
        fix x assume hx: "x \<in> W1 \<inter> W2"
        have hxW1: "x \<in> W1" and hxW2: "x \<in> W2" using hx by blast+
        obtain b1 where hb1: "b1 \<in> ?B" and hxb1: "x \<in> b1" and hb1W1: "b1 \<subseteq> W1"
          using hW1cov[rule_format, OF hxW1] by blast
        obtain b2 where hb2: "b2 \<in> ?B" and hxb2: "x \<in> b2" and hb2W2: "b2 \<subseteq> W2"
          using hW2cov[rule_format, OF hxW2] by blast
        obtain b3 where hb3: "b3 \<in> ?B" and hxb3: "x \<in> b3" and hb3sub: "b3 \<subseteq> b1 \<inter> b2"
          using hBint[rule_format, OF hb1, OF hb2] hxb1 hxb2 by blast
        have hb3W: "b3 \<subseteq> W1 \<inter> W2"
          using hb3sub hb1W1 hb2W2 by blast
        show "\<exists>b\<in>?B. x \<in> b \<and> b \<subseteq> W1 \<inter> W2"
          apply (rule bexI[where x=b3])
           apply (intro conjI hxb3 hb3W)
          apply (rule hb3)
          done
      qed
    qed
  qed

  have hUNIV_P: "UNIV \<in> ?P"
    unfolding product_topology_on_def topology_generated_by_basis_def product_basis_def
    apply (rule CollectI, rule conjI, rule subset_UNIV, rule ballI)
    apply (rule bexI[where x="UNIV \<times> UNIV"])
     apply simp
    apply (rule CollectI, rule exI[where x=UNIV], rule exI[where x=UNIV])
    apply (intro conjI refl hUNIV_TX hUNIV_TY)
    done

  have hFinInter_P: "\<And>F. finite F \<Longrightarrow> F \<subseteq> ?P \<Longrightarrow> \<Inter>F \<in> ?P"
  proof -
    fix F assume hfin: "finite F" and hsub: "F \<subseteq> ?P"
    show "\<Inter>F \<in> ?P"
      using hfin hsub
    proof (induction rule: finite_induct)
      case empty
      show "\<Inter>{} \<in> ?P"
        using hUNIV_P by simp
    next
      case (insert A F)
      have hAopen: "A \<in> ?P" using insert.prems by blast
      have hFsub: "F \<subseteq> ?P" using insert.prems by blast
      have hFopen: "\<Inter>F \<in> ?P" by (rule insert.IH[OF hFsub])
      have "A \<inter> \<Inter>F \<in> ?P"
        apply (rule hBinInter[rule_format])
         apply (rule hAopen)
        apply (rule hFopen)
        done
      thus "\<Inter>(insert A F) \<in> ?P"
        by simp
    qed
  qed

  have hP_top: "is_topology_on (UNIV::('a \<times> 'b) set) ?P"
  proof (unfold is_topology_on_def, intro conjI)
    show "{} \<in> ?P"
      unfolding product_topology_on_def topology_generated_by_basis_def by blast
    show "UNIV \<in> ?P" using hUNIV_P .
    show "\<forall>U. U \<subseteq> ?P \<longrightarrow> \<Union>U \<in> ?P"
    proof (intro allI impI)
      fix U assume hU: "U \<subseteq> ?P"
      show "\<Union>U \<in> ?P"
        unfolding product_topology_on_def topology_generated_by_basis_def
      proof (rule CollectI, rule conjI, rule subset_UNIV)
        show "\<forall>x\<in>\<Union>U. \<exists>b\<in>?B. x \<in> b \<and> b \<subseteq> \<Union>U"
        proof (rule ballI)
          fix x assume hx: "x \<in> \<Union>U"
          obtain W where hWU: "W \<in> U" and hxW: "x \<in> W" using hx by blast
          have hWT: "W \<in> ?P" using hU hWU by blast
          have hWcov: "\<forall>y\<in>W. \<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> W"
            using hWT unfolding product_topology_on_def topology_generated_by_basis_def by blast
          obtain b where hbB: "b \<in> ?B" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
            using hWcov[rule_format, OF hxW] by blast
          have hbU: "b \<subseteq> \<Union>U"
            apply (rule subset_trans[OF hbW])
            apply (rule Union_upper[OF hWU])
            done
          show "\<exists>b\<in>?B. x \<in> b \<and> b \<subseteq> \<Union>U"
            apply (rule bexI[where x=b])
             apply (intro conjI hxb hbU)
            apply (rule hbB)
            done
        qed
      qed
    qed
    show "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?P \<longrightarrow> \<Inter>F \<in> ?P"
    proof (intro allI impI)
      fix F assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?P"
      have hfin: "finite F" using hF by blast
      have hsub: "F \<subseteq> ?P" using hF by blast
      show "\<Inter>F \<in> ?P"
        by (rule hFinInter_P[OF hfin hsub])
    qed
  qed

  have hFinInter_S_sub_P: "finite_intersections S \<subseteq> ?P"
  proof (rule subsetI)
    fix u assume hu: "u \<in> finite_intersections S"
    obtain F where hfin: "finite F" and hFsub: "F \<subseteq> S" and hueq: "u = \<Inter>F"
      using hu unfolding finite_intersections_def by blast
    have hFsubP: "F \<subseteq> ?P"
      apply (rule subset_trans[OF hFsub])
      apply (rule hS_sub_P)
      done
    have "u \<in> ?P"
    proof (cases "F = {}")
      case True
      show ?thesis
        using hUNIV_P hueq True by simp
    next
      case False
      have "finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?P" using hfin False hFsubP by blast
      hence "(\<Inter>F) \<in> ?P"
        using hP_top unfolding is_topology_on_def by blast
      thus ?thesis using hueq by simp
    qed
    thus "u \<in> ?P" .
  qed

  show "?P = topology_generated_by_subbasis UNIV S"
  proof (rule set_eqI)
    fix W
    show "W \<in> ?P \<longleftrightarrow> W \<in> topology_generated_by_subbasis UNIV S"
    proof (rule iffI)
      assume hW: "W \<in> ?P"
      have "W \<in> { \<Union>U | U. U \<subseteq> ?B }"
        using hW unfolding hP_union by simp
      then obtain U where hWU: "W = \<Union>U" and hUB: "U \<subseteq> ?B" by blast
      have hUsub: "U \<subseteq> finite_intersections S"
        apply (rule subset_trans[OF hUB])
        apply (rule hRect_in_finite_intersections)
        done
      show "W \<in> topology_generated_by_subbasis UNIV S"
        unfolding topology_generated_by_subbasis_def
        apply (rule CollectI)
        apply (rule exI[where x=U])
        apply (intro conjI)
         apply (rule hWU)
        apply (rule hUsub)
        done
    next
      assume hW: "W \<in> topology_generated_by_subbasis UNIV S"
      obtain U where hWU: "W = \<Union>U" and hUsub: "U \<subseteq> finite_intersections S"
        using hW unfolding topology_generated_by_subbasis_def by blast
      have hUsubP: "U \<subseteq> ?P"
        apply (rule subset_trans[OF hUsub])
        apply (rule hFinInter_S_sub_P)
        done
      show "W \<in> ?P"
        using hP_top hUsubP hWU unfolding is_topology_on_def by blast
    qed
  qed
qed


section \<open>\<S>16 The Subspace Topology\<close>

(** from \S16 Definition (Subspace topology) [top1.tex:450] **)
(** LATEX VERSION: "T_Y = {Y \<inter> U | U \<in> T}." **)
definition subspace_topology :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "subspace_topology X T Y = {Y \<inter> U | U. U \<in> T}"

(** Subspace topology is a topology (requires the carrier inclusion Y \<subseteq> X). **)
lemma subspace_topology_is_topology_on:
  assumes hT: "is_topology_on X T"
  assumes hYX: "Y \<subseteq> X"
  shows "is_topology_on Y (subspace_topology X T Y)"
proof -
  let ?TY = "subspace_topology X T Y"
  have empty_T: "{} \<in> T"
    by (rule conjunct1[OF hT[unfolded is_topology_on_def]])
  have X_T: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
  have union_T: "\<forall>U. U \<subseteq> T \<longrightarrow> \<Union>U \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])

  have empty_TY: "{} \<in> ?TY"
    unfolding subspace_topology_def
    apply (rule CollectI)
    apply (rule exI[where x="{}"])
    apply (intro conjI)
     apply simp
    apply (rule empty_T)
    done

  have Y_TY: "Y \<in> ?TY"
    unfolding subspace_topology_def
    apply (rule CollectI)
    apply (rule exI[where x=X])
    apply (intro conjI)
     apply (simp add: hYX Int_absorb2)
    apply (rule X_T)
    done

  have union_TY: "\<forall>Uc. Uc \<subseteq> ?TY \<longrightarrow> \<Union>Uc \<in> ?TY"
  proof (intro allI impI)
    fix Uc
    assume hUc: "Uc \<subseteq> ?TY"

    define V where "V = {U. U \<in> T \<and> (Y \<inter> U) \<in> Uc}"
    have hVsub: "V \<subseteq> T"
      unfolding V_def by blast

    have hUnion_eq: "\<Union>Uc = Y \<inter> \<Union>V"
    proof (rule set_eqI)
      fix x
      show "x \<in> \<Union>Uc \<longleftrightarrow> x \<in> Y \<inter> \<Union>V"
      proof
        assume hx: "x \<in> \<Union>Uc"
        obtain W where hW: "W \<in> Uc" and hxW: "x \<in> W"
          using hx by blast
        have hW_TY: "W \<in> ?TY"
          using hUc hW by blast
        obtain U where hU: "U \<in> T" and hWeq: "W = Y \<inter> U"
          using hW_TY unfolding subspace_topology_def by blast
        have hxY: "x \<in> Y" and hxU: "x \<in> U"
          using hxW hWeq by blast+
        have hUV: "U \<in> V"
          unfolding V_def using hU hW hWeq by blast
        have "x \<in> \<Union>V"
          by (rule UnionI[OF hUV], rule hxU)
        thus "x \<in> Y \<inter> \<Union>V"
          using hxY by blast
      next
        assume hx: "x \<in> Y \<inter> \<Union>V"
        have hxY: "x \<in> Y" and hxV: "x \<in> \<Union>V"
          using hx by blast+
        obtain U where hU: "U \<in> V" and hxU: "x \<in> U"
          using hxV by blast
        have hU_T: "U \<in> T" and hYU_Uc: "Y \<inter> U \<in> Uc"
          using hU unfolding V_def by blast+
        have "x \<in> Y \<inter> U" using hxY hxU by blast
        thus "x \<in> \<Union>Uc"
          by (rule UnionI[OF hYU_Uc])
      qed
    qed

    have hUnionV_T: "\<Union>V \<in> T"
      by (rule union_T[rule_format, OF hVsub])

    show "\<Union>Uc \<in> ?TY"
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="\<Union>V"])
      apply (intro conjI)
       apply (rule hUnion_eq)
      apply (rule hUnionV_T)
      done
  qed

  have inter_TY:
    "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TY \<longrightarrow> \<Inter>F \<in> ?TY"
  proof (intro allI impI)
    fix F
    assume hfin: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TY"
    have hFfin: "finite F" and hFne: "F \<noteq> {}" and hFsub: "F \<subseteq> ?TY"
      using hfin by blast+

    have repr:
      "\<exists>U\<in>T. \<Inter>F = Y \<inter> U"
      using hFfin hFne hFsub
    proof (induction rule: finite_induct)
      case empty
      thus ?case by blast
    next
      case (insert W G)
      have hW: "W \<in> ?TY"
        using insert.prems by blast
      obtain UW where hUW: "UW \<in> T" and hWeq: "W = Y \<inter> UW"
        using hW unfolding subspace_topology_def by blast
      show ?case
      proof (cases "G = {}")
        case True
        have "\<Inter>(insert W G) = Y \<inter> UW"
          using True hWeq by simp
        show ?thesis
        proof (rule bexI[where x=UW])
          show "UW \<in> T" by (rule hUW)
          show "\<Inter>(insert W G) = Y \<inter> UW"
            by (rule \<open>\<Inter>(insert W G) = Y \<inter> UW\<close>)
        qed
      next
        case False
        have hGne: "G \<noteq> {}" using False .
        have hGsub: "G \<subseteq> ?TY" using insert.prems by blast
        obtain UG where hUG: "UG \<in> T" and hGeq: "\<Inter>G = Y \<inter> UG"
          using insert.IH[OF hGne hGsub] by blast
        have hInter2: "UW \<inter> UG \<in> T"
          by (rule topology_inter2[OF hT hUW hUG])
        have "\<Inter>(insert W G) = Y \<inter> (UW \<inter> UG)"
          using hWeq hGeq by blast
        show ?thesis
        proof (rule bexI[where x="UW \<inter> UG"])
          show "UW \<inter> UG \<in> T" by (rule hInter2)
          show "\<Inter>(insert W G) = Y \<inter> (UW \<inter> UG)"
            by (rule \<open>\<Inter>(insert W G) = Y \<inter> (UW \<inter> UG)\<close>)
        qed
      qed
    qed

    then obtain U where hU: "U \<in> T" and hInter: "\<Inter>F = Y \<inter> U"
      by blast
    show "\<Inter>F \<in> ?TY"
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      apply (intro conjI)
       apply (rule hInter)
      apply (rule hU)
      done
  qed

  show ?thesis
    unfolding is_topology_on_def
  proof (intro conjI)
    show "{} \<in> ?TY" using empty_TY .
    show "Y \<in> ?TY" using Y_TY .
    show "\<forall>U. U \<subseteq> ?TY \<longrightarrow> \<Union>U \<in> ?TY" using union_TY .
    show "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TY \<longrightarrow> \<Inter>F \<in> ?TY"
      using inter_TY .
  qed
qed

(** Subspace topology is associative: taking a subspace of a subspace gives the same opens. **)
lemma subspace_topology_trans:
  assumes hCB: "C \<subseteq> B"
  shows "subspace_topology B (subspace_topology X T B) C = subspace_topology X T C"
proof (rule set_eqI)
  fix W
  show "W \<in> subspace_topology B (subspace_topology X T B) C \<longleftrightarrow> W \<in> subspace_topology X T C"
  proof
    assume hW: "W \<in> subspace_topology B (subspace_topology X T B) C"
    obtain V where hV: "V \<in> subspace_topology X T B" and hW_eq: "W = C \<inter> V"
      using hW unfolding subspace_topology_def by blast
    obtain U where hU: "U \<in> T" and hV_eq: "V = B \<inter> U"
      using hV unfolding subspace_topology_def by blast
    have hW_eq2: "W = C \<inter> U"
      using hW_eq hV_eq hCB by blast
    show "W \<in> subspace_topology X T C"
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      apply (intro conjI)
       apply (rule hW_eq2)
      apply (rule hU)
      done
  next
    assume hW: "W \<in> subspace_topology X T C"
    obtain U where hU: "U \<in> T" and hW_eq: "W = C \<inter> U"
      using hW unfolding subspace_topology_def by blast
    have hV: "B \<inter> U \<in> subspace_topology X T B"
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      apply (intro conjI)
       apply (rule refl)
      apply (rule hU)
      done
    have hW_eq2: "W = C \<inter> (B \<inter> U)"
      using hW_eq hCB by blast
    show "W \<in> subspace_topology B (subspace_topology X T B) C"
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x="B \<inter> U"])
      apply (intro conjI)
       apply (rule hW_eq2)
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      apply (intro conjI)
       apply (rule refl)
      apply (rule hU)
      done
  qed
qed

(** from \S16 Lemma 16.1 [top1.tex:473] **)
(** LATEX VERSION: "If B is a basis for X, then {B\<inter>Y} is a basis for subspace topology on Y." **)
theorem Lemma_16_1:
  fixes Y :: "'a set"
  assumes hB: "basis_for X B T"
  assumes hYX: "Y \<subseteq> X"
  defines "BY \<equiv> {b \<inter> Y | b. b \<in> B}"
  shows "basis_for Y BY (subspace_topology X T Y)"
proof -
  have hBasis: "is_basis_on X B"
    by (rule conjunct1[OF hB[unfolded basis_for_def]])
  have hBX: "\<forall>b\<in>B. b \<subseteq> X"
    by (rule conjunct1[OF hBasis[unfolded is_basis_on_def]])
  have hBcov: "\<forall>x\<in>X. \<exists>b\<in>B. x \<in> b"
    by (rule conjunct1[OF conjunct2[OF hBasis[unfolded is_basis_on_def]]])
  have hBinter: "\<forall>b1\<in>B. \<forall>b2\<in>B. \<forall>x\<in>(b1 \<inter> b2). \<exists>b3\<in>B. x \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2)"
    by (rule conjunct2[OF conjunct2[OF hBasis[unfolded is_basis_on_def]]])
  have hT_def: "T = topology_generated_by_basis X B"
    by (rule conjunct2[OF hB[unfolded basis_for_def]])
  (* Every basis element of B is open in T *)
  have basis_open: "\<forall>b\<in>B. b \<in> T"
  proof (rule ballI)
    fix b assume hbB: "b \<in> B"
    have hbX: "b \<subseteq> X" by (rule bspec[OF hBX, OF hbB])
    have hbT: "b \<in> topology_generated_by_basis X B"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule hbX)
      show "\<forall>y\<in>b. \<exists>b'\<in>B. y \<in> b' \<and> b' \<subseteq> b"
      proof (rule ballI)
        fix y assume hyb: "y \<in> b"
        obtain b3 where hb3B: "b3 \<in> B" and hyb3: "y \<in> b3" and hb3sub: "b3 \<subseteq> b \<inter> b"
          using hBinter[rule_format, OF hbB, OF hbB] hyb by blast
        have hb3sub': "b3 \<subseteq> b" using hb3sub by (simp only: Int_absorb)
        show "\<exists>b'\<in>B. y \<in> b' \<and> b' \<subseteq> b"
          apply (rule bexI[where x=b3])
           apply (rule conjI[OF hyb3 hb3sub'])
          apply (rule hb3B)
          done
      qed
    qed
    show "b \<in> T" using hbT hT_def by simp
  qed
  (* Arbitrary unions are in T *)
  have union_T: "\<forall>U. U \<subseteq> T \<longrightarrow> \<Union>U \<in> T"
  proof (rule allI, rule impI)
    fix U assume hU: "U \<subseteq> T"
    have hUgen: "U \<subseteq> topology_generated_by_basis X B"
      using hU hT_def by simp
    show "\<Union>U \<in> T"
      unfolding hT_def topology_generated_by_basis_def
    proof (rule CollectI, rule conjI)
      show "\<Union>U \<subseteq> X"
        using hUgen unfolding topology_generated_by_basis_def by blast
      show "\<forall>x\<in>\<Union>U. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> \<Union>U"
      proof (rule ballI)
        fix x assume hx: "x \<in> \<Union>U"
        obtain V where hVU: "V \<in> U" and hxV: "x \<in> V" using hx by blast
        have hVcov: "\<forall>y\<in>V. \<exists>b\<in>B. y \<in> b \<and> b \<subseteq> V"
          using hVU hUgen unfolding topology_generated_by_basis_def by blast
        obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbV: "b \<subseteq> V"
          using hVcov[rule_format, OF hxV] by blast
        show "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> \<Union>U"
          apply (rule bexI[where x=b])
           apply (rule conjI[OF hxb])
           apply (rule subset_trans[OF hbV], rule Union_upper[OF hVU])
          apply (rule hbB)
          done
      qed
    qed
  qed
  (* BY has the three is_basis_on conditions *)
  have hBY1: "\<forall>c\<in>BY. c \<subseteq> Y"
    unfolding BY_def by blast
  have hBY2: "\<forall>y\<in>Y. \<exists>c\<in>BY. y \<in> c"
  proof (rule ballI)
    fix y assume hyY: "y \<in> Y"
    have hyX: "y \<in> X" by (rule subsetD[OF hYX, OF hyY])
    obtain b where hbB: "b \<in> B" and hyb: "y \<in> b"
      using hBcov[rule_format, OF hyX] by blast
    show "\<exists>c\<in>BY. y \<in> c"
      apply (rule bexI[where x="b \<inter> Y"])
       apply (rule IntI[OF hyb hyY])
      apply (simp only: BY_def, rule CollectI, rule exI[where x=b], rule conjI[OF refl hbB])
      done
  qed
  have hBY3: "\<forall>c1\<in>BY. \<forall>c2\<in>BY. \<forall>y\<in>(c1 \<inter> c2). \<exists>c3\<in>BY. y \<in> c3 \<and> c3 \<subseteq> (c1 \<inter> c2)"
  proof (rule ballI, rule ballI, rule ballI)
    fix c1 c2 y
    assume hc1: "c1 \<in> BY" and hc2: "c2 \<in> BY" and hyc12: "y \<in> c1 \<inter> c2"
    obtain b1 where hb1B: "b1 \<in> B" and hc1eq: "c1 = b1 \<inter> Y"
      using hc1 unfolding BY_def by blast
    obtain b2 where hb2B: "b2 \<in> B" and hc2eq: "c2 = b2 \<inter> Y"
      using hc2 unfolding BY_def by blast
    have hyY: "y \<in> Y" using hyc12 hc1eq by blast
    have hyb12: "y \<in> b1 \<inter> b2" using hyc12 hc1eq hc2eq by blast
    obtain b3 where hb3B: "b3 \<in> B" and hyb3: "y \<in> b3" and hb3sub: "b3 \<subseteq> b1 \<inter> b2"
      using hBinter[rule_format, OF hb1B, OF hb2B, OF hyb12] by blast
    have hb3Ysub: "b3 \<inter> Y \<subseteq> c1 \<inter> c2"
      using hb3sub hc1eq hc2eq by blast
    show "\<exists>c3\<in>BY. y \<in> c3 \<and> c3 \<subseteq> c1 \<inter> c2"
      apply (rule bexI[where x="b3 \<inter> Y"])
       apply (rule conjI)
        apply (rule IntI[OF hyb3 hyY])
       apply (rule hb3Ysub)
      apply (simp only: BY_def, rule CollectI, rule exI[where x=b3], rule conjI[OF refl hb3B])
      done
  qed
  have hBYbasis: "is_basis_on Y BY"
    unfolding is_basis_on_def
    apply (rule conjI[OF hBY1])
    apply (rule conjI[OF hBY2 hBY3])
    done
  (* Topology equality: subspace_topology X T Y = topology_generated_by_basis Y BY *)
  have hTeq: "subspace_topology X T Y = topology_generated_by_basis Y BY"
    unfolding subspace_topology_def
  proof (rule set_eqI)
    fix V
    show "V \<in> {Y \<inter> U | U. U \<in> T} \<longleftrightarrow> V \<in> topology_generated_by_basis Y BY"
    proof (rule iffI)
      (* subspace_topology ⊆ tgb Y BY *)
      assume hV: "V \<in> {Y \<inter> U | U. U \<in> T}"
      obtain U where hUT: "U \<in> T" and hVYU: "V = Y \<inter> U" using hV by blast
      have hUgen: "U \<in> topology_generated_by_basis X B" using hUT hT_def by simp
      have hUcov: "\<forall>x\<in>U. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U"
        using hUgen unfolding topology_generated_by_basis_def by blast
      have hVgen: "V \<in> topology_generated_by_basis Y BY"
        unfolding topology_generated_by_basis_def
      proof (rule CollectI, rule conjI)
        show "V \<subseteq> Y" using hVYU by blast
        show "\<forall>y\<in>V. \<exists>c\<in>BY. y \<in> c \<and> c \<subseteq> V"
        proof (rule ballI)
          fix y assume hyV: "y \<in> V"
          have hyU: "y \<in> U" using hyV hVYU by blast
          have hyY: "y \<in> Y" using hyV hVYU by blast
          obtain b where hbB: "b \<in> B" and hyb: "y \<in> b" and hbU: "b \<subseteq> U"
            using hUcov[rule_format, OF hyU] by blast
          have hbYsub: "b \<inter> Y \<subseteq> V" using hbU hVYU by blast
          show "\<exists>c\<in>BY. y \<in> c \<and> c \<subseteq> V"
            apply (rule bexI[where x="b \<inter> Y"])
             apply (rule conjI)
              apply (rule IntI[OF hyb hyY])
             apply (rule hbYsub)
            apply (simp only: BY_def, rule CollectI, rule exI[where x=b], rule conjI[OF refl hbB])
            done
        qed
      qed
      show "V \<in> topology_generated_by_basis Y BY" by (rule hVgen)
    next
      (* tgb Y BY ⊆ subspace_topology *)
      assume hV: "V \<in> topology_generated_by_basis Y BY"
      have hVsub: "V \<subseteq> Y" and hVcov: "\<forall>y\<in>V. \<exists>c\<in>BY. y \<in> c \<and> c \<subseteq> V"
        using hV unfolding topology_generated_by_basis_def by blast+
      have hVcov2: "\<forall>y\<in>V. \<exists>b\<in>B. y \<in> b \<and> b \<inter> Y \<subseteq> V"
        using hVcov unfolding BY_def by blast
      have hW_sub: "{b \<in> B. b \<inter> Y \<subseteq> V} \<subseteq> T"
        using basis_open by blast
      have hW_T: "\<Union>{b \<in> B. b \<inter> Y \<subseteq> V} \<in> T"
        by (rule union_T[rule_format, OF hW_sub])
      have hVeq: "V = Y \<inter> \<Union>{b \<in> B. b \<inter> Y \<subseteq> V}"
      proof (rule set_eqI)
        fix y
        show "y \<in> V \<longleftrightarrow> y \<in> Y \<inter> \<Union>{b \<in> B. b \<inter> Y \<subseteq> V}"
        proof (rule iffI)
          assume hyV: "y \<in> V"
          have hyY: "y \<in> Y" using hyV hVsub by blast
          obtain b where hbB: "b \<in> B" and hyb: "y \<in> b" and hbYV: "b \<inter> Y \<subseteq> V"
            using hVcov2[rule_format, OF hyV] by blast
          show "y \<in> Y \<inter> \<Union>{b \<in> B. b \<inter> Y \<subseteq> V}"
            using hyY hyb hbB hbYV by blast
        next
          assume hy: "y \<in> Y \<inter> \<Union>{b \<in> B. b \<inter> Y \<subseteq> V}"
          have hyY: "y \<in> Y" using hy by blast
          obtain b where hb: "b \<in> {b \<in> B. b \<inter> Y \<subseteq> V}" and hyb: "y \<in> b"
            using hy by blast
          show "y \<in> V" using hyY hyb hb by blast
        qed
      qed
      show "V \<in> {Y \<inter> U | U. U \<in> T}"
        apply (rule CollectI, rule exI[where x="\<Union>{b \<in> B. b \<inter> Y \<subseteq> V}"])
        apply (rule conjI[OF hVeq hW_T])
        done
    qed
  qed
  show "basis_for Y BY (subspace_topology X T Y)"
    unfolding basis_for_def
    apply (rule conjI[OF hBYbasis hTeq])
    done
qed

(** from \S16 Lemma 16.2 [top1.tex:486] **)
(** LATEX VERSION: "If U open in Y and Y open in X, then U open in X." **)
theorem Lemma_16_2:
  assumes "is_topology_on X T"
  assumes "Y \<in> T"  (* Y open in X *)
  assumes "U \<in> subspace_topology X T Y"
  shows "U \<in> T"
proof -
  from assms(3) obtain V where hV: "V \<in> T" and hU: "U = Y \<inter> V"
    unfolding subspace_topology_def by blast
  from assms(1) have inter_T: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
    unfolding is_topology_on_def by blast
  have fin: "finite {Y, V}" by simp
  have sub: "{Y, V} \<subseteq> T" using assms(2) hV by simp
  have "\<Inter>{Y, V} \<in> T" using inter_T fin sub by blast
  moreover have "\<Inter>{Y, V} = Y \<inter> V" by simp
  ultimately show "U \<in> T" using hU by simp
qed

(** from \S16 Theorem 16.3 [top1.tex:492] **)
(** LATEX VERSION: "Product topology on A\<times>B equals subspace topology from X\<times>Y." **)
theorem Theorem_16_3:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  shows "product_topology_on (subspace_topology X TX A) (subspace_topology Y TY B)
       = subspace_topology (X \<times> Y) (product_topology_on TX TY) (A \<times> B)"
proof (rule set_eqI)
  fix W
  show "W \<in> product_topology_on (subspace_topology X TX A) (subspace_topology Y TY B)
      \<longleftrightarrow> W \<in> subspace_topology (X \<times> Y) (product_topology_on TX TY) (A \<times> B)"
  proof (rule iffI)
    (* LHS \<Rightarrow> RHS *)
    assume hW: "W \<in> product_topology_on (subspace_topology X TX A) (subspace_topology Y TY B)"
    (* Extract covering condition from LHS membership *)
    have hWmem: "W \<subseteq> UNIV \<and>
        (\<forall>p\<in>W. \<exists>b \<in> product_basis (subspace_topology X TX A) (subspace_topology Y TY B).
                p \<in> b \<and> b \<subseteq> W)"
      using hW unfolding product_topology_on_def topology_generated_by_basis_def
      by blast
    have hWcov0: "\<forall>p\<in>W. \<exists>b \<in> product_basis (subspace_topology X TX A) (subspace_topology Y TY B).
                           p \<in> b \<and> b \<subseteq> W"
      using hWmem by blast
    (* Extract U, V from basis membership *)
    have hWcov: "\<forall>p\<in>W. \<exists>U\<in>TX. \<exists>V\<in>TY. p \<in> (A \<inter> U) \<times> (B \<inter> V) \<and> (A \<inter> U) \<times> (B \<inter> V) \<subseteq> W"
    proof (rule ballI)
      fix p assume hpW: "p \<in> W"
      obtain b where hb: "b \<in> product_basis (subspace_topology X TX A) (subspace_topology Y TY B)"
          and hpb: "p \<in> b" and hbW: "b \<subseteq> W"
        using hWcov0[rule_format, OF hpW] by blast
      obtain P Q where hbeq: "b = P \<times> Q"
          and hPTA: "P \<in> subspace_topology X TX A" and hQTB: "Q \<in> subspace_topology Y TY B"
        using hb unfolding product_basis_def by blast
      obtain U where hUT: "U \<in> TX" and hPeq: "P = A \<inter> U"
        using hPTA unfolding subspace_topology_def by blast
      obtain V where hVT: "V \<in> TY" and hQeq: "Q = B \<inter> V"
        using hQTB unfolding subspace_topology_def by blast
      have hbeq2: "b = (A \<inter> U) \<times> (B \<inter> V)" using hbeq hPeq hQeq by simp
      show "\<exists>U\<in>TX. \<exists>V\<in>TY. p \<in> (A \<inter> U) \<times> (B \<inter> V) \<and> (A \<inter> U) \<times> (B \<inter> V) \<subseteq> W"
        apply (rule bexI[where x=U], rule bexI[where x=V])
          apply (rule conjI)
           using hpb hbeq2 apply blast
          using hbW hbeq2 apply blast
        apply (rule hVT, rule hUT)
        done
    qed
    (* Define W' = \<Union> of product opens whose A\<times>B-restriction is inside W *)
    let ?G = "{U \<times> V | U V. U \<in> TX \<and> V \<in> TY \<and> (A \<inter> U) \<times> (B \<inter> V) \<subseteq> W}"
    let ?W' = "\<Union>?G"
    have hW'T: "?W' \<in> product_topology_on TX TY"
      unfolding product_topology_on_def topology_generated_by_basis_def product_basis_def
    proof (rule CollectI, rule conjI, rule subset_UNIV)
      show "\<forall>p\<in>?W'. \<exists>b\<in>{U \<times> V | U V. U \<in> TX \<and> V \<in> TY}. p \<in> b \<and> b \<subseteq> ?W'"
      proof (rule ballI)
        fix p assume hp: "p \<in> ?W'"
        obtain UV where hUVG: "UV \<in> ?G" and hpUV: "p \<in> UV" using hp by blast
        obtain U V where hUT: "U \<in> TX" and hVT: "V \<in> TY"
            and hUVW: "(A \<inter> U) \<times> (B \<inter> V) \<subseteq> W" and hUVeq: "UV = U \<times> V"
          using hUVG by blast
        have hpinUV: "p \<in> U \<times> V" using hpUV hUVeq by simp
        have hUVsubW': "U \<times> V \<subseteq> ?W'"
          apply (rule Union_upper)
          apply (rule CollectI, rule exI[where x=U], rule exI[where x=V])
          apply (intro conjI hUT hVT hUVW refl)
          done
        show "\<exists>b\<in>{U \<times> V | U V. U \<in> TX \<and> V \<in> TY}. p \<in> b \<and> b \<subseteq> ?W'"
          apply (rule bexI[where x="U \<times> V"])
           apply (rule conjI[OF hpinUV hUVsubW'])
          apply (rule CollectI, rule exI[where x=U], rule exI[where x=V])
          apply (intro conjI hUT hVT refl)
          done
      qed
    qed
    have hWeq: "W = A \<times> B \<inter> ?W'"
    proof (rule set_eqI)
      fix p
      show "p \<in> W \<longleftrightarrow> p \<in> A \<times> B \<inter> ?W'"
      proof (rule iffI)
        assume hpW: "p \<in> W"
        obtain U V where hUT: "U \<in> TX" and hVT: "V \<in> TY"
            and hpAUBV: "p \<in> (A \<inter> U) \<times> (B \<inter> V)" and hUVW: "(A \<inter> U) \<times> (B \<inter> V) \<subseteq> W"
          using hWcov[rule_format, OF hpW] by blast
        have hpAB: "p \<in> A \<times> B" using hpAUBV by blast
        have hUVinG: "U \<times> V \<in> ?G"
          apply (rule CollectI, rule exI[where x=U], rule exI[where x=V])
          apply (intro conjI hUT hVT hUVW refl)
          done
        have hpinUV: "p \<in> U \<times> V" using hpAUBV by blast
        have hpW': "p \<in> ?W'" using hpinUV hUVinG by blast
        show "p \<in> A \<times> B \<inter> ?W'" using hpAB hpW' by blast
      next
        assume hp: "p \<in> A \<times> B \<inter> ?W'"
        have hpAB: "p \<in> A \<times> B" using hp by blast
        have hpW': "p \<in> ?W'" using hp by blast
        obtain UV where hUVG: "UV \<in> ?G" and hpUV2: "p \<in> UV" using hpW' by blast
        obtain U V where hUT: "U \<in> TX" and hVT: "V \<in> TY"
            and hUVW: "(A \<inter> U) \<times> (B \<inter> V) \<subseteq> W" and hUVeq: "UV = U \<times> V"
          using hUVG by blast
        have hpinUV: "p \<in> U \<times> V" using hpUV2 hUVeq by simp
        have hpAUBV: "p \<in> (A \<inter> U) \<times> (B \<inter> V)" using hpAB hpinUV by blast
        show "p \<in> W" using hUVW hpAUBV by blast
      qed
    qed
    show "W \<in> subspace_topology (X \<times> Y) (product_topology_on TX TY) (A \<times> B)"
      unfolding subspace_topology_def
      apply (rule CollectI, rule exI[where x="?W'"])
      apply (rule conjI[OF hWeq hW'T])
      done
  next
    (* RHS \<Rightarrow> LHS *)
    assume hW: "W \<in> subspace_topology (X \<times> Y) (product_topology_on TX TY) (A \<times> B)"
    obtain W' where hW'T: "W' \<in> product_topology_on TX TY" and hWeq: "W = A \<times> B \<inter> W'"
      using hW unfolding subspace_topology_def by blast
    have hW'mem: "\<forall>p\<in>W'. \<exists>b \<in> product_basis TX TY. p \<in> b \<and> b \<subseteq> W'"
      using hW'T unfolding product_topology_on_def topology_generated_by_basis_def
      by blast
    have hW'cov: "\<forall>p\<in>W'. \<exists>U\<in>TX. \<exists>V\<in>TY. p \<in> U \<times> V \<and> U \<times> V \<subseteq> W'"
    proof (rule ballI)
      fix p assume hpW': "p \<in> W'"
      obtain b where hb: "b \<in> product_basis TX TY" and hpb: "p \<in> b" and hbW': "b \<subseteq> W'"
        using hW'mem[rule_format, OF hpW'] by blast
      obtain U V where hUT: "U \<in> TX" and hVT: "V \<in> TY" and hbeq: "b = U \<times> V"
        using hb unfolding product_basis_def by blast
      show "\<exists>U\<in>TX. \<exists>V\<in>TY. p \<in> U \<times> V \<and> U \<times> V \<subseteq> W'"
        apply (rule bexI[where x=U], rule bexI[where x=V])
          apply (rule conjI)
           using hpb hbeq apply blast
          using hbW' hbeq apply blast
        apply (rule hVT, rule hUT)
        done
    qed
    show "W \<in> product_topology_on (subspace_topology X TX A) (subspace_topology Y TY B)"
      unfolding product_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule subset_UNIV)
      show "\<forall>p\<in>W. \<exists>b \<in> product_basis (subspace_topology X TX A) (subspace_topology Y TY B). p \<in> b \<and> b \<subseteq> W"
      proof (rule ballI)
        fix p assume hpW: "p \<in> W"
        have hpAB: "p \<in> A \<times> B" using hpW hWeq by blast
        have hpW': "p \<in> W'" using hpW hWeq by blast
        obtain U V where hUT: "U \<in> TX" and hVT: "V \<in> TY"
            and hpUV: "p \<in> U \<times> V" and hUVW': "U \<times> V \<subseteq> W'"
          using hW'cov[rule_format, OF hpW'] by blast
        have hpAUBV: "p \<in> (A \<inter> U) \<times> (B \<inter> V)" using hpAB hpUV by blast
        have hAUBV_sub: "(A \<inter> U) \<times> (B \<inter> V) \<subseteq> W"
          using hUVW' hWeq by blast
        have hbasis_mem: "(A \<inter> U) \<times> (B \<inter> V) \<in>
            product_basis (subspace_topology X TX A) (subspace_topology Y TY B)"
          unfolding product_basis_def subspace_topology_def
          apply (rule CollectI, rule exI[where x="A \<inter> U"], rule exI[where x="B \<inter> V"])
          apply (intro conjI refl)
           apply (rule CollectI, rule exI[where x=U], rule conjI[OF refl hUT])
          apply (rule CollectI, rule exI[where x=V], rule conjI[OF refl hVT])
          done
        show "\<exists>b \<in> product_basis (subspace_topology X TX A) (subspace_topology Y TY B). p \<in> b \<and> b \<subseteq> W"
          apply (rule bexI[where x="(A \<inter> U) \<times> (B \<inter> V)"])
           apply (rule conjI[OF hpAUBV hAUBV_sub])
          apply (rule hbasis_mem)
          done
      qed
    qed
  qed
qed

(** from \S16 Theorem 16.4 [top1.tex:544] **)
(** LATEX VERSION: "If Y is convex in ordered X, then order topology on Y = subspace topology." **)

definition convex_in :: "'a::linorder set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "convex_in X Y \<longleftrightarrow>
     Y \<subseteq> X \<and>
     (\<forall>x\<in>Y. \<forall>y\<in>Y. \<forall>z\<in>X. x < z \<and> z < y \<longrightarrow> z \<in> Y)"

lemma Lemma_16_4_aux:
  fixes X :: "'a::linorder set" and Y :: "'a set"
  defines "BY \<equiv> {b \<inter> Y | b. b \<in> basis_order_topology}"
  shows "topology_generated_by_basis Y BY = subspace_topology X order_topology_on_UNIV Y"
proof -
  show "topology_generated_by_basis Y BY = subspace_topology X order_topology_on_UNIV Y"
  proof (rule set_eqI)
    fix W
    show "W \<in> topology_generated_by_basis Y BY \<longleftrightarrow> W \<in> subspace_topology X order_topology_on_UNIV Y"
    proof (rule iffI)
      assume hW: "W \<in> topology_generated_by_basis Y BY"
      have hWsub: "W \<subseteq> Y" and hWcov: "\<forall>x\<in>W. \<exists>b\<in>BY. x \<in> b \<and> b \<subseteq> W"
        using hW unfolding topology_generated_by_basis_def by blast+

      define C where "C = {b \<in> basis_order_topology. b \<inter> Y \<subseteq> W}"
      define U where "U = \<Union>C"

      have hWeq: "W = Y \<inter> U"
      proof (rule equalityI)
        show "W \<subseteq> Y \<inter> U"
        proof (rule subsetI)
          fix x assume hxW: "x \<in> W"
          obtain bY where hbY: "bY \<in> BY" and hxbY: "x \<in> bY" and hbYW: "bY \<subseteq> W"
            using hWcov[rule_format, OF hxW] by blast
          obtain b where hb: "b \<in> basis_order_topology" and hbYeq: "bY = b \<inter> Y"
            using hbY unfolding BY_def by blast
          have hbC: "b \<in> C"
            unfolding C_def using hb hbYW hbYeq by blast
          have hxY: "x \<in> Y" and hxb: "x \<in> b" using hxbY hbYeq by blast+
          have hxU: "x \<in> U" unfolding U_def using hbC hxb by blast
          show "x \<in> Y \<inter> U" using hxY hxU by blast
        qed
        show "Y \<inter> U \<subseteq> W"
        proof (rule subsetI)
          fix x assume hx: "x \<in> Y \<inter> U"
          have hxY: "x \<in> Y" and hxU: "x \<in> U" using hx by blast+
          obtain b where hbC: "b \<in> C" and hxb: "x \<in> b"
            using hxU unfolding U_def by blast
          have hbW: "b \<inter> Y \<subseteq> W" using hbC unfolding C_def by blast
          have "x \<in> b \<inter> Y" using hxY hxb by blast
          show "x \<in> W" using hbW \<open>x \<in> b \<inter> Y\<close> by blast
        qed
      qed

      have hUopen: "U \<in> order_topology_on_UNIV"
        unfolding order_topology_on_UNIV_def topology_generated_by_basis_def
      proof (rule CollectI, rule conjI)
        show "U \<subseteq> (UNIV::'a set)" by simp
        show "\<forall>x\<in>U. \<exists>b\<in>basis_order_topology. x \<in> b \<and> b \<subseteq> U"
        proof (rule ballI)
          fix x assume hxU: "x \<in> U"
          obtain b where hbC: "b \<in> C" and hxb: "x \<in> b"
            using hxU unfolding U_def by blast
          have hbB: "b \<in> basis_order_topology" using hbC unfolding C_def by blast
          have hbU: "b \<subseteq> U"
          proof (rule subsetI)
            fix y assume hy: "y \<in> b"
            show "y \<in> U"
              unfolding U_def using hbC hy by blast
          qed
          show "\<exists>b\<in>basis_order_topology. x \<in> b \<and> b \<subseteq> U"
            apply (rule bexI[where x=b])
             apply (intro conjI hxb hbU)
            apply (rule hbB)
            done
        qed
      qed

      show "W \<in> subspace_topology X order_topology_on_UNIV Y"
        unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x=U])
        apply (intro conjI)
         apply (rule hWeq)
        apply (rule hUopen)
        done
    next
      assume hW: "W \<in> subspace_topology X order_topology_on_UNIV Y"
      obtain U where hUopen: "U \<in> order_topology_on_UNIV" and hWeq: "W = Y \<inter> U"
        using hW unfolding subspace_topology_def by blast
      have hUcov: "\<forall>x\<in>U. \<exists>b\<in>basis_order_topology. x \<in> b \<and> b \<subseteq> U"
        using hUopen unfolding order_topology_on_UNIV_def topology_generated_by_basis_def by blast

      have hWsub: "W \<subseteq> Y" using hWeq by blast
      have hWcov: "\<forall>x\<in>W. \<exists>b\<in>BY. x \<in> b \<and> b \<subseteq> W"
      proof (rule ballI)
        fix x assume hxW: "x \<in> W"
        have hxY: "x \<in> Y" and hxU: "x \<in> U" using hxW hWeq by blast+
        obtain b where hbB: "b \<in> basis_order_topology" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
          using hUcov[rule_format, OF hxU] by blast
        have hbY: "b \<inter> Y \<in> BY" using hbB unfolding BY_def by blast
        have hx_in: "x \<in> b \<inter> Y" using hxY hxb by blast
        have hbW: "b \<inter> Y \<subseteq> W"
        proof (rule subsetI)
          fix y assume hy: "y \<in> b \<inter> Y"
          have hyY: "y \<in> Y" and hyb: "y \<in> b" using hy by blast+
          have hyU: "y \<in> U" using hbU hyb by blast
          show "y \<in> W" using hyY hyU hWeq by blast
        qed
        show "\<exists>b\<in>BY. x \<in> b \<and> b \<subseteq> W"
          apply (rule bexI[where x="b \<inter> Y"])
           apply (intro conjI hx_in hbW)
          apply (rule hbY)
          done
      qed

      show "W \<in> topology_generated_by_basis Y BY"
        unfolding topology_generated_by_basis_def
        apply (rule CollectI)
        apply (intro conjI)
         apply (rule hWsub)
        apply (rule hWcov)
        done
    qed
  qed
qed

lemma basis_order_topology_on_subset:
  assumes hb: "b \<in> basis_order_topology_on X"
  shows "b \<subseteq> X"
  using hb
  unfolding basis_order_topology_on_def open_ray_gt_on_def open_ray_lt_on_def open_interval_on_def
  by blast

lemma basis_order_topology_on_restrict:
  fixes X :: "'a::linorder set" and Y :: "'a set" and bY :: "'a set"
  assumes hYX: "Y \<subseteq> X"
  assumes hbY: "bY \<in> basis_order_topology_on Y"
  shows "\<exists>bX\<in>basis_order_topology_on X. bY = bX \<inter> Y"
proof -
  have hbY_cases:
      "(\<exists>a b. a \<in> Y \<and> b \<in> Y \<and> a < b \<and> bY = open_interval_on Y a b)
    \<or> (\<exists>a. a \<in> Y \<and> bY = open_ray_gt_on Y a)
    \<or> (\<exists>a. a \<in> Y \<and> bY = open_ray_lt_on Y a)
    \<or> bY = Y"
    using hbY unfolding basis_order_topology_on_def by blast

  from hbY_cases show ?thesis
  proof (elim disjE)
    assume hInt: "\<exists>a b. a \<in> Y \<and> b \<in> Y \<and> a < b \<and> bY = open_interval_on Y a b"
    obtain a b where haY: "a \<in> Y" and hbY': "b \<in> Y" and hab: "a < b" and hbYeq: "bY = open_interval_on Y a b"
      using hInt by blast
    have haX: "a \<in> X" using haY hYX by blast
    have hbX: "b \<in> X" using hbY' hYX by blast
    have hbXmem: "open_interval_on X a b \<in> basis_order_topology_on X"
      using haX hbX hab unfolding basis_order_topology_on_def by blast
    have hbYeq': "bY = (open_interval_on X a b) \<inter> Y"
      unfolding hbYeq open_interval_on_def
      apply (simp only: Int_assoc Int_left_commute Int_commute)
      using hYX by blast
    show "\<exists>bX\<in>basis_order_topology_on X. bY = bX \<inter> Y"
      apply (rule bexI[where x="open_interval_on X a b"])
       apply (rule hbYeq')
      apply (rule hbXmem)
      done
  next
    assume hGt: "\<exists>a. a \<in> Y \<and> bY = open_ray_gt_on Y a"
    obtain a where haY: "a \<in> Y" and hbYeq: "bY = open_ray_gt_on Y a"
      using hGt by blast
    have haX: "a \<in> X" using haY hYX by blast
    have hbXmem: "open_ray_gt_on X a \<in> basis_order_topology_on X"
      using haX unfolding basis_order_topology_on_def by blast
    have hbYeq': "bY = (open_ray_gt_on X a) \<inter> Y"
      unfolding hbYeq open_ray_gt_on_def
      apply (simp only: Int_assoc Int_left_commute Int_commute)
      using hYX by blast
    show "\<exists>bX\<in>basis_order_topology_on X. bY = bX \<inter> Y"
      apply (rule bexI[where x="open_ray_gt_on X a"])
       apply (rule hbYeq')
      apply (rule hbXmem)
      done
  next
    assume hLt: "\<exists>a. a \<in> Y \<and> bY = open_ray_lt_on Y a"
    obtain a where haY: "a \<in> Y" and hbYeq: "bY = open_ray_lt_on Y a"
      using hLt by blast
    have haX: "a \<in> X" using haY hYX by blast
    have hbXmem: "open_ray_lt_on X a \<in> basis_order_topology_on X"
      using haX unfolding basis_order_topology_on_def by blast
    have hbYeq': "bY = (open_ray_lt_on X a) \<inter> Y"
      unfolding hbYeq open_ray_lt_on_def
      apply (simp only: Int_assoc Int_left_commute Int_commute)
      using hYX by blast
    show "\<exists>bX\<in>basis_order_topology_on X. bY = bX \<inter> Y"
      apply (rule bexI[where x="open_ray_lt_on X a"])
       apply (rule hbYeq')
      apply (rule hbXmem)
      done
  next
    assume hbYeq: "bY = Y"
    have hbXmem: "X \<in> basis_order_topology_on X"
      unfolding basis_order_topology_on_def by blast
    have hbYeq': "bY = X \<inter> Y"
      using hbYeq hYX by blast
    show "\<exists>bX\<in>basis_order_topology_on X. bY = bX \<inter> Y"
      apply (rule bexI[where x=X])
       apply (rule hbYeq')
      apply (rule hbXmem)
      done
  qed
qed

lemma convex_in_not_mem_imp_all_gt:
  fixes X :: "'a::linorder set" and Y :: "'a set" and a y :: 'a
  assumes hconv: "convex_in X Y"
  assumes haX: "a \<in> X"
  assumes haNY: "a \<notin> Y"
  assumes hyY: "y \<in> Y"
  assumes hay: "a < y"
  shows "\<forall>t\<in>Y. a < t"
proof (rule ballI)
  fix t assume htY: "t \<in> Y"
  show "a < t"
  proof (rule ccontr)
    assume hnot: "\<not> a < t"
    have ht_le: "t \<le> a" using hnot by (simp only: not_less)
    have ht_ne: "t \<noteq> a" using htY haNY by blast
    have ht_lt: "t < a"
    proof -
      have "t < a \<or> t = a" using ht_le by (rule le_imp_less_or_eq)
      thus "t < a" using ht_ne by blast
    qed
    have hprop: "\<forall>x\<in>Y. \<forall>y\<in>Y. \<forall>z\<in>X. x < z \<and> z < y \<longrightarrow> z \<in> Y"
      using hconv unfolding convex_in_def by blast
    have "a \<in> Y"
      using hprop[rule_format, OF htY hyY haX] ht_lt hay by blast
    thus False using haNY by contradiction
  qed
qed

lemma convex_in_not_mem_imp_all_lt:
  fixes X :: "'a::linorder set" and Y :: "'a set" and a y :: 'a
  assumes hconv: "convex_in X Y"
  assumes haX: "a \<in> X"
  assumes haNY: "a \<notin> Y"
  assumes hyY: "y \<in> Y"
  assumes hay: "y < a"
  shows "\<forall>t\<in>Y. t < a"
proof (rule ballI)
  fix t assume htY: "t \<in> Y"
  show "t < a"
  proof (rule ccontr)
    assume hnot: "\<not> t < a"
    have ht_le: "a \<le> t" using hnot by (simp only: not_less)
    have ht_ne': "t \<noteq> a" using htY haNY by blast
    have ht_ne: "a \<noteq> t" using ht_ne' by blast
    have ha_lt_t: "a < t"
    proof -
      have "a < t \<or> a = t" using ht_le by (rule le_imp_less_or_eq)
      thus "a < t" using ht_ne by blast
    qed
    have hprop: "\<forall>x\<in>Y. \<forall>y\<in>Y. \<forall>z\<in>X. x < z \<and> z < y \<longrightarrow> z \<in> Y"
      using hconv unfolding convex_in_def by blast
    have "a \<in> Y"
      using hprop[rule_format, OF hyY htY haX] hay ha_lt_t by blast
    thus False using haNY by contradiction
  qed
qed

lemma convex_in_refine_basis_intersection:
  fixes X :: "'a::linorder set" and Y :: "'a set" and bX :: "'a set" and y :: 'a
  assumes hconv: "convex_in X Y"
  assumes hyY: "y \<in> Y"
  assumes hbX: "bX \<in> basis_order_topology_on X"
  assumes hybX: "y \<in> bX"
  shows "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
proof -
  have hYX: "Y \<subseteq> X" using hconv unfolding convex_in_def by blast

  have hbX_cases:
      "(\<exists>a b. a \<in> X \<and> b \<in> X \<and> a < b \<and> bX = open_interval_on X a b)
    \<or> (\<exists>a. a \<in> X \<and> bX = open_ray_gt_on X a)
    \<or> (\<exists>a. a \<in> X \<and> bX = open_ray_lt_on X a)
    \<or> bX = X"
    using hbX unfolding basis_order_topology_on_def by blast

  from hbX_cases show ?thesis
  proof (elim disjE)
    assume hInt: "\<exists>a b. a \<in> X \<and> b \<in> X \<and> a < b \<and> bX = open_interval_on X a b"
    obtain a b where haX: "a \<in> X" and hbX': "b \<in> X" and hab: "a < b" and hbXeq: "bX = open_interval_on X a b"
      using hInt by blast
    have hay: "a < y" and hyb: "y < b"
      using hybX unfolding hbXeq open_interval_on_def open_interval_def by blast+

    have haY_or: "a \<in> Y \<or> a \<notin> Y" by blast
    have hbY_or: "b \<in> Y \<or> b \<notin> Y" by blast
    from haY_or hbY_or show ?thesis
    proof (elim disjE)
      assume haY: "a \<in> Y"
      assume hbY: "b \<in> Y"
      have hbYmem: "open_interval_on Y a b \<in> basis_order_topology_on Y"
        using haY hbY hab unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> open_interval_on Y a b"
        using hay hyb hyY unfolding open_interval_on_def open_interval_def by blast
      have hsub: "open_interval_on Y a b \<subseteq> bX \<inter> Y"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_interval_on Y a b"
        have htY: "t \<in> Y" and htI: "t \<in> open_interval a b"
          using ht unfolding open_interval_on_def by blast+
        have htX: "t \<in> X" using hYX htY by blast
        show "t \<in> bX \<inter> Y"
          using htX htI htY unfolding hbXeq open_interval_on_def by blast
      qed
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x="open_interval_on Y a b"])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    next
      assume haNY: "a \<notin> Y"
      assume hbY: "b \<in> Y"
      have hall_gt: "\<forall>t\<in>Y. a < t"
        by (rule convex_in_not_mem_imp_all_gt[OF hconv haX haNY hyY hay])
      have hbYmem: "open_ray_lt_on Y b \<in> basis_order_topology_on Y"
        using hbY unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> open_ray_lt_on Y b"
        using hyY hyb unfolding open_ray_lt_on_def open_ray_lt_def by blast
      have hsub: "open_ray_lt_on Y b \<subseteq> bX \<inter> Y"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_ray_lt_on Y b"
        have htY: "t \<in> Y" and htb: "t < b"
          using ht unfolding open_ray_lt_on_def open_ray_lt_def by blast+
        have hta: "a < t" using hall_gt htY by blast
        have htX: "t \<in> X" using hYX htY by blast
        have htI: "t \<in> open_interval a b"
          using hta htb unfolding open_interval_def by blast
        show "t \<in> bX \<inter> Y"
          using htX htI htY unfolding hbXeq open_interval_on_def by blast
      qed
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x="open_ray_lt_on Y b"])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    next
      assume haY: "a \<in> Y"
      assume hbNY: "b \<notin> Y"
      have hall_lt: "\<forall>t\<in>Y. t < b"
        by (rule convex_in_not_mem_imp_all_lt[OF hconv hbX' hbNY hyY hyb])
      have hbYmem: "open_ray_gt_on Y a \<in> basis_order_topology_on Y"
        using haY unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> open_ray_gt_on Y a"
        using hyY hay unfolding open_ray_gt_on_def open_ray_gt_def by blast
      have hsub: "open_ray_gt_on Y a \<subseteq> bX \<inter> Y"
      proof (rule subsetI)
        fix t assume ht: "t \<in> open_ray_gt_on Y a"
        have htY: "t \<in> Y" and hat: "a < t"
          using ht unfolding open_ray_gt_on_def open_ray_gt_def by blast+
        have htb: "t < b" using hall_lt htY by blast
        have htX: "t \<in> X" using hYX htY by blast
        have htI: "t \<in> open_interval a b"
          using hat htb unfolding open_interval_def by blast
        show "t \<in> bX \<inter> Y"
          using htX htI htY unfolding hbXeq open_interval_on_def by blast
      qed
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x="open_ray_gt_on Y a"])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    next
      assume haNY: "a \<notin> Y"
      assume hbNY: "b \<notin> Y"
      have hall_gt: "\<forall>t\<in>Y. a < t"
        by (rule convex_in_not_mem_imp_all_gt[OF hconv haX haNY hyY hay])
      have hall_lt: "\<forall>t\<in>Y. t < b"
        by (rule convex_in_not_mem_imp_all_lt[OF hconv hbX' hbNY hyY hyb])
      have hbYmem: "Y \<in> basis_order_topology_on Y"
        unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> Y" using hyY .
      have hsub: "Y \<subseteq> bX \<inter> Y"
      proof (rule subsetI)
        fix t assume htY: "t \<in> Y"
        have htX: "t \<in> X" using hYX htY by blast
        have hta: "a < t" using hall_gt htY by blast
        have htb: "t < b" using hall_lt htY by blast
        have htI: "t \<in> open_interval a b"
          using hta htb unfolding open_interval_def by blast
        show "t \<in> bX \<inter> Y"
          using htX htI htY unfolding hbXeq open_interval_on_def by blast
      qed
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x=Y])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    qed
  next
    assume hGt: "\<exists>a. a \<in> X \<and> bX = open_ray_gt_on X a"
    obtain a where haX: "a \<in> X" and hbXeq: "bX = open_ray_gt_on X a"
      using hGt by blast
    have hay: "a < y" using hybX unfolding hbXeq open_ray_gt_on_def open_ray_gt_def by blast
    have haY_or: "a \<in> Y \<or> a \<notin> Y" by blast
    from haY_or show ?thesis
    proof (elim disjE)
      assume haY: "a \<in> Y"
      have hbYmem: "open_ray_gt_on Y a \<in> basis_order_topology_on Y"
        using haY unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> open_ray_gt_on Y a"
        using hyY hay unfolding open_ray_gt_on_def open_ray_gt_def by blast
      have hsub: "open_ray_gt_on Y a \<subseteq> bX \<inter> Y"
        unfolding hbXeq open_ray_gt_on_def
        using hYX by blast
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x="open_ray_gt_on Y a"])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    next
      assume haNY: "a \<notin> Y"
      have hall_gt: "\<forall>t\<in>Y. a < t"
        by (rule convex_in_not_mem_imp_all_gt[OF hconv haX haNY hyY hay])
      have hbYmem: "Y \<in> basis_order_topology_on Y"
        unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> Y" using hyY .
      have hsub: "Y \<subseteq> bX \<inter> Y"
      proof (rule subsetI)
        fix t assume htY: "t \<in> Y"
        have hta: "a < t" using hall_gt htY by blast
        have htX: "t \<in> X" using hYX htY by blast
        show "t \<in> bX \<inter> Y"
          using htX hta htY unfolding hbXeq open_ray_gt_on_def open_ray_gt_def by blast
      qed
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x=Y])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    qed
  next
    assume hLt: "\<exists>a. a \<in> X \<and> bX = open_ray_lt_on X a"
    obtain a where haX: "a \<in> X" and hbXeq: "bX = open_ray_lt_on X a"
      using hLt by blast
    have hay: "y < a" using hybX unfolding hbXeq open_ray_lt_on_def open_ray_lt_def by blast
    have haY_or: "a \<in> Y \<or> a \<notin> Y" by blast
    from haY_or show ?thesis
    proof (elim disjE)
      assume haY: "a \<in> Y"
      have hbYmem: "open_ray_lt_on Y a \<in> basis_order_topology_on Y"
        using haY unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> open_ray_lt_on Y a"
        using hyY hay unfolding open_ray_lt_on_def open_ray_lt_def by blast
      have hsub: "open_ray_lt_on Y a \<subseteq> bX \<inter> Y"
        unfolding hbXeq open_ray_lt_on_def
        using hYX by blast
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x="open_ray_lt_on Y a"])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    next
      assume haNY: "a \<notin> Y"
      have hall_lt: "\<forall>t\<in>Y. t < a"
        by (rule convex_in_not_mem_imp_all_lt[OF hconv haX haNY hyY hay])
      have hbYmem: "Y \<in> basis_order_topology_on Y"
        unfolding basis_order_topology_on_def by blast
      have hy_in: "y \<in> Y" using hyY .
      have hsub: "Y \<subseteq> bX \<inter> Y"
      proof (rule subsetI)
        fix t assume htY: "t \<in> Y"
        have hta: "t < a" using hall_lt htY by blast
        have htX: "t \<in> X" using hYX htY by blast
        show "t \<in> bX \<inter> Y"
          using htX hta htY unfolding hbXeq open_ray_lt_on_def open_ray_lt_def by blast
      qed
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
        apply (rule bexI[where x=Y])
         apply (intro conjI hy_in hsub)
        apply (rule hbYmem)
        done
    qed
  next
    assume hbXeq: "bX = X"
    have hbYmem: "Y \<in> basis_order_topology_on Y"
      unfolding basis_order_topology_on_def by blast
    have hy_in: "y \<in> Y" using hyY .
    have hsub: "Y \<subseteq> bX \<inter> Y"
      using hbXeq hYX by blast
    show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> bX \<inter> Y"
      apply (rule bexI[where x=Y])
       apply (intro conjI hy_in hsub)
      apply (rule hbYmem)
      done
  qed
qed

theorem Theorem_16_4:
  fixes X :: "'a::linorder set" and Y :: "'a set"
  assumes hconv: "convex_in X Y"
  shows "order_topology_on Y = subspace_topology X (order_topology_on X) Y"
proof -
  have hYX: "Y \<subseteq> X" using hconv unfolding convex_in_def by blast

  have h1: "order_topology_on Y \<subseteq> subspace_topology X (order_topology_on X) Y"
  proof (rule subsetI)
    fix W assume hW: "W \<in> order_topology_on Y"
    have hWsub: "W \<subseteq> Y" and hWcov: "\<forall>x\<in>W. \<exists>bY\<in>basis_order_topology_on Y. x \<in> bY \<and> bY \<subseteq> W"
      using hW unfolding order_topology_on_def topology_generated_by_basis_def by blast+

    define C where "C = {b \<in> basis_order_topology_on X. b \<inter> Y \<subseteq> W}"
    define U where "U = \<Union>C"

    have hWeq: "W = Y \<inter> U"
    proof (rule equalityI)
      show "W \<subseteq> Y \<inter> U"
      proof (rule subsetI)
        fix x assume hxW: "x \<in> W"
        have hxY: "x \<in> Y" using hWsub hxW by blast
        obtain bY where hbY: "bY \<in> basis_order_topology_on Y" and hxbY: "x \<in> bY" and hbYW: "bY \<subseteq> W"
          using hWcov[rule_format, OF hxW] by blast
        obtain bX where hbX: "bX \<in> basis_order_topology_on X" and hbYeq: "bY = bX \<inter> Y"
          using basis_order_topology_on_restrict[OF hYX hbY] by blast
        have hbC: "bX \<in> C" unfolding C_def using hbX hbYW hbYeq by blast
        have hxbX: "x \<in> bX" using hxbY hbYeq by blast
        have hxU: "x \<in> U" unfolding U_def using hbC hxbX by blast
        show "x \<in> Y \<inter> U" using hxY hxU by blast
      qed
      show "Y \<inter> U \<subseteq> W"
      proof (rule subsetI)
        fix x assume hx: "x \<in> Y \<inter> U"
        have hxY: "x \<in> Y" and hxU: "x \<in> U" using hx by blast+
        obtain bX where hbC: "bX \<in> C" and hxbX: "x \<in> bX"
          using hxU unfolding U_def by blast
        have hbW: "bX \<inter> Y \<subseteq> W" using hbC unfolding C_def by blast
        have "x \<in> bX \<inter> Y" using hxY hxbX by blast
        show "x \<in> W" using hbW \<open>x \<in> bX \<inter> Y\<close> by blast
      qed
    qed

    have hUopen: "U \<in> order_topology_on X"
      unfolding order_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, rule conjI)
      show "U \<subseteq> X"
      proof (rule subsetI)
        fix x assume hxU: "x \<in> U"
        obtain bX where hbC: "bX \<in> C" and hxbX: "x \<in> bX"
          using hxU unfolding U_def by blast
        have hbB: "bX \<in> basis_order_topology_on X" using hbC unfolding C_def by blast
        have hbXsub: "bX \<subseteq> X" by (rule basis_order_topology_on_subset[OF hbB])
        show "x \<in> X" using hbXsub hxbX by blast
      qed
      show "\<forall>x\<in>U. \<exists>b\<in>basis_order_topology_on X. x \<in> b \<and> b \<subseteq> U"
      proof (rule ballI)
        fix x assume hxU: "x \<in> U"
        obtain bX where hbC: "bX \<in> C" and hxbX: "x \<in> bX"
          using hxU unfolding U_def by blast
        have hbB: "bX \<in> basis_order_topology_on X" using hbC unfolding C_def by blast
        have hbU: "bX \<subseteq> U"
        proof (rule subsetI)
          fix t assume ht: "t \<in> bX"
          show "t \<in> U" unfolding U_def using hbC ht by blast
        qed
        show "\<exists>b\<in>basis_order_topology_on X. x \<in> b \<and> b \<subseteq> U"
          apply (rule bexI[where x=bX])
           apply (intro conjI hxbX hbU)
          apply (rule hbB)
          done
      qed
    qed

    show "W \<in> subspace_topology X (order_topology_on X) Y"
      unfolding subspace_topology_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      apply (intro conjI)
       apply (rule hWeq)
      apply (rule hUopen)
      done
  qed

  have h2: "subspace_topology X (order_topology_on X) Y \<subseteq> order_topology_on Y"
  proof (rule subsetI)
    fix W assume hW: "W \<in> subspace_topology X (order_topology_on X) Y"
    obtain U where hUopen: "U \<in> order_topology_on X" and hWeq: "W = Y \<inter> U"
      using hW unfolding subspace_topology_def by blast
    have hUcov: "\<forall>x\<in>U. \<exists>bX\<in>basis_order_topology_on X. x \<in> bX \<and> bX \<subseteq> U"
      using hUopen unfolding order_topology_on_def topology_generated_by_basis_def by blast

    have hWsub: "W \<subseteq> Y" using hWeq by blast
    have hWcov: "\<forall>y\<in>W. \<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> W"
    proof (rule ballI)
      fix y assume hyW: "y \<in> W"
      have hyY: "y \<in> Y" and hyU: "y \<in> U" using hyW hWeq by blast+
      obtain bX where hbX: "bX \<in> basis_order_topology_on X" and hybX: "y \<in> bX" and hbXU: "bX \<subseteq> U"
        using hUcov[rule_format, OF hyU] by blast
      obtain bY where hbY: "bY \<in> basis_order_topology_on Y" and hybY: "y \<in> bY" and hbYsub: "bY \<subseteq> bX \<inter> Y"
        using convex_in_refine_basis_intersection[OF hconv hyY hbX hybX] by blast
      have hbYW: "bY \<subseteq> W"
        using hbYsub hbXU hWeq by blast
      show "\<exists>bY\<in>basis_order_topology_on Y. y \<in> bY \<and> bY \<subseteq> W"
        apply (rule bexI[where x=bY])
         apply (intro conjI hybY hbYW)
        apply (rule hbY)
        done
    qed

    show "W \<in> order_topology_on Y"
      unfolding order_topology_on_def topology_generated_by_basis_def
      apply (rule CollectI)
      apply (intro conjI)
       apply (rule hWsub)
      apply (rule hWcov)
      done
  qed

  show ?thesis using h1 h2 by blast
qed


section \<open>\<S>17 Closed Sets and Limit Points\<close>

subsection \<open>Closed sets\<close>

(** from \S17 Definition (Closed set as complement of open) [top1.tex:~630] **)
definition closedin_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "closedin_on X T A \<longleftrightarrow> A \<subseteq> X \<and> (X - A) \<in> T"

(** de Morgan helper: X - Inter F = Union of (X - A) for A in F **)
lemma diff_Inter_eq: "(X :: 'a set) - \<Inter>F = \<Union>{X - A | A. A \<in> F}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply blast
  apply (rule subsetI)
  apply blast
  done

(** Helper lemmas for closedin_on **)
lemma closedin_sub: "closedin_on X T A \<Longrightarrow> A \<subseteq> X"
  apply (unfold closedin_on_def)
  apply (erule conjE)
  apply assumption
  done

lemma closedin_diff_open: "closedin_on X T A \<Longrightarrow> X - A \<in> T"
  apply (unfold closedin_on_def)
  apply (erule conjE)
  apply assumption
  done

lemma closedin_intro: "A \<subseteq> X \<Longrightarrow> X - A \<in> T \<Longrightarrow> closedin_on X T A"
  apply (unfold closedin_on_def)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

(** from \S17 Theorem 17.1 [top1.tex:640] **)
(** LATEX VERSION: "Empty and X closed; arbitrary intersections closed; finite unions closed." **)
(** Note: Isabelle's Inter {} = UNIV (not X), so the intersection clause needs F \<noteq> {}. **)

(** Auxiliary lemma for Theorem_17_1: finite union of closed sets is closed.
    Use assumes for hfin and hcl, then "using hfin hcl" passes hcl as extra prems
    to finite_induct, giving an IH that includes hcl specialized for the subsets. **)
lemma closedin_Union_finite:
  assumes hT: "is_topology_on X T"
  assumes hfin: "finite F"
  assumes hcl: "\<forall>A\<in>F. closedin_on X T A"
  shows "closedin_on X T (\<Union>F)"
  using hfin hcl
proof (induction rule: finite_induct)
  case empty
  (* ?case = closedin_on X T (\<Union>{}) *)
  (* empty.prems(1) = \<forall>A\<in>{}. closedin_on X T A  [not needed] *)
  have X_T: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
  show ?case
    apply (subst Union_empty)
    apply (rule closedin_intro)
     apply (rule empty_subsetI)
    apply (subst Diff_empty)
    apply (rule X_T)
    done
next
  case (insert a G)
  (* ?case = closedin_on X T (\<Union>(insert a G)) *)
  (* insert.hyps(1) = finite G, insert.hyps(2) = a \<notin> G *)
  (* insert.prems(1) = \<forall>A\<in>insert a G. closedin_on X T A  [specialized hcl] *)
  (* insert.IH = (\<forall>A\<in>G. closedin_on X T A) \<Longrightarrow> closedin_on X T (\<Union>G)  [hopefully] *)
  have inter_T: "\<forall>Gf. finite Gf \<and> Gf \<noteq> {} \<and> Gf \<subseteq> T \<longrightarrow> \<Inter>Gf \<in> T"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  note hall = insert.prems(1)
  have ha: "closedin_on X T a"
    apply (rule bspec[OF hall])
    apply (rule insertI1)
    done
  have hG: "\<forall>A\<in>G. closedin_on X T A"
  proof (rule ballI)
    fix A2 assume hA2G: "A2 \<in> G"
    show "closedin_on X T A2"
      apply (rule bspec[OF hall])
      apply (rule insertI2)
      apply (rule hA2G)
      done
  qed
  have hUG: "closedin_on X T (\<Union>G)"
    by (rule insert.IH[OF hG])
  have a_sub: "a \<subseteq> X" by (rule closedin_sub, rule ha)
  have UG_sub: "\<Union>G \<subseteq> X" by (rule closedin_sub, rule hUG)
  have XmA_T: "X - a \<in> T" by (rule closedin_diff_open, rule ha)
  have XmUG_T: "X - \<Union>G \<in> T" by (rule closedin_diff_open, rule hUG)
  have two_inter: "\<Inter>{X - a, X - \<Union>G} \<in> T"
    apply (rule inter_T[rule_format])
    apply (intro conjI)
      apply (rule finite.insertI, rule finite.insertI, rule finite.emptyI)
     apply (rule insert_not_empty)
    apply (rule subsetI)
    apply (erule insertE)
     apply (erule ssubst, rule XmA_T)
    apply (erule singletonE)
    apply (erule ssubst, rule XmUG_T)
    done
  have inter_eq: "\<Inter>{X - a, X - \<Union>G} = (X - a) \<inter> (X - \<Union>G)"
    by simp
  show ?case
    apply (rule closedin_intro)
     apply (simp only: Union_insert)
     apply (rule Un_least, rule a_sub, rule UG_sub)
    apply (simp only: Union_insert)
    apply (simp only: Diff_Un)
    apply (fold inter_eq)
    apply (rule two_inter)
    done
qed

theorem Theorem_17_1:
  assumes hT: "is_topology_on X T"
  shows "closedin_on X T {} \<and> closedin_on X T X
     \<and> (\<forall>F. F \<noteq> {} \<longrightarrow> (\<forall>A\<in>F. closedin_on X T A) \<longrightarrow> closedin_on X T (\<Inter>F))
     \<and> (\<forall>F. finite F \<longrightarrow> (\<forall>A\<in>F. closedin_on X T A) \<longrightarrow> closedin_on X T (\<Union>F))"
proof -
  (* Extract the four topology axioms *)
  have empty_T: "{} \<in> T"
    by (rule conjunct1[OF hT[unfolded is_topology_on_def]])
  have X_T: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
  have union_T: "\<forall>U. U \<subseteq> T \<longrightarrow> \<Union>U \<in> T"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have inter_T: "\<forall>G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> T \<longrightarrow> \<Inter>G \<in> T"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  have cl_empty: "closedin_on X T {}"
    apply (rule closedin_intro)
     apply (rule empty_subsetI)
    apply (simp only: Diff_empty)
    apply (rule X_T)
    done
  have cl_X: "closedin_on X T X"
    apply (rule closedin_intro)
     apply (rule subset_refl)
    apply (simp only: Diff_cancel)
    apply (rule empty_T)
    done
  have cl_inter: "\<forall>F. F \<noteq> {} \<longrightarrow> (\<forall>A\<in>F. closedin_on X T A) \<longrightarrow> closedin_on X T (\<Inter>F)"
  proof (intro allI impI)
    fix F :: "'a set set"
    assume hFne: "F \<noteq> {}"
    assume hFcl: "\<forall>A\<in>F. closedin_on X T A"
    obtain A where hAF: "A \<in> F" using hFne by blast
    have cl_A: "closedin_on X T A"
      by (rule bspec[OF hFcl hAF])
    have sub_X: "\<Inter>F \<subseteq> X"
      apply (rule subset_trans)
       apply (rule Inter_lower)
       apply (rule hAF)
      apply (rule closedin_sub)
      apply (rule cl_A)
      done
    have comps_in_T: "{X - A | A. A \<in> F} \<subseteq> T"
    proof (rule subsetI)
      fix B assume hB: "B \<in> {X - A | A. A \<in> F}"
      then obtain A2 where hAF2: "A2 \<in> F" and hBA: "B = X - A2" by blast
      show "B \<in> T"
        apply (subst hBA)
        apply (rule closedin_diff_open)
        apply (rule bspec[OF hFcl hAF2])
        done
    qed
    show "closedin_on X T (\<Inter>F)"
      apply (rule closedin_intro)
       apply (rule sub_X)
      apply (subst diff_Inter_eq)
      apply (rule union_T[rule_format])
      apply (rule comps_in_T)
      done
  qed
  have cl_union: "\<forall>F. finite F \<longrightarrow> (\<forall>A\<in>F. closedin_on X T A) \<longrightarrow> closedin_on X T (\<Union>F)"
    apply (intro allI impI)
    apply (rule closedin_Union_finite[OF hT])
    apply assumption
    apply assumption
    done
  show ?thesis
    apply (intro conjI)
       apply (rule cl_empty)
      apply (rule cl_X)
     apply (rule cl_inter)
    apply (rule cl_union)
    done
qed
(** from \S17 Theorem 17.2 [top1.tex:665] **)
(** LATEX VERSION: "A closed in Y iff A = C\<inter>Y for some closed C in X." **)
(** Note: requires Y \<subseteq> X for the backward direction. **)
theorem Theorem_17_2:
  assumes hT: "is_topology_on X T"
  assumes hYX: "Y \<subseteq> X"
  shows "closedin_on Y (subspace_topology X T Y) A \<longleftrightarrow>
     (\<exists>C. closedin_on X T C \<and> A = C \<inter> Y)"
proof -
  have X_T: "X \<in> T"
    by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
  have inter_T: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  show ?thesis
  proof (rule iffI)
    (* \<rightarrow> direction: closedin_on Y T_Y A \<rightarrow> \<exists>C. closedin_on X T C \<and> A = C \<inter> Y *)
    assume hA: "closedin_on Y (subspace_topology X T Y) A"
    have hAsub: "A \<subseteq> Y" by (rule closedin_sub[OF hA])
    have hYmA: "Y - A \<in> subspace_topology X T Y" by (rule closedin_diff_open[OF hA])
    obtain V where hV: "V \<in> T" and hYmA_eq: "Y - A = Y \<inter> V"
      using hYmA unfolding subspace_topology_def by blast
    (* C = X - V is closed in X *)
    have XV_T: "X \<inter> V \<in> T"
    proof -
      have h1: "finite {X, V}" by simp
      have hne: "{X, V} \<noteq> {}" by (rule insert_not_empty)
      have h2: "{X, V} \<subseteq> T" using X_T hV by simp
      have "\<Inter>{X, V} \<in> T"
        apply (rule inter_T[rule_format])
        apply (intro conjI, rule h1, rule hne, rule h2)
        done
      thus ?thesis by simp
    qed
    have C_closed: "closedin_on X T (X - V)"
    proof (rule closedin_intro)
      show "X - V \<subseteq> X" by (rule Diff_subset)
      show "X - (X - V) \<in> T"
      proof -
        have eq: "X - (X - V) = X \<inter> V"
          apply (rule equalityI)
           apply (rule subsetI)
           apply blast
          apply (rule subsetI)
          apply blast
          done
        show ?thesis using eq XV_T by simp
      qed
    qed
    (* A = (X - V) \<inter> Y *)
    have A_eq: "A = (X - V) \<inter> Y"
      apply (rule equalityI)
       apply (rule subsetI)
       apply (rule IntI)
        (* x \<in> A \<rightarrow> x \<in> X - V: x \<in> Y (hAsub), x \<in> X (hYX), x \<notin> V (from hYmA_eq) *)
        apply (rule DiffI)
         apply (rule subsetD[OF hYX], rule subsetD[OF hAsub], assumption)
        (* x \<in> A \<rightarrow> x \<notin> V: from Y - A = Y \<inter> V, x \<in> A \<inter> Y \<rightarrow> x \<notin> Y - A \<rightarrow> x \<notin> Y \<inter> V *)
        using hYmA_eq hAsub apply blast
       apply (rule subsetD[OF hAsub], assumption)
      (* (X - V) \<inter> Y \<subseteq> A: x \<in> X - V \<and> x \<in> Y \<rightarrow> x \<notin> V \<rightarrow> x \<notin> Y \<inter> V = Y - A \<rightarrow> x \<in> A *)
      apply (rule subsetI)
      using hYmA_eq apply blast
      done
    show "\<exists>C. closedin_on X T C \<and> A = C \<inter> Y"
      apply (intro exI conjI)
       apply (rule C_closed)
      apply (rule A_eq)
      done
  next
    (* \<leftarrow> direction: \<exists>C. closedin_on X T C \<and> A = C \<inter> Y \<rightarrow> closedin_on Y T_Y A *)
    assume h: "\<exists>C. closedin_on X T C \<and> A = C \<inter> Y"
    then obtain C where hC: "closedin_on X T C" and hA_eq: "A = C \<inter> Y" by blast
    have hXmC_T: "X - C \<in> T" by (rule closedin_diff_open[OF hC])
    have hA_sub: "A \<subseteq> Y"
      apply (subst hA_eq)
      apply (rule Int_lower2)
      done
    (* Y - A = Y \<inter> (X - C) \<in> subspace_topology X T Y *)
    have YmA_eq: "Y - A = Y \<inter> (X - C)"
      apply (subst hA_eq)
      apply (rule equalityI)
       apply (rule subsetI)
       apply (intro IntI)
        apply blast
       apply (intro DiffI)
        apply (rule subsetD[OF hYX], blast)
       apply blast
      apply (rule subsetI)
      apply (intro DiffI)
       apply blast
      apply blast
      done
    have hYmA_in: "Y - A \<in> subspace_topology X T Y"
      apply (subst YmA_eq)
      apply (unfold subspace_topology_def)
      apply (rule CollectI)
      apply (intro exI conjI)
       apply (rule refl)
      apply (rule hXmC_T)
      done
    show "closedin_on Y (subspace_topology X T Y) A"
      apply (rule closedin_intro)
       apply (rule hA_sub)
      apply (rule hYmA_in)
      done
  qed
qed

(** from \S17 Theorem 17.3 [top1.tex:687] **)
(** LATEX VERSION: "If A closed in Y and Y closed in X then A closed in X." **)
theorem Theorem_17_3:
  assumes hT: "is_topology_on X T"
  assumes hY: "closedin_on X T Y"
  assumes hA: "closedin_on Y (subspace_topology X T Y) A"
  shows "closedin_on X T A"
proof -
  from hY have Y_sub_X: "Y \<subseteq> X" and XmY_T: "X - Y \<in> T"
    unfolding closedin_on_def by blast+
  from hA have A_sub_Y: "A \<subseteq> Y"
    unfolding closedin_on_def by blast
  from hA have YmA_sub: "Y - A \<in> subspace_topology X T Y"
    unfolding closedin_on_def by blast
  from YmA_sub obtain V where hV: "V \<in> T" and hYmA: "Y - A = Y \<inter> V"
    unfolding subspace_topology_def by blast
  from hT have XT: "X \<in> T" and
               inter_T: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T" and
               union_T: "\<forall>U. U \<subseteq> T \<longrightarrow> \<Union>U \<in> T"
    unfolding is_topology_on_def by blast+
  have XV_T: "X \<inter> V \<in> T"
  proof -
    have "finite {X, V} \<and> {X, V} \<noteq> {} \<and> {X, V} \<subseteq> T" using XT hV by simp
    then have "\<Inter>{X, V} \<in> T" using inter_T by blast
    then show ?thesis by simp
  qed
  have XmA_eq: "X - A = (X - Y) \<union> (X \<inter> V)"
    using A_sub_Y hYmA by blast
  have XmA_T: "X - A \<in> T"
  proof -
    have "{X - Y, X \<inter> V} \<subseteq> T" using XmY_T XV_T by simp
    then have "\<Union>{X - Y, X \<inter> V} \<in> T" using union_T by blast
    then show ?thesis using XmA_eq by simp
  qed
  show "closedin_on X T A"
    unfolding closedin_on_def using A_sub_Y Y_sub_X XmA_T by blast
qed


subsection \<open>Closure and interior\<close>

(** from \S17 Definition (Interior and closure) [top1.tex:~690] **)
definition interior_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "interior_on X T A = \<Union>{U. U \<in> T \<and> U \<subseteq> A}"

definition closure_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "closure_on X T A = \<Inter>{C. closedin_on X T C \<and> A \<subseteq> C}"

(** Basic closure properties (used repeatedly later). **)
lemma subset_closure_on:
  shows "A \<subseteq> closure_on X T A"
  unfolding closure_on_def
proof (rule subsetI)
  fix a assume ha: "a \<in> A"
  show "a \<in> \<Inter>{C. closedin_on X T C \<and> A \<subseteq> C}"
  proof (rule InterI)
    fix C assume hC: "C \<in> {D. closedin_on X T D \<and> A \<subseteq> D}"
    have hAC: "A \<subseteq> C"
      by (rule conjunct2[OF CollectD[OF hC]])
    show "a \<in> C"
      by (rule subsetD[OF hAC, OF ha])
  qed
qed

lemma closure_on_mono:
  assumes hAB: "A \<subseteq> B"
  shows "closure_on X T A \<subseteq> closure_on X T B"
proof -
  let ?FA = "{C. closedin_on X T C \<and> A \<subseteq> C}"
  let ?FB = "{C. closedin_on X T C \<and> B \<subseteq> C}"
  have hsub: "?FB \<subseteq> ?FA"
    using hAB by blast
  have hInter: "\<Inter>?FA \<subseteq> \<Inter>?FB"
  proof (rule subsetI)
    fix x
    assume hx: "x \<in> \<Inter>?FA"
    show "x \<in> \<Inter>?FB"
    proof (rule InterI)
      fix C
      assume hC: "C \<in> ?FB"
      have hC': "C \<in> ?FA" using hsub hC by blast
      show "x \<in> C" by (rule InterD[OF hx hC'])
    qed
  qed
  show ?thesis
    unfolding closure_on_def using hInter by simp
qed

lemma closure_on_subset_of_closed:
  assumes hC: "closedin_on X T C"
  assumes hAC: "A \<subseteq> C"
  shows "closure_on X T A \<subseteq> C"
  unfolding closure_on_def
  apply (rule Inter_lower)
  apply (rule CollectI)
  apply (intro conjI)
   apply (rule hC)
  apply (rule hAC)
  done

lemma closure_on_closed:
  assumes hT: "is_topology_on X T"
  assumes hAX: "A \<subseteq> X"
  shows "closedin_on X T (closure_on X T A)"
proof -
  have cl_inter: "\<forall>F. F \<noteq> {} \<longrightarrow> (\<forall>C\<in>F. closedin_on X T C) \<longrightarrow> closedin_on X T (\<Inter>F)"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hT]]]])
  have X_closed: "closedin_on X T X"
    by (rule conjunct1[OF conjunct2[OF Theorem_17_1[OF hT]]])

  let ?F = "{C. closedin_on X T C \<and> A \<subseteq> C}"

  have hX: "X \<in> ?F"
    by (rule CollectI, intro conjI, rule X_closed, rule hAX)

  have F_ne: "?F \<noteq> {}"
  proof
    assume h: "?F = {}"
    show False using hX by (simp add: h)
  qed

  have hFcl: "\<forall>C\<in>?F. closedin_on X T C"
  proof
    fix C
    assume hC: "C \<in> ?F"
    show "closedin_on X T C"
      by (rule conjunct1[OF CollectD[OF hC]])
  qed

  have hInter_imp: "?F \<noteq> {} \<longrightarrow> (\<forall>C\<in>?F. closedin_on X T C) \<longrightarrow> closedin_on X T (\<Inter>?F)"
    by (rule spec[where x="?F", OF cl_inter])
  have hInter_imp2: "(\<forall>C\<in>?F. closedin_on X T C) \<longrightarrow> closedin_on X T (\<Inter>?F)"
    by (rule mp[OF hInter_imp F_ne])
  have hInter: "closedin_on X T (\<Inter>?F)"
    by (rule mp[OF hInter_imp2 hFcl])

  show ?thesis
    unfolding closure_on_def
    using hInter by simp
qed

lemma closure_on_subset_carrier:
  assumes hT: "is_topology_on X T"
  assumes hAX: "A \<subseteq> X"
  shows "closure_on X T A \<subseteq> X"
  by (rule closedin_sub[OF closure_on_closed[OF hT hAX]])

lemma closure_meets_open:
  assumes hT: "is_topology_on X T" and hAX: "A \<subseteq> X"
  assumes hg: "g \<in> closure_on X T A" and hU: "U \<in> T" and hgU: "g \<in> U"
  shows "U \<inter> A \<noteq> {}"
proof (rule ccontr)
  assume "\<not> U \<inter> A \<noteq> {}"
  then have hUA: "A \<subseteq> X - U" using hAX by fast
  have hgX: "g \<in> X" using hg closure_on_subset_carrier[OF hT hAX] by fast
  have "X - U \<subseteq> X" by fast
  have hXintU: "X \<inter> U \<in> T"
    apply (rule topology_inter2[OF hT])
    using hT unfolding is_topology_on_def apply (elim conjE) apply assumption
    apply (rule hU)
    done
  have "closedin_on X T (X - U)" unfolding closedin_on_def
    apply (intro conjI)
    apply fast
    apply (subgoal_tac "X - (X - U) = X \<inter> U")
    prefer 2 apply blast
    apply (simp add: hXintU)
    done
  then have "closure_on X T A \<subseteq> X - U"
    using hUA by (rule closure_on_subset_of_closed)
  then have "g \<notin> U" using hg by fast
  then show False using hgU by fast
qed

(** from \S17 Theorem 17.4 [top1.tex:703] **)
(** LATEX VERSION: "Closure in Y equals closure in X intersect Y." **)
theorem Theorem_17_4:
  assumes hT: "is_topology_on X T"
  assumes hAY: "A \<subseteq> Y" and hYX: "Y \<subseteq> X"
  shows "closure_on Y (subspace_topology X T Y) A = closure_on X T A \<inter> Y"
proof -
  have empty_T: "{} \<in> T"
    by (rule conjunct1[OF hT[unfolded is_topology_on_def]])
  have empty_TY: "{} \<in> subspace_topology X T Y"
    apply (unfold subspace_topology_def)
    apply (rule CollectI)
    apply (rule exI[where x="{}"])
    apply (rule conjI)
     apply (simp only: Int_empty_right)
    apply (rule empty_T)
    done
  have Y_closed: "closedin_on Y (subspace_topology X T Y) Y"
    apply (rule closedin_intro)
     apply (rule subset_refl)
    apply (simp only: Diff_cancel)
    apply (rule empty_TY)
    done
  note t172 = Theorem_17_2[OF hT hYX]
  show ?thesis
  proof (rule equalityI)
    show "closure_on Y (subspace_topology X T Y) A \<subseteq> closure_on X T A \<inter> Y"
      unfolding closure_on_def
    proof (rule subsetI)
      fix x
      assume hx: "x \<in> \<Inter>{C. closedin_on Y (subspace_topology X T Y) C \<and> A \<subseteq> C}"
      show "x \<in> \<Inter>{C. closedin_on X T C \<and> A \<subseteq> C} \<inter> Y"
      proof (rule IntI)
        show "x \<in> \<Inter>{C. closedin_on X T C \<and> A \<subseteq> C}"
        proof (rule InterI)
          fix D assume hD: "D \<in> {C. closedin_on X T C \<and> A \<subseteq> C}"
          have hDcl: "closedin_on X T D"
            by (rule conjunct1[OF CollectD[OF hD]])
          have hAD: "A \<subseteq> D"
            by (rule conjunct2[OF CollectD[OF hD]])
          have DY_cl: "closedin_on Y (subspace_topology X T Y) (D \<inter> Y)"
            apply (rule iffD2[OF t172])
            apply (intro exI conjI, rule hDcl, rule refl)
            done
          have A_DY: "A \<subseteq> D \<inter> Y"
            apply (rule subsetI, rule IntI)
             apply (rule subsetD[OF hAD], assumption)
            apply (rule subsetD[OF hAY], assumption)
            done
          have x_DY: "x \<in> D \<inter> Y"
            apply (rule InterD[OF hx])
            apply (rule CollectI, rule conjI, rule DY_cl, rule A_DY)
            done
          show "x \<in> D"
            by (rule IntD1[OF x_DY])
        qed
        show "x \<in> Y"
          apply (rule InterD[OF hx])
          apply (rule CollectI, rule conjI, rule Y_closed, rule hAY)
          done
      qed
    qed
  next
    show "closure_on X T A \<inter> Y \<subseteq> closure_on Y (subspace_topology X T Y) A"
      unfolding closure_on_def
    proof (rule subsetI)
      fix x
      assume hx: "x \<in> \<Inter>{C. closedin_on X T C \<and> A \<subseteq> C} \<inter> Y"
      have hxcl: "x \<in> \<Inter>{C. closedin_on X T C \<and> A \<subseteq> C}"
        by (rule IntD1[OF hx])
      have hxY: "x \<in> Y"
        by (rule IntD2[OF hx])
      show "x \<in> \<Inter>{C. closedin_on Y (subspace_topology X T Y) C \<and> A \<subseteq> C}"
      proof (rule InterI)
        fix C assume hC: "C \<in> {B. closedin_on Y (subspace_topology X T Y) B \<and> A \<subseteq> B}"
        have hCcl: "closedin_on Y (subspace_topology X T Y) C"
          by (rule conjunct1[OF CollectD[OF hC]])
        have hAC: "A \<subseteq> C"
          by (rule conjunct2[OF CollectD[OF hC]])
        have hCD_ex: "\<exists>D. closedin_on X T D \<and> C = D \<inter> Y"
          by (rule iffD1[OF t172, OF hCcl])
        then obtain D where hDcl: "closedin_on X T D" and hCD: "C = D \<inter> Y"
          by blast
        have hAD: "A \<subseteq> D"
          apply (rule subset_trans[OF hAC])
          apply (subst hCD, rule Int_lower1)
          done
        have xD: "x \<in> D"
          apply (rule InterD[OF hxcl])
          apply (rule CollectI, rule conjI, rule hDcl, rule hAD)
          done
        show "x \<in> C"
          apply (subst hCD, rule IntI, rule xD, rule hxY)
          done
      qed
    qed
  qed
qed

(** from \S17 (Terminology: 'A intersects B' iff A\<inter>B \<noteq> {}) [top1.tex:~707] **)
definition intersects :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "intersects A B \<longleftrightarrow> A \<inter> B \<noteq> {}"

(** from \S17 Theorem 17.5 [top1.tex:713] **)
(** LATEX VERSION: "x\<in>Cl A iff every open neighborhood intersects A; basis version too." **)
definition neighborhood_of :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "neighborhood_of x X T U \<longleftrightarrow> U \<in> T \<and> x \<in> U"

theorem Theorem_17_5a:
  assumes hT: "is_topology_on X T"
  assumes hxX: "x \<in> X" and hAX: "A \<subseteq> X"
  shows "x \<in> closure_on X T A \<longleftrightarrow>
    (\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects U A)"
proof (rule iffI)
  assume hx: "x \<in> closure_on X T A"
  show "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects U A"
  proof (intro allI impI)
    fix U assume hU: "neighborhood_of x X T U"
    have hUT: "U \<in> T"
      by (rule conjunct1[OF hU[unfolded neighborhood_of_def]])
    have hxU: "x \<in> U"
      by (rule conjunct2[OF hU[unfolded neighborhood_of_def]])
    have X_T: "X \<in> T"
      by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
    have inter_T: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
      by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
    have XU_T: "X \<inter> U \<in> T"
    proof -
      have "finite {X, U} \<and> {X, U} \<noteq> {} \<and> {X, U} \<subseteq> T" using X_T hUT by simp
      then have "\<Inter>{X, U} \<in> T" using inter_T by blast
      then show ?thesis by simp
    qed
    have XmU_closed: "closedin_on X T (X - U)"
      apply (rule closedin_intro, rule Diff_subset)
      apply (simp only: Diff_Diff_Int)
      apply (rule XU_T)
      done
    show "intersects U A"
      unfolding intersects_def
    proof (rule notI)
      assume h: "U \<inter> A = {}"
      have A_sub_XmU: "A \<subseteq> X - U"
        using h hAX by blast
      have x_in_XmU: "x \<in> X - U"
        apply (rule InterD[OF hx[unfolded closure_on_def]])
        apply (rule CollectI, rule conjI, rule XmU_closed, rule A_sub_XmU)
        done
      show False
        by (rule DiffD2[OF x_in_XmU, OF hxU])
    qed
  qed
next
  assume h: "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects U A"
  show "x \<in> closure_on X T A"
    unfolding closure_on_def
  proof (rule InterI)
    fix C assume hC: "C \<in> {D. closedin_on X T D \<and> A \<subseteq> D}"
    have hCcl: "closedin_on X T C"
      by (rule conjunct1[OF CollectD[OF hC]])
    have hAC: "A \<subseteq> C"
      by (rule conjunct2[OF CollectD[OF hC]])
    have hXmCT: "X - C \<in> T"
      by (rule closedin_diff_open[OF hCcl])
    show "x \<in> C"
    proof (rule ccontr)
      assume hxnC: "x \<notin> C"
      have hxXmC: "x \<in> X - C"
        apply (rule DiffI, rule hxX, rule hxnC) done
      have hneigh: "neighborhood_of x X T (X - C)"
        apply (unfold neighborhood_of_def, rule conjI, rule hXmCT, rule hxXmC) done
      have hinters: "intersects (X - C) A"
        by (rule h[rule_format, OF hneigh])
      have hdisjoint: "(X - C) \<inter> A = {}"
        using hAC by blast
      show False
        apply (rule notE[OF hinters[unfolded intersects_def]])
        apply (rule hdisjoint)
        done
    qed
  qed
qed

theorem Theorem_17_5b:
  assumes hB: "basis_for X B T"
  assumes hxX: "x \<in> X" and hAX: "A \<subseteq> X"
  shows "x \<in> closure_on X T A \<longleftrightarrow>
    (\<forall>b\<in>B. x \<in> b \<longrightarrow> intersects b A)"
proof (rule iffI)
  assume hcl: "x \<in> closure_on X T A"
  have hBasis: "is_basis_on X B"
    by (rule conjunct1[OF hB[unfolded basis_for_def]])
  have hBX: "\<forall>b'\<in>B. b' \<subseteq> X"
    by (rule conjunct1[OF hBasis[unfolded is_basis_on_def]])
  have hInter_cond: "\<forall>b1\<in>B. \<forall>b2\<in>B. \<forall>y\<in>(b1 \<inter> b2). \<exists>b3\<in>B. y \<in> b3 \<and> b3 \<subseteq> (b1 \<inter> b2)"
    by (rule conjunct2[OF conjunct2[OF hBasis[unfolded is_basis_on_def]]])
  have hT_def': "T = topology_generated_by_basis X B"
    by (rule conjunct2[OF hB[unfolded basis_for_def]])
  show "\<forall>b\<in>B. x \<in> b \<longrightarrow> intersects b A"
  proof (rule ballI, rule impI)
    fix b assume hbB: "b \<in> B" and hxb: "x \<in> b"
    have hbsubX: "b \<subseteq> X" by (rule bspec[OF hBX, OF hbB])
    have hbinT: "b \<in> topology_generated_by_basis X B"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, rule conjI, rule hbsubX)
      show "\<forall>y\<in>b. \<exists>b'\<in>B. y \<in> b' \<and> b' \<subseteq> b"
      proof (rule ballI)
        fix y assume hyb: "y \<in> b"
        have hyin: "y \<in> b \<inter> b" using hyb by simp
        obtain b3 where hb3B: "b3 \<in> B" and hyb3: "y \<in> b3" and hb3sub: "b3 \<subseteq> b \<inter> b"
          using hInter_cond[rule_format, OF hbB, OF hbB, OF hyin] by blast
        have hb3sub': "b3 \<subseteq> b" using hb3sub by (simp only: Int_absorb)
        show "\<exists>b'\<in>B. y \<in> b' \<and> b' \<subseteq> b"
          apply (rule bexI[where x=b3])
           apply (rule conjI[OF hyb3 hb3sub'])
          apply (rule hb3B)
          done
      qed
    qed
    have hbT: "b \<in> T" using hbinT hT_def' by simp
    show "intersects b A"
      unfolding intersects_def
    proof (rule notI)
      assume hbAeq: "b \<inter> A = {}"
      have hAsub_Xmb: "A \<subseteq> X - b" using hAX hbAeq by blast
      have hXmb_eq: "X - (X - b) = b"
        using hbsubX by blast
      have hXmb_cl: "closedin_on X T (X - b)"
        apply (rule closedin_intro, rule Diff_subset)
        apply (subst hXmb_eq, rule hbT)
        done
      have hXmb_in_F: "X - b \<in> {D. closedin_on X T D \<and> A \<subseteq> D}"
        by (rule CollectI, rule conjI, rule hXmb_cl, rule hAsub_Xmb)
      have hx_in_Xmb: "x \<in> X - b"
        by (rule InterD[OF hcl[unfolded closure_on_def], OF hXmb_in_F])
      show False
        using hx_in_Xmb hxb by blast
    qed
  qed
next
  assume h: "\<forall>b\<in>B. x \<in> b \<longrightarrow> intersects b A"
  show "x \<in> closure_on X T A"
    unfolding closure_on_def
  proof (rule InterI)
    fix C assume hC: "C \<in> {D. closedin_on X T D \<and> A \<subseteq> D}"
    have hCcl: "closedin_on X T C"
      by (rule conjunct1[OF CollectD[OF hC]])
    have hAC: "A \<subseteq> C"
      by (rule conjunct2[OF CollectD[OF hC]])
    have hXmCT: "X - C \<in> T"
      by (rule closedin_diff_open[OF hCcl])
    have hT_def: "T = topology_generated_by_basis X B"
      by (rule conjunct2[OF hB[unfolded basis_for_def]])
    show "x \<in> C"
    proof (rule ccontr)
      assume hxnC: "x \<notin> C"
      have hxXmC: "x \<in> X - C"
        apply (rule DiffI, rule hxX, rule hxnC) done
      have hXmC_basis: "X - C \<in> topology_generated_by_basis X B"
        using hXmCT hT_def by simp
      have hex_b: "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> X - C"
        using hXmC_basis hxXmC
        unfolding topology_generated_by_basis_def
        by blast
      then obtain b where hbB: "b \<in> B" and hxb: "x \<in> b" and hbsub: "b \<subseteq> X - C"
        by blast
      have hinters: "intersects b A"
        by (rule h[rule_format, OF hbB, OF hxb])
      have hdisjoint: "b \<inter> A = {}"
        using hbsub hAC by blast
      show False
        apply (rule notE[OF hinters[unfolded intersects_def]])
        apply (rule hdisjoint)
        done
    qed
  qed
qed


subsection \<open>Limit points\<close>

(** from \S17 Definition (Limit point) [top1.tex:~742] **)
definition is_limit_point_of :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_limit_point_of x A X T \<longleftrightarrow>
     x \<in> X \<and> A \<subseteq> X \<and>
     (\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects (U - {x}) A)"

definition limit_points_of :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "limit_points_of A X T = {x\<in>X. is_limit_point_of x A X T}"

(** from \S17 Theorem 17.6 [top1.tex:751] **)
(** LATEX VERSION: "Cl A = A \<union> A'." **)
theorem Theorem_17_6:
  assumes hT: "is_topology_on X T"
  assumes hAX: "A \<subseteq> X"
  shows "closure_on X T A = A \<union> limit_points_of A X T"
proof (rule equalityI)
  show "closure_on X T A \<subseteq> A \<union> limit_points_of A X T"
  proof (rule subsetI)
    fix x assume hx: "x \<in> closure_on X T A"
    have empty_T: "{} \<in> T"
      by (rule conjunct1[OF hT[unfolded is_topology_on_def]])
    have cl_X: "closedin_on X T X"
      apply (rule closedin_intro, rule subset_refl)
      apply (simp only: Diff_cancel)
      apply (rule empty_T)
      done
    have x_in_X: "x \<in> X"
      apply (rule InterD[OF hx[unfolded closure_on_def]])
      apply (rule CollectI, rule conjI, rule cl_X, rule hAX)
      done
    show "x \<in> A \<union> limit_points_of A X T"
    proof (cases "x \<in> A")
      case True show ?thesis by (rule UnI1, rule True)
    next
      case False
      have hxnA: "x \<notin> A" by (rule False)
      have h5a: "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects U A"
        by (rule iffD1[OF Theorem_17_5a[OF hT x_in_X hAX], OF hx])
      have x_lp: "is_limit_point_of x A X T"
        unfolding is_limit_point_of_def
      proof (intro conjI)
        show "x \<in> X" by (rule x_in_X)
        show "A \<subseteq> X" by (rule hAX)
        show "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects (U - {x}) A"
        proof (intro allI impI)
          fix U assume hU: "neighborhood_of x X T U"
          have hUA_ne: "U \<inter> A \<noteq> {}"
            using h5a[rule_format, OF hU] unfolding intersects_def .
          show "intersects (U - {x}) A"
            unfolding intersects_def
          proof (rule notI)
            assume h: "(U - {x}) \<inter> A = {}"
            have UA_empty: "U \<inter> A = {}"
              using h hxnA by blast
            from UA_empty hUA_ne show False by simp
          qed
        qed
      qed
      show "x \<in> A \<union> limit_points_of A X T"
        apply (rule UnI2)
        apply (unfold limit_points_of_def)
        apply (rule CollectI, rule conjI, rule x_in_X, rule x_lp)
        done
    qed
  qed
next
  show "A \<union> limit_points_of A X T \<subseteq> closure_on X T A"
  proof (rule subsetI)
    fix x assume hx: "x \<in> A \<union> limit_points_of A X T"
    show "x \<in> closure_on X T A"
    proof (cases "x \<in> A")
      case True
      have x_in_X: "x \<in> X" by (rule subsetD[OF hAX True])
      show ?thesis
        unfolding closure_on_def
      proof (rule InterI)
        fix C assume hC: "C \<in> {D. closedin_on X T D \<and> A \<subseteq> D}"
        have hAC: "A \<subseteq> C" by (rule conjunct2[OF CollectD[OF hC]])
        show "x \<in> C" by (rule subsetD[OF hAC True])
      qed
    next
      case False
      have hxnA: "x \<notin> A" by (rule False)
      have hxlp: "x \<in> limit_points_of A X T"
        using hx hxnA by blast
      have hx_def: "is_limit_point_of x A X T"
        using hxlp unfolding limit_points_of_def by blast
      have x_in_X: "x \<in> X"
        using hx_def unfolding is_limit_point_of_def by blast
      have hlp_nbds: "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects (U - {x}) A"
        using hx_def unfolding is_limit_point_of_def by blast
      have h_all_nbds: "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects U A"
      proof (intro allI impI)
        fix U assume hU: "neighborhood_of x X T U"
        have h_sub_int: "intersects (U - {x}) A"
          by (rule hlp_nbds[rule_format, OF hU])
        show "intersects U A"
          unfolding intersects_def
        proof (rule notI)
          assume h: "U \<inter> A = {}"
          have h2: "(U - {x}) \<inter> A = {}"
            using h by blast
          from h_sub_int[unfolded intersects_def] h2 show False by simp
        qed
      qed
      show ?thesis
        by (rule iffD2[OF Theorem_17_5a[OF hT x_in_X hAX], OF h_all_nbds])
    qed
  qed
qed

(** from \S17 Corollary 17.7 [top1.tex:761] **)
(** LATEX VERSION: "A closed iff contains all its limit points." **)
theorem Corollary_17_7:
  assumes hT: "is_topology_on X T"
  assumes hAX: "A \<subseteq> X"
  shows "closedin_on X T A \<longleftrightarrow> limit_points_of A X T \<subseteq> A"
proof (rule iffI)
  assume hAcl: "closedin_on X T A"
  show "limit_points_of A X T \<subseteq> A"
  proof (rule subsetI)
    fix x assume hxlp: "x \<in> limit_points_of A X T"
    have hx_def: "is_limit_point_of x A X T"
      using hxlp unfolding limit_points_of_def by blast
    have hxX: "x \<in> X"
      using hx_def unfolding is_limit_point_of_def by blast
    have hlp_nbds: "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects (U - {x}) A"
      using hx_def unfolding is_limit_point_of_def by blast
    show "x \<in> A"
    proof (rule ccontr)
      assume hxnA: "x \<notin> A"
      have hXmAT: "X - A \<in> T" by (rule closedin_diff_open[OF hAcl])
      have hxXmA: "x \<in> X - A" by (rule DiffI, rule hxX, rule hxnA)
      have hneigh: "neighborhood_of x X T (X - A)"
        apply (unfold neighborhood_of_def, rule conjI, rule hXmAT, rule hxXmA) done
      have hinters: "intersects (X - A - {x}) A"
        by (rule hlp_nbds[rule_format, OF hneigh])
      have hdisjoint: "(X - A - {x}) \<inter> A = {}"
        by blast
      show False
        apply (rule notE[OF hinters[unfolded intersects_def]])
        apply (rule hdisjoint)
        done
    qed
  qed
next
  assume hlp: "limit_points_of A X T \<subseteq> A"
  have empty_T: "{} \<in> T"
    by (rule conjunct1[OF hT[unfolded is_topology_on_def]])
  have X_closed: "closedin_on X T X"
    apply (rule closedin_intro, rule subset_refl)
    apply (simp only: Diff_cancel, rule empty_T) done
  have cl_inter: "\<forall>F. F \<noteq> {} \<longrightarrow> (\<forall>C\<in>F. closedin_on X T C) \<longrightarrow> closedin_on X T (\<Inter>F)"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hT]]]])
  have F_ne: "{C. closedin_on X T C \<and> A \<subseteq> C} \<noteq> {}"
  proof (rule notI)
    assume h: "{C. closedin_on X T C \<and> A \<subseteq> C} = {}"
    have "X \<in> {C. closedin_on X T C \<and> A \<subseteq> C}"
      apply (rule CollectI, rule conjI, rule X_closed, rule hAX) done
    from h this show False by blast
  qed
  have cl_closed: "closedin_on X T (closure_on X T A)"
    unfolding closure_on_def
  proof (rule cl_inter[rule_format, OF F_ne])
    fix C assume hC: "C \<in> {D. closedin_on X T D \<and> A \<subseteq> D}"
    show "closedin_on X T C" by (rule conjunct1[OF CollectD[OF hC]])
  qed
  have cl_eq: "closure_on X T A = A"
  proof (rule equalityI)
    show "closure_on X T A \<subseteq> A"
      apply (subst Theorem_17_6[OF hT hAX])
      apply (rule Un_least, rule subset_refl, rule hlp)
      done
    show "A \<subseteq> closure_on X T A"
      unfolding closure_on_def
    proof (rule subsetI)
      fix a assume ha: "a \<in> A"
      show "a \<in> \<Inter>{C. closedin_on X T C \<and> A \<subseteq> C}"
      proof (rule InterI)
        fix C assume hC: "C \<in> {D. closedin_on X T D \<and> A \<subseteq> D}"
        show "a \<in> C" by (rule subsetD[OF conjunct2[OF CollectD[OF hC]], OF ha])
      qed
    qed
  qed
  show "closedin_on X T A"
    using cl_closed by (simp only: cl_eq)
qed


subsection \<open>Hausdorff spaces, T1 axiom, sequences\<close>

(** from \S17 Definition (Hausdorff space) [top1.tex:780] **)
(** LATEX VERSION: "Distinct points have disjoint neighborhoods." **)
definition is_hausdorff_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_hausdorff_on X T \<longleftrightarrow>
     is_topology_on X T \<and>
     (\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
        (\<exists>U V. neighborhood_of x X T U \<and> neighborhood_of y X T V \<and> U \<inter> V = {}))"

(** Helper: every singleton is closed in a Hausdorff space. **)
lemma singleton_closed_in_hausdorff:
  assumes hH: "is_hausdorff_on X T"
  assumes hx0X: "x0 \<in> X"
  shows "closedin_on X T {x0}"
proof -
  have hT: "is_topology_on X T"
    using hH unfolding is_hausdorff_on_def by blast
  have hausd: "\<forall>a\<in>X. \<forall>b\<in>X. a \<noteq> b \<longrightarrow>
      (\<exists>U V. neighborhood_of a X T U \<and> neighborhood_of b X T V \<and> U \<inter> V = {})"
    using hH unfolding is_hausdorff_on_def by blast
  have hlp_sub: "limit_points_of {x0} X T \<subseteq> {x0}"
  proof (rule subsetI)
    fix x assume hxlp: "x \<in> limit_points_of {x0} X T"
    have hx_def: "is_limit_point_of x {x0} X T"
      using hxlp unfolding limit_points_of_def by blast
    have hxX: "x \<in> X" using hx_def unfolding is_limit_point_of_def by blast
    have hall: "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects (U - {x}) {x0}"
      using hx_def unfolding is_limit_point_of_def by blast
    show "x \<in> {x0}"
    proof (rule ccontr)
      assume hxne: "x \<notin> {x0}"
      have hxne': "x \<noteq> x0" using hxne by simp
      obtain U V where hU: "neighborhood_of x X T U"
          and hV: "neighborhood_of x0 X T V" and hdisj: "U \<inter> V = {}"
        using hausd hxX hx0X hxne' by blast
      have hinters: "intersects (U - {x}) {x0}"
        by (rule hall[rule_format, OF hU])
      have hx0inUx: "x0 \<in> U - {x}"
        using hinters unfolding intersects_def by blast
      have hx0V: "x0 \<in> V"
        using hV unfolding neighborhood_of_def by blast
      have hx0U: "x0 \<in> U" using hx0inUx by simp
      show False using hx0U hx0V hdisj by blast
    qed
  qed
  have hx0X': "{x0} \<subseteq> X" using hx0X by simp
  show "closedin_on X T {x0}"
    by (rule iffD2[OF Corollary_17_7[OF hT hx0X'], OF hlp_sub])
qed

(** from \S17 Theorem 17.8 [top1.tex:782] **)
(** LATEX VERSION: "Every finite point set in Hausdorff space is closed." **)
theorem Theorem_17_8:
  assumes hH: "is_hausdorff_on X T"
  assumes hfin: "finite A" and hAX: "A \<subseteq> X"
  shows "closedin_on X T A"
proof -
  have hT: "is_topology_on X T"
    using hH unfolding is_hausdorff_on_def by blast
  have cl_union: "\<forall>F. finite F \<longrightarrow> (\<forall>A\<in>F. closedin_on X T A) \<longrightarrow> closedin_on X T (\<Union>F)"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hT]]]])
  show "closedin_on X T A"
  using hfin hAX proof (induction rule: finite_induct)
    case empty
    show "closedin_on X T {}"
      by (rule conjunct1[OF Theorem_17_1[OF hT]])
  next
    case (insert y F)
    have hyX: "y \<in> X" using insert.prems by simp
    have hFX: "F \<subseteq> X" using insert.prems by simp
    have hF_cl: "closedin_on X T F" by (rule insert.IH[OF hFX])
    have hy_cl: "closedin_on X T {y}"
      by (rule singleton_closed_in_hausdorff[OF hH hyX])
    have G_fin: "finite {{y}, F}" by simp
    have h_union: "closedin_on X T (\<Union>{{y}, F})"
    proof (rule cl_union[rule_format, OF G_fin])
      fix B assume hB: "B \<in> {{y}, F}"
      show "closedin_on X T B"
        using hy_cl hF_cl hB by blast
    qed
    have union_eq: "\<Union>{{y}, F} = insert y F" by simp
    show "closedin_on X T (insert y F)"
      using h_union by (simp only: union_eq)
  qed
qed

(** from \S17 (T1 axiom) [top1.tex:~785] **)
definition satisfies_T1_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "satisfies_T1_on X T \<longleftrightarrow> is_topology_on X T \<and> (\<forall>x\<in>X. closedin_on X T {x})"

(** from \S17 Theorem 17.9 [top1.tex:787] **)
(** LATEX VERSION: "In a T1 space, x is limit point of A iff every neighborhood contains infinitely many points of A." **)
theorem Theorem_17_9:
  assumes hT1: "satisfies_T1_on X T"
  assumes hAX: "A \<subseteq> X" and hxX: "x \<in> X"
  shows "is_limit_point_of x A X T \<longleftrightarrow>
    (\<forall>U. neighborhood_of x X T U \<longrightarrow> infinite (U \<inter> A))"
proof -
  have hT: "is_topology_on X T"
    using hT1 unfolding satisfies_T1_on_def by blast
  have hT1_sc: "\<forall>y\<in>X. closedin_on X T {y}"
    using hT1 unfolding satisfies_T1_on_def by blast
  have cl_union: "\<forall>F. finite F \<longrightarrow> (\<forall>A\<in>F. closedin_on X T A) \<longrightarrow> closedin_on X T (\<Union>F)"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF Theorem_17_1[OF hT]]]])
  have inter_T: "\<forall>G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> T \<longrightarrow> \<Inter>G \<in> T"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hT[unfolded is_topology_on_def]]]])
  show ?thesis
  proof (rule iffI)
    (* → : limit point → every nbhd has infinitely many points of A *)
    assume hlp: "is_limit_point_of x A X T"
    have hlp_nbds: "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects (U - {x}) A"
      using hlp unfolding is_limit_point_of_def by blast
    show "\<forall>U. neighborhood_of x X T U \<longrightarrow> infinite (U \<inter> A)"
    proof (intro allI impI)
      fix U assume hU: "neighborhood_of x X T U"
      have hUT: "U \<in> T" using hU unfolding neighborhood_of_def by blast
      have hxU: "x \<in> U" using hU unfolding neighborhood_of_def by blast
      show "infinite (U \<inter> A)"
      proof (rule notI)
        assume hfin_UA: "finite (U \<inter> A)"
        (* S = the finitely many points of U ∩ (A - {x}) *)
        define S where "S = U \<inter> A - {x}"
        have hS_fin: "finite S"
          apply (unfold S_def)
          apply (rule finite_subset[OF _ hfin_UA])
          apply blast
          done
        have hS_sub_X: "S \<subseteq> X"
          apply (unfold S_def)
          apply (rule subset_trans[OF Diff_subset])
          apply (rule subset_trans[OF Int_lower2 hAX])
          done
        (* S is closed: finite T1 subset of X *)
        have hS_cl: "closedin_on X T S"
          using hS_fin hS_sub_X
        proof (induction rule: finite_induct)
          case empty
          show "closedin_on X T {}"
            by (rule conjunct1[OF Theorem_17_1[OF hT]])
        next
          case (insert z F2)
          have hzX: "z \<in> X" using insert.prems by simp
          have hF2X: "F2 \<subseteq> X" using insert.prems by simp
          have hF2_cl: "closedin_on X T F2" by (rule insert.IH[OF hF2X])
          have hz_cl: "closedin_on X T {z}"
            by (rule bspec[OF hT1_sc, OF hzX])
          have G2_fin: "finite {{z}, F2}" by simp
          have h_u2: "closedin_on X T (\<Union>{{z}, F2})"
          proof (rule cl_union[rule_format, OF G2_fin])
            fix B assume hBG: "B \<in> {{z}, F2}"
            show "closedin_on X T B" using hz_cl hF2_cl hBG by blast
          qed
          show "closedin_on X T (insert z F2)"
            using h_u2 by simp
        qed
        (* X - S is open; U ∩ (X-S) is open *)
        have hXmS_T: "X - S \<in> T" by (rule closedin_diff_open, rule hS_cl)
        have hUXmS_T: "U \<inter> (X - S) \<in> T"
        proof -
          have h_sub: "{U, X - S} \<subseteq> T" using hUT hXmS_T by blast
          have h_inter: "\<Inter>{U, X - S} \<in> T"
            apply (rule inter_T[rule_format])
            apply (intro conjI)
              apply (rule finite.insertI, rule finite.insertI, rule finite.emptyI)
             apply (rule insert_not_empty)
            apply (rule h_sub)
            done
          then show "U \<inter> (X - S) \<in> T" by simp
        qed
        (* x ∈ U ∩ (X-S), so it is a neighborhood of x *)
        have hxnS: "x \<notin> S" unfolding S_def by simp
        have hneigh: "neighborhood_of x X T (U \<inter> (X - S))"
          unfolding neighborhood_of_def
          apply (rule conjI, rule hUXmS_T)
          apply (rule IntI, rule hxU, rule DiffI, rule hxX, rule hxnS)
          done
        (* x limit point → (U ∩ (X-S) - {x}) ∩ A ≠ {} *)
        have hinters: "intersects (U \<inter> (X - S) - {x}) A"
          by (rule hlp_nbds[rule_format, OF hneigh])
        (* But (U ∩ (X-S) - {x}) ∩ A ⊆ S ∩ (X-S) = {} *)
        have h_eq: "(U \<inter> (X - S) - {x}) \<inter> A = {}"
        proof (rule equalityI)
          show "(U \<inter> (X - S) - {x}) \<inter> A \<subseteq> {}"
          proof (rule subsetI)
            fix z assume hz: "z \<in> (U \<inter> (X - S) - {x}) \<inter> A"
            have hzS: "z \<notin> S" using hz by blast
            have hzS2: "z \<in> S"
              unfolding S_def using hz by blast
            show "z \<in> {}" using hzS hzS2 by blast
          qed
          show "{} \<subseteq> (U \<inter> (X - S) - {x}) \<inter> A" by blast
        qed
        show False
          apply (rule notE[OF hinters[unfolded intersects_def]])
          apply (rule h_eq)
          done
      qed
    qed
  next
    (* ← : every nbhd has infinitely many points of A → limit point *)
    assume hback: "\<forall>U. neighborhood_of x X T U \<longrightarrow> infinite (U \<inter> A)"
    show "is_limit_point_of x A X T"
      unfolding is_limit_point_of_def
    proof (intro conjI)
      show "x \<in> X" by (rule hxX)
      show "A \<subseteq> X" by (rule hAX)
      show "\<forall>U. neighborhood_of x X T U \<longrightarrow> intersects (U - {x}) A"
      proof (intro allI impI)
        fix U assume hU: "neighborhood_of x X T U"
        have h_inf: "infinite (U \<inter> A)"
          by (rule hback[rule_format, OF hU])
        show "intersects (U - {x}) A"
          unfolding intersects_def
        proof (rule notI)
          assume h_empty: "(U - {x}) \<inter> A = {}"
          have heq: "U \<inter> A \<subseteq> {x}" using h_empty by blast
          have h_fin: "finite (U \<inter> A)"
            by (rule finite_subset[OF heq], simp)
          from h_inf h_fin show False by simp
        qed
      qed
    qed
  qed
qed

(** from \S17 (Definition of sequence convergence) [top1.tex:~770] **)
definition seq_converges_to_on :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "seq_converges_to_on s x X T \<longleftrightarrow>
     x \<in> X \<and>
     (\<forall>U. neighborhood_of x X T U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> U))"

(** from \S17 Theorem 17.10 [top1.tex:801] **)
(** LATEX VERSION: "In Hausdorff space, a sequence converges to at most one point." **)
theorem Theorem_17_10:
  assumes "is_hausdorff_on X T"
  assumes "seq_converges_to_on s x X T"
  assumes "seq_converges_to_on s y X T"
  shows "x = y"
proof (rule ccontr)
  assume neq: "x \<noteq> y"
  from assms(1) have hausdorff: "\<forall>a\<in>X. \<forall>b\<in>X. a \<noteq> b \<longrightarrow>
      (\<exists>U V. neighborhood_of a X T U \<and> neighborhood_of b X T V \<and> U \<inter> V = {})"
    unfolding is_hausdorff_on_def by blast
  from assms(2) have hx: "x \<in> X"
    and conv_x: "\<forall>U. neighborhood_of x X T U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> U)"
    unfolding seq_converges_to_on_def by blast+
  from assms(3) have hy: "y \<in> X"
    and conv_y: "\<forall>U. neighborhood_of y X T U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> U)"
    unfolding seq_converges_to_on_def by blast+
  from hausdorff hx hy neq obtain U V where
    hU: "neighborhood_of x X T U" and hV: "neighborhood_of y X T V" and disj: "U \<inter> V = {}"
    by blast
  from conv_x hU obtain N1 where N1: "\<forall>n\<ge>N1. s n \<in> U" by blast
  from conv_y hV obtain N2 where N2: "\<forall>n\<ge>N2. s n \<in> V" by blast
  have "s (max N1 N2) \<in> U \<inter> V"
    using N1[rule_format, of "max N1 N2"] N2[rule_format, of "max N1 N2"] by auto
  with disj show False by simp
qed

(** Helper: open rays belong to the order topology **)
lemma open_ray_lt_in_order_topology:
  fixes a :: "'a::linorder"
  shows "open_ray_lt a \<in> order_topology_on_UNIV"
proof -
  have hb: "open_ray_lt a \<in> basis_order_topology"
    unfolding basis_order_topology_def by blast
  show ?thesis
    unfolding order_topology_on_UNIV_def topology_generated_by_basis_def
    using hb by blast
qed

lemma open_ray_gt_in_order_topology:
  fixes a :: "'a::linorder"
  shows "open_ray_gt a \<in> order_topology_on_UNIV"
proof -
  have hb: "open_ray_gt a \<in> basis_order_topology"
    unfolding basis_order_topology_def by blast
  show ?thesis
    unfolding order_topology_on_UNIV_def topology_generated_by_basis_def
    using hb by blast
qed

lemma open_interval_in_order_topology:
  fixes a b :: "'c::linorder"
  assumes hab: "a < b"
  shows "open_interval a b \<in> order_topology_on_UNIV"
proof -
  have hb: "open_interval a b \<in> basis_order_topology"
    unfolding basis_order_topology_def using hab by blast
  show ?thesis
    unfolding order_topology_on_UNIV_def topology_generated_by_basis_def
    using hb by blast
qed

(** from \S17 Theorem 17.11 [top1.tex:809] **)
(** LATEX VERSION: "Order topology on simply ordered set is Hausdorff; products/subspaces preserve Hausdorff." **)
theorem Theorem_17_11:
  shows
    "(is_hausdorff_on (UNIV::'a::linorder set) order_topology_on_UNIV)
     \<and> (\<forall>X1 T1 X2 T2.
            is_hausdorff_on X1 T1 \<and> is_hausdorff_on X2 T2 \<longrightarrow>
            is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2))
     \<and> (\<forall>X T Y.
            is_hausdorff_on X T \<and> Y \<subseteq> X \<longrightarrow>
            is_hausdorff_on Y (subspace_topology X T Y))"
proof (intro conjI)
  show "is_hausdorff_on (UNIV::'a::linorder set) order_topology_on_UNIV"
  proof (unfold is_hausdorff_on_def, intro conjI)
    show "is_topology_on (UNIV::'a::linorder set) order_topology_on_UNIV"
      by (rule order_topology_on_UNIV_is_topology_on)
    show "\<forall>x\<in>(UNIV::'a set). \<forall>y\<in>UNIV. x \<noteq> y \<longrightarrow>
           (\<exists>U V. neighborhood_of x UNIV order_topology_on_UNIV U \<and>
                  neighborhood_of y UNIV order_topology_on_UNIV V \<and> U \<inter> V = {})"
    proof (intro ballI impI)
      fix x y :: 'a
      assume hne: "x \<noteq> y"
      have hcase: "x < y \<or> y < x" using hne neq_iff by blast
      show "\<exists>U V. neighborhood_of x UNIV order_topology_on_UNIV U \<and>
                 neighborhood_of y UNIV order_topology_on_UNIV V \<and> U \<inter> V = {}"
      proof (rule disjE[OF hcase])
        assume hxy: "x < y"
        show "\<exists>U V. neighborhood_of x UNIV order_topology_on_UNIV U \<and>
                   neighborhood_of y UNIV order_topology_on_UNIV V \<and> U \<inter> V = {}"
        proof (cases "\<exists>z. x < z \<and> z < y")
          case True
          then obtain z where hxz: "x < z" and hzy: "z < y" by blast
          have hUx: "neighborhood_of x UNIV order_topology_on_UNIV (open_ray_lt z)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_lt_in_order_topology])
            apply (simp add: open_ray_lt_def hxz)
            done
          have hVy: "neighborhood_of y UNIV order_topology_on_UNIV (open_ray_gt z)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_gt_in_order_topology])
            apply (simp add: open_ray_gt_def hzy)
            done
          have hdisj: "open_ray_lt z \<inter> open_ray_gt z = {}"
            unfolding open_ray_lt_def open_ray_gt_def by auto
          show ?thesis using hUx hVy hdisj by blast
        next
          case False
          have hnmid: "\<forall>z. \<not>(x < z \<and> z < y)" using False by blast
          have hUx: "neighborhood_of x UNIV order_topology_on_UNIV (open_ray_lt y)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_lt_in_order_topology])
            apply (simp add: open_ray_lt_def hxy)
            done
          have hVy: "neighborhood_of y UNIV order_topology_on_UNIV (open_ray_gt x)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_gt_in_order_topology])
            apply (simp add: open_ray_gt_def hxy)
            done
          have hdisj: "open_ray_lt y \<inter> open_ray_gt x = {}"
            unfolding open_ray_lt_def open_ray_gt_def using hnmid by blast
          show ?thesis using hUx hVy hdisj by blast
        qed
      next
        assume hyx: "y < x"
        show "\<exists>U V. neighborhood_of x UNIV order_topology_on_UNIV U \<and>
                   neighborhood_of y UNIV order_topology_on_UNIV V \<and> U \<inter> V = {}"
        proof (cases "\<exists>z. y < z \<and> z < x")
          case True
          then obtain z where hyz: "y < z" and hzx: "z < x" by blast
          have hUx: "neighborhood_of x UNIV order_topology_on_UNIV (open_ray_gt z)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_gt_in_order_topology])
            apply (simp add: open_ray_gt_def hzx)
            done
          have hVy: "neighborhood_of y UNIV order_topology_on_UNIV (open_ray_lt z)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_lt_in_order_topology])
            apply (simp add: open_ray_lt_def hyz)
            done
          have hdisj: "open_ray_gt z \<inter> open_ray_lt z = {}"
            unfolding open_ray_gt_def open_ray_lt_def by auto
          show ?thesis using hUx hVy hdisj by blast
        next
          case False
          have hnmid: "\<forall>z. \<not>(y < z \<and> z < x)" using False by blast
          have hUx: "neighborhood_of x UNIV order_topology_on_UNIV (open_ray_gt y)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_gt_in_order_topology])
            apply (simp add: open_ray_gt_def hyx)
            done
          have hVy: "neighborhood_of y UNIV order_topology_on_UNIV (open_ray_lt x)"
            unfolding neighborhood_of_def
            apply (rule conjI[OF open_ray_lt_in_order_topology])
            apply (simp add: open_ray_lt_def hyx)
            done
          have hdisj: "open_ray_gt y \<inter> open_ray_lt x = {}"
            unfolding open_ray_gt_def open_ray_lt_def using hnmid by blast
          show ?thesis using hUx hVy hdisj by blast
        qed
      qed
    qed
  qed
next
  show "\<forall>X1 T1 X2 T2.
            is_hausdorff_on X1 T1 \<and> is_hausdorff_on X2 T2 \<longrightarrow>
            is_hausdorff_on (X1 \<times> X2) (product_topology_on T1 T2)"
  proof (intro allI impI, elim conjE)
    fix X1 T1 X2 T2
    assume hH1: "is_hausdorff_on X1 T1" and hH2: "is_hausdorff_on X2 T2"
    let ?TP = "product_topology_on T1 T2"
    have hT1: "is_topology_on X1 T1" using hH1 unfolding is_hausdorff_on_def by blast
    have hT2: "is_topology_on X2 T2" using hH2 unfolding is_hausdorff_on_def by blast
    have hX1T1: "X1 \<in> T1" using hT1 unfolding is_topology_on_def by blast
    have hX2T2: "X2 \<in> T2" using hT2 unfolding is_topology_on_def by blast
    have hinterT1: "\<forall>G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> T1 \<longrightarrow> \<Inter>G \<in> T1"
      using hT1 unfolding is_topology_on_def by blast
    have hinterT2: "\<forall>G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> T2 \<longrightarrow> \<Inter>G \<in> T2"
      using hT2 unfolding is_topology_on_def by blast
    have hausd1: "\<forall>x\<in>X1. \<forall>y\<in>X1. x \<noteq> y \<longrightarrow>
                   (\<exists>U V. neighborhood_of x X1 T1 U \<and> neighborhood_of y X1 T1 V \<and> U \<inter> V = {})"
      using hH1 unfolding is_hausdorff_on_def by blast
    have hausd2: "\<forall>x\<in>X2. \<forall>y\<in>X2. x \<noteq> y \<longrightarrow>
                   (\<exists>U V. neighborhood_of x X2 T2 U \<and> neighborhood_of y X2 T2 V \<and> U \<inter> V = {})"
      using hH2 unfolding is_hausdorff_on_def by blast
    (* Helper: product of opens is open in ?TP *)
    have prod_open: "\<forall>U\<in>T1. \<forall>V\<in>T2. U \<times> V \<in> ?TP"
    proof (intro ballI)
      fix U V assume hU: "U \<in> T1" and hV: "V \<in> T2"
      show "U \<times> V \<in> ?TP"
        unfolding product_topology_on_def topology_generated_by_basis_def product_basis_def
      proof (rule CollectI, rule conjI, rule subset_UNIV)
        show "\<forall>x\<in>U \<times> V. \<exists>b\<in>{U \<times> V | U V. U \<in> T1 \<and> V \<in> T2}. x \<in> b \<and> b \<subseteq> U \<times> V"
        proof (rule ballI)
          fix x assume hx: "x \<in> U \<times> V"
          show "\<exists>b\<in>{U \<times> V | U V. U \<in> T1 \<and> V \<in> T2}. x \<in> b \<and> b \<subseteq> U \<times> V"
            apply (rule bexI[where x="U \<times> V"])
             apply (rule conjI[OF hx], blast)
            apply (rule CollectI, rule exI[where x=U], rule exI[where x=V])
            apply (intro conjI refl hU hV)
            done
        qed
      qed
    qed
    (* Helper: binary intersection of product topology elements is in product topology *)
    have bin_inter: "\<forall>W1 W2. W1 \<in> ?TP \<longrightarrow> W2 \<in> ?TP \<longrightarrow> W1 \<inter> W2 \<in> ?TP"
    proof (intro allI impI)
      fix W1 W2 assume hW1: "W1 \<in> ?TP" and hW2: "W2 \<in> ?TP"
      have hW1cov: "\<forall>x\<in>W1. \<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> W1"
        using hW1 unfolding product_topology_on_def topology_generated_by_basis_def by blast
      have hW2cov: "\<forall>x\<in>W2. \<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> W2"
        using hW2 unfolding product_topology_on_def topology_generated_by_basis_def by blast
      show "W1 \<inter> W2 \<in> ?TP"
        unfolding product_topology_on_def topology_generated_by_basis_def
      proof (rule CollectI, rule conjI, rule subset_UNIV)
        show "\<forall>x\<in>W1 \<inter> W2. \<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> W1 \<inter> W2"
        proof (rule ballI)
          fix x assume hx: "x \<in> W1 \<inter> W2"
          have hxW1: "x \<in> W1" and hxW2: "x \<in> W2" using hx by blast+
          obtain b1 where hb1: "b1 \<in> product_basis T1 T2" and hxb1: "x \<in> b1" and hb1W1: "b1 \<subseteq> W1"
            using hW1cov[rule_format, OF hxW1] by blast
          obtain b2 where hb2: "b2 \<in> product_basis T1 T2" and hxb2: "x \<in> b2" and hb2W2: "b2 \<subseteq> W2"
            using hW2cov[rule_format, OF hxW2] by blast
          obtain U1 V1 where hU1T1: "U1 \<in> T1" and hV1T2: "V1 \<in> T2" and hb1eq: "b1 = U1 \<times> V1"
            using hb1 unfolding product_basis_def by blast
          obtain U2 V2 where hU2T1: "U2 \<in> T1" and hV2T2: "V2 \<in> T2" and hb2eq: "b2 = U2 \<times> V2"
            using hb2 unfolding product_basis_def by blast
          have hU12T1: "U1 \<inter> U2 \<in> T1"
          proof -
            have "finite {U1,U2} \<and> {U1,U2} \<noteq> {} \<and> {U1,U2} \<subseteq> T1"
              using hU1T1 hU2T1 by auto
            hence "(\<Inter>{U1,U2}) \<in> T1" using hinterT1[rule_format] by blast
            thus ?thesis by simp
          qed
          have hV12T2: "V1 \<inter> V2 \<in> T2"
          proof -
            have "finite {V1,V2} \<and> {V1,V2} \<noteq> {} \<and> {V1,V2} \<subseteq> T2"
              using hV1T2 hV2T2 by auto
            hence "(\<Inter>{V1,V2}) \<in> T2" using hinterT2[rule_format] by blast
            thus ?thesis by simp
          qed
          have hbasis: "(U1 \<inter> U2) \<times> (V1 \<inter> V2) \<in> product_basis T1 T2"
            unfolding product_basis_def
            apply (rule CollectI, rule exI[where x="U1 \<inter> U2"], rule exI[where x="V1 \<inter> V2"])
            apply (intro conjI refl hU12T1 hV12T2)
            done
          have hx_in: "x \<in> (U1 \<inter> U2) \<times> (V1 \<inter> V2)"
            using hxb1 hb1eq hxb2 hb2eq by blast
          have hcovW: "(U1 \<inter> U2) \<times> (V1 \<inter> V2) \<subseteq> W1 \<inter> W2"
            using hb1eq hb2eq hb1W1 hb2W2 by blast
          show "\<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> W1 \<inter> W2"
            apply (rule bexI[where x="(U1 \<inter> U2) \<times> (V1 \<inter> V2)"])
             apply (rule conjI[OF hx_in hcovW])
            apply (rule hbasis)
            done
        qed
      qed
    qed
    (* is_topology_on (X1 × X2) ?TP *)
    have hTP_top: "is_topology_on (X1 \<times> X2) ?TP"
    proof (unfold is_topology_on_def, intro conjI)
      show "{} \<in> ?TP"
        unfolding product_topology_on_def topology_generated_by_basis_def by blast
      show "X1 \<times> X2 \<in> ?TP"
        using prod_open[rule_format, OF hX1T1 hX2T2] by blast
      show "\<forall>U. U \<subseteq> ?TP \<longrightarrow> \<Union>U \<in> ?TP"
      proof (intro allI impI)
        fix U assume hU: "U \<subseteq> ?TP"
        have hUcov: "\<forall>W\<in>U. \<forall>x\<in>W. \<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> W"
        proof (rule ballI)
          fix W assume hWU: "W \<in> U"
          have hWT: "W \<in> ?TP" using hU hWU by blast
          show "\<forall>x\<in>W. \<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> W"
            using hWT unfolding product_topology_on_def topology_generated_by_basis_def by blast
        qed
        show "\<Union>U \<in> ?TP"
          unfolding product_topology_on_def topology_generated_by_basis_def
        proof (rule CollectI, rule conjI, rule subset_UNIV)
          show "\<forall>x\<in>\<Union>U. \<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> \<Union>U"
          proof (rule ballI)
            fix x assume hx: "x \<in> \<Union>U"
            obtain W where hWU: "W \<in> U" and hxW: "x \<in> W" using hx by blast
            obtain b where hb: "b \<in> product_basis T1 T2" and hxb: "x \<in> b" and hbW: "b \<subseteq> W"
              using hUcov[rule_format, OF hWU, rule_format, OF hxW] by blast
            show "\<exists>b\<in>product_basis T1 T2. x \<in> b \<and> b \<subseteq> \<Union>U"
              apply (rule bexI[where x=b])
               apply (rule conjI[OF hxb])
               using hbW hWU apply blast
              apply (rule hb)
              done
          qed
        qed
      qed
      show "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TP \<longrightarrow> \<Inter>F \<in> ?TP"
      proof (intro allI impI, elim conjE)
        fix F assume hfin: "finite F" and hne: "F \<noteq> {}" and hF: "F \<subseteq> ?TP"
        show "\<Inter>F \<in> ?TP"
        using hfin hne hF
        proof (induction F rule: finite_induct)
          case empty thus ?case by simp
        next
          case (insert W F0)
          have hWT: "W \<in> ?TP" using insert.prems by blast
          show "\<Inter>(insert W F0) \<in> ?TP"
          proof (cases "F0 = {}")
            case True thus ?thesis using hWT by simp
          next
            case False
            have hF0T: "F0 \<subseteq> ?TP" using insert.prems by blast
            have hIF0: "\<Inter>F0 \<in> ?TP" using insert.IH insert.hyps False hF0T by blast
            have hinter: "\<Inter>(insert W F0) = W \<inter> \<Inter>F0" by simp
            show ?thesis using hinter bin_inter[rule_format, OF hWT hIF0] by simp
          qed
        qed
      qed
    qed
    (* Hausdorff separation for X1 × X2 *)
    have hhausd_prod: "\<forall>p\<in>X1\<times>X2. \<forall>q\<in>X1\<times>X2. p \<noteq> q \<longrightarrow>
              (\<exists>U V. neighborhood_of p (X1\<times>X2) ?TP U \<and> neighborhood_of q (X1\<times>X2) ?TP V \<and> U \<inter> V = {})"
    proof (intro ballI impI)
      fix p q assume hpX: "p \<in> X1 \<times> X2" and hqX: "q \<in> X1 \<times> X2" and hpq: "p \<noteq> q"
      obtain p1 p2 where hpeq: "p = (p1, p2)" by (cases p)
      obtain q1 q2 where hqeq: "q = (q1, q2)" by (cases q)
      have hp1X1: "p1 \<in> X1" and hp2X2: "p2 \<in> X2" using hpX hpeq by auto
      have hq1X1: "q1 \<in> X1" and hq2X2: "q2 \<in> X2" using hqX hqeq by auto
      have hne: "p1 \<noteq> q1 \<or> p2 \<noteq> q2" using hpq hpeq hqeq by auto
      show "\<exists>U V. neighborhood_of p (X1\<times>X2) ?TP U \<and> neighborhood_of q (X1\<times>X2) ?TP V \<and> U \<inter> V = {}"
      proof (rule disjE[OF hne])
        assume hne1: "p1 \<noteq> q1"
        obtain U1 V1 where hU1: "neighborhood_of p1 X1 T1 U1"
            and hV1: "neighborhood_of q1 X1 T1 V1" and hdisj1: "U1 \<inter> V1 = {}"
          using hausd1 hp1X1 hq1X1 hne1 by blast
        have hU1T1: "U1 \<in> T1" and hp1U1: "p1 \<in> U1"
          using hU1 unfolding neighborhood_of_def by blast+
        have hV1T1: "V1 \<in> T1" and hq1V1: "q1 \<in> V1"
          using hV1 unfolding neighborhood_of_def by blast+
        have hU1X2: "U1 \<times> X2 \<in> ?TP" using prod_open[rule_format, OF hU1T1 hX2T2] by blast
        have hV1X2: "V1 \<times> X2 \<in> ?TP" using prod_open[rule_format, OF hV1T1 hX2T2] by blast
        have hp_in: "p \<in> U1 \<times> X2" using hp1U1 hp2X2 hpeq by simp
        have hq_in: "q \<in> V1 \<times> X2" using hq1V1 hq2X2 hqeq by simp
        have hdisj: "(U1 \<times> X2) \<inter> (V1 \<times> X2) = {}" using hdisj1 by blast
        have hnp: "neighborhood_of p (X1 \<times> X2) ?TP (U1 \<times> X2)"
          unfolding neighborhood_of_def using hU1X2 hp_in by blast
        have hnq: "neighborhood_of q (X1 \<times> X2) ?TP (V1 \<times> X2)"
          unfolding neighborhood_of_def using hV1X2 hq_in by blast
        show ?thesis using hnp hnq hdisj by blast
      next
        assume hne2: "p2 \<noteq> q2"
        obtain U2 V2 where hU2: "neighborhood_of p2 X2 T2 U2"
            and hV2: "neighborhood_of q2 X2 T2 V2" and hdisj2: "U2 \<inter> V2 = {}"
          using hausd2 hp2X2 hq2X2 hne2 by blast
        have hU2T2: "U2 \<in> T2" and hp2U2: "p2 \<in> U2"
          using hU2 unfolding neighborhood_of_def by blast+
        have hV2T2: "V2 \<in> T2" and hq2V2: "q2 \<in> V2"
          using hV2 unfolding neighborhood_of_def by blast+
        have hX1U2: "X1 \<times> U2 \<in> ?TP" using prod_open[rule_format, OF hX1T1 hU2T2] by blast
        have hX1V2: "X1 \<times> V2 \<in> ?TP" using prod_open[rule_format, OF hX1T1 hV2T2] by blast
        have hp_in: "p \<in> X1 \<times> U2" using hp1X1 hp2U2 hpeq by simp
        have hq_in: "q \<in> X1 \<times> V2" using hq1X1 hq2V2 hqeq by simp
        have hdisj: "(X1 \<times> U2) \<inter> (X1 \<times> V2) = {}" using hdisj2 by blast
        have hnp: "neighborhood_of p (X1 \<times> X2) ?TP (X1 \<times> U2)"
          unfolding neighborhood_of_def using hX1U2 hp_in by blast
        have hnq: "neighborhood_of q (X1 \<times> X2) ?TP (X1 \<times> V2)"
          unfolding neighborhood_of_def using hX1V2 hq_in by blast
        show ?thesis using hnp hnq hdisj by blast
      qed
    qed
    show "is_hausdorff_on (X1 \<times> X2) ?TP"
      unfolding is_hausdorff_on_def using hTP_top hhausd_prod by blast
  qed
next
  show "\<forall>X T Y.
            is_hausdorff_on X T \<and> Y \<subseteq> X \<longrightarrow>
            is_hausdorff_on Y (subspace_topology X T Y)"
  proof (intro allI impI, elim conjE)
    fix X T Y
    assume hH: "is_hausdorff_on X T" and hYX: "Y \<subseteq> X"
    have hT: "is_topology_on X T" using hH unfolding is_hausdorff_on_def by blast
    have hempty: "{} \<in> T" and hXT: "X \<in> T"
      and hunion: "\<forall>U. U \<subseteq> T \<longrightarrow> \<Union>U \<in> T"
      and hinter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
      using hT unfolding is_topology_on_def by blast+
    have hausd: "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
                   (\<exists>U V. neighborhood_of x X T U \<and> neighborhood_of y X T V \<and> U \<inter> V = {})"
      using hH unfolding is_hausdorff_on_def by blast
    let ?TY = "subspace_topology X T Y"
    have hTY: "is_topology_on Y ?TY"
    proof (unfold is_topology_on_def, intro conjI)
      show "{} \<in> ?TY"
        unfolding subspace_topology_def using hempty by blast
      show "Y \<in> ?TY"
        unfolding subspace_topology_def using hXT hYX by blast
      show "\<forall>U. U \<subseteq> ?TY \<longrightarrow> \<Union>U \<in> ?TY"
      proof (intro allI impI)
        fix U assume hU: "U \<subseteq> ?TY"
        have hcov: "\<forall>W\<in>U. \<exists>V. V \<in> T \<and> W = Y \<inter> V"
          using hU unfolding subspace_topology_def by blast
        obtain Vf where hVf: "\<forall>W\<in>U. Vf W \<in> T \<and> W = Y \<inter> Vf W"
          using bchoice[OF hcov] by blast
        have union_eq: "\<Union>U = Y \<inter> \<Union>(Vf ` U)"
        proof (rule set_eqI)
          fix x show "x \<in> \<Union>U \<longleftrightarrow> x \<in> Y \<inter> \<Union>(Vf ` U)"
          proof
            assume "x \<in> \<Union>U"
            then obtain W where hW: "W \<in> U" and hxW: "x \<in> W" by blast
            have heq: "W = Y \<inter> Vf W" using hVf hW by blast
            have hxY: "x \<in> Y" and hxVf: "x \<in> Vf W" using hxW heq by blast+
            show "x \<in> Y \<inter> \<Union>(Vf ` U)" using hxY hW hxVf by blast
          next
            assume "x \<in> Y \<inter> \<Union>(Vf ` U)"
            then obtain W where hxY: "x \<in> Y" and hW: "W \<in> U" and hxVf: "x \<in> Vf W"
              by blast
            have heq: "W = Y \<inter> Vf W" using hVf hW by blast
            show "x \<in> \<Union>U" using hW heq hxY hxVf by blast
          qed
        qed
        have hVfT: "Vf ` U \<subseteq> T" using hVf by blast
        have hUVf: "\<Union>(Vf ` U) \<in> T" using hunion hVfT by blast
        show "\<Union>U \<in> ?TY"
          unfolding subspace_topology_def using hUVf union_eq by blast
      qed
      show "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TY \<longrightarrow> \<Inter>F \<in> ?TY"
      proof (intro allI impI, elim conjE)
        fix F
        assume hfin: "finite F" and hne: "F \<noteq> {}" and hF: "F \<subseteq> ?TY"
        have hcov: "\<forall>W\<in>F. \<exists>V. V \<in> T \<and> W = Y \<inter> V"
          using hF unfolding subspace_topology_def by blast
        obtain Vf where hVf: "\<forall>W\<in>F. Vf W \<in> T \<and> W = Y \<inter> Vf W"
          using bchoice[OF hcov] by blast
        have inter_eq: "\<Inter>F = Y \<inter> \<Inter>(Vf ` F)"
        proof (rule set_eqI)
          fix x show "x \<in> \<Inter>F \<longleftrightarrow> x \<in> Y \<inter> \<Inter>(Vf ` F)"
          proof
            assume hx: "x \<in> \<Inter>F"
            obtain W where hW: "W \<in> F" using hne by blast
            have hxW: "x \<in> W" using hx hW by blast
            have heq: "W = Y \<inter> Vf W" using hVf hW by blast
            have hxY: "x \<in> Y" using hxW heq by blast
            have hxVfF: "x \<in> \<Inter>(Vf ` F)"
            proof (rule InterI)
              fix S assume "S \<in> Vf ` F"
              then obtain W2 where hW2: "W2 \<in> F" and hS: "S = Vf W2" by blast
              have "x \<in> W2" using hx hW2 by blast
              moreover have "W2 = Y \<inter> Vf W2" using hVf hW2 by blast
              ultimately show "x \<in> S" using hS by blast
            qed
            show "x \<in> Y \<inter> \<Inter>(Vf ` F)" using hxY hxVfF by blast
          next
            assume hx: "x \<in> Y \<inter> \<Inter>(Vf ` F)"
            then have hxY: "x \<in> Y" and hxVfF: "x \<in> \<Inter>(Vf ` F)" by blast+
            show "x \<in> \<Inter>F"
            proof (rule InterI)
              fix W assume hW: "W \<in> F"
              have "Vf W \<in> Vf ` F" using hW by blast
              hence "x \<in> Vf W" using hxVfF by blast
              moreover have "W = Y \<inter> Vf W" using hVf hW by blast
              ultimately show "x \<in> W" using hxY by blast
            qed
          qed
        qed
        have hVfFT: "Vf ` F \<subseteq> T" using hVf by blast
        have hfVfF: "finite (Vf ` F)" using hfin by (rule finite_imageI)
        have hneVfF: "Vf ` F \<noteq> {}" using hne by blast
        have h_inter: "\<Inter>(Vf ` F) \<in> T"
          using hinter hfVfF hneVfF hVfFT by blast
        show "\<Inter>F \<in> ?TY"
          unfolding subspace_topology_def using h_inter inter_eq by blast
      qed
    qed
    show "is_hausdorff_on Y (subspace_topology X T Y)"
    proof (unfold is_hausdorff_on_def, intro conjI)
      show "is_topology_on Y ?TY" using hTY .
      show "\<forall>x\<in>Y. \<forall>y\<in>Y. x \<noteq> y \<longrightarrow>
               (\<exists>U V. neighborhood_of x Y ?TY U \<and> neighborhood_of y Y ?TY V \<and> U \<inter> V = {})"
      proof (intro ballI impI)
        fix x y
        assume hxY: "x \<in> Y" and hyY: "y \<in> Y" and hne: "x \<noteq> y"
        have hxX: "x \<in> X" using hxY hYX by blast
        have hyX: "y \<in> X" using hyY hYX by blast
        obtain U V where hU: "neighborhood_of x X T U"
            and hV: "neighborhood_of y X T V" and hdisj: "U \<inter> V = {}"
          using hausd hxX hyX hne by blast
        have hUT: "U \<in> T" and hxU: "x \<in> U"
          using hU unfolding neighborhood_of_def by blast+
        have hVT: "V \<in> T" and hyV: "y \<in> V"
          using hV unfolding neighborhood_of_def by blast+
        have hYUT: "Y \<inter> U \<in> ?TY"
          unfolding subspace_topology_def using hUT by blast
        have hYVT: "Y \<inter> V \<in> ?TY"
          unfolding subspace_topology_def using hVT by blast
        have hdisj': "(Y \<inter> U) \<inter> (Y \<inter> V) = {}" using hdisj by blast
        show "\<exists>U' V'. neighborhood_of x Y ?TY U' \<and> neighborhood_of y Y ?TY V' \<and> U' \<inter> V' = {}"
          using hYUT hxY hxU hYVT hyY hyV hdisj'
          unfolding neighborhood_of_def by blast
      qed
    qed
  qed
qed

section \<open>\<S>18 Continuous Functions\<close>

(** from \S18 Definition (Continuity) [top1.tex:~930] **)
(** LATEX VERSION: "f : X \<rightarrow> Y is continuous iff inverse images of open sets are open." **)
definition top1_continuous_map_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
     (\<forall>x\<in>X. f x \<in> Y) \<and> (\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX)"

(** Helper: an injective continuous map into a Hausdorff space has Hausdorff domain. **)
lemma hausdorff_on_of_inj_continuous_map:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes hTopX: "is_topology_on X TX"
  assumes hHausZ: "is_hausdorff_on Z TZ"
  assumes hcont: "top1_continuous_map_on X TX Z TZ f"
  assumes hinj: "inj_on f X"
  shows "is_hausdorff_on X TX"
proof (unfold is_hausdorff_on_def, intro conjI)
  show "is_topology_on X TX"
    by (rule hTopX)

  have hmap: "\<forall>x\<in>X. f x \<in> Z"
    using hcont unfolding top1_continuous_map_on_def by blast

  have hopen: "\<forall>V\<in>TZ. {x\<in>X. f x \<in> V} \<in> TX"
    using hcont unfolding top1_continuous_map_on_def by blast

  have hausZ:
      "\<forall>a\<in>Z. \<forall>b\<in>Z. a \<noteq> b \<longrightarrow>
         (\<exists>U V. neighborhood_of a Z TZ U \<and> neighborhood_of b Z TZ V \<and> U \<inter> V = {})"
    using hHausZ unfolding is_hausdorff_on_def by blast

  show "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
        (\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
  proof (intro ballI impI)
    fix x y
    assume hxX: "x \<in> X" and hyX: "y \<in> X" and hxy: "x \<noteq> y"

    have hfxZ: "f x \<in> Z"
      using hmap hxX by blast
    have hfyZ: "f y \<in> Z"
      using hmap hyX by blast

    have hfxy: "f x \<noteq> f y"
    proof
      assume hfeq: "f x = f y"
      have "x = y"
        using hinj hxX hyX hfeq unfolding inj_on_def by blast
      thus False
        using hxy by contradiction
    qed

    obtain U V where hU: "neighborhood_of (f x) Z TZ U"
        and hV: "neighborhood_of (f y) Z TZ V"
        and hdisj: "U \<inter> V = {}"
      using hausZ hfxZ hfyZ hfxy by blast

    have hUTZ: "U \<in> TZ" and hfxU: "f x \<in> U"
      using hU unfolding neighborhood_of_def by blast+
    have hVTZ: "V \<in> TZ" and hfyV: "f y \<in> V"
      using hV unfolding neighborhood_of_def by blast+

    let ?Ux = "{a\<in>X. f a \<in> U}"
    let ?Vy = "{a\<in>X. f a \<in> V}"

    have hUxT: "?Ux \<in> TX"
      using hopen hUTZ by blast
    have hVyT: "?Vy \<in> TX"
      using hopen hVTZ by blast

    have hxUx: "x \<in> ?Ux"
      using hxX hfxU by simp
    have hyVy: "y \<in> ?Vy"
      using hyX hfyV by simp

    have hneigh_x: "neighborhood_of x X TX ?Ux"
      unfolding neighborhood_of_def using hUxT hxUx by blast
    have hneigh_y: "neighborhood_of y X TX ?Vy"
      unfolding neighborhood_of_def using hVyT hyVy by blast

    have hpre_disj: "?Ux \<inter> ?Vy = {}"
    proof (rule ccontr)
      assume hnon: "?Ux \<inter> ?Vy \<noteq> {}"
      then obtain a where ha: "a \<in> ?Ux \<inter> ?Vy"
        by blast
      have hfaU: "f a \<in> U"
        using ha by simp
      have hfaV: "f a \<in> V"
        using ha by simp
      have "f a \<in> U \<inter> V"
        using hfaU hfaV by simp
      thus False
        using hdisj by simp
    qed

    show "\<exists>U' V'. neighborhood_of x X TX U' \<and> neighborhood_of y X TX V' \<and> U' \<inter> V' = {}"
    proof (rule exI[where x = ?Ux], rule exI[where x = ?Vy], intro conjI)
      show "neighborhood_of x X TX ?Ux"
        by (rule hneigh_x)
      show "neighborhood_of y X TX ?Vy"
        by (rule hneigh_y)
      show "?Ux \<inter> ?Vy = {}"
        by (rule hpre_disj)
    qed
  qed
qed

lemma top1_continuous_map_on_generated_by_basis:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes hTopX: "is_topology_on X TX"
  assumes hBasis: "basis_for Y B TY"
  assumes hmap: "\<forall>x\<in>X. f x \<in> Y"
  assumes hpre: "\<forall>b\<in>B. {x\<in>X. f x \<in> b} \<in> TX"
  shows "top1_continuous_map_on X TX Y TY f"
proof -
  have hUnionTX: "\<forall>U. U \<subseteq> TX \<longrightarrow> (\<Union>U) \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]]])

  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. f x \<in> Y"
      by (rule hmap)
    show "\<forall>V\<in>TY. {x \<in> X. f x \<in> V} \<in> TX"
    proof (intro ballI)
      fix V assume hV: "V \<in> TY"
      have hTY: "TY = {\<Union>U | U. U \<subseteq> B}"
        by (rule Lemma_13_1[OF hBasis])
      obtain U where hUsub: "U \<subseteq> B" and hVeq: "V = \<Union>U"
        using hV unfolding hTY by blast

      define PU where "PU = {{x\<in>X. f x \<in> b} | b. b \<in> U}"
      have hPU_sub: "PU \<subseteq> TX"
      proof (rule subsetI)
        fix W assume hW: "W \<in> PU"
        obtain b where hbU: "b \<in> U" and hWeq: "W = {x\<in>X. f x \<in> b}"
          using hW unfolding PU_def by blast
        have hbB: "b \<in> B"
          using hbU hUsub by blast
        show "W \<in> TX"
          unfolding hWeq using hpre hbB by blast
      qed

      have hUnionPU: "\<Union>PU \<in> TX"
        using hUnionTX hPU_sub by blast

      have hpre_eq: "{x\<in>X. f x \<in> V} = \<Union>PU"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x\<in>X. f x \<in> V} \<longleftrightarrow> x \<in> \<Union>PU"
	        proof (rule iffI)
	          assume hx: "x \<in> {x\<in>X. f x \<in> V}"
	          have hx_conj: "x \<in> X \<and> f x \<in> V"
	            using hx by simp
	          have hxX: "x \<in> X"
	            using hx_conj by (rule conjunct1)
	          have hfx: "f x \<in> V"
	            using hx_conj by (rule conjunct2)
	          have hfxU: "f x \<in> \<Union>U"
	            using hfx by (simp add: hVeq)
	          obtain b where hbU: "b \<in> U" and hfxb: "f x \<in> b"
	            using hfxU by blast
          have "x \<in> {x\<in>X. f x \<in> b}"
            using hxX hfxb by simp
          have "{x\<in>X. f x \<in> b} \<in> PU"
            unfolding PU_def using hbU by blast
          thus "x \<in> \<Union>PU"
            using \<open>x \<in> {x\<in>X. f x \<in> b}\<close> by blast
        next
          assume hx: "x \<in> \<Union>PU"
          then obtain W where hW: "W \<in> PU" and hxW: "x \<in> W"
            by blast
	          obtain b where hbU: "b \<in> U" and hWeq: "W = {x\<in>X. f x \<in> b}"
	            using hW unfolding PU_def by blast
	          have hxW_conj: "x \<in> X \<and> f x \<in> b"
	            using hxW unfolding hWeq by simp
	          have hxX: "x \<in> X"
	            using hxW_conj by (rule conjunct1)
	          have hfxb: "f x \<in> b"
	            using hxW_conj by (rule conjunct2)
	          have hfxU: "f x \<in> \<Union>U"
	            using hbU hfxb by blast
	          have "f x \<in> V"
	            unfolding hVeq using hfxU by simp
          thus "x \<in> {x\<in>X. f x \<in> V}"
            using hxX by simp
        qed
      qed

      show "{x \<in> X. f x \<in> V} \<in> TX"
        unfolding hpre_eq using hUnionPU .
    qed
  qed
qed

lemma top1_continuous_map_on_comp:
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
  assumes hf: "top1_continuous_map_on X TX Y TY f"
  assumes hg: "top1_continuous_map_on Y TY Z TZ g"
  shows "top1_continuous_map_on X TX Z TZ (g \<circ> f)"
proof -
  have hfmap: "\<forall>x\<in>X. f x \<in> Y"
    using hf unfolding top1_continuous_map_on_def by blast
  have hfpre: "\<forall>U\<in>TY. {x\<in>X. f x \<in> U} \<in> TX"
    using hf unfolding top1_continuous_map_on_def by blast
  have hgmap: "\<forall>y\<in>Y. g y \<in> Z"
    using hg unfolding top1_continuous_map_on_def by blast
  have hgpre: "\<forall>V\<in>TZ. {y\<in>Y. g y \<in> V} \<in> TY"
    using hg unfolding top1_continuous_map_on_def by blast

  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. (g \<circ> f) x \<in> Z"
    proof (intro ballI)
      fix x assume hx: "x \<in> X"
      have hfx: "f x \<in> Y" using hfmap hx by blast
      have "g (f x) \<in> Z" using hgmap hfx by blast
      thus "(g \<circ> f) x \<in> Z" by simp
    qed
    show "\<forall>V\<in>TZ. {x \<in> X. (g \<circ> f) x \<in> V} \<in> TX"
    proof (intro ballI)
      fix V assume hV: "V \<in> TZ"
      have hpreV: "{y\<in>Y. g y \<in> V} \<in> TY"
        using hgpre hV by blast
      have hEq: "{x \<in> X. (g \<circ> f) x \<in> V} = {x \<in> X. f x \<in> {y\<in>Y. g y \<in> V}}"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x \<in> X. (g \<circ> f) x \<in> V} \<longleftrightarrow> x \<in> {x \<in> X. f x \<in> {y\<in>Y. g y \<in> V}}"
	        proof
	          assume hx: "x \<in> {x \<in> X. (g \<circ> f) x \<in> V}"
	          have hx_conj: "x \<in> X \<and> g (f x) \<in> V"
	            using hx by simp
	          have hxX: "x \<in> X"
	            using hx_conj by (rule conjunct1)
	          have hgf: "g (f x) \<in> V"
	            using hx_conj by (rule conjunct2)
	          have hfxY: "f x \<in> Y" using hfmap hxX by blast
	          have "f x \<in> {y\<in>Y. g y \<in> V}"
	            using hfxY hgf by simp
	          thus "x \<in> {x \<in> X. f x \<in> {y\<in>Y. g y \<in> V}}"
            using hxX by simp
	        next
	          assume hx: "x \<in> {x \<in> X. f x \<in> {y\<in>Y. g y \<in> V}}"
	          have hx_conj: "x \<in> X \<and> f x \<in> {y\<in>Y. g y \<in> V}"
	            using hx by simp
	          have hxX: "x \<in> X"
	            using hx_conj by (rule conjunct1)
	          have hfx: "f x \<in> {y\<in>Y. g y \<in> V}"
	            using hx_conj by (rule conjunct2)
	          have hgf: "g (f x) \<in> V"
	            using hfx by simp
	          show "x \<in> {x \<in> X. (g \<circ> f) x \<in> V}"
	            using hxX hgf by simp
	        qed
      qed
      have "{x\<in>X. f x \<in> {y\<in>Y. g y \<in> V}} \<in> TX"
        using hfpre hpreV by blast
      thus "{x \<in> X. (g \<circ> f) x \<in> V} \<in> TX"
        using hEq by simp
    qed
  qed
qed

(** Continuity into a topology generated by a subbasis.
    It suffices to check inverse images of subbasic opens. **)
lemma top1_continuous_map_on_to_topology_generated_by_subbasis:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes hTopA: "is_topology_on A TA"
  assumes hMap: "\<forall>a\<in>A. f a \<in> X"
  assumes hPreS: "\<forall>U\<in>S. {a\<in>A. f a \<in> U} \<in> TA"
  shows "top1_continuous_map_on A TA X (topology_generated_by_subbasis X S) f"
proof -
  have hAopen: "A \<in> TA"
    using hTopA unfolding is_topology_on_def by blast

  have hUnionTA: "\<forall>Uc. Uc \<subseteq> TA \<longrightarrow> (\<Union>Uc) \<in> TA"
    using hTopA unfolding is_topology_on_def by blast

  have hPreFI: "\<forall>W\<in>finite_intersections S. {a\<in>A. f a \<in> W} \<in> TA"
  proof (intro ballI)
    fix W
    assume hW: "W \<in> finite_intersections S"
    obtain F where hfin: "finite F" and hFsub: "F \<subseteq> S" and hWeq: "W = \<Inter>F"
      using hW unfolding finite_intersections_def by blast

    have hPreInter: "{a\<in>A. f a \<in> \<Inter>F} \<in> TA"
      using hfin hFsub
    proof (induction F)
      case empty
      have hEq: "{a\<in>A. f a \<in> \<Inter>{}} = A"
        by (rule set_eqI) simp
      show ?case
        unfolding hEq by (rule hAopen)
    next
      case (insert U F)
      have hUF: "U \<in> S"
        using insert.prems by blast
      have hPreU: "{a\<in>A. f a \<in> U} \<in> TA"
        using hPreS hUF by blast

      have hPreF: "{a\<in>A. f a \<in> \<Inter>F} \<in> TA"
        using insert.IH insert.prems by blast

      have hEq: "{a\<in>A. f a \<in> \<Inter>(insert U F)} = {a\<in>A. f a \<in> U} \<inter> {a\<in>A. f a \<in> \<Inter>F}"
      proof (rule set_eqI)
        fix a
        show "a \<in> {a\<in>A. f a \<in> \<Inter>(insert U F)} \<longleftrightarrow>
              a \<in> {a\<in>A. f a \<in> U} \<inter> {a\<in>A. f a \<in> \<Inter>F}"
        proof
          assume ha: "a \<in> {a\<in>A. f a \<in> \<Inter>(insert U F)}"
          have haA: "a \<in> A"
            using ha by simp
          have hfaU: "f a \<in> U"
            using ha by simp
          have hfaF: "f a \<in> \<Inter>F"
            using ha by simp
          have ha1: "a \<in> {a\<in>A. f a \<in> U}"
            using haA hfaU by simp
          have ha2: "a \<in> {a\<in>A. f a \<in> \<Inter>F}"
            using haA hfaF by simp
          show "a \<in> {a\<in>A. f a \<in> U} \<inter> {a\<in>A. f a \<in> \<Inter>F}"
            using ha1 ha2 by simp
        next
          assume ha: "a \<in> {a\<in>A. f a \<in> U} \<inter> {a\<in>A. f a \<in> \<Inter>F}"
          have haA: "a \<in> A"
            using ha by simp
          have hfaU: "f a \<in> U"
            using ha by simp
          have hfaF: "f a \<in> \<Inter>F"
            using ha by simp
          show "a \<in> {a\<in>A. f a \<in> \<Inter>(insert U F)}"
            using haA hfaU hfaF by simp
        qed
      qed

      show ?case
        unfolding hEq
        by (rule topology_inter2[OF hTopA hPreU hPreF])
    qed

    show "{a\<in>A. f a \<in> W} \<in> TA"
      unfolding hWeq by (rule hPreInter)
  qed

  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>a\<in>A. f a \<in> X"
      by (rule hMap)

    show "\<forall>V\<in>topology_generated_by_subbasis X S. {a\<in>A. f a \<in> V} \<in> TA"
    proof (intro ballI)
      fix V
      assume hV: "V \<in> topology_generated_by_subbasis X S"
      obtain Uc where hVeq: "V = \<Union>Uc" and hUcsub: "Uc \<subseteq> finite_intersections S"
        using hV unfolding topology_generated_by_subbasis_def by blast

      have hImgSub: "(\<lambda>W. {a\<in>A. f a \<in> W}) ` Uc \<subseteq> TA"
      proof
        fix P
        assume hP: "P \<in> (\<lambda>W. {a\<in>A. f a \<in> W}) ` Uc"
        obtain W where hWUc: "W \<in> Uc" and hPeq: "P = {a\<in>A. f a \<in> W}"
          using hP by blast
        have hWfi: "W \<in> finite_intersections S"
          using hUcsub hWUc by blast
        show "P \<in> TA"
          unfolding hPeq using hPreFI hWfi by blast
      qed

      have hEq: "{a\<in>A. f a \<in> V} = \<Union>((\<lambda>W. {a\<in>A. f a \<in> W}) ` Uc)"
        unfolding hVeq
        by (rule set_eqI) blast

      show "{a\<in>A. f a \<in> V} \<in> TA"
        unfolding hEq
        by (rule hUnionTA[rule_format, OF hImgSub])
    qed
  qed
qed

definition top1_continuous_at_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_continuous_at_on X TX Y TY f x \<longleftrightarrow>
     x \<in> X \<and>
     (\<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow>
          (\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V))"

(** from \S18 Definition (Homeomorphism) [top1.tex:~990] **)
definition top1_homeomorphism_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_homeomorphism_on X TX Y TY f \<longleftrightarrow>
     is_topology_on X TX
     \<and> is_topology_on Y TY
     \<and> bij_betw f X Y
     \<and> top1_continuous_map_on X TX Y TY f
     \<and> top1_continuous_map_on Y TY X TX (inv_into X f)"

(** An imbedding (topological embedding) of \<open>X\<close> into \<open>Y\<close> is a homeomorphism of \<open>X\<close> onto its image
    (with the subspace topology). **)
definition top1_embedding_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_embedding_on X TX Y TY f \<longleftrightarrow>
     (f ` X \<subseteq> Y)
     \<and> top1_homeomorphism_on X TX (f ` X) (subspace_topology Y TY (f ` X)) f"

(** from \S18 Theorem 18.1 [top1.tex:966] **)
(** LATEX VERSION: "Equivalent formulations of continuity (closure/closed/neighborhood)." **)
theorem Theorem_18_1:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  shows cont_closure:
    "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
       ((\<forall>x\<in>X. f x \<in> Y) \<and>
        (\<forall>A. A \<subseteq> X \<longrightarrow> f ` (closure_on X TX A) \<subseteq> closure_on Y TY (f ` A)))"
    and cont_closed:
    "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
       ((\<forall>x\<in>X. f x \<in> Y) \<and>
        (\<forall>B. closedin_on Y TY B \<longrightarrow> closedin_on X TX {x\<in>X. f x \<in> B}))"
    and cont_nbhd:
    "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
       ((\<forall>x\<in>X. f x \<in> Y) \<and>
        (\<forall>x\<in>X. \<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow>
            (\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V)))"
proof -
  let ?mapXY = "(\<forall>x\<in>X. f x \<in> Y)"

  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])

  have empty_TY: "{} \<in> TY"
    by (rule conjunct1[OF hTY[unfolded is_topology_on_def]])
  have X_open: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])
  have Y_open: "Y \<in> TY"
    by (rule conjunct1[OF conjunct2[OF hTY[unfolded is_topology_on_def]]])

  have Y_closed: "closedin_on Y TY Y"
    by (rule closedin_intro[OF subset_refl], simp only: Diff_cancel, rule empty_TY)

  have preimage_compl_eq:
    "\<And>B. B \<subseteq> Y \<Longrightarrow> ?mapXY \<Longrightarrow>
        X - {x \<in> X. f x \<in> B} = {x \<in> X. f x \<in> Y - B}"
  proof -
    fix B
    assume hBY: "B \<subseteq> Y"
    assume hmap: ?mapXY
    show "X - {x \<in> X. f x \<in> B} = {x \<in> X. f x \<in> Y - B}"
    proof (rule set_eqI)
      fix x
      show "x \<in> X - {x \<in> X. f x \<in> B} \<longleftrightarrow> x \<in> {x \<in> X. f x \<in> Y - B}"
      proof
        assume hx: "x \<in> X - {x \<in> X. f x \<in> B}"
        have hxX: "x \<in> X" and hnot: "x \<notin> {x \<in> X. f x \<in> B}"
          using hx by blast+
        have hfyY: "f x \<in> Y" using hmap hxX by blast
        have hfyB: "f x \<notin> B" using hxX hnot by simp
        have "f x \<in> Y - B" using hfyY hfyB by blast
        thus "x \<in> {x \<in> X. f x \<in> Y - B}" using hxX by simp
      next
        assume hx: "x \<in> {x \<in> X. f x \<in> Y - B}"
        have hxX: "x \<in> X" and hfy: "f x \<in> Y - B" using hx by blast+
        have hfyB: "f x \<notin> B" using hfy by blast
        have "x \<notin> {x \<in> X. f x \<in> B}" using hxX hfyB by simp
        thus "x \<in> X - {x \<in> X. f x \<in> B}" using hxX by blast
      qed
    qed
  qed

  have preimage_interY_eq:
    "\<And>V. ?mapXY \<Longrightarrow> {x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> Y \<inter> V}"
  proof -
    fix V
    assume hmap: ?mapXY
    show "{x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> Y \<inter> V}"
    proof (rule set_eqI)
      fix x
      show "x \<in> {x \<in> X. f x \<in> V} \<longleftrightarrow> x \<in> {x \<in> X. f x \<in> Y \<inter> V}"
      proof
        assume hx: "x \<in> {x \<in> X. f x \<in> V}"
        have hx_conj: "x \<in> X \<and> f x \<in> V"
          using hx by simp
        have hxX: "x \<in> X"
          using hx_conj by (rule conjunct1)
        have hfxV: "f x \<in> V"
          using hx_conj by (rule conjunct2)
        have hfxY: "f x \<in> Y" using hmap hxX by blast
        show "x \<in> {x \<in> X. f x \<in> Y \<inter> V}"
          using hxX hfxY hfxV by simp
      next
        assume hx: "x \<in> {x \<in> X. f x \<in> Y \<inter> V}"
        thus "x \<in> {x \<in> X. f x \<in> V}" by simp
      qed
    qed
  qed

  show cont_closure:
    "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
       (?mapXY \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A)))"
  proof (rule iffI)
    assume hcont: "top1_continuous_map_on X TX Y TY f"
    have hmap: ?mapXY
      using hcont unfolding top1_continuous_map_on_def by blast
    have hpre: "\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX"
      using hcont unfolding top1_continuous_map_on_def by blast
    show "?mapXY \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A))"
    proof (intro conjI)
      show ?mapXY using hmap .
      show "\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A)"
      proof (intro allI impI)
        fix A
        assume hAX: "A \<subseteq> X"
        have hclX: "closure_on X TX A \<subseteq> X"
          by (rule closure_on_subset_carrier[OF hTX hAX])
        have hfA: "f ` A \<subseteq> Y"
          using hmap hAX by blast
        show "f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A)"
        proof (rule subsetI)
          fix y
          assume hy: "y \<in> f ` closure_on X TX A"
          obtain x where hxcl: "x \<in> closure_on X TX A" and hyfx: "y = f x"
            using hy by blast
          have hxX: "x \<in> X"
            using hclX hxcl by blast
          have hfyY: "f x \<in> Y"
            using hmap hxX by blast
          have hfx_closure:
            "f x \<in> closure_on Y TY (f ` A)"
          proof -
            have hnbhd: "\<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow> intersects V (f ` A)"
            proof (intro allI impI)
              fix V
              assume hV: "neighborhood_of (f x) Y TY V"
              have hVTY: "V \<in> TY" and hfxV: "f x \<in> V"
                using hV unfolding neighborhood_of_def by blast+
              have hpreV: "{z \<in> X. f z \<in> V} \<in> TX"
                using hpre hVTY by blast
              have hneigh: "neighborhood_of x X TX {z \<in> X. f z \<in> V}"
                unfolding neighborhood_of_def using hpreV hxX hfxV by simp
              have hcl_char:
                "\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U A"
                using Theorem_17_5a[OF hTX hxX hAX] hxcl by blast
              have hinter: "intersects {z \<in> X. f z \<in> V} A"
                using hcl_char hneigh by blast
              obtain a where haA: "a \<in> A" and haU: "a \<in> {z \<in> X. f z \<in> V}"
                using hinter unfolding intersects_def by blast
              have hfaV: "f a \<in> V" using haU by simp
              have "f a \<in> V \<inter> (f ` A)"
                using hfaV haA by blast
              thus "intersects V (f ` A)"
                unfolding intersects_def by blast
            qed
            show ?thesis
              using Theorem_17_5a[OF hTY hfyY hfA] hnbhd by blast
          qed
          show "y \<in> closure_on Y TY (f ` A)"
            using hfx_closure hyfx by simp
        qed
      qed
    qed
  next
    assume hprop: "?mapXY \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A))"
    have hmap: ?mapXY by (rule conjunct1[OF hprop])
    have hcl: "\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X TX A \<subseteq> closure_on Y TY (f ` A)"
      by (rule conjunct2[OF hprop])

    have hclosed_pre: "\<forall>B. closedin_on Y TY B \<longrightarrow> closedin_on X TX {x\<in>X. f x \<in> B}"
    proof (intro allI impI)
      fix B
      assume hB: "closedin_on Y TY B"
      have hBX: "B \<subseteq> Y"
        by (rule closedin_sub[OF hB])
      define A0 where "A0 = {x\<in>X. f x \<in> B}"
      have hA0X: "A0 \<subseteq> X" unfolding A0_def by blast
      have hfA0: "f ` A0 \<subseteq> B"
        unfolding A0_def by blast
      have hfA0Y: "f ` A0 \<subseteq> Y"
        using hfA0 hBX by blast

      have hclA0: "closure_on X TX A0 \<subseteq> A0"
      proof (rule subsetI)
        fix x
        assume hxcl: "x \<in> closure_on X TX A0"
        have hxX: "x \<in> X"
          using closure_on_subset_carrier[OF hTX hA0X] hxcl by blast
        have hfxB: "f x \<in> B"
        proof -
          have "f x \<in> f ` closure_on X TX A0" using hxcl by blast
          also have "... \<subseteq> closure_on Y TY (f ` A0)"
            using hcl hA0X by blast
          finally have hfx_in_cl: "f x \<in> closure_on Y TY (f ` A0)" .
          have hcl_in_B: "closure_on Y TY (f ` A0) \<subseteq> B"
            by (rule closure_on_subset_of_closed[OF hB], rule hfA0)
          show "f x \<in> B" using hcl_in_B hfx_in_cl by blast
        qed
        show "x \<in> A0"
          unfolding A0_def using hxX hfxB by simp
      qed

      have hA0cl: "closure_on X TX A0 = A0"
      proof (rule equalityI)
        show "closure_on X TX A0 \<subseteq> A0" using hclA0 .
        show "A0 \<subseteq> closure_on X TX A0" by (rule subset_closure_on)
      qed

      have hclA0_closed: "closedin_on X TX (closure_on X TX A0)"
        by (rule closure_on_closed[OF hTX hA0X])
      have hA0_closed: "closedin_on X TX A0"
        using hclA0_closed hA0cl by simp
      show "closedin_on X TX {x \<in> X. f x \<in> B}"
        using hA0_closed by (simp add: A0_def)
    qed

    have hcont: "top1_continuous_map_on X TX Y TY f"
    proof -
      have hpre: "\<forall>V\<in>TY. {x \<in> X. f x \<in> V} \<in> TX"
      proof (intro ballI)
        fix V assume hV: "V \<in> TY"
        define B where "B = Y - V"
        have hBcl: "closedin_on Y TY B"
          unfolding B_def
          apply (rule closedin_intro)
           apply (rule Diff_subset)
          apply (simp only: Diff_Diff_Int)
          apply (rule topology_inter2[OF hTY Y_open hV])
          done
        have hpreBcl: "closedin_on X TX {x\<in>X. f x \<in> B}"
          using hclosed_pre hBcl by blast
        have hcomp_open: "X - {x\<in>X. f x \<in> B} \<in> TX"
          using hpreBcl unfolding closedin_on_def by blast
        have hEq1: "X - {x \<in> X. f x \<in> B} = {x \<in> X. f x \<in> Y \<inter> V}"
          unfolding B_def using preimage_compl_eq[OF Diff_subset hmap] by (simp add: Diff_Diff_Int)
        have hEq: "{x \<in> X. f x \<in> V} = X - {x \<in> X. f x \<in> B}"
        proof -
          have "{x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> Y \<inter> V}"
            by (rule preimage_interY_eq[OF hmap])
          also have "... = X - {x \<in> X. f x \<in> B}"
            by (rule sym[OF hEq1])
          finally show ?thesis .
        qed
        show "{x \<in> X. f x \<in> V} \<in> TX"
          using hcomp_open hEq by simp
      qed
      show ?thesis
        unfolding top1_continuous_map_on_def
        by (intro conjI hmap, rule hpre)
    qed
    show "top1_continuous_map_on X TX Y TY f"
      using hcont .
  qed

  show cont_closed:
    "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
       (?mapXY \<and> (\<forall>B. closedin_on Y TY B \<longrightarrow> closedin_on X TX {x \<in> X. f x \<in> B}))"
  proof (rule iffI)
    assume hcont: "top1_continuous_map_on X TX Y TY f"
    have hmap: ?mapXY
      using hcont unfolding top1_continuous_map_on_def by blast
    have hpre: "\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX"
      using hcont unfolding top1_continuous_map_on_def by blast
    show "?mapXY \<and> (\<forall>B. closedin_on Y TY B \<longrightarrow> closedin_on X TX {x \<in> X. f x \<in> B})"
    proof (intro conjI)
      show ?mapXY using hmap .
      show "\<forall>B. closedin_on Y TY B \<longrightarrow> closedin_on X TX {x \<in> X. f x \<in> B}"
      proof (intro allI impI)
        fix B
        assume hB: "closedin_on Y TY B"
        have hBY: "B \<subseteq> Y"
          by (rule closedin_sub[OF hB])
        have hYmB_open: "Y - B \<in> TY"
          by (rule closedin_diff_open[OF hB])
        have hpre_open: "{x \<in> X. f x \<in> Y - B} \<in> TX"
          using hpre hYmB_open by blast
        have hEq: "X - {x \<in> X. f x \<in> B} = {x \<in> X. f x \<in> Y - B}"
          using preimage_compl_eq[OF hBY hmap] by simp
        show "closedin_on X TX {x \<in> X. f x \<in> B}"
        proof (rule closedin_intro)
          show "{x \<in> X. f x \<in> B} \<subseteq> X" by blast
          show "X - {x \<in> X. f x \<in> B} \<in> TX"
            using hEq hpre_open by simp
        qed
      qed
    qed
  next
    assume hprop: "?mapXY \<and> (\<forall>B. closedin_on Y TY B \<longrightarrow> closedin_on X TX {x \<in> X. f x \<in> B})"
    have hmap: ?mapXY by (rule conjunct1[OF hprop])
    have hclosed_pre: "\<forall>B. closedin_on Y TY B \<longrightarrow> closedin_on X TX {x \<in> X. f x \<in> B}"
      by (rule conjunct2[OF hprop])
    have hpre: "\<forall>V\<in>TY. {x \<in> X. f x \<in> V} \<in> TX"
    proof (intro ballI)
      fix V
      assume hV: "V \<in> TY"
      define B where "B = Y - V"
      have hBcl: "closedin_on Y TY B"
        unfolding B_def
        apply (rule closedin_intro)
         apply (rule Diff_subset)
        apply (simp only: Diff_Diff_Int)
        apply (rule topology_inter2[OF hTY Y_open hV])
        done
      have hpreBcl: "closedin_on X TX {x\<in>X. f x \<in> B}"
        using hclosed_pre hBcl by blast
      have hcomp_open: "X - {x\<in>X. f x \<in> B} \<in> TX"
        using hpreBcl unfolding closedin_on_def by blast
      have hEq1: "X - {x \<in> X. f x \<in> B} = {x \<in> X. f x \<in> Y \<inter> V}"
        unfolding B_def using preimage_compl_eq[OF Diff_subset hmap] by (simp add: Diff_Diff_Int)
      have hEq: "{x \<in> X. f x \<in> V} = X - {x \<in> X. f x \<in> B}"
      proof -
        have "{x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> Y \<inter> V}"
          by (rule preimage_interY_eq[OF hmap])
        also have "... = X - {x \<in> X. f x \<in> B}"
          by (rule sym[OF hEq1])
        finally show ?thesis .
      qed
      show "{x \<in> X. f x \<in> V} \<in> TX"
        using hcomp_open hEq by simp
    qed
    show "top1_continuous_map_on X TX Y TY f"
      unfolding top1_continuous_map_on_def
      by (intro conjI hmap, rule hpre)
  qed

  show cont_nbhd:
    "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
       (?mapXY \<and> (\<forall>x\<in>X. \<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow>
           (\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V)))"
  proof (rule iffI)
    assume hcont: "top1_continuous_map_on X TX Y TY f"
    have hmap: ?mapXY
      using hcont unfolding top1_continuous_map_on_def by blast
    have hpre: "\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX"
      using hcont unfolding top1_continuous_map_on_def by blast
    show "?mapXY \<and> (\<forall>x\<in>X. \<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow>
            (\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V))"
    proof (intro conjI)
      show ?mapXY using hmap .
      show "\<forall>x\<in>X. \<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow>
            (\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V)"
      proof (intro ballI allI impI)
        fix x V
        assume hxX: "x \<in> X"
        assume hV: "neighborhood_of (f x) Y TY V"
        have hVTY: "V \<in> TY" and hfxV: "f x \<in> V"
          using hV unfolding neighborhood_of_def by blast+
        have hUopen: "{z \<in> X. f z \<in> V} \<in> TX"
          using hpre hVTY by blast
        have hU: "neighborhood_of x X TX {z \<in> X. f z \<in> V}"
          unfolding neighborhood_of_def using hUopen hxX hfxV by simp
        have himg: "f ` {z \<in> X. f z \<in> V} \<subseteq> V" by blast
        show "\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V"
          apply (rule exI[where x="{z \<in> X. f z \<in> V}"])
          apply (intro conjI)
           apply (rule hU)
          apply (rule himg)
          done
      qed
    qed
  next
    assume hprop: "?mapXY \<and> (\<forall>x\<in>X. \<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow>
            (\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V))"
    have hmap: ?mapXY by (rule conjunct1[OF hprop])
    have hloc: "\<forall>x\<in>X. \<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow>
            (\<exists>U. neighborhood_of x X TX U \<and> f ` U \<subseteq> V)"
      by (rule conjunct2[OF hprop])
    have hpre: "\<forall>V\<in>TY. {x \<in> X. f x \<in> V} \<in> TX"
    proof (intro ballI)
      fix V assume hV: "V \<in> TY"
      define S where "S = {x \<in> X. f x \<in> V}"

      have hSsub: "{U. U \<in> TX \<and> U \<subseteq> S} \<subseteq> TX" by blast

      have hUnion: "\<Union>{U. U \<in> TX \<and> U \<subseteq> S} = S"
      proof (rule set_eqI)
        fix x
        show "x \<in> \<Union>{U. U \<in> TX \<and> U \<subseteq> S} \<longleftrightarrow> x \<in> S"
        proof
          assume hx: "x \<in> \<Union>{U. U \<in> TX \<and> U \<subseteq> S}"
          obtain U where hU: "U \<in> TX \<and> U \<subseteq> S" and hxU: "x \<in> U"
            using hx by blast
          show "x \<in> S" using hU hxU by blast
        next
          assume hxS: "x \<in> S"
          have hxX: "x \<in> X" and hfxV: "f x \<in> V" using hxS unfolding S_def by blast+
          have hnbhdV: "neighborhood_of (f x) Y TY V"
            unfolding neighborhood_of_def using hV hfxV by blast
          obtain U where hU: "neighborhood_of x X TX U" and hfU: "f ` U \<subseteq> V"
            using hloc hxX hnbhdV by blast
          have hU_TX: "U \<in> TX" and hxU: "x \<in> U"
            using hU unfolding neighborhood_of_def by blast+
          have hUX_open: "U \<inter> X \<in> TX"
            by (rule topology_inter2[OF hTX hU_TX X_open])
          have hUsubS: "U \<inter> X \<subseteq> S"
          proof (rule subsetI)
            fix u assume hu: "u \<in> U \<inter> X"
            have huU: "u \<in> U" and huX: "u \<in> X" using hu by blast+
            have "f u \<in> V" using hfU huU by blast
            thus "u \<in> S" using huX unfolding S_def by simp
          qed
          have hxUX: "x \<in> U \<inter> X" using hxU hxX by blast
          have hUX_mem: "U \<inter> X \<in> {W. W \<in> TX \<and> W \<subseteq> S}"
            apply (rule CollectI)
            apply (intro conjI)
             apply (rule hUX_open)
            apply (rule hUsubS)
            done
          show "x \<in> \<Union>{U. U \<in> TX \<and> U \<subseteq> S}"
            by (rule UnionI[OF hUX_mem hxUX])
        qed
      qed

      have hOpen: "\<Union>{U. U \<in> TX \<and> U \<subseteq> S} \<in> TX"
        by (rule union_TX[rule_format, OF hSsub])

      show "{x \<in> X. f x \<in> V} \<in> TX"
      proof -
        have hUnion': "S = \<Union>{U. U \<in> TX \<and> U \<subseteq> S}"
          by (rule sym[OF hUnion])
        have hSopen: "S \<in> TX"
          apply (subst hUnion')
          apply (rule hOpen)
          done
        show "{x \<in> X. f x \<in> V} \<in> TX"
          using hSopen by (simp add: S_def)
      qed
    qed
    show "top1_continuous_map_on X TX Y TY f"
      unfolding top1_continuous_map_on_def
      by (intro conjI hmap, rule hpre)
  qed
qed

(** from \S18 Theorem 18.2 [top1.tex:1089] **)
(** LATEX VERSION: "Rules for constructing continuous functions." **)
theorem Theorem_18_2:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hTZ: "is_topology_on Z TZ"
  shows const_fun:
    "(\<forall>y0\<in>Y. top1_continuous_map_on X TX Y TY (\<lambda>x. y0))"
    and inclusion:
    "(\<forall>A. A \<subseteq> X \<longrightarrow> top1_continuous_map_on A (subspace_topology X TX A) X TX id)"
    and composites:
    "(\<forall>f g. top1_continuous_map_on X TX Y TY f \<and> top1_continuous_map_on Y TY Z TZ g
           \<longrightarrow> top1_continuous_map_on X TX Z TZ (g \<circ> f))"
    and restrict_domain:
    "(\<forall>A f. top1_continuous_map_on X TX Y TY f \<and> A \<subseteq> X
           \<longrightarrow> top1_continuous_map_on A (subspace_topology X TX A) Y TY f)"
    and restrict_range:
    "(\<forall>W f. top1_continuous_map_on X TX Y TY f \<and> W \<subseteq> Y \<and> f ` X \<subseteq> W
           \<longrightarrow> top1_continuous_map_on X TX W (subspace_topology Y TY W) f)"
    and expand_range:
    "(\<forall>W f. top1_continuous_map_on X TX Y TY f \<and> Y \<subseteq> W \<and> TY = subspace_topology W TZ Y
           \<longrightarrow> top1_continuous_map_on X TX W TZ f)"
    and local_form:
    "(\<forall>Uc f. (\<Union>Uc = X) \<and> (\<forall>U\<in>Uc. U \<in> TX \<and> top1_continuous_map_on U (subspace_topology X TX U) Y TY f)
           \<longrightarrow> top1_continuous_map_on X TX Y TY f)"
proof -
  have empty_TX: "{} \<in> TX"
    by (rule conjunct1[OF hTX[unfolded is_topology_on_def]])
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])

  show const_fun:
    "(\<forall>y0\<in>Y. top1_continuous_map_on X TX Y TY (\<lambda>x. y0))"
  proof (intro ballI)
    fix y0 assume hy0: "y0 \<in> Y"
    show "top1_continuous_map_on X TX Y TY (\<lambda>x. y0)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>x\<in>X. (\<lambda>x. y0) x \<in> Y" using hy0 by simp
      show "\<forall>V\<in>TY. {x \<in> X. (\<lambda>x. y0) x \<in> V} \<in> TX"
      proof (intro ballI)
        fix V assume hV: "V \<in> TY"
        have hset: "{x \<in> X. (\<lambda>x. y0) x \<in> V} = (if y0 \<in> V then X else {})"
        proof (rule set_eqI)
          fix x
          show "x \<in> {x \<in> X. (\<lambda>x. y0) x \<in> V} \<longleftrightarrow> x \<in> (if y0 \<in> V then X else {})"
          proof (cases "y0 \<in> V")
            case True
            then show ?thesis by simp
          next
            case False
            then show ?thesis by simp
          qed
        qed
        show "{x \<in> X. (\<lambda>x. y0) x \<in> V} \<in> TX"
        proof (cases "y0 \<in> V")
          case True
          then show ?thesis using hset X_TX by simp
        next
          case False
          then show ?thesis using hset empty_TX by simp
        qed
      qed
    qed
  qed

  show inclusion:
    "(\<forall>A. A \<subseteq> X \<longrightarrow> top1_continuous_map_on A (subspace_topology X TX A) X TX id)"
  proof (intro allI impI)
    fix A assume hAX: "A \<subseteq> X"
    show "top1_continuous_map_on A (subspace_topology X TX A) X TX id"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>x\<in>A. id x \<in> X"
      proof (intro ballI)
        fix x assume hxA: "x \<in> A"
        have hxX: "x \<in> X" by (rule subsetD[OF hAX hxA])
        show "id x \<in> X" using hxX by simp
      qed
      show "\<forall>V\<in>TX. {x \<in> A. id x \<in> V} \<in> subspace_topology X TX A"
      proof (intro ballI)
        fix V assume hV: "V \<in> TX"
        have hEq: "{x \<in> A. id x \<in> V} = A \<inter> V"
        proof (rule set_eqI)
          fix x
          show "x \<in> {x \<in> A. id x \<in> V} \<longleftrightarrow> x \<in> A \<inter> V" by simp
        qed
        show "{x \<in> A. id x \<in> V} \<in> subspace_topology X TX A"
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[where x=V])
          apply (intro conjI)
           apply (rule hEq)
          apply (rule hV)
          done
      qed
    qed
  qed

  show composites:
    "(\<forall>f g. top1_continuous_map_on X TX Y TY f \<and> top1_continuous_map_on Y TY Z TZ g
           \<longrightarrow> top1_continuous_map_on X TX Z TZ (g \<circ> f))"
  proof (intro allI impI)
    fix f g
    assume hfg: "top1_continuous_map_on X TX Y TY f \<and> top1_continuous_map_on Y TY Z TZ g"
    have hf: "top1_continuous_map_on X TX Y TY f" and hg: "top1_continuous_map_on Y TY Z TZ g"
      using hfg by blast+
    show "top1_continuous_map_on X TX Z TZ (g \<circ> f)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      have hfY: "\<forall>x\<in>X. f x \<in> Y" using hf unfolding top1_continuous_map_on_def by blast
      have hgZ: "\<forall>y\<in>Y. g y \<in> Z" using hg unfolding top1_continuous_map_on_def by blast
      show "\<forall>x\<in>X. (g \<circ> f) x \<in> Z" using hfY hgZ by simp
      show "\<forall>W\<in>TZ. {x \<in> X. (g \<circ> f) x \<in> W} \<in> TX"
      proof (intro ballI)
        fix W assume hW: "W \<in> TZ"
        have hgW: "{y \<in> Y. g y \<in> W} \<in> TY"
          using hg hW unfolding top1_continuous_map_on_def by blast
        have hfW: "{x \<in> X. f x \<in> {y \<in> Y. g y \<in> W}} \<in> TX"
          using hf hgW unfolding top1_continuous_map_on_def by blast
        have hEq: "{x \<in> X. (g \<circ> f) x \<in> W} = {x \<in> X. f x \<in> {y \<in> Y. g y \<in> W}}"
        proof (rule set_eqI)
          fix x
          show "x \<in> {x \<in> X. (g \<circ> f) x \<in> W} \<longleftrightarrow> x \<in> {x \<in> X. f x \<in> {y \<in> Y. g y \<in> W}}"
          proof
            assume hx: "x \<in> {x \<in> X. (g \<circ> f) x \<in> W}"
            have hx_conj: "x \<in> X \<and> g (f x) \<in> W"
              using hx by simp
            have hxX: "x \<in> X"
              using hx_conj by (rule conjunct1)
            have hgfx: "g (f x) \<in> W"
              using hx_conj by (rule conjunct2)
            have hfxY: "f x \<in> Y" using hfY hxX by blast
            have "f x \<in> {y \<in> Y. g y \<in> W}" using hfxY hgfx by blast
            thus "x \<in> {x \<in> X. f x \<in> {y \<in> Y. g y \<in> W}}" using hxX by blast
          next
            assume hx: "x \<in> {x \<in> X. f x \<in> {y \<in> Y. g y \<in> W}}"
            have hxX: "x \<in> X" and hfx: "f x \<in> {y \<in> Y. g y \<in> W}" using hx by blast+
            have hgfx: "g (f x) \<in> W" using hfx by blast
            show "x \<in> {x \<in> X. (g \<circ> f) x \<in> W}" using hxX hgfx by simp
          qed
        qed
        show "{x \<in> X. (g \<circ> f) x \<in> W} \<in> TX"
          using hfW hEq by simp
      qed
    qed
  qed

  show restrict_domain:
    "(\<forall>A f. top1_continuous_map_on X TX Y TY f \<and> A \<subseteq> X
           \<longrightarrow> top1_continuous_map_on A (subspace_topology X TX A) Y TY f)"
  proof (intro allI impI)
    fix A f
    assume hAf: "top1_continuous_map_on X TX Y TY f \<and> A \<subseteq> X"
    have hf: "top1_continuous_map_on X TX Y TY f" and hAX: "A \<subseteq> X"
      using hAf by blast+
    show "top1_continuous_map_on A (subspace_topology X TX A) Y TY f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      have hfY: "\<forall>x\<in>X. f x \<in> Y" using hf unfolding top1_continuous_map_on_def by blast
      show "\<forall>x\<in>A. f x \<in> Y" using hfY hAX by blast
      show "\<forall>V\<in>TY. {x \<in> A. f x \<in> V} \<in> subspace_topology X TX A"
      proof (intro ballI)
        fix V assume hV: "V \<in> TY"
        have hOpen: "{x \<in> X. f x \<in> V} \<in> TX"
          using hf hV unfolding top1_continuous_map_on_def by blast
        have hEq: "{x \<in> A. f x \<in> V} = A \<inter> {x \<in> X. f x \<in> V}"
          using hAX by blast
        show "{x \<in> A. f x \<in> V} \<in> subspace_topology X TX A"
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[where x="{x \<in> X. f x \<in> V}"])
          apply (intro conjI)
           apply (simp only: hEq Int_assoc Int_commute Int_left_commute)
          apply (rule hOpen)
          done
      qed
    qed
  qed

  show restrict_range:
    "(\<forall>W f. top1_continuous_map_on X TX Y TY f \<and> W \<subseteq> Y \<and> f ` X \<subseteq> W
           \<longrightarrow> top1_continuous_map_on X TX W (subspace_topology Y TY W) f)"
  proof (intro allI impI)
    fix W f
    assume hWf: "top1_continuous_map_on X TX Y TY f \<and> W \<subseteq> Y \<and> f ` X \<subseteq> W"
    have hf: "top1_continuous_map_on X TX Y TY f" and hWY: "W \<subseteq> Y" and hfWimg: "f ` X \<subseteq> W"
      using hWf by blast+
    have hfW: "\<forall>x\<in>X. f x \<in> W"
      using hfWimg by blast
    show "top1_continuous_map_on X TX W (subspace_topology Y TY W) f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>x\<in>X. f x \<in> W" using hfW .
      show "\<forall>V\<in>subspace_topology Y TY W. {x \<in> X. f x \<in> V} \<in> TX"
      proof (intro ballI)
        fix V assume hV: "V \<in> subspace_topology Y TY W"
        obtain U where hU: "U \<in> TY" and hVeq: "V = W \<inter> U"
          using hV unfolding subspace_topology_def by blast
        have hOpen: "{x \<in> X. f x \<in> U} \<in> TX"
          using hf hU unfolding top1_continuous_map_on_def by blast
        have hEq: "{x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> U}"
          unfolding hVeq
          using hfW by blast
        show "{x \<in> X. f x \<in> V} \<in> TX"
          using hOpen hEq by simp
      qed
    qed
  qed

  show expand_range:
    "(\<forall>W f. top1_continuous_map_on X TX Y TY f \<and> Y \<subseteq> W \<and> TY = subspace_topology W TZ Y
           \<longrightarrow> top1_continuous_map_on X TX W TZ f)"
  proof (intro allI impI)
    fix W f
    assume hWf: "top1_continuous_map_on X TX Y TY f \<and> Y \<subseteq> W \<and> TY = subspace_topology W TZ Y"
    have hf: "top1_continuous_map_on X TX Y TY f" and hYW: "Y \<subseteq> W" and hTYeq: "TY = subspace_topology W TZ Y"
      using hWf by blast+
    have hfY: "\<forall>x\<in>X. f x \<in> Y"
      using hf unfolding top1_continuous_map_on_def by blast
    show "top1_continuous_map_on X TX W TZ f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>x\<in>X. f x \<in> W" using hfY hYW by blast
      show "\<forall>V\<in>TZ. {x \<in> X. f x \<in> V} \<in> TX"
      proof (intro ballI)
        fix V assume hV: "V \<in> TZ"
        have hVY: "Y \<inter> V \<in> TY"
          unfolding hTYeq subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[where x=V])
          apply (intro conjI)
           apply (rule refl)
          apply (rule hV)
          done
        have hOpen: "{x \<in> X. f x \<in> (Y \<inter> V)} \<in> TX"
          using hf hVY unfolding top1_continuous_map_on_def by blast
        have hEq: "{x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> (Y \<inter> V)}"
          using hfY by blast
        show "{x \<in> X. f x \<in> V} \<in> TX" using hOpen hEq by simp
      qed
    qed
  qed

  show local_form:
    "(\<forall>Uc f. (\<Union>Uc = X) \<and> (\<forall>U\<in>Uc. U \<in> TX \<and> top1_continuous_map_on U (subspace_topology X TX U) Y TY f)
           \<longrightarrow> top1_continuous_map_on X TX Y TY f)"
  proof (intro allI impI)
    fix Uc f
    assume hUc: "(\<Union>Uc = X) \<and> (\<forall>U\<in>Uc. U \<in> TX \<and> top1_continuous_map_on U (subspace_topology X TX U) Y TY f)"
    have hUX: "\<Union>Uc = X" and hall: "\<forall>U\<in>Uc. U \<in> TX \<and> top1_continuous_map_on U (subspace_topology X TX U) Y TY f"
      using hUc by blast+

    have hfY: "\<forall>x\<in>X. f x \<in> Y"
    proof (rule ballI)
      fix x assume hxX: "x \<in> X"
      obtain U where hU: "U \<in> Uc" and hxU: "x \<in> U"
        using hxX hUX by blast
      have hcontU: "top1_continuous_map_on U (subspace_topology X TX U) Y TY f"
        using hall hU by blast
      have hUrange: "\<forall>u\<in>U. f u \<in> Y"
        using hcontU unfolding top1_continuous_map_on_def by blast
      show "f x \<in> Y" using hUrange hxU by blast
    qed

    show "top1_continuous_map_on X TX Y TY f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>x\<in>X. f x \<in> Y" using hfY .
      show "\<forall>V\<in>TY. {x \<in> X. f x \<in> V} \<in> TX"
      proof (intro ballI)
        fix V assume hV: "V \<in> TY"
        define S where "S = {{x \<in> U. f x \<in> V} | U. U \<in> Uc}"

        have hSsub: "S \<subseteq> TX"
        proof (rule subsetI)
          fix W assume hW: "W \<in> S"
          obtain U where hUUc: "U \<in> Uc" and hWeq: "W = {x \<in> U. f x \<in> V}"
            using hW unfolding S_def by blast
          have hUopen: "U \<in> TX" and hcontU: "top1_continuous_map_on U (subspace_topology X TX U) Y TY f"
            using hall hUUc by blast+
          have hpre: "{x \<in> U. f x \<in> V} \<in> subspace_topology X TX U"
            using hcontU hV unfolding top1_continuous_map_on_def by blast
          obtain oset where hoset: "oset \<in> TX" and hpre_eq: "{x \<in> U. f x \<in> V} = U \<inter> oset"
            using hpre unfolding subspace_topology_def by blast
          have hUo: "U \<inter> oset \<in> TX"
            by (rule topology_inter2[OF hTX hUopen hoset])
          show "W \<in> TX"
            using hWeq hpre_eq hUo by simp
        qed

        have hUnionS: "\<Union>S = {x \<in> X. f x \<in> V}"
        proof (rule set_eqI)
          fix x
          show "x \<in> \<Union>S \<longleftrightarrow> x \<in> {x \<in> X. f x \<in> V}"
          proof (rule iffI)
            assume hx: "x \<in> \<Union>S"
            obtain W where hW: "W \<in> S" and hxW: "x \<in> W" using hx by blast
            obtain U where hUUc: "U \<in> Uc" and hWeq: "W = {x \<in> U. f x \<in> V}"
              using hW unfolding S_def by blast
            have hxU: "x \<in> U" and hfx: "f x \<in> V" using hxW unfolding hWeq by blast+
            have hxX: "x \<in> X" using hxU hUX hUUc by blast
            show "x \<in> {x \<in> X. f x \<in> V}" using hxX hfx by blast
          next
            assume hx: "x \<in> {x \<in> X. f x \<in> V}"
            have hxX: "x \<in> X" and hfx: "f x \<in> V" using hx by blast+
            obtain U where hUUc: "U \<in> Uc" and hxU: "x \<in> U"
              using hxX hUX by blast
            have hxW: "x \<in> {x \<in> U. f x \<in> V}" using hxU hfx by blast
            have "{x \<in> U. f x \<in> V} \<in> S" unfolding S_def using hUUc by blast
            thus "x \<in> \<Union>S" using hxW by blast
          qed
        qed

        have hOpen: "\<Union>S \<in> TX"
          by (rule union_TX[rule_format, OF hSsub])

        show "{x \<in> X. f x \<in> V} \<in> TX"
          using hOpen hUnionS by simp
      qed
    qed
  qed
qed

(** from \S18 Theorem 18.3 [top1.tex:1127] **)
(** LATEX VERSION: "Pasting lemma." **)
theorem Theorem_18_3:
  fixes f g :: "'a \<Rightarrow> 'b"
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hA: "closedin_on X TX A"
  assumes hB: "closedin_on X TX B"
  assumes hX: "X = A \<union> B"
  assumes hf: "top1_continuous_map_on A (subspace_topology X TX A) Y TY f"
  assumes hg: "top1_continuous_map_on B (subspace_topology X TX B) Y TY g"
  assumes hagree: "\<forall>x\<in>(A \<inter> B). f x = g x"
  defines "h \<equiv> (\<lambda>x. if x \<in> A then f x else g x)"
  shows "top1_continuous_map_on X TX Y TY h"
proof -
  have hAX: "A \<subseteq> X"
    by (rule closedin_sub[OF hA])
  have hBX: "B \<subseteq> X"
    by (rule closedin_sub[OF hB])

  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])

  have closed_inter2:
    "\<And>C D. closedin_on X TX C \<Longrightarrow> closedin_on X TX D \<Longrightarrow> closedin_on X TX (C \<inter> D)"
  proof -
    fix C D
    assume hC: "closedin_on X TX C"
    assume hD: "closedin_on X TX D"
    have hCsub: "C \<subseteq> X"
      by (rule closedin_sub[OF hC])
    have hDsub: "D \<subseteq> X"
      by (rule closedin_sub[OF hD])
    have hXmC: "X - C \<in> TX"
      by (rule closedin_diff_open[OF hC])
    have hXmD: "X - D \<in> TX"
      by (rule closedin_diff_open[OF hD])
    have hUnion: "(X - C) \<union> (X - D) \<in> TX"
    proof -
      have hUD: "{X - C, X - D} \<subseteq> TX"
        using hXmC hXmD by blast
      have hUnion_imp: "{X - C, X - D} \<subseteq> TX \<longrightarrow> \<Union>{X - C, X - D} \<in> TX"
        by (rule spec[where x="{X - C, X - D}", OF union_TX])
      have "\<Union>{X - C, X - D} \<in> TX"
        by (rule mp[OF hUnion_imp hUD])
      thus ?thesis by simp
    qed
    have hEq: "X - (C \<inter> D) = (X - C) \<union> (X - D)"
      by blast
    have hsub: "C \<inter> D \<subseteq> X"
      using hCsub hDsub by blast
    show "closedin_on X TX (C \<inter> D)"
      by (rule closedin_intro[OF hsub], simp add: hEq hUnion)
  qed

  have map_f: "\<forall>x\<in>A. f x \<in> Y"
    using hf unfolding top1_continuous_map_on_def by blast
  have map_g: "\<forall>x\<in>B. g x \<in> Y"
    using hg unfolding top1_continuous_map_on_def by blast

  have map_h: "\<forall>x\<in>X. h x \<in> Y"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hx: "x \<in> A \<or> x \<in> B"
      using hxX hX by blast
    show "h x \<in> Y"
    proof (cases "x \<in> A")
      case True
      have "f x \<in> Y" using map_f True by blast
      thus ?thesis unfolding h_def using True by simp
    next
      case False
      have hxB: "x \<in> B" using hx False by blast
      have "g x \<in> Y" using map_g hxB by blast
      thus ?thesis unfolding h_def using False by simp
    qed
  qed

  have closed_preimage_h:
    "\<forall>C. closedin_on Y TY C \<longrightarrow> closedin_on X TX {x \<in> X. h x \<in> C}"
  proof (intro allI impI)
    fix C
    assume hC: "closedin_on Y TY C"
    have hYmC: "Y - C \<in> TY"
      by (rule closedin_diff_open[OF hC])

    define PA where "PA = {x \<in> A. f x \<in> C}"
    define PB where "PB = {x \<in> B. g x \<in> C}"

    have hPA_closed_A: "closedin_on A (subspace_topology X TX A) PA"
    proof -
      have hpre_open: "{x \<in> A. f x \<in> Y - C} \<in> subspace_topology X TX A"
        using hf hYmC unfolding top1_continuous_map_on_def by blast
      have hcomp: "A - PA = {x \<in> A. f x \<in> Y - C}"
      proof (rule set_eqI)
        fix x
        show "x \<in> A - PA \<longleftrightarrow> x \<in> {x \<in> A. f x \<in> Y - C}"
        proof
          assume hx: "x \<in> A - PA"
          have hxA: "x \<in> A" and hxPA: "x \<notin> PA" using hx by blast+
          have hfxY: "f x \<in> Y" using map_f hxA by blast
          have hfxC: "f x \<notin> C"
            using hxA hxPA unfolding PA_def by simp
          have "f x \<in> Y - C" using hfxY hfxC by blast
          thus "x \<in> {x \<in> A. f x \<in> Y - C}" using hxA by simp
        next
          assume hx: "x \<in> {x \<in> A. f x \<in> Y - C}"
          have hxA: "x \<in> A" and hfx: "f x \<in> Y - C" using hx by blast+
          have hfxC: "f x \<notin> C" using hfx by blast
          have "x \<notin> PA" unfolding PA_def using hxA hfxC by simp
          thus "x \<in> A - PA" using hxA by blast
        qed
      qed
      have hPA_sub: "PA \<subseteq> A"
        unfolding PA_def by blast
      have "A - PA \<in> subspace_topology X TX A"
        using hpre_open hcomp by simp
      thus ?thesis
        by (rule closedin_intro[OF hPA_sub])
    qed

    have hPB_closed_B: "closedin_on B (subspace_topology X TX B) PB"
    proof -
      have hpre_open: "{x \<in> B. g x \<in> Y - C} \<in> subspace_topology X TX B"
        using hg hYmC unfolding top1_continuous_map_on_def by blast
      have hcomp: "B - PB = {x \<in> B. g x \<in> Y - C}"
      proof (rule set_eqI)
        fix x
        show "x \<in> B - PB \<longleftrightarrow> x \<in> {x \<in> B. g x \<in> Y - C}"
        proof
          assume hx: "x \<in> B - PB"
          have hxB: "x \<in> B" and hxPB: "x \<notin> PB" using hx by blast+
          have hgxY: "g x \<in> Y" using map_g hxB by blast
          have hgxC: "g x \<notin> C"
            using hxB hxPB unfolding PB_def by simp
          have "g x \<in> Y - C" using hgxY hgxC by blast
          thus "x \<in> {x \<in> B. g x \<in> Y - C}" using hxB by simp
        next
          assume hx: "x \<in> {x \<in> B. g x \<in> Y - C}"
          have hxB: "x \<in> B" and hgx: "g x \<in> Y - C" using hx by blast+
          have hgxC: "g x \<notin> C" using hgx by blast
          have "x \<notin> PB" unfolding PB_def using hxB hgxC by simp
          thus "x \<in> B - PB" using hxB by blast
        qed
      qed
      have hPB_sub: "PB \<subseteq> B"
        unfolding PB_def by blast
      have "B - PB \<in> subspace_topology X TX B"
        using hpre_open hcomp by simp
      thus ?thesis
        by (rule closedin_intro[OF hPB_sub])
    qed

    have hPA_closed_X: "closedin_on X TX PA"
    proof -
      have hPA_ex: "\<exists>D. closedin_on X TX D \<and> PA = D \<inter> A"
        by (rule iffD1[OF Theorem_17_2[OF hTX hAX] hPA_closed_A])
      then obtain D where hD: "closedin_on X TX D" and hPA: "PA = D \<inter> A"
        by blast
      have "closedin_on X TX (D \<inter> A)"
        by (rule closed_inter2[OF hD hA])
      thus ?thesis using hPA by simp
    qed

    have hPB_closed_X: "closedin_on X TX PB"
    proof -
      have hPB_ex: "\<exists>D. closedin_on X TX D \<and> PB = D \<inter> B"
        by (rule iffD1[OF Theorem_17_2[OF hTX hBX] hPB_closed_B])
      then obtain D where hD: "closedin_on X TX D" and hPB: "PB = D \<inter> B"
        by blast
      have "closedin_on X TX (D \<inter> B)"
        by (rule closed_inter2[OF hD hB])
      thus ?thesis using hPB by simp
    qed

    have hPh_eq: "{x \<in> X. h x \<in> C} = PA \<union> PB"
    proof (rule set_eqI)
      fix x
      show "x \<in> {x \<in> X. h x \<in> C} \<longleftrightarrow> x \<in> PA \<union> PB"
      proof
        assume hx: "x \<in> {x \<in> X. h x \<in> C}"
        have hxX: "x \<in> X" and hhx: "h x \<in> C" using hx by blast+
        have hxAB: "x \<in> A \<or> x \<in> B" using hxX hX by blast
        show "x \<in> PA \<union> PB"
        proof (cases "x \<in> A")
          case True
          have "f x \<in> C" using hhx unfolding h_def using True by simp
          hence "x \<in> PA" unfolding PA_def using True by simp
          thus ?thesis by blast
        next
          case False
          have hxB: "x \<in> B" using hxAB False by blast
          have "g x \<in> C" using hhx unfolding h_def using False by simp
          hence "x \<in> PB" unfolding PB_def using hxB by simp
          thus ?thesis by blast
        qed
      next
        assume hx: "x \<in> PA \<union> PB"
        show "x \<in> {x \<in> X. h x \<in> C}"
        proof (cases "x \<in> PA")
          case True
          have hxA: "x \<in> A" and hfxC: "f x \<in> C"
            using True unfolding PA_def by blast+
          have hxX: "x \<in> X" using hAX hxA by blast
          have "h x = f x" unfolding h_def using hxA by simp
          thus ?thesis using hxX hfxC by simp
        next
          case False
          have hxPB: "x \<in> PB" using hx False by blast
          have hxB: "x \<in> B" and hgxC: "g x \<in> C"
            using hxPB unfolding PB_def by blast+
          have hxX: "x \<in> X" using hBX hxB by blast
          show ?thesis
          proof (cases "x \<in> A")
            case True
            have hxAB: "x \<in> A \<inter> B" using True hxB by blast
            have "f x = g x" using hagree hxAB by blast
            hence "f x \<in> C" using hgxC by simp
            moreover have "h x = f x" unfolding h_def using True by simp
            ultimately show ?thesis using hxX by simp
          next
            case FalseA: False
            have "h x = g x" unfolding h_def using FalseA by simp
            thus ?thesis using hxX hgxC by simp
          qed
        qed
      qed
    qed

    have hUnion_closed: "closedin_on X TX (PA \<union> PB)"
    proof -
      have hfin: "finite {PA, PB}" by simp
      have hall: "\<forall>S\<in>{PA, PB}. closedin_on X TX S"
        using hPA_closed_X hPB_closed_X by simp
      have "closedin_on X TX (\<Union>{PA, PB})"
        by (rule closedin_Union_finite[OF hTX hfin hall])
      thus ?thesis by simp
    qed

    show "closedin_on X TX {x \<in> X. h x \<in> C}"
      using hUnion_closed hPh_eq by simp
  qed

  have cont_closed_h:
    "top1_continuous_map_on X TX Y TY h \<longleftrightarrow>
       ((\<forall>x\<in>X. h x \<in> Y) \<and>
        (\<forall>C. closedin_on Y TY C \<longrightarrow> closedin_on X TX {x \<in> X. h x \<in> C}))"
    by (rule Theorem_18_1(2)[OF hTX hTY])

  show ?thesis
    by (rule iffD2[OF cont_closed_h], intro conjI, rule map_h, rule closed_preimage_h)
qed

(** from \S18 Theorem 18.4 [top1.tex:1167] **)
(** LATEX VERSION: "Map into a product is continuous iff both components are continuous." **)
theorem Theorem_18_4:
  fixes f :: "'a \<Rightarrow> ('b \<times> 'c)"
  assumes hTA: "is_topology_on A TA"
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  shows
    "top1_continuous_map_on A TA (X \<times> Y) (product_topology_on TX TY) f
     \<longleftrightarrow>
       (top1_continuous_map_on A TA X TX (pi1 \<circ> f)
        \<and> top1_continuous_map_on A TA Y TY (pi2 \<circ> f))"
proof (rule iffI)
  let ?TP = "product_topology_on TX TY"

  assume hf: "top1_continuous_map_on A TA (X \<times> Y) ?TP f"
  have hf_range: "\<forall>a\<in>A. f a \<in> X \<times> Y"
    using hf unfolding top1_continuous_map_on_def by blast
  have hf_pre: "\<forall>W\<in>?TP. {a \<in> A. f a \<in> W} \<in> TA"
    using hf unfolding top1_continuous_map_on_def by blast

  have hX_open: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])
  have hY_open: "Y \<in> TY"
    by (rule conjunct1[OF conjunct2[OF hTY[unfolded is_topology_on_def]]])

  have basis_mem_open:
    "\<forall>b\<in>product_basis TX TY. b \<in> ?TP"
  proof (intro ballI)
    fix b assume hb: "b \<in> product_basis TX TY"
    show "b \<in> ?TP"
      unfolding product_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> (UNIV::('b \<times> 'c) set)" by simp
      show "\<forall>p\<in>b. \<exists>b'\<in>product_basis TX TY. p \<in> b' \<and> b' \<subseteq> b"
      proof (intro ballI)
        fix p assume hp: "p \<in> b"
        show "\<exists>b'\<in>product_basis TX TY. p \<in> b' \<and> b' \<subseteq> b"
          apply (rule bexI[where x=b])
           apply (intro conjI)
            apply (rule hp)
           apply (rule subset_refl)
          apply (rule hb)
          done
      qed
    qed
  qed

  have hpi1: "top1_continuous_map_on A TA X TX (pi1 \<circ> f)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>a\<in>A. (pi1 \<circ> f) a \<in> X"
    proof (intro ballI)
      fix a assume haA: "a \<in> A"
      have hfa: "f a \<in> X \<times> Y" using hf_range haA by blast
      have hfst: "fst (f a) \<in> X" using hfa by (simp add: mem_Times_iff)
      show "(pi1 \<circ> f) a \<in> X" using hfst unfolding pi1_def by simp
    qed
    show "\<forall>U\<in>TX. {a \<in> A. (pi1 \<circ> f) a \<in> U} \<in> TA"
    proof (intro ballI)
      fix U assume hU: "U \<in> TX"
      have hUY: "U \<times> Y \<in> product_basis TX TY"
        unfolding product_basis_def using hU hY_open by blast
      have hUY_open: "U \<times> Y \<in> ?TP"
        using basis_mem_open hUY by blast
      have hpre: "{a \<in> A. f a \<in> U \<times> Y} \<in> TA"
        using hf_pre hUY_open by blast
      have hEq: "{a \<in> A. (pi1 \<circ> f) a \<in> U} = {a \<in> A. f a \<in> U \<times> Y}"
      proof (rule set_eqI)
        fix a
        show "a \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U} \<longleftrightarrow> a \<in> {a \<in> A. f a \<in> U \<times> Y}"
        proof
          assume ha: "a \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U}"
          have ha_conj: "a \<in> A \<and> pi1 (f a) \<in> U"
            using ha by simp
          have haA: "a \<in> A"
            using ha_conj by (rule conjunct1)
          have hfst: "pi1 (f a) \<in> U"
            using ha_conj by (rule conjunct2)
          have hfa: "f a \<in> X \<times> Y" using hf_range haA by blast
          have hfa_xy: "fst (f a) \<in> X \<and> snd (f a) \<in> Y"
            using hfa by (simp add: mem_Times_iff)
          have hsnd: "snd (f a) \<in> Y"
            by (rule conjunct2[OF hfa_xy])
          have "f a \<in> U \<times> Y"
            using hfst hsnd unfolding pi1_def by (simp add: mem_Times_iff)
          thus "a \<in> {a \<in> A. f a \<in> U \<times> Y}" using haA by blast
        next
          assume ha: "a \<in> {a \<in> A. f a \<in> U \<times> Y}"
          have haA: "a \<in> A" and hfa: "f a \<in> U \<times> Y" using ha by blast+
          have hfa_UY: "fst (f a) \<in> U \<and> snd (f a) \<in> Y"
            using hfa by (simp add: mem_Times_iff)
          have hfst: "fst (f a) \<in> U"
            by (rule conjunct1[OF hfa_UY])
          show "a \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U}"
            using haA hfst unfolding pi1_def by simp
        qed
      qed
      show "{a \<in> A. (pi1 \<circ> f) a \<in> U} \<in> TA" using hpre hEq by simp
    qed
  qed

  have hpi2: "top1_continuous_map_on A TA Y TY (pi2 \<circ> f)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>a\<in>A. (pi2 \<circ> f) a \<in> Y"
    proof (intro ballI)
      fix a assume haA: "a \<in> A"
      have hfa: "f a \<in> X \<times> Y" using hf_range haA by blast
      have hsnd: "snd (f a) \<in> Y" using hfa by (simp add: mem_Times_iff)
      show "(pi2 \<circ> f) a \<in> Y" using hsnd unfolding pi2_def by simp
    qed
    show "\<forall>V\<in>TY. {a \<in> A. (pi2 \<circ> f) a \<in> V} \<in> TA"
    proof (intro ballI)
      fix V assume hV: "V \<in> TY"
      have hXV: "X \<times> V \<in> product_basis TX TY"
        unfolding product_basis_def using hX_open hV by blast
      have hXV_open: "X \<times> V \<in> ?TP"
        using basis_mem_open hXV by blast
      have hpre: "{a \<in> A. f a \<in> X \<times> V} \<in> TA"
        using hf_pre hXV_open by blast
      have hEq: "{a \<in> A. (pi2 \<circ> f) a \<in> V} = {a \<in> A. f a \<in> X \<times> V}"
      proof (rule set_eqI)
        fix a
        show "a \<in> {a \<in> A. (pi2 \<circ> f) a \<in> V} \<longleftrightarrow> a \<in> {a \<in> A. f a \<in> X \<times> V}"
        proof
          assume ha: "a \<in> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
          have ha_conj: "a \<in> A \<and> pi2 (f a) \<in> V"
            using ha by simp
          have haA: "a \<in> A"
            using ha_conj by (rule conjunct1)
          have hsnd: "pi2 (f a) \<in> V"
            using ha_conj by (rule conjunct2)
          have hfa: "f a \<in> X \<times> Y" using hf_range haA by blast
          have hfa_xy: "fst (f a) \<in> X \<and> snd (f a) \<in> Y"
            using hfa by (simp add: mem_Times_iff)
          have hfst: "fst (f a) \<in> X"
            by (rule conjunct1[OF hfa_xy])
          have "f a \<in> X \<times> V"
            using hfst hsnd unfolding pi2_def by (simp add: mem_Times_iff)
          thus "a \<in> {a \<in> A. f a \<in> X \<times> V}" using haA by blast
        next
          assume ha: "a \<in> {a \<in> A. f a \<in> X \<times> V}"
          have haA: "a \<in> A" and hfa: "f a \<in> X \<times> V" using ha by blast+
          have hfa_XV: "fst (f a) \<in> X \<and> snd (f a) \<in> V"
            using hfa by (simp add: mem_Times_iff)
          have hsnd: "snd (f a) \<in> V"
            by (rule conjunct2[OF hfa_XV])
          show "a \<in> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
            using haA hsnd unfolding pi2_def by simp
        qed
      qed
      show "{a \<in> A. (pi2 \<circ> f) a \<in> V} \<in> TA" using hpre hEq by simp
    qed
  qed

  show "top1_continuous_map_on A TA X TX (pi1 \<circ> f) \<and> top1_continuous_map_on A TA Y TY (pi2 \<circ> f)"
  proof (intro conjI)
    show "top1_continuous_map_on A TA X TX (pi1 \<circ> f)" using hpi1 .
    show "top1_continuous_map_on A TA Y TY (pi2 \<circ> f)" using hpi2 .
  qed
next
  let ?TP = "product_topology_on TX TY"

  assume hcomp:
    "top1_continuous_map_on A TA X TX (pi1 \<circ> f) \<and> top1_continuous_map_on A TA Y TY (pi2 \<circ> f)"
  have hpi1: "top1_continuous_map_on A TA X TX (pi1 \<circ> f)"
    by (rule conjunct1[OF hcomp])
  have hpi2: "top1_continuous_map_on A TA Y TY (pi2 \<circ> f)"
    by (rule conjunct2[OF hcomp])

  have union_TA: "\<forall>U. U \<subseteq> TA \<longrightarrow> \<Union>U \<in> TA"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTA[unfolded is_topology_on_def]]]])

  have hrect_pre:
    "\<forall>b\<in>product_basis TX TY. {a \<in> A. f a \<in> b} \<in> TA"
  proof (intro ballI)
    fix b assume hb: "b \<in> product_basis TX TY"
    obtain U V where hU: "U \<in> TX" and hV: "V \<in> TY" and hbEq: "b = U \<times> V"
      using hb unfolding product_basis_def by blast
    have hpre1: "{a \<in> A. (pi1 \<circ> f) a \<in> U} \<in> TA"
      using hpi1 hU unfolding top1_continuous_map_on_def by blast
    have hpre2: "{a \<in> A. (pi2 \<circ> f) a \<in> V} \<in> TA"
      using hpi2 hV unfolding top1_continuous_map_on_def by blast

    have hEq: "{a \<in> A. f a \<in> b} = {a \<in> A. (pi1 \<circ> f) a \<in> U} \<inter> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
    proof (rule set_eqI)
      fix x
      show "x \<in> {a \<in> A. f a \<in> b} \<longleftrightarrow>
            x \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U} \<inter> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
        unfolding hbEq
	      proof
	        assume hx: "x \<in> {a \<in> A. f a \<in> U \<times> V}"
	        have hx_conj: "x \<in> A \<and> f x \<in> U \<times> V"
	          using hx by simp
	        have hxA: "x \<in> A"
	          using hx_conj by (rule conjunct1)
	        have hfx: "f x \<in> U \<times> V"
	          using hx_conj by (rule conjunct2)
	        have hfx_uv: "fst (f x) \<in> U \<and> snd (f x) \<in> V"
	          using hfx by (simp add: mem_Times_iff)
	        have hpi1: "pi1 (f x) \<in> U"
	          using hfx_uv unfolding pi1_def by simp
        have hpi2: "pi2 (f x) \<in> V"
          using hfx_uv unfolding pi2_def by simp
        have hx1: "x \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U}"
          using hxA hpi1 by (simp add: o_def)
        have hx2: "x \<in> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
          using hxA hpi2 by (simp add: o_def)
        show "x \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U} \<inter> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
          by (rule IntI[OF hx1 hx2])
      next
        assume hx: "x \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U} \<inter> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
        have hx1: "x \<in> {a \<in> A. (pi1 \<circ> f) a \<in> U}"
          by (rule IntD1[OF hx])
        have hx2: "x \<in> {a \<in> A. (pi2 \<circ> f) a \<in> V}"
          by (rule IntD2[OF hx])
        have hx1': "x \<in> A \<and> pi1 (f x) \<in> U"
          using hx1 by (simp add: o_def)
        have hxA: "x \<in> A"
          by (rule conjunct1[OF hx1'])
        have hpi1: "pi1 (f x) \<in> U"
          by (rule conjunct2[OF hx1'])
        have hx2': "x \<in> A \<and> pi2 (f x) \<in> V"
          using hx2 by (simp add: o_def)
        have hpi2: "pi2 (f x) \<in> V"
          by (rule conjunct2[OF hx2'])
        have hfx: "f x \<in> U \<times> V"
          using hpi1 hpi2 unfolding pi1_def pi2_def by (simp add: mem_Times_iff)
        show "x \<in> {a \<in> A. f a \<in> U \<times> V}"
          using hxA hfx by simp
      qed
    qed

    have hinter: "{a \<in> A. (pi1 \<circ> f) a \<in> U} \<inter> {a \<in> A. (pi2 \<circ> f) a \<in> V} \<in> TA"
      by (rule topology_inter2[OF hTA hpre1 hpre2])

    show "{a \<in> A. f a \<in> b} \<in> TA" using hinter hEq by simp
  qed

  show "top1_continuous_map_on A TA (X \<times> Y) ?TP f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    have hpi1_range: "\<forall>a\<in>A. (pi1 \<circ> f) a \<in> X"
      using hpi1 unfolding top1_continuous_map_on_def by blast
    have hpi2_range: "\<forall>a\<in>A. (pi2 \<circ> f) a \<in> Y"
      using hpi2 unfolding top1_continuous_map_on_def by blast
    show "\<forall>a\<in>A. f a \<in> X \<times> Y"
      using hpi1_range hpi2_range unfolding pi1_def pi2_def by (simp add: mem_Times_iff)

    show "\<forall>W\<in>?TP. {a \<in> A. f a \<in> W} \<in> TA"
      unfolding product_topology_on_def topology_generated_by_basis_def
    proof (intro ballI)
      fix W assume hW: "W \<in> {U. U \<subseteq> (UNIV::('b \<times> 'c) set) \<and>
           (\<forall>x\<in>U. \<exists>b\<in>product_basis TX TY. x \<in> b \<and> b \<subseteq> U)}"
      have hWcov: "\<forall>x\<in>W. \<exists>b\<in>product_basis TX TY. x \<in> b \<and> b \<subseteq> W"
        using hW by blast

      define S where "S = {{a \<in> A. f a \<in> b} | b. b \<in> product_basis TX TY \<and> b \<subseteq> W}"
      have hSsub: "S \<subseteq> TA"
      proof (rule subsetI)
        fix P assume hP: "P \<in> S"
        obtain b where hb: "b \<in> product_basis TX TY" and hbW: "b \<subseteq> W" and hPeq: "P = {a \<in> A. f a \<in> b}"
          using hP unfolding S_def by blast
        show "P \<in> TA" using hrect_pre hb hPeq by simp
      qed

      have hUnion: "\<Union>S = {a \<in> A. f a \<in> W}"
      proof (rule set_eqI)
        fix a
        show "a \<in> \<Union>S \<longleftrightarrow> a \<in> {a \<in> A. f a \<in> W}"
        proof
          assume ha: "a \<in> \<Union>S"
          obtain P where hP: "P \<in> S" and haP: "a \<in> P" using ha by blast
          obtain b where hb: "b \<in> product_basis TX TY" and hbW: "b \<subseteq> W" and hPeq: "P = {a \<in> A. f a \<in> b}"
            using hP unfolding S_def by blast
          have haA: "a \<in> A" and hfb: "f a \<in> b" using haP unfolding hPeq by blast+
          have "f a \<in> W" using hfb hbW by blast
          thus "a \<in> {a \<in> A. f a \<in> W}" using haA by blast
        next
          assume ha: "a \<in> {a \<in> A. f a \<in> W}"
          have haA: "a \<in> A" and hfW: "f a \<in> W" using ha by blast+
          obtain b where hb: "b \<in> product_basis TX TY" and hfb: "f a \<in> b" and hbW: "b \<subseteq> W"
            using hWcov[rule_format, OF hfW] by blast
          have "{a \<in> A. f a \<in> b} \<in> S"
            unfolding S_def using hb hbW by blast
          moreover have "a \<in> {a \<in> A. f a \<in> b}" using haA hfb by blast
          ultimately show "a \<in> \<Union>S" by blast
        qed
      qed

      have hOpen: "\<Union>S \<in> TA" using union_TA hSsub by blast
      show "{a \<in> A. f a \<in> W} \<in> TA" using hOpen hUnion by simp
    qed
  qed
qed

lemma top1_continuous_pi1:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  shows "top1_continuous_map_on (X \<times> Y) (product_topology_on TX TY) X TX pi1"
proof -
  let ?TP = "product_topology_on TX TY"

  have hX: "X \<in> TX"
    using hTX unfolding is_topology_on_def by blast
  have hY: "Y \<in> TY"
    using hTY unfolding is_topology_on_def by blast

  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>p\<in>X \<times> Y. pi1 p \<in> X"
      unfolding pi1_def by auto
    show "\<forall>U\<in>TX. {p \<in> X \<times> Y. pi1 p \<in> U} \<in> ?TP"
    proof (intro ballI)
      fix U assume hU: "U \<in> TX"
      have hUX: "U \<inter> X \<in> TX"
        by (rule topology_inter2[OF hTX hU hX])
      have hrect: "(U \<inter> X) \<times> Y \<in> ?TP"
        by (rule product_rect_open[OF hUX hY])

      have hEq: "{p \<in> X \<times> Y. pi1 p \<in> U} = (U \<inter> X) \<times> Y"
      proof (rule set_eqI)
        fix p
        show "p \<in> {p \<in> X \<times> Y. pi1 p \<in> U} \<longleftrightarrow> p \<in> (U \<inter> X) \<times> Y"
          unfolding pi1_def by auto
      qed
      show "{p \<in> X \<times> Y. pi1 p \<in> U} \<in> ?TP"
        using hrect hEq by simp
    qed
  qed
qed

lemma top1_continuous_pi2:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  shows "top1_continuous_map_on (X \<times> Y) (product_topology_on TX TY) Y TY pi2"
proof -
  let ?TP = "product_topology_on TX TY"

  have hX: "X \<in> TX"
    using hTX unfolding is_topology_on_def by blast
  have hY: "Y \<in> TY"
    using hTY unfolding is_topology_on_def by blast

  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>p\<in>X \<times> Y. pi2 p \<in> Y"
      unfolding pi2_def by auto
    show "\<forall>V\<in>TY. {p \<in> X \<times> Y. pi2 p \<in> V} \<in> ?TP"
    proof (intro ballI)
      fix V assume hV: "V \<in> TY"
      have hVY: "V \<inter> Y \<in> TY"
        by (rule topology_inter2[OF hTY hV hY])
      have hrect: "X \<times> (V \<inter> Y) \<in> ?TP"
        by (rule product_rect_open[OF hX hVY])

      have hEq: "{p \<in> X \<times> Y. pi2 p \<in> V} = X \<times> (V \<inter> Y)"
      proof (rule set_eqI)
        fix p
        show "p \<in> {p \<in> X \<times> Y. pi2 p \<in> V} \<longleftrightarrow> p \<in> X \<times> (V \<inter> Y)"
          unfolding pi2_def by auto
      qed
      show "{p \<in> X \<times> Y. pi2 p \<in> V} \<in> ?TP"
        using hrect hEq by simp
    qed
  qed
qed

section \<open>\<S>19 The Product Topology (indexed products)\<close>

text \<open>
  The development so far includes a binary product topology on \<open>X \<times> Y\<close>.
  Section \<S>19 of \<open>top1.tex\<close> treats indexed products (box vs product topologies).

  In HOL, functions are total; to model a \<open>J\<close>-tuple (a function with domain exactly \<open>J\<close>)
  we use an extensional function space \<open>top1_PiE J X\<close>, i.e. functions that take values
  in \<open>X j\<close> on \<open>j \<in> J\<close> and equal \<open>undefined\<close> outside \<open>J\<close>. (Isabelle also provides
  a similar notion in \<open>HOL-Library.FuncSet\<close>; we keep this development self-contained.)
\<close>

definition top1_extensional :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a) set" where
  "top1_extensional I = {f. \<forall>i. i \<notin> I \<longrightarrow> f i = undefined}"

definition top1_Pi :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a) set" where
  "top1_Pi I X = {f. \<forall>i\<in>I. f i \<in> X i}"

definition top1_PiE :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a) set" where
  "top1_PiE I X = top1_Pi I X \<inter> top1_extensional I"

lemma top1_PiE_iff:
  "f \<in> top1_PiE I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i) \<and> (\<forall>i. i \<notin> I \<longrightarrow> f i = undefined)"
  unfolding top1_PiE_def top1_Pi_def top1_extensional_def by simp

definition top1_box_basis_on ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a set set) \<Rightarrow> ('i \<Rightarrow> 'a) set set"
  where
  "top1_box_basis_on I X T =
     { top1_PiE I U | U. (\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i) }"

definition top1_box_topology_on ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a set set) \<Rightarrow> ('i \<Rightarrow> 'a) set set"
  where
  "top1_box_topology_on I X T =
     topology_generated_by_basis (top1_PiE I X) (top1_box_basis_on I X T)"

definition top1_product_basis_on ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a set set) \<Rightarrow> ('i \<Rightarrow> 'a) set set"
  where
  "top1_product_basis_on I X T =
     { top1_PiE I U | U.
         (\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i)
         \<and> finite {i \<in> I. U i \<noteq> X i} }"

definition top1_product_topology_on ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> 'a set set) \<Rightarrow> ('i \<Rightarrow> 'a) set set"
  where
  "top1_product_topology_on I X T =
     topology_generated_by_basis (top1_PiE I X) (top1_product_basis_on I X T)"

lemma top1_PiE_mono:
  assumes hsub: "\<forall>i\<in>I. U i \<subseteq> V i"
  shows "top1_PiE I U \<subseteq> top1_PiE I V"
proof (rule subsetI)
  fix f assume hf: "f \<in> top1_PiE I U"
  have hfPi: "f \<in> top1_Pi I U" and hfext: "f \<in> top1_extensional I"
    using hf unfolding top1_PiE_def by blast+
  have hfV: "\<forall>i\<in>I. f i \<in> V i"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hfiU: "f i \<in> U i"
      using hfPi hi unfolding top1_Pi_def by blast
    show "f i \<in> V i"
      using hsub hi hfiU by blast
  qed
  have "f \<in> top1_Pi I V"
    unfolding top1_Pi_def using hfV by blast
  thus "f \<in> top1_PiE I V"
    unfolding top1_PiE_def using hfext by blast
qed

lemma top1_PiE_Int:
  "top1_PiE I U \<inter> top1_PiE I V = top1_PiE I (\<lambda>i. U i \<inter> V i)"
proof (rule set_eqI)
  fix f
  show "f \<in> top1_PiE I U \<inter> top1_PiE I V \<longleftrightarrow> f \<in> top1_PiE I (\<lambda>i. U i \<inter> V i)"
    unfolding top1_PiE_def top1_extensional_def top1_Pi_def by blast
qed

lemma top1_PiE_cong_on:
  assumes hUV: "\<forall>i\<in>I. U i = V i"
  shows "top1_PiE I U = top1_PiE I V"
proof (rule set_eqI)
  fix f
  have hmem: "(\<forall>i\<in>I. f i \<in> U i) \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> V i)"
  proof (rule iffI)
    assume h: "\<forall>i\<in>I. f i \<in> U i"
    show "\<forall>i\<in>I. f i \<in> V i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have "U i = V i"
        using hUV hi by blast
      thus "f i \<in> V i"
        using h[rule_format, OF hi] by simp
    qed
  next
    assume h: "\<forall>i\<in>I. f i \<in> V i"
    show "\<forall>i\<in>I. f i \<in> U i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have "U i = V i"
        using hUV hi by blast
      thus "f i \<in> U i"
        using h[rule_format, OF hi] by simp
    qed
  qed
  show "f \<in> top1_PiE I U \<longleftrightarrow> f \<in> top1_PiE I V"
    unfolding top1_PiE_iff using hmem by simp
qed

lemma top1_box_basis_is_basis_on:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  shows "is_basis_on (top1_PiE I X) (top1_box_basis_on I X T)"
proof (unfold is_basis_on_def, intro conjI)
  show "\<forall>b\<in>top1_box_basis_on I X T. b \<subseteq> top1_PiE I X"
  proof (intro ballI)
    fix b assume hb: "b \<in> top1_box_basis_on I X T"
    obtain U where hbU: "b = top1_PiE I U" and hU: "\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i"
      using hb unfolding top1_box_basis_on_def by blast
    have hsub: "\<forall>i\<in>I. U i \<subseteq> X i"
      using hU by blast
    have "top1_PiE I U \<subseteq> top1_PiE I X"
      by (rule top1_PiE_mono[OF hsub])
    thus "b \<subseteq> top1_PiE I X"
      using hbU by simp
  qed

  show "\<forall>x\<in>top1_PiE I X. \<exists>b\<in>top1_box_basis_on I X T. x \<in> b"
  proof (intro ballI)
    fix x assume hx: "x \<in> top1_PiE I X"
    have hX: "\<forall>i\<in>I. X i \<in> T i \<and> X i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have "X i \<in> T i"
        using hTop hi unfolding is_topology_on_def by blast
      thus "X i \<in> T i \<and> X i \<subseteq> X i"
        by simp
    qed
    have "top1_PiE I X \<in> top1_box_basis_on I X T"
      unfolding top1_box_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=X])
      apply (intro conjI)
       apply simp
      apply (rule hX)
      done
    thus "\<exists>b\<in>top1_box_basis_on I X T. x \<in> b"
      using hx by blast
  qed

  show "\<forall>b1\<in>top1_box_basis_on I X T.
         \<forall>b2\<in>top1_box_basis_on I X T.
           \<forall>x\<in>b1 \<inter> b2. \<exists>b3\<in>top1_box_basis_on I X T. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
  proof (intro ballI)
    fix b1 assume hb1: "b1 \<in> top1_box_basis_on I X T"
    fix b2 assume hb2: "b2 \<in> top1_box_basis_on I X T"
    fix x assume hx: "x \<in> b1 \<inter> b2"
    obtain U where hb1U: "b1 = top1_PiE I U" and hU: "\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i"
      using hb1 unfolding top1_box_basis_on_def by blast
    obtain V where hb2V: "b2 = top1_PiE I V" and hV: "\<forall>i\<in>I. V i \<in> T i \<and> V i \<subseteq> X i"
      using hb2 unfolding top1_box_basis_on_def by blast

    define W where "W = (\<lambda>i. U i \<inter> V i)"
    have hW: "\<forall>i\<in>I. W i \<in> T i \<and> W i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hTi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hUi: "U i \<in> T i" and hUsub: "U i \<subseteq> X i"
        using hU hi by blast+
      have hVi: "V i \<in> T i" and hVsub: "V i \<subseteq> X i"
        using hV hi by blast+
      have "U i \<inter> V i \<in> T i"
        by (rule topology_inter2[OF hTi hUi hVi])
      moreover have "U i \<inter> V i \<subseteq> X i"
        using hUsub hVsub by blast
      ultimately show "W i \<in> T i \<and> W i \<subseteq> X i"
        unfolding W_def by simp
    qed

    have hInt: "top1_PiE I W = b1 \<inter> b2"
      unfolding hb1U hb2V W_def using top1_PiE_Int[of I U V] by simp

    have hb3: "top1_PiE I W \<in> top1_box_basis_on I X T"
      unfolding top1_box_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=W])
      apply (intro conjI)
       apply simp
      apply (rule hW)
      done

    show "\<exists>b3\<in>top1_box_basis_on I X T. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
    proof -
      have hxW: "x \<in> top1_PiE I W"
        unfolding hInt by (rule hx)
      have hsubW: "top1_PiE I W \<subseteq> b1 \<inter> b2"
        unfolding hInt by simp
      show ?thesis
        apply (rule bexI[where x="top1_PiE I W"])
         apply (intro conjI)
          apply (rule hxW)
         apply (rule hsubW)
        apply (rule hb3)
        done
    qed
  qed
qed

lemma top1_box_topology_on_is_topology_on:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  shows "is_topology_on (top1_PiE I X) (top1_box_topology_on I X T)"
  unfolding top1_box_topology_on_def
  by (rule topology_generated_by_basis_is_topology_on[OF top1_box_basis_is_basis_on[OF hTop]])

lemma top1_product_basis_is_basis_on:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  shows "is_basis_on (top1_PiE I X) (top1_product_basis_on I X T)"
proof (unfold is_basis_on_def, intro conjI)
  show "\<forall>b\<in>top1_product_basis_on I X T. b \<subseteq> top1_PiE I X"
  proof (intro ballI)
    fix b assume hb: "b \<in> top1_product_basis_on I X T"
    obtain U where hbU: "b = top1_PiE I U"
      and hU: "(\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i)"
      using hb unfolding top1_product_basis_on_def by blast
    have hsub: "\<forall>i\<in>I. U i \<subseteq> X i"
      using hU by blast
    have "top1_PiE I U \<subseteq> top1_PiE I X"
      by (rule top1_PiE_mono[OF hsub])
    thus "b \<subseteq> top1_PiE I X"
      using hbU by simp
  qed

  show "\<forall>x\<in>top1_PiE I X. \<exists>b\<in>top1_product_basis_on I X T. x \<in> b"
  proof (intro ballI)
    fix x assume hx: "x \<in> top1_PiE I X"
    have hX: "\<forall>i\<in>I. X i \<in> T i \<and> X i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have "X i \<in> T i"
        using hTop hi unfolding is_topology_on_def by blast
      thus "X i \<in> T i \<and> X i \<subseteq> X i"
        by simp
    qed
    have hfin: "finite {i \<in> I. X i \<noteq> X i}"
      by simp
    have "top1_PiE I X \<in> top1_product_basis_on I X T"
      unfolding top1_product_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=X])
      apply (intro conjI)
       apply simp
      apply (rule hX)
      apply (rule hfin)
      done
    thus "\<exists>b\<in>top1_product_basis_on I X T. x \<in> b"
      using hx by blast
  qed

  show "\<forall>b1\<in>top1_product_basis_on I X T.
         \<forall>b2\<in>top1_product_basis_on I X T.
           \<forall>x\<in>b1 \<inter> b2. \<exists>b3\<in>top1_product_basis_on I X T. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
  proof (intro ballI)
    fix b1 assume hb1: "b1 \<in> top1_product_basis_on I X T"
    fix b2 assume hb2: "b2 \<in> top1_product_basis_on I X T"
    fix x assume hx: "x \<in> b1 \<inter> b2"
    obtain U where hb1U: "b1 = top1_PiE I U"
      and hU: "(\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i)"
      and hUfin: "finite {i \<in> I. U i \<noteq> X i}"
      using hb1 unfolding top1_product_basis_on_def by blast
    obtain V where hb2V: "b2 = top1_PiE I V"
      and hV: "(\<forall>i\<in>I. V i \<in> T i \<and> V i \<subseteq> X i)"
      and hVfin: "finite {i \<in> I. V i \<noteq> X i}"
      using hb2 unfolding top1_product_basis_on_def by blast

    define W where "W = (\<lambda>i. U i \<inter> V i)"
    have hW: "\<forall>i\<in>I. W i \<in> T i \<and> W i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hTi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hUi: "U i \<in> T i" and hUsub: "U i \<subseteq> X i"
        using hU hi by blast+
      have hVi: "V i \<in> T i" and hVsub: "V i \<subseteq> X i"
        using hV hi by blast+
      have "U i \<inter> V i \<in> T i"
        by (rule topology_inter2[OF hTi hUi hVi])
      moreover have "U i \<inter> V i \<subseteq> X i"
        using hUsub hVsub by blast
      ultimately show "W i \<in> T i \<and> W i \<subseteq> X i"
        unfolding W_def by simp
    qed

    have hWfin: "finite {i \<in> I. W i \<noteq> X i}"
    proof -
      have hsub:
        "{i \<in> I. W i \<noteq> X i} \<subseteq> {i \<in> I. U i \<noteq> X i} \<union> {i \<in> I. V i \<noteq> X i}"
      proof (rule subsetI)
        fix i assume hi: "i \<in> {i \<in> I. W i \<noteq> X i}"
        have hiI: "i \<in> I" and hneq: "W i \<noteq> X i"
          using hi by blast+
        have "U i \<noteq> X i \<or> V i \<noteq> X i"
        proof (rule ccontr)
          assume hnot: "\<not> (U i \<noteq> X i \<or> V i \<noteq> X i)"
          have hUeq: "U i = X i" and hVeq: "V i = X i"
            using hnot by blast+
          have "W i = X i"
            unfolding W_def using hUeq hVeq by simp
          thus False
            using hneq by blast
        qed
        thus "i \<in> {i \<in> I. U i \<noteq> X i} \<union> {i \<in> I. V i \<noteq> X i}"
          using hiI by blast
      qed
      have "finite ({i \<in> I. U i \<noteq> X i} \<union> {i \<in> I. V i \<noteq> X i})"
        using hUfin hVfin by blast
      thus ?thesis
        using finite_subset[OF hsub] by blast
    qed

    have hInt: "top1_PiE I W = b1 \<inter> b2"
      unfolding hb1U hb2V W_def using top1_PiE_Int[of I U V] by simp

    have hb3: "top1_PiE I W \<in> top1_product_basis_on I X T"
      unfolding top1_product_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=W])
      apply (rule conjI)
       apply simp
      apply (rule conjI)
       apply (rule hW)
      apply (rule hWfin)
      done

    show "\<exists>b3\<in>top1_product_basis_on I X T. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
    proof -
      have hxW: "x \<in> top1_PiE I W"
        unfolding hInt by (rule hx)
      have hsubW: "top1_PiE I W \<subseteq> b1 \<inter> b2"
        unfolding hInt by simp
      show ?thesis
        apply (rule bexI[where x="top1_PiE I W"])
         apply (intro conjI)
          apply (rule hxW)
         apply (rule hsubW)
        apply (rule hb3)
        done
    qed
  qed
qed

lemma top1_product_topology_on_is_topology_on:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  shows "is_topology_on (top1_PiE I X) (top1_product_topology_on I X T)"
  unfolding top1_product_topology_on_def
  by (rule topology_generated_by_basis_is_topology_on[OF top1_product_basis_is_basis_on[OF hTop]])

(** from \S19 Theorem 19.1 (Comparison of the box and product topologies) [top1.tex:1382] **)
theorem Theorem_19_1:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  shows "basis_for (top1_PiE I X) (top1_box_basis_on I X T) (top1_box_topology_on I X T)"
    and "basis_for (top1_PiE I X) (top1_product_basis_on I X T) (top1_product_topology_on I X T)"
proof -
  have hBoxBasis: "is_basis_on (top1_PiE I X) (top1_box_basis_on I X T)"
    by (rule top1_box_basis_is_basis_on[OF hTop])
  have hProdBasis: "is_basis_on (top1_PiE I X) (top1_product_basis_on I X T)"
    by (rule top1_product_basis_is_basis_on[OF hTop])

  show "basis_for (top1_PiE I X) (top1_box_basis_on I X T) (top1_box_topology_on I X T)"
    unfolding basis_for_def top1_box_topology_on_def
    using hBoxBasis by simp
  show "basis_for (top1_PiE I X) (top1_product_basis_on I X T) (top1_product_topology_on I X T)"
    unfolding basis_for_def top1_product_topology_on_def
    using hProdBasis by simp
qed

lemma top1_product_basis_eq_box_basis_if_finite:
  assumes hfinI: "finite I"
  shows "top1_product_basis_on I X T = top1_box_basis_on I X T"
proof (rule equalityI)
  show "top1_product_basis_on I X T \<subseteq> top1_box_basis_on I X T"
    unfolding top1_product_basis_on_def top1_box_basis_on_def by blast
  show "top1_box_basis_on I X T \<subseteq> top1_product_basis_on I X T"
  proof (rule subsetI)
    fix b assume hb: "b \<in> top1_box_basis_on I X T"
    obtain U where hbU: "b = top1_PiE I U" and hU: "\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i"
      using hb unfolding top1_box_basis_on_def by blast
    have hsub: "{i \<in> I. U i \<noteq> X i} \<subseteq> I"
      by blast
    have hfin: "finite {i \<in> I. U i \<noteq> X i}"
      by (rule finite_subset[OF hsub hfinI])
    show "b \<in> top1_product_basis_on I X T"
      unfolding top1_product_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      apply (rule conjI)
       apply (rule hbU)
      apply (rule conjI)
       apply (rule hU)
      apply (rule hfin)
      done
  qed
qed

lemma top1_product_topology_eq_box_topology_if_finite:
  assumes hfinI: "finite I"
  shows "top1_product_topology_on I X T = top1_box_topology_on I X T"
proof -
  have hbasis: "top1_product_basis_on I X T = top1_box_basis_on I X T"
    by (rule top1_product_basis_eq_box_basis_if_finite[OF hfinI])
  show ?thesis
    unfolding top1_product_topology_on_def top1_box_topology_on_def
    using hbasis by simp
qed

subsection \<open>Projections and continuity (\<S>19)\<close>

lemma top1_PiE_fun_eqI:
  assumes hf: "f \<in> top1_PiE I X"
  assumes hg: "g \<in> top1_PiE I X"
  assumes heq: "\<forall>i\<in>I. f i = g i"
  shows "f = g"
proof (rule ext)
  fix i
  show "f i = g i"
  proof (cases "i \<in> I")
    case True
    thus ?thesis
      using heq by blast
  next
    case False
    have hfext: "\<forall>j. j \<notin> I \<longrightarrow> f j = undefined"
      using hf unfolding top1_PiE_iff by blast
    have hgext: "\<forall>j. j \<notin> I \<longrightarrow> g j = undefined"
      using hg unfolding top1_PiE_iff by blast
    have "f i = undefined"
      using hfext False by blast
    moreover have "g i = undefined"
      using hgext False by blast
    ultimately show ?thesis
      by simp
  qed
qed

lemma top1_PiE_neq_imp_coord_neq:
  assumes hf: "f \<in> top1_PiE I X"
  assumes hg: "g \<in> top1_PiE I X"
  assumes hneq: "f \<noteq> g"
  shows "\<exists>i\<in>I. f i \<noteq> g i"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>i\<in>I. f i \<noteq> g i)"
  have heq: "\<forall>i\<in>I. f i = g i"
    using hno by blast
  have "f = g"
    by (rule top1_PiE_fun_eqI[OF hf hg heq])
  thus False
    using hneq by blast
qed

lemma top1_product_cylinder_in_basis:
  assumes hTop: "\<forall>j\<in>I. is_topology_on (X j) (T j)"
  assumes hi: "i \<in> I"
  assumes hU: "U \<in> T i"
  shows "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<in> top1_product_basis_on I X T"
proof -
  define W where "W = (\<lambda>j. if j = i then U \<inter> X i else X j)"
  have hW: "\<forall>j\<in>I. W j \<in> T j \<and> W j \<subseteq> X j"
  proof (intro ballI)
    fix j assume hj: "j \<in> I"
    have hTj: "is_topology_on (X j) (T j)"
      using hTop hj by blast
    have hXj: "X j \<in> T j"
      using hTj unfolding is_topology_on_def by blast
    show "W j \<in> T j \<and> W j \<subseteq> X j"
    proof (cases "j = i")
      case True
      have hTi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hUX: "U \<inter> X i \<in> T i"
        by (rule topology_inter2[OF hTi hU hXj[unfolded True]])
      have hTji: "T j = T i"
        using True by simp
      have hXji: "X j = X i"
        using True by simp
      have hWj: "W j = U \<inter> X i"
        unfolding W_def using True by simp
      show ?thesis
        unfolding hWj
        apply (intro conjI)
         apply (simp add: hTji hUX)
        apply (simp add: hXji)
        done
    next
      case False
      have hWj: "W j = X j"
        unfolding W_def using False by simp
      show ?thesis
        unfolding hWj using hXj by simp
    qed
  qed

  have hfin: "finite {j \<in> I. W j \<noteq> X j}"
  proof -
    have hsub: "{j \<in> I. W j \<noteq> X j} \<subseteq> {i}"
    proof (rule subsetI)
      fix j assume hj: "j \<in> {j \<in> I. W j \<noteq> X j}"
      have hneq: "W j \<noteq> X j"
        using hj by blast
      have "j = i"
      proof (rule ccontr)
        assume hji: "j \<noteq> i"
        have "W j = X j"
          unfolding W_def using hji by simp
        thus False
          using hneq by blast
      qed
      thus "j \<in> {i}"
        by simp
    qed
    show ?thesis
      by (rule finite_subset[OF hsub], simp)
  qed

  show ?thesis
    unfolding top1_product_basis_on_def
    apply (rule CollectI)
    apply (rule exI[where x=W])
    apply (intro conjI)
     apply (simp add: W_def)
    apply (rule hW)
    apply (rule hfin)
    done
qed

lemma top1_product_cylinder_eq:
  assumes hi: "i \<in> I"
  shows "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j)
         = {f \<in> top1_PiE I X. f i \<in> U}"
proof (rule set_eqI)
  fix f
  show "f \<in> top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<longleftrightarrow>
        f \<in> {f \<in> top1_PiE I X. f i \<in> U}"
  proof
    assume hf: "f \<in> top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j)"
    have hfX: "f \<in> top1_PiE I X"
    proof -
      have hsub: "\<forall>j\<in>I. (if j = i then U \<inter> X i else X j) \<subseteq> X j"
        by simp
      have "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<subseteq> top1_PiE I X"
        by (rule top1_PiE_mono[OF hsub])
      thus ?thesis
        using hf by blast
    qed
    have hmem: "\<forall>j\<in>I. f j \<in> (if j = i then U \<inter> X i else X j)"
      using hf unfolding top1_PiE_iff by blast
    have hfi: "f i \<in> U \<inter> X i"
    proof -
      have "f i \<in> (if i = i then U \<inter> X i else X i)"
        by (rule bspec[OF hmem hi])
      thus ?thesis
        by simp
    qed
    have hfiU: "f i \<in> U"
      using hfi by simp
    show "f \<in> {f \<in> top1_PiE I X. f i \<in> U}"
      using hfX hfiU by simp
	  next
	    assume hf: "f \<in> {f \<in> top1_PiE I X. f i \<in> U}"
	    have hf_conj: "f \<in> top1_PiE I X \<and> f i \<in> U"
	      using hf by simp
	    have hfX: "f \<in> top1_PiE I X"
	      using hf_conj by (rule conjunct1)
	    have hfiU: "f i \<in> U"
	      using hf_conj by (rule conjunct2)
	    have hfext: "\<forall>j. j \<notin> I \<longrightarrow> f j = undefined"
	      using hfX unfolding top1_PiE_iff by blast
	    have hmem: "\<forall>j\<in>I. f j \<in> (if j = i then U \<inter> X i else X j)"
    proof (intro ballI)
      fix j assume hj: "j \<in> I"
      have hfXj: "f j \<in> X j"
        using hfX hj unfolding top1_PiE_iff by blast
      show "f j \<in> (if j = i then U \<inter> X i else X j)"
      proof (cases "j = i")
        case True
        have "f i \<in> X i"
          using hfXj True by simp
        show ?thesis
          unfolding True using hfiU \<open>f i \<in> X i\<close> by simp
      next
        case False
        show ?thesis
          using hfXj False by simp
      qed
    qed
    show "f \<in> top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j)"
      unfolding top1_PiE_iff using hmem hfext by blast
  qed
qed

lemma top1_continuous_map_on_product_projection:
  assumes hTop: "\<forall>j\<in>I. is_topology_on (X j) (T j)"
  assumes hi: "i \<in> I"
  shows "top1_continuous_map_on (top1_PiE I X) (top1_product_topology_on I X T) (X i) (T i) (\<lambda>f. f i)"
proof -
  have hTopProd: "is_topology_on (top1_PiE I X) (top1_product_topology_on I X T)"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  have hXi: "is_topology_on (X i) (T i)"
    using hTop hi by blast

  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>f\<in>top1_PiE I X. f i \<in> X i"
    proof (intro ballI)
      fix f assume hf: "f \<in> top1_PiE I X"
      have hmem: "\<forall>j\<in>I. f j \<in> X j"
        using hf unfolding top1_PiE_iff by blast
      show "f i \<in> X i"
        using hmem hi by blast
    qed

    show "\<forall>U\<in>T i. {f \<in> top1_PiE I X. f i \<in> U} \<in> top1_product_topology_on I X T"
    proof (intro ballI)
      fix U assume hU: "U \<in> T i"
      have hbasis: "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<in> top1_product_basis_on I X T"
        by (rule top1_product_cylinder_in_basis[OF hTop hi hU])
      have hB: "is_basis_on (top1_PiE I X) (top1_product_basis_on I X T)"
        by (rule top1_product_basis_is_basis_on[OF hTop])
      have hopen: "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<in> top1_product_topology_on I X T"
        unfolding top1_product_topology_on_def
        by (rule basis_elem_open_in_generated_topology[OF hB hbasis])
      have hEq:
        "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) = {f \<in> top1_PiE I X. f i \<in> U}"
        by (rule top1_product_cylinder_eq[OF hi])
      show "{f \<in> top1_PiE I X. f i \<in> U} \<in> top1_product_topology_on I X T"
        using hopen hEq by simp
    qed
  qed
qed

(** from \S19 Theorem 19.6 (Continuity into product spaces) [top1.tex:~?] **)
theorem Theorem_19_6:
  assumes hTA: "is_topology_on A TA"
  assumes hTop: "\<forall>j\<in>I. is_topology_on (X j) (T j)"
  assumes hfmap: "\<forall>a\<in>A. f a \<in> top1_PiE I X"
  shows "top1_continuous_map_on A TA (top1_PiE I X) (top1_product_topology_on I X T) f
         \<longleftrightarrow> (\<forall>i\<in>I. top1_continuous_map_on A TA (X i) (T i) (\<lambda>a. (f a) i))"
text \<open>
  The forward direction is immediate from continuity of projections. The converse is proved
  by checking inverse images of basic product-open sets, which constrain only finitely many
  coordinates; this is a standard argument. We postpone the fully structured proof here
  to keep build times comfortably below the session timeout.
\<close>
proof (rule iffI)
  assume hcont: "top1_continuous_map_on A TA (top1_PiE I X) (top1_product_topology_on I X T) f"
  show "\<forall>i\<in>I. top1_continuous_map_on A TA (X i) (T i) (\<lambda>a. (f a) i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"

    have hproj:
      "top1_continuous_map_on (top1_PiE I X) (top1_product_topology_on I X T) (X i) (T i) (\<lambda>h. h i)"
      by (rule top1_continuous_map_on_product_projection[OF hTop hi])

    show "top1_continuous_map_on A TA (X i) (T i) (\<lambda>a. (f a) i)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>a\<in>A. (f a) i \<in> X i"
      proof (intro ballI)
        fix a assume ha: "a \<in> A"
        have hfa: "f a \<in> top1_PiE I X"
          using hcont ha unfolding top1_continuous_map_on_def by blast
        show "(f a) i \<in> X i"
          using hfa hi unfolding top1_PiE_iff by blast
      qed

      show "\<forall>U\<in>T i. {a \<in> A. (f a) i \<in> U} \<in> TA"
      proof (intro ballI)
        fix U assume hU: "U \<in> T i"

        have hopen: "{h \<in> top1_PiE I X. h i \<in> U} \<in> top1_product_topology_on I X T"
        proof -
          have "\<forall>V\<in>T i. {h \<in> top1_PiE I X. (\<lambda>h. h i) h \<in> V} \<in> top1_product_topology_on I X T"
            using hproj unfolding top1_continuous_map_on_def by blast
          hence "{h \<in> top1_PiE I X. h i \<in> U} \<in> top1_product_topology_on I X T"
            by (rule bspec[OF _ hU])
          thus ?thesis .
        qed

        have hpreim: "{a \<in> A. f a \<in> {h \<in> top1_PiE I X. h i \<in> U}} \<in> TA"
          using hcont hopen unfolding top1_continuous_map_on_def by blast

        have hmapA: "\<forall>a\<in>A. f a \<in> top1_PiE I X"
          using hcont unfolding top1_continuous_map_on_def by blast

        have hEq: "{a \<in> A. f a \<in> {h \<in> top1_PiE I X. h i \<in> U}} = {a \<in> A. (f a) i \<in> U}"
        proof (rule set_eqI)
          fix a
          show "a \<in> {a \<in> A. f a \<in> {h \<in> top1_PiE I X. h i \<in> U}} \<longleftrightarrow> a \<in> {a \<in> A. (f a) i \<in> U}"
          proof (rule iffI)
            assume ha: "a \<in> {a \<in> A. f a \<in> {h \<in> top1_PiE I X. h i \<in> U}}"
            then show "a \<in> {a \<in> A. (f a) i \<in> U}"
              by simp
          next
            assume ha: "a \<in> {a \<in> A. (f a) i \<in> U}"
            have haA: "a \<in> A"
              using ha by simp
            have hfa: "f a \<in> top1_PiE I X"
              using hmapA haA by blast
            show "a \<in> {a \<in> A. f a \<in> {h \<in> top1_PiE I X. h i \<in> U}}"
              using haA ha hfa by simp
          qed
        qed

        show "{a \<in> A. (f a) i \<in> U} \<in> TA"
          using hpreim unfolding hEq by simp
      qed
    qed
  qed
next
  assume hcoords: "\<forall>i\<in>I. top1_continuous_map_on A TA (X i) (T i) (\<lambda>a. (f a) i)"

  have hBasisProd:
    "basis_for (top1_PiE I X) (top1_product_basis_on I X T) (top1_product_topology_on I X T)"
    unfolding basis_for_def top1_product_topology_on_def
    apply (intro conjI)
     apply (rule top1_product_basis_is_basis_on[OF hTop])
    apply simp
    done

  have hpre: "\<forall>b\<in>top1_product_basis_on I X T. {a\<in>A. f a \<in> b} \<in> TA"
  proof (intro ballI)
    fix b assume hb: "b \<in> top1_product_basis_on I X T"
    obtain U where hbdef: "b = top1_PiE I U"
      and hU: "(\<forall>i\<in>I. U i \<in> T i \<and> U i \<subseteq> X i)"
      and hfin: "finite {i \<in> I. U i \<noteq> X i}"
      using hb unfolding top1_product_basis_on_def by blast

    define S where "S = {i \<in> I. U i \<noteq> X i}"
    have hSfin: "finite S"
      using hfin unfolding S_def by simp

    define F where "F = ((\<lambda>i. {a\<in>A. (f a) i \<in> U i}) ` S)"
    have hFfin: "finite F"
      unfolding F_def using hSfin by simp

    have hinterTA:
      "\<forall>G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> TA \<longrightarrow> \<Inter>G \<in> TA"
      by (rule conjunct2[OF conjunct2[OF conjunct2[OF hTA[unfolded is_topology_on_def]]]])

    have hFsubTA: "F \<subseteq> TA"
    proof (rule subsetI)
      fix W assume hW: "W \<in> F"
      obtain i where hiS: "i \<in> S" and hWeq: "W = {a\<in>A. (f a) i \<in> U i}"
        using hW unfolding F_def by blast

      have hiI: "i \<in> I"
        using hiS unfolding S_def by blast
      have hUiT: "U i \<in> T i"
        using hU hiI by blast
      have hcont_i: "top1_continuous_map_on A TA (X i) (T i) (\<lambda>a. (f a) i)"
        using hcoords hiI by blast
      have "{a\<in>A. (f a) i \<in> U i} \<in> TA"
        using hcont_i hUiT unfolding top1_continuous_map_on_def by blast
      show "W \<in> TA"
        unfolding hWeq using \<open>{a\<in>A. (f a) i \<in> U i} \<in> TA\<close> by simp
    qed

    have hpre_eq:
      "{a\<in>A. f a \<in> top1_PiE I U} = (if S = {} then A else \<Inter>F)"
    proof (cases "S = {}")
      case True
      have hAll: "\<forall>i\<in>I. U i = X i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have "i \<notin> S"
          using True by simp
        hence "\<not> (i \<in> I \<and> U i \<noteq> X i)"
          unfolding S_def by simp
        thus "U i = X i"
          using hi by blast
      qed

      have hAeq: "{a\<in>A. f a \<in> top1_PiE I U} = A"
      proof (rule set_eqI)
        fix a
        show "a \<in> {a\<in>A. f a \<in> top1_PiE I U} \<longleftrightarrow> a \<in> A"
        proof (rule iffI)
          assume ha: "a \<in> {a\<in>A. f a \<in> top1_PiE I U}"
          thus "a \<in> A" by simp
        next
          assume ha: "a \<in> A"
          have hfaX: "f a \<in> top1_PiE I X"
            using hfmap ha by blast
          have hfext: "\<forall>i. i \<notin> I \<longrightarrow> f a i = undefined"
            using hfaX unfolding top1_PiE_iff by blast
          have hfiU: "\<forall>i\<in>I. f a i \<in> U i"
          proof (intro ballI)
            fix i assume hi: "i \<in> I"
            have hfiX: "f a i \<in> X i"
              using hfaX hi unfolding top1_PiE_iff by blast
            show "f a i \<in> U i"
              using hAll hi hfiX by simp
          qed
          have hfaU: "f a \<in> top1_PiE I U"
            unfolding top1_PiE_iff using hfiU hfext by blast
          show "a \<in> {a\<in>A. f a \<in> top1_PiE I U}"
            using ha hfaU by simp
        qed
      qed
      show ?thesis
        unfolding True using hAeq by simp
	    next
	      case False
	      have hFne: "F \<noteq> {}"
	      proof -
	        obtain i where hiS: "i \<in> S"
	          using False by blast
        have "{a\<in>A. (f a) i \<in> U i} \<in> F"
          unfolding F_def using hiS by blast
        thus ?thesis by blast
      qed

      have hInter_open: "\<Inter>F \<in> TA"
        using hinterTA hFfin hFne hFsubTA by blast

      have hEq: "{a\<in>A. f a \<in> top1_PiE I U} = \<Inter>F"
      proof (rule set_eqI)
        fix a
        show "a \<in> {a\<in>A. f a \<in> top1_PiE I U} \<longleftrightarrow> a \<in> \<Inter>F"
	        proof (rule iffI)
	          assume ha: "a \<in> {a\<in>A. f a \<in> top1_PiE I U}"
	          have ha_conj: "a \<in> A \<and> f a \<in> top1_PiE I U"
	            using ha by simp
	          have haA: "a \<in> A"
	            using ha_conj by (rule conjunct1)
	          have hfaU: "f a \<in> top1_PiE I U"
	            using ha_conj by (rule conjunct2)
	          have hmem: "\<forall>i\<in>I. f a i \<in> U i"
	            using hfaU unfolding top1_PiE_iff by blast
	          have "a \<in> \<Inter>F"
	          proof (rule InterI)
            fix W assume hW: "W \<in> F"
            obtain i where hiS: "i \<in> S" and hWeq: "W = {a\<in>A. (f a) i \<in> U i}"
              using hW unfolding F_def by blast
            have hiI: "i \<in> I"
              using hiS unfolding S_def by blast
            have hfi: "f a i \<in> U i"
              using hmem hiI by blast
            show "a \<in> W"
              unfolding hWeq using haA hfi by simp
          qed
          thus "a \<in> \<Inter>F" .
        next
          assume haInter: "a \<in> \<Inter>F"

          have hsome: "\<exists>W\<in>F. True"
            using hFne by blast
          obtain W0 where hW0: "W0 \<in> F"
            using hsome by blast
	          obtain i0 where hi0S: "i0 \<in> S" and hW0eq: "W0 = {a\<in>A. (f a) i0 \<in> U i0}"
	            using hW0 unfolding F_def by blast
	          have haA: "a \<in> A"
	          proof -
	            have haW0: "a \<in> W0"
	              using haInter hW0 by blast
	            thus ?thesis
	              unfolding hW0eq by simp
	          qed

          have hfaX: "f a \<in> top1_PiE I X"
            using hfmap haA by blast
          have hfext: "\<forall>i. i \<notin> I \<longrightarrow> f a i = undefined"
            using hfaX unfolding top1_PiE_iff by blast
          have hfaXmem: "\<forall>i\<in>I. f a i \<in> X i"
            using hfaX unfolding top1_PiE_iff by blast

          have hmemS: "\<forall>i\<in>S. f a i \<in> U i"
          proof (intro ballI)
            fix i assume hiS: "i \<in> S"
            have "{a\<in>A. (f a) i \<in> U i} \<in> F"
              unfolding F_def using hiS by blast
            hence "a \<in> {a\<in>A. (f a) i \<in> U i}"
              using haInter by blast
            thus "f a i \<in> U i" by simp
          qed

          have hmemI: "\<forall>i\<in>I. f a i \<in> U i"
          proof (intro ballI)
            fix i assume hi: "i \<in> I"
            show "f a i \<in> U i"
            proof (cases "i \<in> S")
              case True
              show ?thesis
                using hmemS True by blast
	            next
	              case False
	              have hUi_eq: "U i = X i"
	              proof -
	                have hiSnot: "i \<notin> S"
	                  using False by simp
	                have "\<not> (i \<in> I \<and> U i \<noteq> X i)"
	                  using hiSnot unfolding S_def by simp
	                hence "\<not> (U i \<noteq> X i)"
	                  using hi by blast
	                thus ?thesis by simp
	              qed
	              have hfiX: "f a i \<in> X i"
	                using hfaXmem hi by blast
	              show ?thesis
	                unfolding hUi_eq using hfiX by simp
            qed
          qed

          have hfaU: "f a \<in> top1_PiE I U"
            unfolding top1_PiE_iff using hmemI hfext by blast

          show "a \<in> {a\<in>A. f a \<in> top1_PiE I U}"
            using haA hfaU by simp
        qed
      qed
	
	      show ?thesis
	      proof -
	        have "S = {} \<longrightarrow> False"
	          using False by simp
	        thus ?thesis
	          using hEq by simp
	      qed
	    qed

	    have hOpen: "(if S = {} then A else \<Inter>F) \<in> TA"
	    proof (cases "S = {}")
	      case True
	      have hAT: "A \<in> TA"
	        using hTA unfolding is_topology_on_def by blast
	      show ?thesis
	        unfolding True using hAT by simp
	    next
	      case False
	      have hFne: "F \<noteq> {}"
	      proof -
	        obtain i where hiS: "i \<in> S"
	          using False by blast
	        have "{a\<in>A. (f a) i \<in> U i} \<in> F"
	          unfolding F_def using hiS by blast
	        thus ?thesis by blast
	      qed
	      have hInterT: "\<Inter>F \<in> TA"
	        using hinterTA hFfin hFne hFsubTA by blast
	      show ?thesis
	      proof -
	        have hIf: "(if S = {} then A else \<Inter>F) = \<Inter>F"
	          using False by simp
	        show ?thesis
	          unfolding hIf using hInterT by simp
	      qed
	    qed

    have "{a\<in>A. f a \<in> top1_PiE I U} \<in> TA"
      using hOpen unfolding hpre_eq by simp
    thus "{a\<in>A. f a \<in> b} \<in> TA"
      unfolding hbdef by simp
  qed

  show "top1_continuous_map_on A TA (top1_PiE I X) (top1_product_topology_on I X T) f"
    by (rule top1_continuous_map_on_generated_by_basis[OF hTA hBasisProd hfmap hpre])
qed

(** from \S19 Theorem 19.2 (Bases for box/product topologies) [top1.tex] **)
theorem Theorem_19_2_box:
  assumes hB: "\<forall>i\<in>I. basis_for (X i) (B i) (T i)"
  shows "basis_for (top1_PiE I X)
           {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}
           (top1_box_topology_on I X T)"
proof -
  define Cc where "Cc = {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}"

  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hBi: "basis_for (X i) (B i) (T i)"
      using hB hi by blast
    show "is_topology_on (X i) (T i)"
      by (rule basis_for_is_topology_on[OF hBi])
  qed

  have hTopBox: "is_topology_on (top1_PiE I X) (top1_box_topology_on I X T)"
    by (rule top1_box_topology_on_is_topology_on[OF hTop])

  have hCcT: "Cc \<subseteq> top1_box_topology_on I X T"
  proof (rule subsetI)
    fix W assume hW: "W \<in> Cc"
    obtain U where hWdef: "W = top1_PiE I U" and hUiB: "\<forall>i\<in>I. U i \<in> B i"
      using hW unfolding Cc_def by blast

    have hUiT: "\<forall>i\<in>I. U i \<in> T i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      show "U i \<in> T i"
        by (rule basis_elem_open_if_basis_for[OF hBi], rule hUiB[rule_format, OF hi])
    qed

    have hUiX: "\<forall>i\<in>I. U i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      have hBasis_i: "is_basis_on (X i) (B i)"
        using hBi unfolding basis_for_def by blast
      have hsub: "\<forall>b\<in>B i. b \<subseteq> X i"
        using hBasis_i unfolding is_basis_on_def by blast
      show "U i \<subseteq> X i"
        by (rule bspec[OF hsub], rule hUiB[rule_format, OF hi])
    qed

    have hUbox: "top1_PiE I U \<in> top1_box_basis_on I X T"
      unfolding top1_box_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      using hUiT hUiX by blast

    have hBasisBox: "is_basis_on (top1_PiE I X) (top1_box_basis_on I X T)"
      by (rule top1_box_basis_is_basis_on[OF hTop])
    have hOpen: "top1_PiE I U \<in> top1_box_topology_on I X T"
      unfolding top1_box_topology_on_def
      by (rule basis_elem_open_in_generated_topology[OF hBasisBox hUbox])
    show "W \<in> top1_box_topology_on I X T"
      unfolding hWdef using hOpen by simp
  qed

  have hTX: "\<forall>U\<in>top1_box_topology_on I X T. U \<subseteq> top1_PiE I X"
    unfolding top1_box_topology_on_def topology_generated_by_basis_def by blast

  have hrefine:
    "\<And>U x. U \<in> top1_box_topology_on I X T \<Longrightarrow> x \<in> U \<Longrightarrow>
      \<exists>C\<in>Cc. C \<in> top1_box_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
  proof -
    fix U x
    assume hU: "U \<in> top1_box_topology_on I X T"
    assume hxU: "x \<in> U"

    have hxX: "x \<in> top1_PiE I X"
      using hTX hU hxU by blast

    have hUgen: "U \<in> topology_generated_by_basis (top1_PiE I X) (top1_box_basis_on I X T)"
      using hU unfolding top1_box_topology_on_def by simp
    have hcov: "\<forall>y\<in>U. \<exists>b\<in>top1_box_basis_on I X T. y \<in> b \<and> b \<subseteq> U"
      using hUgen unfolding topology_generated_by_basis_def by blast

    obtain b where hb: "b \<in> top1_box_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
      using hcov hxU by blast

    obtain U0 where hbdef: "b = top1_PiE I U0"
      and hU0: "\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i"
      using hb unfolding top1_box_basis_on_def by blast

    have hxU0: "\<forall>i\<in>I. x i \<in> U0 i"
      using hxb unfolding hbdef top1_PiE_iff by blast

    have hchoose: "\<forall>i\<in>I. \<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
	      have hU0i: "U0 i \<in> T i"
	        using hU0 hi by blast
	      have hxi: "x i \<in> U0 i"
	        using hxU0 hi by blast
	      show "\<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
	      proof -
	        have hTeq: "T i = topology_generated_by_basis (X i) (B i)"
	          using hBi unfolding basis_for_def by blast
	        have hU0gen: "U0 i \<in> topology_generated_by_basis (X i) (B i)"
	          using hU0i unfolding hTeq by simp
	        have hcov: "\<forall>y\<in>U0 i. \<exists>b\<in>B i. y \<in> b \<and> b \<subseteq> U0 i"
	          using hU0gen unfolding topology_generated_by_basis_def by blast
	        obtain V where hV: "V \<in> B i" and hxV: "x i \<in> V" and hVsub: "V \<subseteq> U0 i"
	          using hcov hxi by blast
	        show ?thesis
	          using hV hxV hVsub by blast
	      qed
	    qed
	
	    obtain V where hV: "\<forall>i\<in>I. V i \<in> B i \<and> x i \<in> V i \<and> V i \<subseteq> U0 i"
	      using bchoice[OF hchoose] by blast

    have hCmem: "top1_PiE I V \<in> Cc"
      unfolding Cc_def
      apply (rule CollectI)
      apply (rule exI[where x=V])
      using hV by blast

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hxX unfolding top1_PiE_iff by blast
    have hxV: "\<forall>i\<in>I. x i \<in> V i"
      using hV by blast
    have hxC: "x \<in> top1_PiE I V"
      unfolding top1_PiE_iff using hxV hxext by blast

    have hVsub: "\<forall>i\<in>I. V i \<subseteq> U0 i"
      using hV by blast
    have hCsub_b: "top1_PiE I V \<subseteq> top1_PiE I U0"
      by (rule top1_PiE_mono[OF hVsub])
    have hCsubU: "top1_PiE I V \<subseteq> U"
      using hCsub_b hbdef hbU by blast

    have hCopen: "top1_PiE I V \<in> top1_box_topology_on I X T"
      using hCcT hCmem by blast

    show "\<exists>C\<in>Cc. C \<in> top1_box_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
      apply (rule bexI[where x="top1_PiE I V"])
       apply (intro conjI)
         apply (rule hCopen)
        apply (rule hxC)
       apply (rule hCsubU)
      apply (rule hCmem)
      done
  qed

	  have hBF: "basis_for (top1_PiE I X) Cc (top1_box_topology_on I X T)"
	    apply (rule Lemma_13_2)
	       apply (rule hTopBox)
	      apply (rule hCcT)
	     apply (rule hTX)
	    apply (rule hrefine)
	     apply assumption
	    apply assumption
	    done

  show ?thesis
    by (rule hBF[unfolded Cc_def])
qed

theorem Theorem_19_2_product:
  assumes hB: "\<forall>i\<in>I. basis_for (X i) (B i) (T i)"
  shows "basis_for (top1_PiE I X)
           {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}
           (top1_product_topology_on I X T)"
proof -
  define Cc where
    "Cc = {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}"

  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hBi: "basis_for (X i) (B i) (T i)"
      using hB hi by blast
    show "is_topology_on (X i) (T i)"
      by (rule basis_for_is_topology_on[OF hBi])
  qed

  have hTopProd: "is_topology_on (top1_PiE I X) (top1_product_topology_on I X T)"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  have hCcT: "Cc \<subseteq> top1_product_topology_on I X T"
  proof (rule subsetI)
    fix W assume hW: "W \<in> Cc"
    obtain U where hWdef: "W = top1_PiE I U"
      and hUiB: "(\<forall>i\<in>I. U i = X i \<or> U i \<in> B i)"
      and hfin: "finite {i \<in> I. U i \<noteq> X i}"
      using hW unfolding Cc_def by blast

    have hUiT: "\<forall>i\<in>I. U i \<in> T i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      have hTopi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hXi: "X i \<in> T i"
        using hTopi unfolding is_topology_on_def by blast
      show "U i \<in> T i"
      proof (cases "U i = X i")
        case True
        show ?thesis
          unfolding True using hXi by simp
      next
        case False
        have hUiBi: "U i \<in> B i"
          using hUiB hi False by blast
        show ?thesis
          by (rule basis_elem_open_if_basis_for[OF hBi hUiBi])
      qed
    qed

    have hUiX: "\<forall>i\<in>I. U i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      show "U i \<subseteq> X i"
      proof (cases "U i = X i")
        case True
        show ?thesis
          unfolding True by simp
      next
        case False
        have hBi: "basis_for (X i) (B i) (T i)"
          using hB hi by blast
        have hBasis_i: "is_basis_on (X i) (B i)"
          using hBi unfolding basis_for_def by blast
        have hsub: "\<forall>b\<in>B i. b \<subseteq> X i"
          using hBasis_i unfolding is_basis_on_def by blast
        have hUiBi: "U i \<in> B i"
          using hUiB hi False by blast
        show ?thesis
          by (rule bspec[OF hsub hUiBi])
      qed
    qed

    have hUprod: "top1_PiE I U \<in> top1_product_basis_on I X T"
      unfolding top1_product_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      using hUiT hUiX hfin by blast

    have hBasisProd: "is_basis_on (top1_PiE I X) (top1_product_basis_on I X T)"
      by (rule top1_product_basis_is_basis_on[OF hTop])
    have hOpen: "top1_PiE I U \<in> top1_product_topology_on I X T"
      unfolding top1_product_topology_on_def
      by (rule basis_elem_open_in_generated_topology[OF hBasisProd hUprod])

    show "W \<in> top1_product_topology_on I X T"
      unfolding hWdef using hOpen by simp
  qed

  have hTX: "\<forall>U\<in>top1_product_topology_on I X T. U \<subseteq> top1_PiE I X"
    unfolding top1_product_topology_on_def topology_generated_by_basis_def by blast

  have hrefine:
    "\<And>U x. U \<in> top1_product_topology_on I X T \<Longrightarrow> x \<in> U \<Longrightarrow>
      \<exists>C\<in>Cc. C \<in> top1_product_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
  proof -
    fix U x
    assume hU: "U \<in> top1_product_topology_on I X T"
    assume hxU: "x \<in> U"

    have hxX: "x \<in> top1_PiE I X"
      using hTX hU hxU by blast

    have hUgen:
      "U \<in> topology_generated_by_basis (top1_PiE I X) (top1_product_basis_on I X T)"
      using hU unfolding top1_product_topology_on_def by simp
    have hcov:
      "\<forall>y\<in>U. \<exists>b\<in>top1_product_basis_on I X T. y \<in> b \<and> b \<subseteq> U"
      using hUgen unfolding topology_generated_by_basis_def by blast

    obtain b where hb: "b \<in> top1_product_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
      using hcov hxU by blast

    obtain U0 where hbdef: "b = top1_PiE I U0"
      and hU0: "(\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i)"
      and hfin0: "finite {i \<in> I. U0 i \<noteq> X i}"
      using hb unfolding top1_product_basis_on_def by blast

    define S where "S = {i \<in> I. U0 i \<noteq> X i}"
    have hSfin: "finite S"
      using hfin0 unfolding S_def by simp

    have hxU0: "\<forall>i\<in>I. x i \<in> U0 i"
      using hxb unfolding hbdef top1_PiE_iff by blast

    have hchoose: "\<forall>i\<in>S. \<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
    proof (intro ballI)
      fix i assume hiS: "i \<in> S"
      have hi: "i \<in> I"
        using hiS unfolding S_def by blast
      have hBi: "basis_for (X i) (B i) (T i)"
        using hB hi by blast
      have hU0i: "U0 i \<in> T i"
        using hU0 hi by blast
      have hxi: "x i \<in> U0 i"
        using hxU0 hi by blast

      (* unfold continuity in the topology generated by a basis to obtain a basis element around x i *)
      have hTeq: "T i = topology_generated_by_basis (X i) (B i)"
        using hBi unfolding basis_for_def by blast
      have hU0gen: "U0 i \<in> topology_generated_by_basis (X i) (B i)"
        using hU0i unfolding hTeq by simp
      have hcov': "\<forall>y\<in>U0 i. \<exists>b\<in>B i. y \<in> b \<and> b \<subseteq> U0 i"
        using hU0gen unfolding topology_generated_by_basis_def by blast
      obtain V where hV: "V \<in> B i" and hxV: "x i \<in> V" and hVsub: "V \<subseteq> U0 i"
        using hcov' hxi by blast
      show "\<exists>V. V \<in> B i \<and> x i \<in> V \<and> V \<subseteq> U0 i"
        using hV hxV hVsub by blast
    qed

    obtain W where hW: "\<forall>i\<in>S. W i \<in> B i \<and> x i \<in> W i \<and> W i \<subseteq> U0 i"
      using bchoice[OF hchoose] by blast

    define V where "V = (\<lambda>i. if i \<in> S then W i else X i)"

    have hV_prop: "(\<forall>i\<in>I. V i = X i \<or> V i \<in> B i) \<and> finite {i \<in> I. V i \<noteq> X i}"
    proof (intro conjI)
      show "\<forall>i\<in>I. V i = X i \<or> V i \<in> B i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        show "V i = X i \<or> V i \<in> B i"
        proof (cases "i \<in> S")
          case True
          have "V i = W i"
            unfolding V_def using True by simp
          moreover have "W i \<in> B i"
            using hW True by blast
          ultimately show ?thesis
            by simp
        next
          case False
          have "V i = X i"
            unfolding V_def using False by simp
          thus ?thesis
            by simp
        qed
      qed

      have "{i \<in> I. V i \<noteq> X i} \<subseteq> S"
      proof (rule subsetI)
        fix i assume hi: "i \<in> {i \<in> I. V i \<noteq> X i}"
        have hiI: "i \<in> I" and hneq: "V i \<noteq> X i"
          using hi by blast+
        have "i \<in> S"
        proof (rule ccontr)
          assume hin: "i \<notin> S"
          have "V i = X i"
            unfolding V_def using hin by simp
          thus False
            using hneq by contradiction
        qed
        thus "i \<in> S" .
      qed
      thus "finite {i \<in> I. V i \<noteq> X i}"
        using hSfin finite_subset by blast
    qed

    have hCmem: "top1_PiE I V \<in> Cc"
      unfolding Cc_def
      apply (rule CollectI)
      apply (rule exI[where x=V])
      using hV_prop by blast

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hxX unfolding top1_PiE_iff by blast
    have hxV: "\<forall>i\<in>I. x i \<in> V i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      show "x i \<in> V i"
      proof (cases "i \<in> S")
        case True
        have "V i = W i"
          unfolding V_def using True by simp
        moreover have "x i \<in> W i"
          using hW True by blast
        ultimately show ?thesis
          by simp
      next
        case False
        have "V i = X i"
          unfolding V_def using False by simp
        moreover have "x i \<in> X i"
          using hxX hi unfolding top1_PiE_iff by blast
        ultimately show ?thesis
          by simp
      qed
    qed
    have hxC: "x \<in> top1_PiE I V"
      unfolding top1_PiE_iff using hxV hxext by blast

    have hVsub: "\<forall>i\<in>I. V i \<subseteq> U0 i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      show "V i \<subseteq> U0 i"
      proof (cases "i \<in> S")
        case True
        have "V i = W i"
          unfolding V_def using True by simp
        moreover have "W i \<subseteq> U0 i"
          using hW True by blast
        ultimately show ?thesis
          by simp
      next
        case False
        have hU0eq: "U0 i = X i"
        proof -
          have "i \<notin> {i \<in> I. U0 i \<noteq> X i}"
            using False unfolding S_def by simp
          hence "\<not> (U0 i \<noteq> X i)"
            using hi by blast
          thus ?thesis by simp
        qed
        have "V i = X i"
          unfolding V_def using False by simp
        thus ?thesis
          unfolding hU0eq by simp
      qed
    qed

    have hCsub_b: "top1_PiE I V \<subseteq> top1_PiE I U0"
      by (rule top1_PiE_mono[OF hVsub])
    have hCsubU: "top1_PiE I V \<subseteq> U"
      using hCsub_b hbdef hbU by blast

    have hCopen: "top1_PiE I V \<in> top1_product_topology_on I X T"
      using hCcT hCmem by blast

    show "\<exists>C\<in>Cc. C \<in> top1_product_topology_on I X T \<and> x \<in> C \<and> C \<subseteq> U"
      apply (rule bexI[where x="top1_PiE I V"])
       apply (intro conjI)
         apply (rule hCopen)
        apply (rule hxC)
       apply (rule hCsubU)
      apply (rule hCmem)
      done
  qed

  have hBF: "basis_for (top1_PiE I X) Cc (top1_product_topology_on I X T)"
    apply (rule Lemma_13_2)
       apply (rule hTopProd)
      apply (rule hCcT)
     apply (rule hTX)
    apply (rule hrefine)
     apply assumption
    apply assumption
    done

  show ?thesis
    by (rule hBF[unfolded Cc_def])
qed

(** from \S19 Theorem 19.3 (Product of subspaces is a subspace) [top1.tex] **)
theorem Theorem_19_3_box:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  assumes hsub: "\<forall>i\<in>I. A i \<subseteq> X i"
  defines "TA \<equiv> (\<lambda>i. subspace_topology (X i) (T i) (A i))"
  shows "top1_box_topology_on I A TA =
         subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
proof -
  have hAX: "top1_PiE I A \<subseteq> top1_PiE I X"
    by (rule top1_PiE_mono[OF hsub])

  have hTopBoxX: "is_topology_on (top1_PiE I X) (top1_box_topology_on I X T)"
    by (rule top1_box_topology_on_is_topology_on[OF hTop])

  have hTopSub: "is_topology_on (top1_PiE I A)
      (subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A))"
    by (rule subspace_topology_is_topology_on[OF hTopBoxX hAX])

  have hTopA: "\<forall>i\<in>I. is_topology_on (A i) (TA i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hTopi: "is_topology_on (X i) (T i)"
      using hTop hi by blast
    have hsubi: "A i \<subseteq> X i"
      using hsub hi by blast
    have "is_topology_on (A i) (subspace_topology (X i) (T i) (A i))"
      by (rule subspace_topology_is_topology_on[OF hTopi hsubi])
    thus "is_topology_on (A i) (TA i)"
      unfolding TA_def by simp
  qed

  have hBasisBoxX: "is_basis_on (top1_PiE I X) (top1_box_basis_on I X T)"
    by (rule top1_box_basis_is_basis_on[OF hTop])

  have hBasisBoxA: "is_basis_on (top1_PiE I A) (top1_box_basis_on I A TA)"
    by (rule top1_box_basis_is_basis_on[OF hTopA])

  have hLeft_sub:
    "top1_box_topology_on I A TA \<subseteq>
      subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
  proof -
    have hBsub:
      "top1_box_basis_on I A TA \<subseteq>
        subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
    proof (rule subsetI)
      fix b assume hb: "b \<in> top1_box_basis_on I A TA"
      obtain U where hbdef: "b = top1_PiE I U"
        and hU: "\<forall>i\<in>I. U i \<in> TA i \<and> U i \<subseteq> A i"
        using hb unfolding top1_box_basis_on_def by blast

      have hchoice: "\<forall>i\<in>I. \<exists>V. V \<in> T i \<and> U i = (A i \<inter> V)"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have "U i \<in> TA i"
          using hU hi by blast
        hence "U i \<in> subspace_topology (X i) (T i) (A i)"
          unfolding TA_def by simp
        then obtain V where hV: "V \<in> T i" and hUi: "U i = A i \<inter> V"
          unfolding subspace_topology_def by blast
        show "\<exists>V. V \<in> T i \<and> U i = A i \<inter> V"
          using hV hUi by blast
      qed

      obtain V where hV: "\<forall>i\<in>I. V i \<in> T i \<and> U i = A i \<inter> V i"
        using bchoice[OF hchoice] by blast

      define W where "W = (\<lambda>i. V i \<inter> X i)"

      have hW: "\<forall>i\<in>I. W i \<in> T i \<and> W i \<subseteq> X i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have hTopi: "is_topology_on (X i) (T i)"
          using hTop hi by blast
        have hXi: "X i \<in> T i"
          using hTopi unfolding is_topology_on_def by blast
        have hVi: "V i \<in> T i"
          using hV hi by blast
        have hWiT: "W i \<in> T i"
          unfolding W_def by (rule topology_inter2[OF hTopi hVi hXi])
        have hWiX: "W i \<subseteq> X i"
          unfolding W_def by blast
        show "W i \<in> T i \<and> W i \<subseteq> X i"
          using hWiT hWiX by blast
      qed

      have hUeq: "\<forall>i\<in>I. U i = A i \<inter> W i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have hUi: "U i = A i \<inter> V i"
          using hV hi by blast
        have hAiX: "A i \<subseteq> X i"
          using hsub hi by blast
        have "A i \<inter> V i = A i \<inter> (V i \<inter> X i)"
          using hAiX by blast
        thus "U i = A i \<inter> W i"
          unfolding W_def using hUi by simp
      qed

	      have hbInt: "top1_PiE I U = top1_PiE I A \<inter> top1_PiE I W"
	      proof -
	        have "top1_PiE I U = top1_PiE I (\<lambda>i. A i \<inter> W i)"
	          by (rule top1_PiE_cong_on[OF hUeq])
	        also have "\<dots> = top1_PiE I A \<inter> top1_PiE I W"
	          by (simp add: top1_PiE_Int[symmetric])
	        finally show ?thesis
	          by simp
	      qed

      have hWbasis: "top1_PiE I W \<in> top1_box_basis_on I X T"
        unfolding top1_box_basis_on_def
        apply (rule CollectI)
        apply (rule exI[where x=W])
        using hW by blast

      have hWopen: "top1_PiE I W \<in> top1_box_topology_on I X T"
        unfolding top1_box_topology_on_def
        by (rule basis_elem_open_in_generated_topology[OF hBasisBoxX hWbasis])

      have "b \<in> subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
        unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x="top1_PiE I W"])
        apply (intro conjI)
         apply (simp add: hbdef hbInt)
        apply (rule hWopen)
        done
      thus "b \<in> subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
        by simp
    qed

	    have "top1_box_topology_on I A TA \<subseteq>
	      subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
	    proof -
	      have hBsub':
	        "top1_box_basis_on I A TA \<subseteq>
	          subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
	        using hBsub by simp
	      have "topology_generated_by_basis (top1_PiE I A) (top1_box_basis_on I A TA)
	        \<subseteq> subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
	        by (rule topology_generated_by_basis_subset[OF hTopSub hBsub'])
	      thus ?thesis
	        unfolding top1_box_topology_on_def by simp
	    qed
	    thus ?thesis .
	  qed

  have hRight_sub:
    "subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)
      \<subseteq> top1_box_topology_on I A TA"
  proof (rule subsetI)
    fix W assume hW: "W \<in> subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
    obtain U where hWeq: "W = top1_PiE I A \<inter> U" and hU: "U \<in> top1_box_topology_on I X T"
      using hW unfolding subspace_topology_def by blast

    have hUgen: "U \<in> topology_generated_by_basis (top1_PiE I X) (top1_box_basis_on I X T)"
      using hU unfolding top1_box_topology_on_def by simp

    have hWsub: "W \<subseteq> top1_PiE I A"
      unfolding hWeq by blast

    have href: "\<forall>x\<in>W. \<exists>b\<in>top1_box_basis_on I A TA. x \<in> b \<and> b \<subseteq> W"
    proof (intro ballI)
      fix x assume hxW: "x \<in> W"
      have hxA: "x \<in> top1_PiE I A"
        using hWsub hxW by blast
      have hxU: "x \<in> U"
        using hxW unfolding hWeq by simp

      have hcov: "\<forall>y\<in>U. \<exists>b\<in>top1_box_basis_on I X T. y \<in> b \<and> b \<subseteq> U"
        using hUgen unfolding topology_generated_by_basis_def by blast
      obtain b where hb: "b \<in> top1_box_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
        using hcov hxU by blast

      obtain U0 where hbdef: "b = top1_PiE I U0"
        and hU0: "\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i"
        using hb unfolding top1_box_basis_on_def by blast

      define V where "V = (\<lambda>i. A i \<inter> U0 i)"

      have hVbasis: "top1_PiE I V \<in> top1_box_basis_on I A TA"
      proof -
        have hV: "\<forall>i\<in>I. V i \<in> TA i \<and> V i \<subseteq> A i"
        proof (intro ballI)
          fix i assume hi: "i \<in> I"
          have hUi: "U0 i \<in> T i"
            using hU0 hi by blast
          have "V i \<in> subspace_topology (X i) (T i) (A i)"
            unfolding subspace_topology_def V_def
            apply (rule CollectI)
            apply (rule exI[where x="U0 i"])
            using hUi by simp
          moreover have "V i \<subseteq> A i"
            unfolding V_def by blast
          ultimately show "V i \<in> TA i \<and> V i \<subseteq> A i"
            unfolding TA_def by simp
        qed
        show ?thesis
          unfolding top1_box_basis_on_def
          apply (rule CollectI)
          apply (rule exI[where x=V])
          using hV by blast
      qed

      have hxV: "x \<in> top1_PiE I V"
      proof -
        have hxmemA: "\<forall>i\<in>I. x i \<in> A i"
          using hxA unfolding top1_PiE_iff by blast
        have hxmemU0: "\<forall>i\<in>I. x i \<in> U0 i"
          using hxb unfolding hbdef top1_PiE_iff by blast
        have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
          using hxA unfolding top1_PiE_iff by blast
        have hxmemV: "\<forall>i\<in>I. x i \<in> V i"
          unfolding V_def using hxmemA hxmemU0 by blast
        show ?thesis
          unfolding top1_PiE_iff using hxmemV hxext by blast
      qed

      have hVsubA: "top1_PiE I V \<subseteq> top1_PiE I A"
      proof -
        have "\<forall>i\<in>I. V i \<subseteq> A i"
          unfolding V_def by blast
        thus ?thesis
          by (rule top1_PiE_mono)
      qed

	      have hVsubb: "top1_PiE I V \<subseteq> b"
	      proof -
	        have hsubVU0: "\<forall>i\<in>I. V i \<subseteq> U0 i"
	        proof (intro ballI)
	          fix i assume hi: "i \<in> I"
	          show "V i \<subseteq> U0 i"
	            unfolding V_def by blast
	        qed
	        have "top1_PiE I V \<subseteq> top1_PiE I U0"
	          by (rule top1_PiE_mono[OF hsubVU0])
	        thus ?thesis
	          unfolding hbdef by simp
	      qed

      have hVsubW: "top1_PiE I V \<subseteq> W"
        unfolding hWeq
        using hVsubA hVsubb hbU by blast

      show "\<exists>b\<in>top1_box_basis_on I A TA. x \<in> b \<and> b \<subseteq> W"
        apply (rule bexI[where x="top1_PiE I V"])
         apply (intro conjI)
           apply (rule hxV)
          apply (rule hVsubW)
        apply (rule hVbasis)
        done
    qed

    have "W \<in> top1_box_topology_on I A TA"
      unfolding top1_box_topology_on_def topology_generated_by_basis_def
      apply (rule CollectI)
      apply (intro conjI)
       apply (rule hWsub)
      apply (rule href)
      done
    thus "W \<in> top1_box_topology_on I A TA" .
  qed

  show ?thesis
    by (rule equalityI[OF hLeft_sub hRight_sub])
qed

theorem Theorem_19_3_product:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  assumes hsub: "\<forall>i\<in>I. A i \<subseteq> X i"
  defines "TA \<equiv> (\<lambda>i. subspace_topology (X i) (T i) (A i))"
  shows "top1_product_topology_on I A TA =
         subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
proof -
  have hAX: "top1_PiE I A \<subseteq> top1_PiE I X"
    by (rule top1_PiE_mono[OF hsub])

  have hTopProdX: "is_topology_on (top1_PiE I X) (top1_product_topology_on I X T)"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  have hTopSub: "is_topology_on (top1_PiE I A)
      (subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A))"
    by (rule subspace_topology_is_topology_on[OF hTopProdX hAX])

  have hTopA: "\<forall>i\<in>I. is_topology_on (A i) (TA i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hTopi: "is_topology_on (X i) (T i)"
      using hTop hi by blast
    have hsubi: "A i \<subseteq> X i"
      using hsub hi by blast
    have "is_topology_on (A i) (subspace_topology (X i) (T i) (A i))"
      by (rule subspace_topology_is_topology_on[OF hTopi hsubi])
    thus "is_topology_on (A i) (TA i)"
      unfolding TA_def by simp
  qed

  have hBasisProdX: "is_basis_on (top1_PiE I X) (top1_product_basis_on I X T)"
    by (rule top1_product_basis_is_basis_on[OF hTop])

  have hBasisProdA: "is_basis_on (top1_PiE I A) (top1_product_basis_on I A TA)"
    by (rule top1_product_basis_is_basis_on[OF hTopA])

  have hLeft_sub:
    "top1_product_topology_on I A TA \<subseteq>
      subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
  proof -
    have hBsub:
      "top1_product_basis_on I A TA \<subseteq>
        subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
    proof (rule subsetI)
      fix b assume hb: "b \<in> top1_product_basis_on I A TA"
	      obtain U where hbdef: "b = top1_PiE I U"
	        and hU: "(\<forall>i\<in>I. U i \<in> TA i \<and> U i \<subseteq> A i)"
	        and hfin: "finite {i \<in> I. U i \<noteq> A i}"
	        using hb unfolding top1_product_basis_on_def by blast

	      define S0 where "S0 = {i \<in> I. U i \<noteq> A i}"
	      have hS0fin: "finite S0"
	        using hfin unfolding S0_def by simp

	      have hchoice0: "\<forall>i\<in>S0. \<exists>V. V \<in> T i \<and> U i = A i \<inter> V"
	      proof (intro ballI)
	        fix i assume hiS0: "i \<in> S0"
	        have hi: "i \<in> I"
	          using hiS0 unfolding S0_def by blast
	        have "U i \<in> TA i"
	          using hU hi by blast
	        hence "U i \<in> subspace_topology (X i) (T i) (A i)"
	          unfolding TA_def by simp
	        then obtain V where hV: "V \<in> T i" and hUi: "U i = A i \<inter> V"
	          unfolding subspace_topology_def by blast
	        show "\<exists>V. V \<in> T i \<and> U i = A i \<inter> V"
	          using hV hUi by blast
	      qed

	      obtain V0 where hV0: "\<forall>i\<in>S0. V0 i \<in> T i \<and> U i = A i \<inter> V0 i"
	        using bchoice[OF hchoice0] by blast

	      define V where "V = (\<lambda>i. if i \<in> S0 then V0 i else X i)"

	      have hV: "\<forall>i\<in>I. V i \<in> T i \<and> U i = A i \<inter> V i"
	      proof (intro ballI)
	        fix i assume hi: "i \<in> I"
	        show "V i \<in> T i \<and> U i = A i \<inter> V i"
	        proof (cases "i \<in> S0")
	          case True
	          have "V0 i \<in> T i \<and> U i = A i \<inter> V0 i"
	            using hV0 True by blast
	          thus ?thesis
	            unfolding V_def using True by simp
	        next
	          case False
	          have hTopi: "is_topology_on (X i) (T i)"
	            using hTop hi by blast
	          have hXi: "X i \<in> T i"
	            using hTopi unfolding is_topology_on_def by blast
	          have hUi: "U i = A i"
	            using False hi unfolding S0_def by blast
	          have hAiX: "A i \<subseteq> X i"
	            using hsub hi by blast
	          have "A i \<inter> X i = A i"
	            using hAiX by blast
	          thus ?thesis
	            unfolding V_def using False hXi hUi by simp
	        qed
	      qed

	      define W where "W = (\<lambda>i. V i \<inter> X i)"

      have hW: "\<forall>i\<in>I. W i \<in> T i \<and> W i \<subseteq> X i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have hTopi: "is_topology_on (X i) (T i)"
          using hTop hi by blast
        have hXi: "X i \<in> T i"
          using hTopi unfolding is_topology_on_def by blast
        have hVi: "V i \<in> T i"
          using hV hi by blast
        have hWiT: "W i \<in> T i"
          unfolding W_def by (rule topology_inter2[OF hTopi hVi hXi])
        have hWiX: "W i \<subseteq> X i"
          unfolding W_def by blast
        show "W i \<in> T i \<and> W i \<subseteq> X i"
          using hWiT hWiX by blast
      qed

      have hUeq: "\<forall>i\<in>I. U i = A i \<inter> W i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have hUi: "U i = A i \<inter> V i"
          using hV hi by blast
        have hAiX: "A i \<subseteq> X i"
          using hsub hi by blast
        have "A i \<inter> V i = A i \<inter> (V i \<inter> X i)"
          using hAiX by blast
        thus "U i = A i \<inter> W i"
          unfolding W_def using hUi by simp
      qed

      have hbInt: "top1_PiE I U = top1_PiE I A \<inter> top1_PiE I W"
      proof -
        have "top1_PiE I U = top1_PiE I (\<lambda>i. A i \<inter> W i)"
          by (rule top1_PiE_cong_on[OF hUeq])
        also have "\<dots> = top1_PiE I A \<inter> top1_PiE I W"
          by (simp add: top1_PiE_Int[symmetric])
        finally show ?thesis
          by simp
      qed

	      have hWbasis: "top1_PiE I W \<in> top1_product_basis_on I X T"
	      proof -
	        define S where "S = {i \<in> I. W i \<noteq> X i}"
	        have hSfin: "finite S"
	        proof -
	          have hSsub: "S \<subseteq> S0"
	          proof (rule subsetI)
	            fix i assume hiS: "i \<in> S"
	            have hiI: "i \<in> I" and hWneq: "W i \<noteq> X i"
	              using hiS unfolding S_def by blast+
	            show "i \<in> S0"
	            proof (rule ccontr)
	              assume hi0: "i \<notin> S0"
	              have hVi: "V i = X i"
	                unfolding V_def using hi0 by simp
	              have "W i = X i"
	                unfolding W_def using hVi by simp
	              thus False
	                using hWneq by contradiction
	            qed
	          qed
	          show ?thesis
	            using finite_subset[OF hSsub hS0fin] by simp
	        qed
	        have hWbasis': "top1_PiE I W \<in> top1_product_basis_on I X T"
	          unfolding top1_product_basis_on_def
	          apply (rule CollectI)
	          apply (rule exI[where x=W])
	          apply (intro conjI)
	           apply simp
	          apply (rule hW)
	          apply (rule finite_subset[OF subset_refl])
	           apply (rule hSfin[unfolded S_def])
	          done
	        show ?thesis
	          using hWbasis' by simp
	      qed

      have hWopen: "top1_PiE I W \<in> top1_product_topology_on I X T"
        unfolding top1_product_topology_on_def
        by (rule basis_elem_open_in_generated_topology[OF hBasisProdX hWbasis])

      have "b \<in> subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
        unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x="top1_PiE I W"])
        apply (intro conjI)
         apply (simp add: hbdef hbInt)
        apply (rule hWopen)
        done
      thus "b \<in> subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
        by simp
    qed

    have "top1_product_topology_on I A TA \<subseteq>
      subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
    proof -
      have "topology_generated_by_basis (top1_PiE I A) (top1_product_basis_on I A TA)
        \<subseteq> subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
        by (rule topology_generated_by_basis_subset[OF hTopSub hBsub])
      thus ?thesis
        unfolding top1_product_topology_on_def by simp
    qed
    thus ?thesis .
  qed

  have hRight_sub:
    "subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)
      \<subseteq> top1_product_topology_on I A TA"
  proof (rule subsetI)
    fix W assume hW: "W \<in> subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
    obtain U where hWeq: "W = top1_PiE I A \<inter> U" and hU: "U \<in> top1_product_topology_on I X T"
      using hW unfolding subspace_topology_def by blast

    have hUgen: "U \<in> topology_generated_by_basis (top1_PiE I X) (top1_product_basis_on I X T)"
      using hU unfolding top1_product_topology_on_def by simp

    have hWsub: "W \<subseteq> top1_PiE I A"
      unfolding hWeq by blast

    have href: "\<forall>x\<in>W. \<exists>b\<in>top1_product_basis_on I A TA. x \<in> b \<and> b \<subseteq> W"
    proof (intro ballI)
      fix x assume hxW: "x \<in> W"
      have hxU: "x \<in> U"
        using hxW unfolding hWeq by simp

      have hcov: "\<forall>y\<in>U. \<exists>b\<in>top1_product_basis_on I X T. y \<in> b \<and> b \<subseteq> U"
        using hUgen unfolding topology_generated_by_basis_def by blast
      obtain b where hb: "b \<in> top1_product_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
        using hcov hxU by blast

      obtain U0 where hbdef: "b = top1_PiE I U0"
        and hU0: "(\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i)"
        and hfin0: "finite {i \<in> I. U0 i \<noteq> X i}"
        using hb unfolding top1_product_basis_on_def by blast

      define V where "V = (\<lambda>i. A i \<inter> U0 i)"
      have hVbasis: "top1_PiE I V \<in> top1_product_basis_on I A TA"
      proof -
        have hV: "\<forall>i\<in>I. V i \<in> TA i \<and> V i \<subseteq> A i"
        proof (intro ballI)
          fix i assume hi: "i \<in> I"
          have hUi: "U0 i \<in> T i"
            using hU0 hi by blast
          have "V i \<in> subspace_topology (X i) (T i) (A i)"
            unfolding subspace_topology_def V_def
            apply (rule CollectI)
            apply (rule exI[where x="U0 i"])
            using hUi by simp
          moreover have "V i \<subseteq> A i"
            unfolding V_def by blast
          ultimately show "V i \<in> TA i \<and> V i \<subseteq> A i"
            unfolding TA_def by simp
        qed
        have hfin: "finite {i \<in> I. V i \<noteq> A i}"
        proof -
          have "{i \<in> I. V i \<noteq> A i} \<subseteq> {i \<in> I. U0 i \<noteq> X i}"
          proof (rule subsetI)
            fix i assume hi: "i \<in> {i \<in> I. V i \<noteq> A i}"
            have hiI: "i \<in> I" and hneq: "V i \<noteq> A i"
              using hi by blast+
            have hAiX: "A i \<subseteq> X i"
              using hsub hiI by blast
            have hUeq: "U0 i = X i \<Longrightarrow> V i = A i"
              unfolding V_def using hAiX by blast
            have "U0 i \<noteq> X i"
              using hUeq hneq by blast
            thus "i \<in> {i \<in> I. U0 i \<noteq> X i}"
              using hiI by blast
          qed
          thus ?thesis
            using hfin0 finite_subset by blast
        qed
        show ?thesis
          unfolding top1_product_basis_on_def
          apply (rule CollectI)
          apply (rule exI[where x=V])
          using hV hfin by blast
      qed

      have hxV: "x \<in> top1_PiE I V"
      proof -
        have hxA: "x \<in> top1_PiE I A"
          using hxW hWeq by simp
        have hxmemA: "\<forall>i\<in>I. x i \<in> A i"
          using hxA unfolding top1_PiE_iff by blast
        have hxmemU0: "\<forall>i\<in>I. x i \<in> U0 i"
          using hxb unfolding hbdef top1_PiE_iff by blast
        have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
          using hxA unfolding top1_PiE_iff by blast
        have hxmemV: "\<forall>i\<in>I. x i \<in> V i"
          unfolding V_def using hxmemA hxmemU0 by blast
        show ?thesis
          unfolding top1_PiE_iff using hxmemV hxext by blast
      qed

      have hVsubA: "top1_PiE I V \<subseteq> top1_PiE I A"
      proof -
        have "\<forall>i\<in>I. V i \<subseteq> A i"
          unfolding V_def by blast
        thus ?thesis
          by (rule top1_PiE_mono)
      qed

      have hVsubb: "top1_PiE I V \<subseteq> b"
      proof -
        have hsubVU0: "\<forall>i\<in>I. V i \<subseteq> U0 i"
          unfolding V_def by blast
        have "top1_PiE I V \<subseteq> top1_PiE I U0"
          by (rule top1_PiE_mono[OF hsubVU0])
        thus ?thesis
          unfolding hbdef by simp
      qed

      have hVsubW: "top1_PiE I V \<subseteq> W"
        unfolding hWeq
        using hVsubA hVsubb hbU by blast

      show "\<exists>b\<in>top1_product_basis_on I A TA. x \<in> b \<and> b \<subseteq> W"
        apply (rule bexI[where x="top1_PiE I V"])
         apply (intro conjI)
           apply (rule hxV)
          apply (rule hVsubW)
        apply (rule hVbasis)
        done
    qed

    have "W \<in> top1_product_topology_on I A TA"
      unfolding top1_product_topology_on_def topology_generated_by_basis_def
      apply (rule CollectI)
      apply (intro conjI)
       apply (rule hWsub)
      apply (rule href)
      done
    thus "W \<in> top1_product_topology_on I A TA" .
  qed

  show ?thesis
    by (rule equalityI[OF hLeft_sub hRight_sub])
qed

(** from \S19 Theorem 19.4 (Products of Hausdorff spaces are Hausdorff) [top1.tex] **)
theorem Theorem_19_4_box:
  assumes hH: "\<forall>i\<in>I. is_hausdorff_on (X i) (T i)"
  shows "is_hausdorff_on (top1_PiE I X) (top1_box_topology_on I X T)"
proof -
  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
    using hH unfolding is_hausdorff_on_def by blast

  have hTopBox: "is_topology_on (top1_PiE I X) (top1_box_topology_on I X T)"
    by (rule top1_box_topology_on_is_topology_on[OF hTop])

  have hBasis: "is_basis_on (top1_PiE I X) (top1_box_basis_on I X T)"
    by (rule top1_box_basis_is_basis_on[OF hTop])

  show ?thesis
    unfolding is_hausdorff_on_def
  proof (intro conjI)
    show "is_topology_on (top1_PiE I X) (top1_box_topology_on I X T)"
      by (rule hTopBox)

    show "\<forall>f\<in>top1_PiE I X. \<forall>g\<in>top1_PiE I X. f \<noteq> g \<longrightarrow>
            (\<exists>U V.
                neighborhood_of f (top1_PiE I X) (top1_box_topology_on I X T) U \<and>
                neighborhood_of g (top1_PiE I X) (top1_box_topology_on I X T) V \<and>
                U \<inter> V = {})"
    proof (intro ballI impI)
      fix f g
      assume hf: "f \<in> top1_PiE I X"
      assume hg: "g \<in> top1_PiE I X"
      assume hneq: "f \<noteq> g"

      obtain i where hi: "i \<in> I" and hfi: "f i \<noteq> g i"
        using top1_PiE_neq_imp_coord_neq[OF hf hg hneq] by blast

      have hHi: "is_hausdorff_on (X i) (T i)"
        using hH hi by blast
      have hTopi: "is_topology_on (X i) (T i)"
        using hHi unfolding is_hausdorff_on_def by blast
      have hSep:
        "\<forall>x\<in>X i. \<forall>y\<in>X i. x \<noteq> y \<longrightarrow>
           (\<exists>U V.
              neighborhood_of x (X i) (T i) U \<and>
              neighborhood_of y (X i) (T i) V \<and> U \<inter> V = {})"
        using hHi unfolding is_hausdorff_on_def by blast

      have hfiX: "f i \<in> X i"
        using hf hi unfolding top1_PiE_iff by blast
      have hgiX: "g i \<in> X i"
        using hg hi unfolding top1_PiE_iff by blast

      obtain Ui Vi where hUi: "neighborhood_of (f i) (X i) (T i) Ui"
        and hVi: "neighborhood_of (g i) (X i) (T i) Vi"
        and hdisj: "Ui \<inter> Vi = {}"
        using hSep hfiX hgiX hfi by blast

      have hXi: "X i \<in> T i"
        using hTopi unfolding is_topology_on_def by blast
      have hUi_open: "Ui \<in> T i"
        using hUi unfolding neighborhood_of_def by blast
      have hVi_open: "Vi \<in> T i"
        using hVi unfolding neighborhood_of_def by blast
      have hUiX_open: "Ui \<inter> X i \<in> T i"
        by (rule topology_inter2[OF hTopi hUi_open hXi])
      have hViX_open: "Vi \<inter> X i \<in> T i"
        by (rule topology_inter2[OF hTopi hVi_open hXi])

      define WU where "WU = (\<lambda>j. if j = i then Ui \<inter> X i else X j)"
      define WV where "WV = (\<lambda>j. if j = i then Vi \<inter> X i else X j)"

      have hWU_basis: "top1_PiE I WU \<in> top1_box_basis_on I X T"
      proof -
        have hWU: "\<forall>j\<in>I. WU j \<in> T j \<and> WU j \<subseteq> X j"
        proof (intro ballI)
          fix j assume hj: "j \<in> I"
          have hTopj: "is_topology_on (X j) (T j)"
            using hTop hj by blast
          have hXj: "X j \<in> T j"
            using hTopj unfolding is_topology_on_def by blast
          show "WU j \<in> T j \<and> WU j \<subseteq> X j"
          proof (cases "j = i")
            case True
            have hTji: "T j = T i"
              using True by simp
            have hXji: "X j = X i"
              using True by simp
            have hWUj: "WU j = Ui \<inter> X i"
              unfolding WU_def using True by simp
            show ?thesis
              unfolding hWUj
              apply (intro conjI)
               apply (simp add: hTji hUiX_open)
              apply (simp add: hXji)
              done
          next
            case False
            have hWUj: "WU j = X j"
              unfolding WU_def using False by simp
            show ?thesis
              unfolding hWUj using hXj by simp
          qed
        qed
        show ?thesis
          unfolding top1_box_basis_on_def
          apply (rule CollectI)
          apply (rule exI[where x=WU])
          apply (intro conjI)
           apply (simp add: WU_def)
          apply (rule hWU)
          done
      qed

      have hWV_basis: "top1_PiE I WV \<in> top1_box_basis_on I X T"
      proof -
        have hWV: "\<forall>j\<in>I. WV j \<in> T j \<and> WV j \<subseteq> X j"
        proof (intro ballI)
          fix j assume hj: "j \<in> I"
          have hTopj: "is_topology_on (X j) (T j)"
            using hTop hj by blast
          have hXj: "X j \<in> T j"
            using hTopj unfolding is_topology_on_def by blast
          show "WV j \<in> T j \<and> WV j \<subseteq> X j"
          proof (cases "j = i")
            case True
            have hTji: "T j = T i"
              using True by simp
            have hXji: "X j = X i"
              using True by simp
            have hWVj: "WV j = Vi \<inter> X i"
              unfolding WV_def using True by simp
            show ?thesis
              unfolding hWVj
              apply (intro conjI)
               apply (simp add: hTji hViX_open)
              apply (simp add: hXji)
              done
          next
            case False
            have hWVj: "WV j = X j"
              unfolding WV_def using False by simp
            show ?thesis
              unfolding hWVj using hXj by simp
          qed
        qed
        show ?thesis
          unfolding top1_box_basis_on_def
          apply (rule CollectI)
          apply (rule exI[where x=WV])
          apply (intro conjI)
           apply (simp add: WV_def)
          apply (rule hWV)
          done
      qed

      have hUopen: "top1_PiE I WU \<in> top1_box_topology_on I X T"
        unfolding top1_box_topology_on_def
        by (rule basis_elem_open_in_generated_topology[OF hBasis hWU_basis])
      have hVopen: "top1_PiE I WV \<in> top1_box_topology_on I X T"
        unfolding top1_box_topology_on_def
        by (rule basis_elem_open_in_generated_topology[OF hBasis hWV_basis])

      have hfU: "f \<in> top1_PiE I WU"
      proof -
        have hfiUi: "f i \<in> Ui"
          using hUi unfolding neighborhood_of_def by blast
        have hfiUix: "f i \<in> Ui \<inter> X i"
          using hfiUi hfiX by blast
        have hmem: "\<forall>j\<in>I. f j \<in> WU j"
        proof (intro ballI)
          fix j assume hj: "j \<in> I"
          show "f j \<in> WU j"
          proof (cases "j = i")
            case True
            show ?thesis
              unfolding WU_def True using hfiUix by simp
	          next
	            case False
	            have hWUj: "WU j = X j"
	              unfolding WU_def using False by simp
	            have hfjX: "f j \<in> X j"
	              using hf hj unfolding top1_PiE_iff by blast
	            show ?thesis
	              unfolding hWUj using hfjX by simp
	          qed
	        qed
	        have hfext: "\<forall>j. j \<notin> I \<longrightarrow> f j = undefined"
	          using hf unfolding top1_PiE_iff by blast
        show ?thesis
          unfolding top1_PiE_iff using hmem hfext by blast
      qed

      have hgV: "g \<in> top1_PiE I WV"
      proof -
        have hgiVi: "g i \<in> Vi"
          using hVi unfolding neighborhood_of_def by blast
        have hgiVix: "g i \<in> Vi \<inter> X i"
          using hgiVi hgiX by blast
        have hmem: "\<forall>j\<in>I. g j \<in> WV j"
        proof (intro ballI)
          fix j assume hj: "j \<in> I"
          show "g j \<in> WV j"
          proof (cases "j = i")
            case True
            show ?thesis
              unfolding WV_def True using hgiVix by simp
	          next
	            case False
	            have hWVj: "WV j = X j"
	              unfolding WV_def using False by simp
	            have hgjX: "g j \<in> X j"
	              using hg hj unfolding top1_PiE_iff by blast
	            show ?thesis
	              unfolding hWVj using hgjX by simp
	          qed
	        qed
	        have hgext: "\<forall>j. j \<notin> I \<longrightarrow> g j = undefined"
	          using hg unfolding top1_PiE_iff by blast
        show ?thesis
          unfolding top1_PiE_iff using hmem hgext by blast
      qed

      have hUVdisj: "top1_PiE I WU \<inter> top1_PiE I WV = {}"
      proof (rule equalityI)
        show "top1_PiE I WU \<inter> top1_PiE I WV \<subseteq> {}"
	        proof (rule subsetI)
	          fix h assume hh: "h \<in> top1_PiE I WU \<inter> top1_PiE I WV"
	          have hWU: "h \<in> top1_PiE I WU"
	            using hh by simp
	          have hWV: "h \<in> top1_PiE I WV"
	            using hh by simp
	          have h1: "\<forall>j\<in>I. h j \<in> WU j"
	            using hWU unfolding top1_PiE_iff by simp
	          have h2: "\<forall>j\<in>I. h j \<in> WV j"
	            using hWV unfolding top1_PiE_iff by simp
	          have "h i \<in> WU i"
	            using h1 hi by blast
	          hence hiU: "h i \<in> Ui \<inter> X i"
	            unfolding WU_def by simp
          have "h i \<in> WV i"
            using h2 hi by blast
          hence hiV: "h i \<in> Vi \<inter> X i"
            unfolding WV_def by simp
          have "h i \<in> Ui \<inter> Vi"
            using hiU hiV by blast
          thus "h \<in> {}"
            using hdisj by blast
        qed
        show "{} \<subseteq> top1_PiE I WU \<inter> top1_PiE I WV"
          by simp
      qed

      show "\<exists>U V.
              neighborhood_of f (top1_PiE I X) (top1_box_topology_on I X T) U \<and>
              neighborhood_of g (top1_PiE I X) (top1_box_topology_on I X T) V \<and>
              U \<inter> V = {}"
        apply (rule exI[where x="top1_PiE I WU"])
        apply (rule exI[where x="top1_PiE I WV"])
        unfolding neighborhood_of_def
        apply (intro conjI)
          apply (rule hUopen)
         apply (rule hfU)
          apply (rule hVopen)
         apply (rule hgV)
        apply (rule hUVdisj)
        done
    qed
  qed
qed

theorem Theorem_19_4_product:
  assumes hH: "\<forall>i\<in>I. is_hausdorff_on (X i) (T i)"
  shows "is_hausdorff_on (top1_PiE I X) (top1_product_topology_on I X T)"
proof -
  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
    using hH unfolding is_hausdorff_on_def by blast
  have hTopProd: "is_topology_on (top1_PiE I X) (top1_product_topology_on I X T)"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  show ?thesis
    unfolding is_hausdorff_on_def
  proof (intro conjI)
    show "is_topology_on (top1_PiE I X) (top1_product_topology_on I X T)"
      by (rule hTopProd)

    show "\<forall>f\<in>top1_PiE I X. \<forall>g\<in>top1_PiE I X. f \<noteq> g \<longrightarrow>
            (\<exists>U V.
                neighborhood_of f (top1_PiE I X) (top1_product_topology_on I X T) U \<and>
                neighborhood_of g (top1_PiE I X) (top1_product_topology_on I X T) V \<and>
                U \<inter> V = {})"
    proof (intro ballI impI)
      fix f g
      assume hf: "f \<in> top1_PiE I X"
      assume hg: "g \<in> top1_PiE I X"
      assume hneq: "f \<noteq> g"

      obtain i where hi: "i \<in> I" and hfi: "f i \<noteq> g i"
        using top1_PiE_neq_imp_coord_neq[OF hf hg hneq] by blast

      have hHi: "is_hausdorff_on (X i) (T i)"
        using hH hi by blast
      have hTopi: "is_topology_on (X i) (T i)"
        using hHi unfolding is_hausdorff_on_def by blast
      have hSep:
        "\<forall>x\<in>X i. \<forall>y\<in>X i. x \<noteq> y \<longrightarrow>
           (\<exists>U V.
              neighborhood_of x (X i) (T i) U \<and>
              neighborhood_of y (X i) (T i) V \<and> U \<inter> V = {})"
        using hHi unfolding is_hausdorff_on_def by blast

      have hfiX: "f i \<in> X i"
        using hf hi unfolding top1_PiE_iff by blast
      have hgiX: "g i \<in> X i"
        using hg hi unfolding top1_PiE_iff by blast

      obtain Ui Vi where hUi: "neighborhood_of (f i) (X i) (T i) Ui"
        and hVi: "neighborhood_of (g i) (X i) (T i) Vi"
        and hdisj: "Ui \<inter> Vi = {}"
        using hSep hfiX hgiX hfi by blast

      have hXi: "X i \<in> T i"
        using hTopi unfolding is_topology_on_def by blast
      have hUi_open: "Ui \<in> T i"
        using hUi unfolding neighborhood_of_def by blast
      have hVi_open: "Vi \<in> T i"
        using hVi unfolding neighborhood_of_def by blast
      have hUiX_open: "Ui \<inter> X i \<in> T i"
        by (rule topology_inter2[OF hTopi hUi_open hXi])
      have hViX_open: "Vi \<inter> X i \<in> T i"
        by (rule topology_inter2[OF hTopi hVi_open hXi])

      define U0 where "U0 = {h \<in> top1_PiE I X. h i \<in> Ui \<inter> X i}"
      define V0 where "V0 = {h \<in> top1_PiE I X. h i \<in> Vi \<inter> X i}"

      have hproj_cont:
        "top1_continuous_map_on (top1_PiE I X) (top1_product_topology_on I X T) (X i) (T i) (\<lambda>h. h i)"
        by (rule top1_continuous_map_on_product_projection[OF hTop hi])

      have hU0open: "U0 \<in> top1_product_topology_on I X T"
      proof -
        have hpre: "\<forall>W\<in>T i. {h \<in> top1_PiE I X. (\<lambda>h. h i) h \<in> W} \<in> top1_product_topology_on I X T"
          using hproj_cont unfolding top1_continuous_map_on_def by blast
        have "{h \<in> top1_PiE I X. h i \<in> Ui \<inter> X i} \<in> top1_product_topology_on I X T"
          by (rule bspec[OF hpre hUiX_open])
        thus ?thesis
          unfolding U0_def by simp
      qed

      have hV0open: "V0 \<in> top1_product_topology_on I X T"
      proof -
        have hpre: "\<forall>W\<in>T i. {h \<in> top1_PiE I X. (\<lambda>h. h i) h \<in> W} \<in> top1_product_topology_on I X T"
          using hproj_cont unfolding top1_continuous_map_on_def by blast
        have "{h \<in> top1_PiE I X. h i \<in> Vi \<inter> X i} \<in> top1_product_topology_on I X T"
          by (rule bspec[OF hpre hViX_open])
        thus ?thesis
          unfolding V0_def by simp
      qed

      have hfU0: "f \<in> U0"
      proof -
        have hfiUi: "f i \<in> Ui"
          using hUi unfolding neighborhood_of_def by blast
        have "f i \<in> Ui \<inter> X i"
          using hfiUi hfiX by blast
        thus ?thesis
          unfolding U0_def using hf by simp
      qed
      have hgV0: "g \<in> V0"
      proof -
        have hgiVi: "g i \<in> Vi"
          using hVi unfolding neighborhood_of_def by blast
        have "g i \<in> Vi \<inter> X i"
          using hgiVi hgiX by blast
        thus ?thesis
          unfolding V0_def using hg by simp
      qed

      have hU0V0_disj: "U0 \<inter> V0 = {}"
      proof (rule equalityI)
        show "U0 \<inter> V0 \<subseteq> {}"
        proof (rule subsetI)
          fix h assume hh: "h \<in> U0 \<inter> V0"
          have hUi': "h i \<in> Ui \<inter> X i"
            using hh unfolding U0_def by simp
          have hVi': "h i \<in> Vi \<inter> X i"
            using hh unfolding V0_def by simp
          have "h i \<in> Ui \<inter> Vi"
            using hUi' hVi' by blast
          thus "h \<in> {}"
            using hdisj by blast
        qed
        show "{} \<subseteq> U0 \<inter> V0"
          by simp
      qed

      show "\<exists>U V.
              neighborhood_of f (top1_PiE I X) (top1_product_topology_on I X T) U \<and>
              neighborhood_of g (top1_PiE I X) (top1_product_topology_on I X T) V \<and>
              U \<inter> V = {}"
        apply (rule exI[where x=U0])
        apply (rule exI[where x=V0])
        unfolding neighborhood_of_def
        apply (intro conjI)
          apply (rule hU0open)
         apply (rule hfU0)
          apply (rule hV0open)
         apply (rule hgV0)
        apply (rule hU0V0_disj)
        done
    qed
  qed
qed

(** from \S19 Theorem 19.5 (Closure in products) [top1.tex] **)
theorem Theorem_19_5_box:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  assumes hA: "\<forall>i\<in>I. A i \<subseteq> X i"
  shows "closure_on (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)
        = top1_PiE I (\<lambda>i. closure_on (X i) (T i) (A i))"
proof (rule equalityI)
  let ?PX = "top1_PiE I X"
  let ?PA = "top1_PiE I A"
  let ?TB = "top1_box_topology_on I X T"
  let ?C = "(\<lambda>i. closure_on (X i) (T i) (A i))"

  have hTopBox: "is_topology_on ?PX ?TB"
    by (rule top1_box_topology_on_is_topology_on[OF hTop])

  have hPA_PX: "?PA \<subseteq> ?PX"
    by (rule top1_PiE_mono[OF hA])

  show "closure_on ?PX ?TB ?PA \<subseteq> top1_PiE I ?C"
  proof (rule subsetI)
    fix x assume hxcl: "x \<in> closure_on ?PX ?TB ?PA"

    have hxPX: "x \<in> ?PX"
    proof -
      have "closure_on ?PX ?TB ?PA \<subseteq> ?PX"
        by (rule closure_on_subset_carrier[OF hTopBox hPA_PX])
      thus ?thesis
        using hxcl by blast
    qed

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hxPX unfolding top1_PiE_iff by blast

    have hxcl_prop: "\<forall>U. neighborhood_of x ?PX ?TB U \<longrightarrow> intersects U ?PA"
      by (rule iffD1[OF Theorem_17_5a[OF hTopBox hxPX hPA_PX], OF hxcl])

    have hxC: "\<forall>i\<in>I. x i \<in> ?C i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"

      have hTopi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hAiX: "A i \<subseteq> X i"
        using hA hi by blast

      have hxiX: "x i \<in> X i"
        using hxPX hi unfolding top1_PiE_iff by blast

      have hxcoord: "\<forall>U. neighborhood_of (x i) (X i) (T i) U \<longrightarrow> intersects U (A i)"
      proof (intro allI impI)
        fix U assume hnbd: "neighborhood_of (x i) (X i) (T i) U"

        have hUT: "U \<in> T i" and hxiU: "x i \<in> U"
          using hnbd unfolding neighborhood_of_def by blast+

        have hXi: "X i \<in> T i"
          using hTopi unfolding is_topology_on_def by blast

        have hUiX_open: "U \<inter> X i \<in> T i"
          by (rule topology_inter2[OF hTopi hUT hXi])

        define V where "V = U \<inter> X i"
        define W where "W = (\<lambda>j. if j = i then V else X j)"

        have hWbasis: "top1_PiE I W \<in> top1_box_basis_on I X T"
        proof -
          have hW: "\<forall>j\<in>I. W j \<in> T j \<and> W j \<subseteq> X j"
          proof (intro ballI)
            fix j assume hj: "j \<in> I"
            have hTopj: "is_topology_on (X j) (T j)"
              using hTop hj by blast
            have hXj: "X j \<in> T j"
              using hTopj unfolding is_topology_on_def by blast
            show "W j \<in> T j \<and> W j \<subseteq> X j"
            proof (cases "j = i")
              case True
              have "W j = V"
                unfolding W_def using True by simp
              moreover have "V \<in> T i"
                unfolding V_def using hUiX_open by simp
              moreover have "V \<subseteq> X i"
                unfolding V_def by blast
              ultimately show ?thesis
                using True by simp
            next
              case False
              have "W j = X j"
                unfolding W_def using False by simp
              thus ?thesis
                using hXj by simp
            qed
          qed
          show ?thesis
            unfolding top1_box_basis_on_def
            apply (rule CollectI)
            apply (rule exI[where x=W])
            using hW by blast
        qed

        have hBasisBox: "is_basis_on ?PX (top1_box_basis_on I X T)"
          by (rule top1_box_basis_is_basis_on[OF hTop])

        have hWopen: "top1_PiE I W \<in> ?TB"
          unfolding top1_box_topology_on_def
          by (rule basis_elem_open_in_generated_topology[OF hBasisBox hWbasis])

        have hxW: "x \<in> top1_PiE I W"
        proof -
          have hxmem: "\<forall>j\<in>I. x j \<in> W j"
          proof (intro ballI)
            fix j assume hj: "j \<in> I"
            show "x j \<in> W j"
            proof (cases "j = i")
              case True
              have "W j = V"
                unfolding W_def using True by simp
              moreover have "x i \<in> V"
                unfolding V_def using hxiU hxiX by blast
              ultimately show ?thesis
                using True by simp
            next
              case False
              have "W j = X j"
                unfolding W_def using False by simp
              moreover have "x j \<in> X j"
                using hxPX hj unfolding top1_PiE_iff by blast
              ultimately show ?thesis
                by simp
            qed
          qed
          show ?thesis
            unfolding top1_PiE_iff using hxmem hxext by blast
        qed

        have hnbdW: "neighborhood_of x ?PX ?TB (top1_PiE I W)"
          unfolding neighborhood_of_def using hWopen hxW by blast

        have hinter: "intersects (top1_PiE I W) ?PA"
          using hxcl_prop hnbdW by blast

	        obtain y where hy: "y \<in> top1_PiE I W \<inter> ?PA"
	          using hinter unfolding intersects_def by blast
	
	        have hyV: "y i \<in> V"
	        proof -
	          have hyW: "y \<in> top1_PiE I W"
	            using hy by simp
	          have "\<forall>j\<in>I. y j \<in> W j"
	            using hyW unfolding top1_PiE_iff by blast
	          hence "y i \<in> W i"
	            using hi by blast
	          thus ?thesis
	            unfolding W_def by simp
	        qed
	        have hyAi: "y i \<in> A i"
	        proof -
	          have hyA: "y \<in> top1_PiE I A"
	            using hy by simp
	          have "\<forall>j\<in>I. y j \<in> A j"
	            using hyA unfolding top1_PiE_iff by blast
	          thus ?thesis
	            using hi by blast
	        qed

        have hyU': "y i \<in> U"
          using hyV unfolding V_def by blast
        have "y i \<in> U \<inter> A i"
          using hyU' hyAi by blast
        thus "intersects U (A i)"
          unfolding intersects_def by blast
      qed

      show "x i \<in> closure_on (X i) (T i) (A i)"
        by (rule iffD2[OF Theorem_17_5a[OF hTopi hxiX hAiX], OF hxcoord])
    qed

    show "x \<in> top1_PiE I ?C"
      unfolding top1_PiE_iff using hxC hxext by blast
  qed

  show "top1_PiE I ?C \<subseteq> closure_on ?PX ?TB ?PA"
  proof (rule subsetI)
    fix x assume hx: "x \<in> top1_PiE I ?C"

    have hCsub: "\<forall>i\<in>I. ?C i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hTopi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hAiX: "A i \<subseteq> X i"
        using hA hi by blast
      show "?C i \<subseteq> X i"
        by (rule closure_on_subset_carrier[OF hTopi hAiX])
    qed

    have hxPX: "x \<in> ?PX"
      by (rule subsetD[OF top1_PiE_mono[OF hCsub], OF hx])

    have hxcoord: "\<forall>i\<in>I. x i \<in> ?C i"
      using hx unfolding top1_PiE_iff by blast

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hx unfolding top1_PiE_iff by blast

    have hx_intersects: "\<forall>U. neighborhood_of x ?PX ?TB U \<longrightarrow> intersects U ?PA"
    proof (intro allI impI)
      fix U assume hnbd: "neighborhood_of x ?PX ?TB U"
      have hUopen: "U \<in> ?TB" and hxU: "x \<in> U"
        using hnbd unfolding neighborhood_of_def by blast+

      have hUgen: "U \<in> topology_generated_by_basis ?PX (top1_box_basis_on I X T)"
        using hUopen unfolding top1_box_topology_on_def by simp

      have hcov: "\<forall>z\<in>U. \<exists>b\<in>top1_box_basis_on I X T. z \<in> b \<and> b \<subseteq> U"
        using hUgen unfolding topology_generated_by_basis_def by blast

      obtain b where hb: "b \<in> top1_box_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
        using hcov hxU by blast

      obtain U0 where hbdef: "b = top1_PiE I U0"
        and hU0: "\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i"
        using hb unfolding top1_box_basis_on_def by blast

      have hxU0: "\<forall>i\<in>I. x i \<in> U0 i"
        using hxb unfolding hbdef top1_PiE_iff by blast

      have hchoose: "\<forall>i\<in>I. \<exists>y. y \<in> U0 i \<inter> A i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have hTopi: "is_topology_on (X i) (T i)"
          using hTop hi by blast
        have hAiX: "A i \<subseteq> X i"
          using hA hi by blast

        have hxiX: "x i \<in> X i"
          using hxPX hi unfolding top1_PiE_iff by blast
        have hxiU0: "x i \<in> U0 i"
          using hxU0 hi by blast
        have hU0i: "U0 i \<in> T i"
          using hU0 hi by blast

        have hxcl_i_prop: "\<forall>V. neighborhood_of (x i) (X i) (T i) V \<longrightarrow> intersects V (A i)"
          by (rule iffD1[OF Theorem_17_5a[OF hTopi hxiX hAiX], OF hxcoord[rule_format, OF hi]])

        have "intersects (U0 i) (A i)"
          using hxcl_i_prop hU0i hxiU0 unfolding neighborhood_of_def by blast
        thus "\<exists>y. y \<in> U0 i \<inter> A i"
          unfolding intersects_def by blast
      qed

      obtain y0 where hy0: "\<forall>i\<in>I. y0 i \<in> U0 i \<inter> A i"
        using bchoice[OF hchoose] by blast

      define y where "y = (\<lambda>i. if i \<in> I then y0 i else undefined)"

      have hyext: "\<forall>i. i \<notin> I \<longrightarrow> y i = undefined"
        unfolding y_def by simp

	      have hyA: "\<forall>i\<in>I. y i \<in> A i"
		      proof (intro ballI)
		        fix i assume hi: "i \<in> I"
		        have "y i = y0 i"
		          unfolding y_def using hi by simp
		        moreover have "y0 i \<in> U0 i \<inter> A i"
		          using hy0 hi by blast
		        ultimately show "y i \<in> A i"
		        proof -
		          have "y0 i \<in> A i"
		            using \<open>y0 i \<in> U0 i \<inter> A i\<close> by blast
		          thus ?thesis
		            using \<open>y i = y0 i\<close> by simp
		        qed
		      qed
	      have hyU0: "\<forall>i\<in>I. y i \<in> U0 i"
		      proof (intro ballI)
		        fix i assume hi: "i \<in> I"
		        have "y i = y0 i"
		          unfolding y_def using hi by simp
		        moreover have "y0 i \<in> U0 i \<inter> A i"
		          using hy0 hi by blast
		        ultimately show "y i \<in> U0 i"
		        proof -
		          have "y0 i \<in> U0 i"
		            using \<open>y0 i \<in> U0 i \<inter> A i\<close> by blast
		          thus ?thesis
		            using \<open>y i = y0 i\<close> by simp
		        qed
		      qed

      have hyPA: "y \<in> ?PA"
        unfolding top1_PiE_iff using hyA hyext by blast
      have hyb: "y \<in> b"
        unfolding hbdef top1_PiE_iff using hyU0 hyext by blast

      have "y \<in> U \<inter> ?PA"
        using hyPA hyb hbU by blast
      thus "intersects U ?PA"
        unfolding intersects_def by blast
    qed

    show "x \<in> closure_on ?PX ?TB ?PA"
      by (rule iffD2[OF Theorem_17_5a[OF hTopBox hxPX hPA_PX], OF hx_intersects])
  qed
qed

theorem Theorem_19_5_product:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  assumes hA: "\<forall>i\<in>I. A i \<subseteq> X i"
  shows "closure_on (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)
        = top1_PiE I (\<lambda>i. closure_on (X i) (T i) (A i))"
proof (rule equalityI)
  let ?PX = "top1_PiE I X"
  let ?PA = "top1_PiE I A"
  let ?TP = "top1_product_topology_on I X T"
  let ?C = "(\<lambda>i. closure_on (X i) (T i) (A i))"

  have hTopProd: "is_topology_on ?PX ?TP"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  have hPA_PX: "?PA \<subseteq> ?PX"
    by (rule top1_PiE_mono[OF hA])

  show "closure_on ?PX ?TP ?PA \<subseteq> top1_PiE I ?C"
  proof (rule subsetI)
    fix x assume hxcl: "x \<in> closure_on ?PX ?TP ?PA"

    have hxPX: "x \<in> ?PX"
    proof -
      have "closure_on ?PX ?TP ?PA \<subseteq> ?PX"
        by (rule closure_on_subset_carrier[OF hTopProd hPA_PX])
      thus ?thesis
        using hxcl by blast
    qed

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hxPX unfolding top1_PiE_iff by blast

    have hxcl_prop: "\<forall>U. neighborhood_of x ?PX ?TP U \<longrightarrow> intersects U ?PA"
      by (rule iffD1[OF Theorem_17_5a[OF hTopProd hxPX hPA_PX], OF hxcl])

    have hxC: "\<forall>i\<in>I. x i \<in> ?C i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"

      have hTopi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hAiX: "A i \<subseteq> X i"
        using hA hi by blast

      have hxiX: "x i \<in> X i"
        using hxPX hi unfolding top1_PiE_iff by blast

      have hxcoord: "\<forall>U. neighborhood_of (x i) (X i) (T i) U \<longrightarrow> intersects U (A i)"
      proof (intro allI impI)
        fix U assume hnbd: "neighborhood_of (x i) (X i) (T i) U"

        have hUT: "U \<in> T i" and hxiU: "x i \<in> U"
          using hnbd unfolding neighborhood_of_def by blast+

        have hXi: "X i \<in> T i"
          using hTopi unfolding is_topology_on_def by blast

        have hUiX_open: "U \<inter> X i \<in> T i"
          by (rule topology_inter2[OF hTopi hUT hXi])

        define V where "V = U \<inter> X i"
        define W where "W = (\<lambda>j. if j = i then V else X j)"

        have hWbasis: "top1_PiE I W \<in> top1_product_basis_on I X T"
        proof -
          have hW: "\<forall>j\<in>I. W j \<in> T j \<and> W j \<subseteq> X j"
          proof (intro ballI)
            fix j assume hj: "j \<in> I"
            have hTopj: "is_topology_on (X j) (T j)"
              using hTop hj by blast
            have hXj: "X j \<in> T j"
              using hTopj unfolding is_topology_on_def by blast
            show "W j \<in> T j \<and> W j \<subseteq> X j"
            proof (cases "j = i")
              case True
              have "W j = V"
                unfolding W_def using True by simp
              moreover have "V \<in> T i"
                unfolding V_def using hUiX_open by simp
              moreover have "V \<subseteq> X i"
                unfolding V_def by blast
              ultimately show ?thesis
                using True by simp
            next
              case False
              have "W j = X j"
                unfolding W_def using False by simp
              thus ?thesis
                using hXj by simp
            qed
          qed

          have hfin: "finite {j \<in> I. W j \<noteq> X j}"
            unfolding W_def by simp

          show ?thesis
            unfolding top1_product_basis_on_def
            apply (rule CollectI)
            apply (rule exI[where x=W])
            using hW hfin by blast
        qed

        have hBasisProd: "is_basis_on ?PX (top1_product_basis_on I X T)"
          by (rule top1_product_basis_is_basis_on[OF hTop])

        have hWopen: "top1_PiE I W \<in> ?TP"
          unfolding top1_product_topology_on_def
          by (rule basis_elem_open_in_generated_topology[OF hBasisProd hWbasis])

        have hxW: "x \<in> top1_PiE I W"
        proof -
          have hxmem: "\<forall>j\<in>I. x j \<in> W j"
          proof (intro ballI)
            fix j assume hj: "j \<in> I"
            show "x j \<in> W j"
            proof (cases "j = i")
              case True
              have "W j = V"
                unfolding W_def using True by simp
              moreover have "x i \<in> V"
                unfolding V_def using hxiU hxiX by blast
              ultimately show ?thesis
                using True by simp
            next
              case False
              have "W j = X j"
                unfolding W_def using False by simp
              moreover have "x j \<in> X j"
                using hxPX hj unfolding top1_PiE_iff by blast
              ultimately show ?thesis
                by simp
            qed
          qed
          show ?thesis
            unfolding top1_PiE_iff using hxmem hxext by blast
        qed

        have hnbdW: "neighborhood_of x ?PX ?TP (top1_PiE I W)"
          unfolding neighborhood_of_def using hWopen hxW by blast

        have hinter: "intersects (top1_PiE I W) ?PA"
          using hxcl_prop hnbdW by blast

	        obtain y where hy: "y \<in> top1_PiE I W \<inter> ?PA"
	          using hinter unfolding intersects_def by blast
	
	        have hyV: "y i \<in> V"
	        proof -
	          have hyW: "y \<in> top1_PiE I W"
	            using hy by simp
	          have "\<forall>j\<in>I. y j \<in> W j"
	            using hyW unfolding top1_PiE_iff by blast
	          hence "y i \<in> W i"
	            using hi by blast
	          thus ?thesis
	            unfolding W_def by simp
	        qed
	        have hyAi: "y i \<in> A i"
	        proof -
	          have hyA: "y \<in> top1_PiE I A"
	            using hy by simp
	          have "\<forall>j\<in>I. y j \<in> A j"
	            using hyA unfolding top1_PiE_iff by blast
	          thus ?thesis
	            using hi by blast
	        qed

        have hyU': "y i \<in> U"
          using hyV unfolding V_def by blast
        have "y i \<in> U \<inter> A i"
          using hyU' hyAi by blast
        thus "intersects U (A i)"
          unfolding intersects_def by blast
      qed

      show "x i \<in> closure_on (X i) (T i) (A i)"
        by (rule iffD2[OF Theorem_17_5a[OF hTopi hxiX hAiX], OF hxcoord])
    qed

    show "x \<in> top1_PiE I ?C"
      unfolding top1_PiE_iff using hxC hxext by blast
  qed

  show "top1_PiE I ?C \<subseteq> closure_on ?PX ?TP ?PA"
  proof (rule subsetI)
    fix x assume hx: "x \<in> top1_PiE I ?C"

    have hCsub: "\<forall>i\<in>I. ?C i \<subseteq> X i"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hTopi: "is_topology_on (X i) (T i)"
        using hTop hi by blast
      have hAiX: "A i \<subseteq> X i"
        using hA hi by blast
      show "?C i \<subseteq> X i"
        by (rule closure_on_subset_carrier[OF hTopi hAiX])
    qed

    have hxPX: "x \<in> ?PX"
      by (rule subsetD[OF top1_PiE_mono[OF hCsub], OF hx])

    have hxcoord: "\<forall>i\<in>I. x i \<in> ?C i"
      using hx unfolding top1_PiE_iff by blast

    have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
      using hx unfolding top1_PiE_iff by blast

    have hx_intersects: "\<forall>U. neighborhood_of x ?PX ?TP U \<longrightarrow> intersects U ?PA"
    proof (intro allI impI)
      fix U assume hnbd: "neighborhood_of x ?PX ?TP U"
      have hUopen: "U \<in> ?TP" and hxU: "x \<in> U"
        using hnbd unfolding neighborhood_of_def by blast+

      have hUgen: "U \<in> topology_generated_by_basis ?PX (top1_product_basis_on I X T)"
        using hUopen unfolding top1_product_topology_on_def by simp

      have hcov: "\<forall>z\<in>U. \<exists>b\<in>top1_product_basis_on I X T. z \<in> b \<and> b \<subseteq> U"
        using hUgen unfolding topology_generated_by_basis_def by blast

      obtain b where hb: "b \<in> top1_product_basis_on I X T" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
        using hcov hxU by blast

      obtain U0 where hbdef: "b = top1_PiE I U0"
        and hU0: "(\<forall>i\<in>I. U0 i \<in> T i \<and> U0 i \<subseteq> X i)"
        and hfin0: "finite {i \<in> I. U0 i \<noteq> X i}"
        using hb unfolding top1_product_basis_on_def by blast

      have hxU0: "\<forall>i\<in>I. x i \<in> U0 i"
        using hxb unfolding hbdef top1_PiE_iff by blast

      have hchoose: "\<forall>i\<in>I. \<exists>y. y \<in> U0 i \<inter> A i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have hTopi: "is_topology_on (X i) (T i)"
          using hTop hi by blast
        have hAiX: "A i \<subseteq> X i"
          using hA hi by blast

        have hxiX: "x i \<in> X i"
          using hxPX hi unfolding top1_PiE_iff by blast
        have hxiU0: "x i \<in> U0 i"
          using hxU0 hi by blast
        have hU0i: "U0 i \<in> T i"
          using hU0 hi by blast

        have hxcl_i_prop: "\<forall>V. neighborhood_of (x i) (X i) (T i) V \<longrightarrow> intersects V (A i)"
          by (rule iffD1[OF Theorem_17_5a[OF hTopi hxiX hAiX], OF hxcoord[rule_format, OF hi]])

        have "intersects (U0 i) (A i)"
          using hxcl_i_prop hU0i hxiU0 unfolding neighborhood_of_def by blast
        thus "\<exists>y. y \<in> U0 i \<inter> A i"
          unfolding intersects_def by blast
      qed

      obtain y0 where hy0: "\<forall>i\<in>I. y0 i \<in> U0 i \<inter> A i"
        using bchoice[OF hchoose] by blast

      define y where "y = (\<lambda>i. if i \<in> I then y0 i else undefined)"

      have hyext: "\<forall>i. i \<notin> I \<longrightarrow> y i = undefined"
        unfolding y_def by simp

      have hyA: "\<forall>i\<in>I. y i \<in> A i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have "y i = y0 i"
          unfolding y_def using hi by simp
        moreover have "y0 i \<in> U0 i \<inter> A i"
          using hy0 hi by blast
        ultimately show "y i \<in> A i"
        proof -
          have "y0 i \<in> A i"
            using \<open>y0 i \<in> U0 i \<inter> A i\<close> by blast
          thus ?thesis
            using \<open>y i = y0 i\<close> by simp
        qed
      qed
      have hyU0: "\<forall>i\<in>I. y i \<in> U0 i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have "y i = y0 i"
          unfolding y_def using hi by simp
        moreover have "y0 i \<in> U0 i \<inter> A i"
          using hy0 hi by blast
        ultimately show "y i \<in> U0 i"
        proof -
          have "y0 i \<in> U0 i"
            using \<open>y0 i \<in> U0 i \<inter> A i\<close> by blast
          thus ?thesis
            using \<open>y i = y0 i\<close> by simp
        qed
      qed

      have hyPA: "y \<in> ?PA"
        unfolding top1_PiE_iff using hyA hyext by blast
      have hyb: "y \<in> b"
        unfolding hbdef top1_PiE_iff using hyU0 hyext by blast

      have "y \<in> U \<inter> ?PA"
        using hyPA hyb hbU by blast
      thus "intersects U ?PA"
        unfolding intersects_def by blast
    qed

    show "x \<in> closure_on ?PX ?TP ?PA"
      by (rule iffD2[OF Theorem_17_5a[OF hTopProd hxPX hPA_PX], OF hx_intersects])
  qed
qed

(** Convenience wrappers so theorem numbers from \<open>top1.tex\<close> exist verbatim. **)

theorem Theorem_19_2:
  assumes hB: "\<forall>i\<in>I. basis_for (X i) (B i) (T i)"
  shows "basis_for (top1_PiE I X)
           {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}
           (top1_box_topology_on I X T)"
    and "basis_for (top1_PiE I X)
           {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}
           (top1_product_topology_on I X T)"
proof -
  show "basis_for (top1_PiE I X)
           {top1_PiE I U | U. \<forall>i\<in>I. U i \<in> B i}
           (top1_box_topology_on I X T)"
    by (rule Theorem_19_2_box[OF hB])
  show "basis_for (top1_PiE I X)
           {top1_PiE I U | U. (\<forall>i\<in>I. U i = X i \<or> U i \<in> B i) \<and> finite {i \<in> I. U i \<noteq> X i}}
           (top1_product_topology_on I X T)"
    by (rule Theorem_19_2_product[OF hB])
qed

theorem Theorem_19_3:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  assumes hA: "\<forall>i\<in>I. A i \<subseteq> X i"
  shows "top1_box_topology_on I A (\<lambda>i. subspace_topology (X i) (T i) (A i))
           = subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
    and "top1_product_topology_on I A (\<lambda>i. subspace_topology (X i) (T i) (A i))
           = subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
proof -
  show "top1_box_topology_on I A (\<lambda>i. subspace_topology (X i) (T i) (A i))
           = subspace_topology (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)"
    by (rule Theorem_19_3_box[OF hTop hA])
  show "top1_product_topology_on I A (\<lambda>i. subspace_topology (X i) (T i) (A i))
           = subspace_topology (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)"
    by (rule Theorem_19_3_product[OF hTop hA])
qed

theorem Theorem_19_4:
  assumes hH: "\<forall>i\<in>I. is_hausdorff_on (X i) (T i)"
  shows "is_hausdorff_on (top1_PiE I X) (top1_box_topology_on I X T)"
    and "is_hausdorff_on (top1_PiE I X) (top1_product_topology_on I X T)"
proof -
  show "is_hausdorff_on (top1_PiE I X) (top1_box_topology_on I X T)"
    by (rule Theorem_19_4_box[OF hH])
  show "is_hausdorff_on (top1_PiE I X) (top1_product_topology_on I X T)"
    by (rule Theorem_19_4_product[OF hH])
qed

theorem Theorem_19_5:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (T i)"
  assumes hA: "\<forall>i\<in>I. A i \<subseteq> X i"
  shows "closure_on (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)
          = top1_PiE I (\<lambda>i. closure_on (X i) (T i) (A i))"
    and "closure_on (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)
          = top1_PiE I (\<lambda>i. closure_on (X i) (T i) (A i))"
proof -
  show "closure_on (top1_PiE I X) (top1_box_topology_on I X T) (top1_PiE I A)
          = top1_PiE I (\<lambda>i. closure_on (X i) (T i) (A i))"
    by (rule Theorem_19_5_box[OF hTop hA])
  show "closure_on (top1_PiE I X) (top1_product_topology_on I X T) (top1_PiE I A)
          = top1_PiE I (\<lambda>i. closure_on (X i) (T i) (A i))"
    by (rule Theorem_19_5_product[OF hTop hA])
qed

section \<open>\<S>20 The Metric Topology\<close>

(** from \S20 Definition (Metric) [top1.tex:~1512] **)
definition top1_metric_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "top1_metric_on X d \<longleftrightarrow>
     (\<forall>x\<in>X. 0 \<le> d x x) \<and>
     (\<forall>x\<in>X. \<forall>y\<in>X. 0 \<le> d x y) \<and>
     (\<forall>x\<in>X. \<forall>y\<in>X. d x y = 0 \<longleftrightarrow> x = y) \<and>
     (\<forall>x\<in>X. \<forall>y\<in>X. d x y = d y x) \<and>
     (\<forall>x\<in>X. \<forall>y\<in>X. \<forall>z\<in>X. d x z \<le> d x y + d y z)"

definition top1_ball_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set" where
  "top1_ball_on X d x e = {y \<in> X. d x y < e}"

definition top1_metric_basis_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set set" where
  "top1_metric_basis_on X d = {top1_ball_on X d x e | x e. x \<in> X \<and> 0 < e}"

definition top1_metric_topology_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set set" where
  "top1_metric_topology_on X d = topology_generated_by_basis X (top1_metric_basis_on X d)"

definition top1_metrizable_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_metrizable_on X T \<longleftrightarrow> (\<exists>d. top1_metric_on X d \<and> T = top1_metric_topology_on X d)"

(** The standard ball family forms a basis (for the metric topology) on the carrier. **)
lemma top1_metric_basis_is_basis_on:
  assumes hd: "top1_metric_on X d"
  shows "is_basis_on X (top1_metric_basis_on X d)"
proof (unfold is_basis_on_def, intro conjI)
  show "\<forall>b\<in>top1_metric_basis_on X d. b \<subseteq> X"
    unfolding top1_metric_basis_on_def top1_ball_on_def by blast

  show "\<forall>x\<in>X. \<exists>b\<in>top1_metric_basis_on X d. x \<in> b"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hdx: "d x x = 0"
      using hd hxX unfolding top1_metric_on_def by blast
    have hxball: "x \<in> top1_ball_on X d x 1"
      unfolding top1_ball_on_def using hxX hdx by simp
    show "\<exists>b\<in>top1_metric_basis_on X d. x \<in> b"
      unfolding top1_metric_basis_on_def
      apply (rule bexI[where x="top1_ball_on X d x 1"])
       apply (rule hxball)
      apply (rule CollectI)
      apply (rule exI[where x=x])
      apply (rule exI[where x="1::real"])
      using hxX by simp
  qed

  show "\<forall>b1\<in>top1_metric_basis_on X d. \<forall>b2\<in>top1_metric_basis_on X d. \<forall>x\<in>b1 \<inter> b2.
         \<exists>b3\<in>top1_metric_basis_on X d. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
  proof (intro ballI)
    fix b1 b2 x
    assume hb1: "b1 \<in> top1_metric_basis_on X d"
    assume hb2: "b2 \<in> top1_metric_basis_on X d"
    assume hx: "x \<in> b1 \<inter> b2"

    obtain x1 e1 where hx1X: "x1 \<in> X" and he1: "0 < e1" and hb1eq: "b1 = top1_ball_on X d x1 e1"
      using hb1 unfolding top1_metric_basis_on_def by blast
    obtain x2 e2 where hx2X: "x2 \<in> X" and he2: "0 < e2" and hb2eq: "b2 = top1_ball_on X d x2 e2"
      using hb2 unfolding top1_metric_basis_on_def by blast

    have hx1: "x \<in> top1_ball_on X d x1 e1" and hx2: "x \<in> top1_ball_on X d x2 e2"
      using hx unfolding hb1eq hb2eq by blast+
    have hxX: "x \<in> X"
      using hx1 unfolding top1_ball_on_def by blast
    have hdx1: "d x1 x < e1"
      using hx1 unfolding top1_ball_on_def by blast
    have hdx2: "d x2 x < e2"
      using hx2 unfolding top1_ball_on_def by blast

    define r where "r = min (e1 - d x1 x) (e2 - d x2 x)"
    have hr_pos: "0 < r"
      unfolding r_def using hdx1 hdx2 by linarith

    have hdx0: "d x x = 0"
      using hd hxX unfolding top1_metric_on_def by blast
    have hx_in_r: "x \<in> top1_ball_on X d x r"
      unfolding top1_ball_on_def using hxX hdx0 hr_pos by simp

    have htri: "\<forall>a\<in>X. \<forall>b\<in>X. \<forall>c\<in>X. d a c \<le> d a b + d b c"
      using hd unfolding top1_metric_on_def by blast

    have hsub: "top1_ball_on X d x r \<subseteq> b1 \<inter> b2"
    proof (rule subsetI)
      fix z assume hz: "z \<in> top1_ball_on X d x r"
      have hzX: "z \<in> X" and hdxz: "d x z < r"
        using hz unfolding top1_ball_on_def by blast+
      have hr_le1: "r \<le> e1 - d x1 x"
        unfolding r_def by simp
      have hr_le2: "r \<le> e2 - d x2 x"
        unfolding r_def by simp

      have hdx1z_le: "d x1 z \<le> d x1 x + d x z"
        using htri hx1X hxX hzX by blast
      have hdx2z_le: "d x2 z \<le> d x2 x + d x z"
        using htri hx2X hxX hzX by blast

      have hdx1z: "d x1 z < e1"
        using hdx1z_le hdxz hr_le1 by linarith
      have hdx2z: "d x2 z < e2"
        using hdx2z_le hdxz hr_le2 by linarith

      have hz1: "z \<in> top1_ball_on X d x1 e1"
        unfolding top1_ball_on_def using hzX hdx1z by blast
      have hz2: "z \<in> top1_ball_on X d x2 e2"
        unfolding top1_ball_on_def using hzX hdx2z by blast

      show "z \<in> b1 \<inter> b2"
        unfolding hb1eq hb2eq using hz1 hz2 by blast
    qed

    show "\<exists>b3\<in>top1_metric_basis_on X d. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
      unfolding top1_metric_basis_on_def
      apply (rule bexI[where x="top1_ball_on X d x r"])
       apply (intro conjI)
        apply (rule hx_in_r)
       apply (rule hsub)
      apply (rule CollectI)
      apply (rule exI[where x=x])
      apply (rule exI[where x=r])
      using hxX hr_pos by simp
  qed
qed

lemma top1_ball_open_in_metric_topology:
  assumes hd: "top1_metric_on X d"
  assumes hxX: "x \<in> X"
  assumes he: "0 < e"
  shows "top1_ball_on X d x e \<in> top1_metric_topology_on X d"
proof -
  have hB: "is_basis_on X (top1_metric_basis_on X d)"
    by (rule top1_metric_basis_is_basis_on[OF hd])
  have hb: "top1_ball_on X d x e \<in> top1_metric_basis_on X d"
    unfolding top1_metric_basis_on_def using hxX he by blast
  have hopen: "top1_ball_on X d x e \<in> topology_generated_by_basis X (top1_metric_basis_on X d)"
    by (rule basis_elem_open_in_generated_topology[OF hB hb])
  show ?thesis
    unfolding top1_metric_topology_on_def using hopen by simp
qed

lemma top1_metric_topology_on_is_topology_on:
  assumes hd: "top1_metric_on X d"
  shows "is_topology_on X (top1_metric_topology_on X d)"
proof -
  have hB: "is_basis_on X (top1_metric_basis_on X d)"
    by (rule top1_metric_basis_is_basis_on[OF hd])
  have hTop: "is_topology_on X (topology_generated_by_basis X (top1_metric_basis_on X d))"
    by (rule topology_generated_by_basis_is_topology_on[OF hB])
  show ?thesis
    unfolding top1_metric_topology_on_def using hTop by simp
qed

(** Standard bounded metric corresponding to a given metric (top1.tex, Theorem 20.1). **)
definition top1_bounded_metric :: "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
  "top1_bounded_metric d x y = min (d x y) 1"

lemma top1_bounded_metric_on:
  assumes hd: "top1_metric_on X d"
  shows "top1_metric_on X (top1_bounded_metric d)"
proof -
  have h0iff: "\<forall>x\<in>X. \<forall>y\<in>X. d x y = 0 \<longleftrightarrow> x = y"
    using hd unfolding top1_metric_on_def by blast
  have hsym: "\<forall>x\<in>X. \<forall>y\<in>X. d x y = d y x"
    using hd unfolding top1_metric_on_def by blast
  have htri: "\<forall>x\<in>X. \<forall>y\<in>X. \<forall>z\<in>X. d x z \<le> d x y + d y z"
    using hd unfolding top1_metric_on_def by blast

  show ?thesis
    unfolding top1_metric_on_def top1_bounded_metric_def
  proof (intro conjI)
    show "\<forall>x\<in>X. 0 \<le> min (d x x) 1"
      using hd unfolding top1_metric_on_def by simp
    show "\<forall>x\<in>X. \<forall>y\<in>X. 0 \<le> min (d x y) 1"
      using hd unfolding top1_metric_on_def by simp
    show "\<forall>x\<in>X. \<forall>y\<in>X. (min (d x y) 1 = 0) = (x = y)"
    proof (intro ballI)
      fix x y assume hxX: "x \<in> X" and hyX: "y \<in> X"
      have hd0: "d x y = 0 \<longleftrightarrow> x = y"
        using h0iff hxX hyX by blast
      show "(min (d x y) 1 = 0) = (x = y)"
      proof (cases "d x y \<le> 1")
        case True
        then have "min (d x y) 1 = d x y"
          by simp
        thus ?thesis
          by (simp add: hd0)
      next
        case False
        then have "min (d x y) 1 = 1"
          by simp
        thus ?thesis
        proof -
          have hxy: "x \<noteq> y"
          proof
            assume hxy': "x = y"
            have "d x y = 0"
              using hxy' hd0 by simp
            hence "d x y \<le> 1"
              by simp
            thus False
              using False by blast
          qed
          show "(min (d x y) 1 = 0) = (x = y)"
            by (simp add: \<open>min (d x y) 1 = 1\<close> hxy)
        qed
      qed
    qed
    show "\<forall>x\<in>X. \<forall>y\<in>X. min (d x y) 1 = min (d y x) 1"
      using hsym by simp
    show "\<forall>x\<in>X. \<forall>y\<in>X. \<forall>z\<in>X. min (d x z) 1 \<le> min (d x y) 1 + min (d y z) 1"
    proof (intro ballI)
      fix x y z assume hxX: "x \<in> X" and hyX: "y \<in> X" and hzX: "z \<in> X"
      have htri_xyz: "d x z \<le> d x y + d y z"
        using htri hxX hyX hzX by blast
      show "min (d x z) 1 \<le> min (d x y) 1 + min (d y z) 1"
      proof (cases "d x y < 1")
        case False
        then have hminxy: "min (d x y) 1 = 1"
          by simp
        have "min (d x z) 1 \<le> 1"
          by simp
        also have "... \<le> min (d x y) 1 + min (d y z) 1"
        proof -
          have hnonneg: "0 \<le> d y z"
            using hd hyX hzX unfolding top1_metric_on_def by blast
          have hminnonneg: "0 \<le> min (d y z) 1"
            using hnonneg by simp
          have "1 \<le> 1 + min (d y z) 1"
            using hminnonneg by linarith
          thus ?thesis
            by (simp add: hminxy)
        qed
        finally show ?thesis .
      next
        case True
        then have hminxy: "min (d x y) 1 = d x y"
          by simp
        show ?thesis
        proof (cases "d y z < 1")
          case False
          then have hminyz: "min (d y z) 1 = 1"
            by simp
          have "min (d x z) 1 \<le> 1"
            by simp
          also have "... \<le> min (d x y) 1 + min (d y z) 1"
          proof -
            have hnonneg: "0 \<le> d x y"
              using hd hxX hyX unfolding top1_metric_on_def by blast
            have hminnonneg: "0 \<le> min (d x y) 1"
              using hnonneg by simp
            have "1 \<le> min (d x y) 1 + 1"
              using hminnonneg by linarith
            thus ?thesis
              by (simp add: hminyz)
          qed
          finally show ?thesis .
        next
          case True
          then have hminyz: "min (d y z) 1 = d y z"
            by simp
          have "min (d x z) 1 \<le> d x z"
            by simp
          also have "... \<le> d x y + d y z"
            using htri_xyz by simp
          also have "... = min (d x y) 1 + min (d y z) 1"
            by (simp add: hminxy hminyz)
          finally show ?thesis .
        qed
      qed
    qed
  qed
qed

lemma top1_ball_on_bounded_metric_eq:
  assumes he: "e \<le> (1::real)"
  shows "top1_ball_on X (top1_bounded_metric d) x e = top1_ball_on X d x e"
proof (rule set_eqI)
  fix y
  show "y \<in> top1_ball_on X (top1_bounded_metric d) x e \<longleftrightarrow> y \<in> top1_ball_on X d x e"
  proof
    assume hy: "y \<in> top1_ball_on X (top1_bounded_metric d) x e"
    have hyX: "y \<in> X" and hmin: "top1_bounded_metric d x y < e"
      using hy unfolding top1_ball_on_def by blast+
    have hmin': "min (d x y) 1 < e"
      using hmin unfolding top1_bounded_metric_def by simp
    have "d x y < e"
    proof (cases "d x y \<le> 1")
      case True
      thus ?thesis using hmin' by simp
    next
      case False
      then have "min (d x y) 1 = 1"
        by simp
      hence "1 < e"
        using hmin' by simp
      thus ?thesis
        using he by simp
    qed
    show "y \<in> top1_ball_on X d x e"
      unfolding top1_ball_on_def using hyX \<open>d x y < e\<close> by blast
  next
    assume hy: "y \<in> top1_ball_on X d x e"
    have hyX: "y \<in> X" and hdist: "d x y < e"
      using hy unfolding top1_ball_on_def by blast+
    have "top1_bounded_metric d x y < e"
      unfolding top1_bounded_metric_def using hdist by simp
    show "y \<in> top1_ball_on X (top1_bounded_metric d) x e"
      unfolding top1_ball_on_def using hyX \<open>top1_bounded_metric d x y < e\<close> by blast
  qed
qed

lemma top1_metric_open_contains_ball:
  assumes hd: "top1_metric_on X d"
  assumes hU: "U \<in> top1_metric_topology_on X d"
  assumes hxU: "x \<in> U"
  shows "\<exists>e>0. top1_ball_on X d x e \<subseteq> U"
proof -
  have hUgen: "U \<in> topology_generated_by_basis X (top1_metric_basis_on X d)"
    using hU unfolding top1_metric_topology_on_def by simp
  have hprop: "\<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> U"
    using hUgen hxU unfolding topology_generated_by_basis_def by blast
  obtain b where hb: "b \<in> top1_metric_basis_on X d" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
    using hprop by blast
  obtain c e where hbdef: "b = top1_ball_on X d c e" and hcX: "c \<in> X" and he: "0 < e"
    using hb unfolding top1_metric_basis_on_def by blast
  have hxX: "x \<in> X"
    using hxb unfolding hbdef top1_ball_on_def by blast
  have hdcx: "d c x < e"
    using hxb unfolding hbdef top1_ball_on_def by blast

  define r where "r = (e - d c x) / 2"
  have hr_pos: "0 < r"
    using hdcx he unfolding r_def by simp

  have hball_sub: "top1_ball_on X d x r \<subseteq> top1_ball_on X d c e"
  proof (rule subsetI)
    fix y assume hy: "y \<in> top1_ball_on X d x r"
    have hyX: "y \<in> X" and hdxy: "d x y < r"
      using hy unfolding top1_ball_on_def by blast+
    have htri_cxy: "d c y \<le> d c x + d x y"
      using hd hcX hxX hyX unfolding top1_metric_on_def by blast
    have "d c y < d c x + r"
      using htri_cxy hdxy by simp
    also have "... = (d c x + e) / 2"
      unfolding r_def by (simp add: field_simps algebra_simps)
    also have "... < e"
      using hdcx by simp
    finally have "d c y < e" .
    show "y \<in> top1_ball_on X d c e"
      unfolding top1_ball_on_def using hyX \<open>d c y < e\<close> by blast
  qed

  have hsubU: "top1_ball_on X d x r \<subseteq> U"
    using hball_sub hbU unfolding hbdef by blast

  show ?thesis
    by (rule exI[where x=r], intro conjI, rule hr_pos, rule hsubU)
qed

(** from \S20 Theorem 20.1 (Standard bounded metric) [top1.tex:1606] **)
theorem Theorem_20_1:
  assumes hd: "top1_metric_on X d"
  shows "top1_metric_on X (top1_bounded_metric d)
    \<and> top1_metric_topology_on X (top1_bounded_metric d) = top1_metric_topology_on X d"
proof -
  have hdb: "top1_metric_on X (top1_bounded_metric d)"
    by (rule top1_bounded_metric_on[OF hd])

  have hTop_d: "is_topology_on X (top1_metric_topology_on X d)"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])
  have hTop_db: "is_topology_on X (top1_metric_topology_on X (top1_bounded_metric d))"
    by (rule top1_metric_topology_on_is_topology_on[OF hdb])

  have hEq: "top1_metric_topology_on X (top1_bounded_metric d) = top1_metric_topology_on X d"
  proof (rule equalityI)
    show "top1_metric_topology_on X d \<subseteq> top1_metric_topology_on X (top1_bounded_metric d)"
    proof (rule subsetI)
      fix U assume hU: "U \<in> top1_metric_topology_on X d"
      have hUX: "U \<subseteq> X"
        using hU unfolding top1_metric_topology_on_def topology_generated_by_basis_def by blast
      have hlocal: "\<forall>x\<in>U. \<exists>b\<in>top1_metric_basis_on X (top1_bounded_metric d). x \<in> b \<and> b \<subseteq> U"
      proof (intro ballI)
        fix x assume hxU: "x \<in> U"
        obtain e where he: "e > 0" and hballsub: "top1_ball_on X d x e \<subseteq> U"
          using top1_metric_open_contains_ball[OF hd hU hxU] by blast
        define e' where "e' = min e (1/2)"
        have he'pos: "e' > 0"
          unfolding e'_def using he by simp
        have he'le1: "e' \<le> (1::real)"
          unfolding e'_def by simp
        have he'le: "e' \<le> e"
          unfolding e'_def by simp
        have hballsub': "top1_ball_on X d x e' \<subseteq> U"
        proof (rule subsetI)
          fix y assume hy: "y \<in> top1_ball_on X d x e'"
          have hyX: "y \<in> X" and hdist: "d x y < e'"
            using hy unfolding top1_ball_on_def by blast+
          have "d x y < e"
            using hdist he'le by linarith
          have "y \<in> top1_ball_on X d x e"
            unfolding top1_ball_on_def using hyX \<open>d x y < e\<close> by blast
          thus "y \<in> U"
            using hballsub by blast
        qed
        have hball_eq: "top1_ball_on X (top1_bounded_metric d) x e' = top1_ball_on X d x e'"
          by (rule top1_ball_on_bounded_metric_eq[OF he'le1])
        have hball_basis: "top1_ball_on X (top1_bounded_metric d) x e' \<in> top1_metric_basis_on X (top1_bounded_metric d)"
          unfolding top1_metric_basis_on_def using hUX hxU he'pos
          by (cases "x \<in> X", blast, blast)
        have hx_in: "x \<in> top1_ball_on X (top1_bounded_metric d) x e'"
        proof -
          have hxX: "x \<in> X" using hUX hxU by blast
          have "top1_bounded_metric d x x = 0"
            using hdb hxX unfolding top1_metric_on_def by blast
          thus ?thesis
            unfolding top1_ball_on_def using hxX he'pos by simp
        qed
        have hsubU': "top1_ball_on X (top1_bounded_metric d) x e' \<subseteq> U"
          unfolding hball_eq using hballsub' by simp
        show "\<exists>b\<in>top1_metric_basis_on X (top1_bounded_metric d). x \<in> b \<and> b \<subseteq> U"
          by (rule bexI[where x="top1_ball_on X (top1_bounded_metric d) x e'"], intro conjI, rule hx_in, rule hsubU', rule hball_basis)
      qed
      have "U \<in> topology_generated_by_basis X (top1_metric_basis_on X (top1_bounded_metric d))"
        unfolding topology_generated_by_basis_def using hUX hlocal by blast
      thus "U \<in> top1_metric_topology_on X (top1_bounded_metric d)"
        unfolding top1_metric_topology_on_def by simp
    qed
    show "top1_metric_topology_on X (top1_bounded_metric d) \<subseteq> top1_metric_topology_on X d"
    proof (rule subsetI)
      fix U assume hU: "U \<in> top1_metric_topology_on X (top1_bounded_metric d)"
      have hUX: "U \<subseteq> X"
        using hU unfolding top1_metric_topology_on_def topology_generated_by_basis_def by blast
      have hlocal: "\<forall>x\<in>U. \<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> U"
      proof (intro ballI)
        fix x assume hxU: "x \<in> U"
        obtain e where he: "e > 0" and hballsub: "top1_ball_on X (top1_bounded_metric d) x e \<subseteq> U"
          using top1_metric_open_contains_ball[OF hdb hU hxU] by blast
        define e' where "e' = min e (1/2)"
        have he'pos: "e' > 0"
          unfolding e'_def using he by simp
        have he'le1: "e' \<le> (1::real)"
          unfolding e'_def by simp
        have he'le: "e' \<le> e"
          unfolding e'_def by simp
        have hballsub': "top1_ball_on X (top1_bounded_metric d) x e' \<subseteq> U"
        proof (rule subsetI)
          fix y assume hy: "y \<in> top1_ball_on X (top1_bounded_metric d) x e'"
          have hyX: "y \<in> X" and hdist: "top1_bounded_metric d x y < e'"
            using hy unfolding top1_ball_on_def by blast+
          have "top1_bounded_metric d x y < e"
            using hdist he'le by linarith
          have "y \<in> top1_ball_on X (top1_bounded_metric d) x e"
            unfolding top1_ball_on_def using hyX \<open>top1_bounded_metric d x y < e\<close> by blast
          thus "y \<in> U"
            using hballsub by blast
        qed
        have hball_eq: "top1_ball_on X (top1_bounded_metric d) x e' = top1_ball_on X d x e'"
          by (rule top1_ball_on_bounded_metric_eq[OF he'le1])
        have hball_basis: "top1_ball_on X d x e' \<in> top1_metric_basis_on X d"
          unfolding top1_metric_basis_on_def using hUX hxU he'pos
          by (cases "x \<in> X", blast, blast)
        have hx_in: "x \<in> top1_ball_on X d x e'"
        proof -
          have hxX: "x \<in> X" using hUX hxU by blast
          have "d x x = 0"
            using hd hxX unfolding top1_metric_on_def by blast
          thus ?thesis
            unfolding top1_ball_on_def using hxX he'pos by simp
        qed
        have hsubU': "top1_ball_on X d x e' \<subseteq> U"
          using hballsub' by (simp add: hball_eq[symmetric])
        show "\<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> U"
          by (rule bexI[where x="top1_ball_on X d x e'"], intro conjI, rule hx_in, rule hsubU', rule hball_basis)
      qed
      have "U \<in> topology_generated_by_basis X (top1_metric_basis_on X d)"
        unfolding topology_generated_by_basis_def using hUX hlocal by blast
      thus "U \<in> top1_metric_topology_on X d"
        unfolding top1_metric_topology_on_def by simp
    qed
  qed

  show ?thesis
    by (intro conjI, rule hdb, rule hEq)
qed

(** from \S20 Lemma 20.2 (Comparison of metric topologies) [top1.tex:1674] **)
theorem Lemma_20_2:
  assumes hd: "top1_metric_on X d"
  assumes hd': "top1_metric_on X d'"
  defines "T \<equiv> top1_metric_topology_on X d"
  defines "T' \<equiv> top1_metric_topology_on X d'"
  shows "T \<subseteq> T' \<longleftrightarrow>
    (\<forall>x\<in>X. \<forall>\<epsilon>>0. \<exists>\<delta>>0. top1_ball_on X d' x \<delta> \<subseteq> top1_ball_on X d x \<epsilon>)"
proof (rule iffI)
  assume hsub: "T \<subseteq> T'"

  show "\<forall>x\<in>X. \<forall>\<epsilon>>0. \<exists>\<delta>>0. top1_ball_on X d' x \<delta> \<subseteq> top1_ball_on X d x \<epsilon>"
  proof (intro ballI allI impI)
    fix x :: 'a
    fix \<epsilon> :: real
    assume hxX: "x \<in> X"
    assume heps: "\<epsilon> > 0"

    have hopen_ball: "top1_ball_on X d x \<epsilon> \<in> T"
      unfolding T_def by (rule top1_ball_open_in_metric_topology[OF hd hxX heps])
    have hopen_ball': "top1_ball_on X d x \<epsilon> \<in> T'"
      using hsub hopen_ball by blast

    have hdx0: "d x x = 0"
      using hd hxX unfolding top1_metric_on_def by blast
    have hx_in_ball: "x \<in> top1_ball_on X d x \<epsilon>"
      unfolding top1_ball_on_def using hxX hdx0 heps by simp

    have hopen_ball_metric: "top1_ball_on X d x \<epsilon> \<in> top1_metric_topology_on X d'"
      using hopen_ball' unfolding T'_def by simp

    obtain \<delta> where hdel: "\<delta> > 0" and hsub_ball: "top1_ball_on X d' x \<delta> \<subseteq> top1_ball_on X d x \<epsilon>"
      using top1_metric_open_contains_ball[OF hd' hopen_ball_metric hx_in_ball] by blast

    show "\<exists>\<delta>>0. top1_ball_on X d' x \<delta> \<subseteq> top1_ball_on X d x \<epsilon>"
      by (rule exI[where x=\<delta>], intro conjI, rule hdel, rule hsub_ball)
  qed
next
  assume hballs: "\<forall>x\<in>X. \<forall>\<epsilon>>0. \<exists>\<delta>>0. top1_ball_on X d' x \<delta> \<subseteq> top1_ball_on X d x \<epsilon>"

  have hTopT': "is_topology_on X T'"
    unfolding T'_def by (rule top1_metric_topology_on_is_topology_on[OF hd'])

  have hBasisSub: "top1_metric_basis_on X d \<subseteq> T'"
  proof (rule subsetI)
    fix b assume hb: "b \<in> top1_metric_basis_on X d"
    obtain x \<epsilon> where hbdef: "b = top1_ball_on X d x \<epsilon>" and hxX: "x \<in> X" and heps: "\<epsilon> > 0"
      using hb unfolding top1_metric_basis_on_def by blast

    have hb_open_gen: "b \<in> topology_generated_by_basis X (top1_metric_basis_on X d')"
      unfolding hbdef topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "top1_ball_on X d x \<epsilon> \<subseteq> X"
        unfolding top1_ball_on_def by blast
      show "\<forall>y\<in>top1_ball_on X d x \<epsilon>.
          \<exists>b'\<in>top1_metric_basis_on X d'. y \<in> b' \<and> b' \<subseteq> top1_ball_on X d x \<epsilon>"
      proof (intro ballI)
        fix y assume hyU: "y \<in> top1_ball_on X d x \<epsilon>"
        have hyX: "y \<in> X" and hdxy: "d x y < \<epsilon>"
          using hyU unfolding top1_ball_on_def by blast+

        define r where "r = (\<epsilon> - d x y) / 2"
        have hr_pos: "r > 0"
          using hdxy heps unfolding r_def by simp

        have hball_sub: "top1_ball_on X d y r \<subseteq> top1_ball_on X d x \<epsilon>"
        proof (rule subsetI)
          fix z assume hz: "z \<in> top1_ball_on X d y r"
          have hzX: "z \<in> X" and hdyz: "d y z < r"
            using hz unfolding top1_ball_on_def by blast+
          have htri: "d x z \<le> d x y + d y z"
            using hd hxX hyX hzX unfolding top1_metric_on_def by blast
          have "d x z < d x y + r"
            using htri hdyz by simp
          also have "... = (d x y + \<epsilon>) / 2"
            unfolding r_def by (simp add: field_simps algebra_simps)
          also have "... < \<epsilon>"
            using hdxy by simp
          finally have hdxz: "d x z < \<epsilon>" .
          show "z \<in> top1_ball_on X d x \<epsilon>"
            unfolding top1_ball_on_def using hzX hdxz by blast
        qed

        obtain \<delta> where hdel: "\<delta> > 0" and hsub1: "top1_ball_on X d' y \<delta> \<subseteq> top1_ball_on X d y r"
          using hballs hyX hr_pos by blast
        have hsub2: "top1_ball_on X d' y \<delta> \<subseteq> top1_ball_on X d x \<epsilon>"
          using hsub1 hball_sub by blast

        have hdy0: "d' y y = 0"
          using hd' hyX unfolding top1_metric_on_def by blast
        have hy_in: "y \<in> top1_ball_on X d' y \<delta>"
          unfolding top1_ball_on_def using hyX hdy0 hdel by simp

        have hbasis: "top1_ball_on X d' y \<delta> \<in> top1_metric_basis_on X d'"
          unfolding top1_metric_basis_on_def using hyX hdel by blast

        show "\<exists>b'\<in>top1_metric_basis_on X d'. y \<in> b' \<and> b' \<subseteq> top1_ball_on X d x \<epsilon>"
          apply (rule bexI[where x="top1_ball_on X d' y \<delta>"])
           apply (intro conjI)
            apply (rule hy_in)
           apply (rule hsub2)
          apply (rule hbasis)
          done
      qed
    qed

    have "b \<in> top1_metric_topology_on X d'"
      unfolding top1_metric_topology_on_def using hb_open_gen by simp
    thus "b \<in> T'"
      unfolding T'_def by simp
  qed

  have hInc: "topology_generated_by_basis X (top1_metric_basis_on X d) \<subseteq> T'"
    by (rule topology_generated_by_basis_subset[OF hTopT' hBasisSub])
  have "top1_metric_topology_on X d \<subseteq> T'"
    unfolding top1_metric_topology_on_def using hInc by simp
  thus "T \<subseteq> T'"
    unfolding T_def by simp
qed

(** Metrics on products of reals used in \S20 of \<open>top1.tex\<close>. **)

(** Standard bounded metric on \<open>\<real>\<close>: \<open>\<bar>d(a,b) = min(|a-b|,1)\<close>. **)
definition top1_real_bounded_metric :: "real \<Rightarrow> real \<Rightarrow> real" where
  "top1_real_bounded_metric a b = min (abs (a - b)) 1"

(** Helper: monotonicity of \<open>min _ 1\<close> in its argument. **)
lemma top1_min_mono_1:
  fixes u v :: real
  assumes huv: "u \<le> v"
  shows "min u 1 \<le> min v 1"
proof (cases "v \<le> 1")
  case True
  have "min u 1 \<le> u"
    by simp
  also have "u \<le> v"
    by (rule huv)
  also have "v = min v 1"
    using True by simp
  finally show ?thesis
    by simp
next
  case False
  have "min u 1 \<le> 1"
    by simp
  also have "1 = min v 1"
    using False by simp
  finally show ?thesis .
qed

(** Helper: subadditivity of \<open>min _ 1\<close> on nonnegative reals. **)
lemma top1_min_add_le:
  fixes u v :: real
  assumes hu: "0 \<le> u"
  assumes hv: "0 \<le> v"
  shows "min (u + v) 1 \<le> min u 1 + min v 1"
proof (cases "u \<ge> 1 \<or> v \<ge> 1")
  case True
  have hL: "min (u + v) 1 \<le> 1"
    by simp
  have hR: "1 \<le> min u 1 + min v 1"
  proof (cases "u \<ge> 1")
    case True
    have hmu: "min u 1 = 1"
      using True by simp
    have hmv0: "0 \<le> min v 1"
      using hv by simp
    have "1 \<le> 1 + min v 1"
      using hmv0 by simp
    thus ?thesis
      using hmu by simp
  next
    case False
    have "v \<ge> 1"
      using True False by blast
    then have hmv: "min v 1 = 1"
      by simp
    have hmu0: "0 \<le> min u 1"
      using hu by simp
    have "1 \<le> min u 1 + 1"
      using hmu0 by simp
    thus ?thesis
      using hmv by simp
  qed
  show ?thesis
    by (rule order_trans[OF hL hR])
next
  case False
  have hu1: "u < 1"
  proof -
    have "\<not> (1 \<le> u)"
      using False by auto
    thus ?thesis
      by (simp add: not_le)
  qed
  have hv1: "v < 1"
  proof -
    have "\<not> (1 \<le> v)"
      using False by auto
    thus ?thesis
      by (simp add: not_le)
  qed
  have hu_le1: "u \<le> 1"
    using hu1 by simp
  have hv_le1: "v \<le> 1"
    using hv1 by simp
  have hmu: "min u 1 = u"
    using hu_le1 by simp
  have hmv: "min v 1 = v"
    using hv_le1 by simp
  have "min (u + v) 1 \<le> u + v"
    by simp
  thus ?thesis
    using hmu hmv by simp
qed

lemma top1_real_bounded_metric_triangle:
  shows "top1_real_bounded_metric a c
    \<le> top1_real_bounded_metric a b + top1_real_bounded_metric b c"
proof -
  have habc: "abs (a - c) \<le> abs (a - b) + abs (b - c)"
  proof -
    have "abs (a - c) = abs ((a - b) + (b - c))"
      by simp
    also have "\<dots> \<le> abs (a - b) + abs (b - c)"
      by (rule abs_triangle_ineq)
    finally show ?thesis .
  qed

  have h1: "min (abs (a - c)) 1 \<le> min (abs (a - b) + abs (b - c)) 1"
    by (rule top1_min_mono_1[OF habc])
  have h2: "min (abs (a - b) + abs (b - c)) 1 \<le> min (abs (a - b)) 1 + min (abs (b - c)) 1"
  proof -
    have hu: "0 \<le> abs (a - b)"
      by simp
    have hv: "0 \<le> abs (b - c)"
      by simp
    show ?thesis
      by (rule top1_min_add_le[OF hu hv])
  qed

  show ?thesis
    unfolding top1_real_bounded_metric_def
    by (rule order_trans[OF h1 h2])
qed

lemma top1_real_bounded_metric_metric_on:
  shows "top1_metric_on UNIV top1_real_bounded_metric"
proof (unfold top1_metric_on_def, intro conjI)
  show "\<forall>x\<in>UNIV. 0 \<le> top1_real_bounded_metric x x"
    unfolding top1_real_bounded_metric_def by simp
  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. 0 \<le> top1_real_bounded_metric x y"
    unfolding top1_real_bounded_metric_def by simp

  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. top1_real_bounded_metric x y = 0 \<longleftrightarrow> x = y"
  proof (intro ballI)
    fix x y :: real
    show "top1_real_bounded_metric x y = 0 \<longleftrightarrow> x = y"
    proof (rule iffI)
      assume h0: "top1_real_bounded_metric x y = 0"
      have habs0: "abs (x - y) = 0"
      proof (cases "abs (x - y) \<le> 1")
        case True
        have "top1_real_bounded_metric x y = abs (x - y)"
          unfolding top1_real_bounded_metric_def using True by simp
        thus ?thesis
          using h0 by simp
      next
        case False
        have "top1_real_bounded_metric x y = 1"
          unfolding top1_real_bounded_metric_def using False by simp
        thus ?thesis
          using h0 by simp
      qed
      show "x = y"
        using habs0 by simp
    next
      assume hxy: "x = y"
      show "top1_real_bounded_metric x y = 0"
        unfolding top1_real_bounded_metric_def using hxy by simp
    qed
  qed

  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. top1_real_bounded_metric x y = top1_real_bounded_metric y x"
    unfolding top1_real_bounded_metric_def by (simp add: abs_minus_commute)

  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. \<forall>z\<in>UNIV.
          top1_real_bounded_metric x z \<le> top1_real_bounded_metric x y + top1_real_bounded_metric y z"
  proof (intro ballI)
    fix x y z :: real
    show "top1_real_bounded_metric x z \<le> top1_real_bounded_metric x y + top1_real_bounded_metric y z"
      by (rule top1_real_bounded_metric_triangle)
  qed
qed

lemma top1_real_bounded_metric_ball_in_order_topology:
  fixes a e :: real
  assumes he: "0 < e"
  shows "top1_ball_on UNIV top1_real_bounded_metric a e \<in> (order_topology_on_UNIV::real set set)"
proof (cases "1 < e")
  case True
  have hEq: "top1_ball_on UNIV top1_real_bounded_metric a e = (UNIV::real set)"
  proof (rule set_eqI)
    fix y :: real
    show "y \<in> top1_ball_on UNIV top1_real_bounded_metric a e \<longleftrightarrow> y \<in> (UNIV::real set)"
    proof
      assume "y \<in> top1_ball_on UNIV top1_real_bounded_metric a e"
      then show "y \<in> (UNIV::real set)"
        by simp
    next
      assume "y \<in> (UNIV::real set)"
      have hle: "top1_real_bounded_metric a y \<le> 1"
        unfolding top1_real_bounded_metric_def by simp
      have "top1_real_bounded_metric a y < e"
        by (rule le_less_trans[OF hle True])
      then show "y \<in> top1_ball_on UNIV top1_real_bounded_metric a e"
        unfolding top1_ball_on_def by simp
    qed
  qed
  have hTop: "is_topology_on (UNIV::real set) order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_is_topology_on)
  have "UNIV \<in> (order_topology_on_UNIV::real set set)"
    using hTop unfolding is_topology_on_def by blast
  thus ?thesis
    using hEq by simp
next
  case False
  have he1: "e \<le> 1"
    using False by simp
  have hab: "a - e < a + e"
    using he by simp

  have hEq: "top1_ball_on UNIV top1_real_bounded_metric a e = open_interval (a - e) (a + e)"
  proof (rule set_eqI)
    fix y :: real
    show "y \<in> top1_ball_on UNIV top1_real_bounded_metric a e \<longleftrightarrow> y \<in> open_interval (a - e) (a + e)"
    proof -
      have h1: "y \<in> top1_ball_on UNIV top1_real_bounded_metric a e \<longleftrightarrow> top1_real_bounded_metric a y < e"
        unfolding top1_ball_on_def by simp
      have h2: "top1_real_bounded_metric a y < e \<longleftrightarrow> abs (a - y) < e"
      proof (rule iffI)
        assume hlt: "top1_real_bounded_metric a y < e"
        have hmin: "min (abs (a - y)) 1 < e"
          using hlt unfolding top1_real_bounded_metric_def .
        show "abs (a - y) < e"
        proof (cases "abs (a - y) \<le> 1")
          case True
          have "min (abs (a - y)) 1 = abs (a - y)"
            using True by simp
          thus ?thesis
            using hmin by simp
        next
          case False
          have "min (abs (a - y)) 1 = 1"
            using False by simp
          then have "1 < e"
            using hmin by simp
          thus ?thesis
            using he1 by simp
        qed
      next
        assume habs: "abs (a - y) < e"
        have habs1: "abs (a - y) < 1"
          by (rule less_le_trans[OF habs he1])
        have "min (abs (a - y)) 1 = abs (a - y)"
          using habs1 by simp
        thus "top1_real_bounded_metric a y < e"
          unfolding top1_real_bounded_metric_def using habs by simp
      qed

      have h3: "abs (a - y) < e \<longleftrightarrow> a - e < y \<and> y < a + e"
      proof -
        have "abs (a - y) < e \<longleftrightarrow> abs (y - a) < e"
          by (simp add: abs_minus_commute)
        also have "\<dots> \<longleftrightarrow> a - e < y \<and> y < a + e"
          by (simp add: abs_diff_less_iff)
        finally show ?thesis .
      qed

      have h4: "y \<in> open_interval (a - e) (a + e) \<longleftrightarrow> a - e < y \<and> y < a + e"
        unfolding open_interval_def by simp
      show ?thesis
        using h1 h2 h3 h4 by simp
    qed
  qed

  have "open_interval (a - e) (a + e) \<in> (order_topology_on_UNIV::real set set)"
    by (rule open_interval_in_order_topology[OF hab])
  thus ?thesis
    using hEq by simp
qed

(** For radii \<open>e \<le> 1\<close>, the bounded metric ball condition is equivalent to the usual absolute-value bound. **)
lemma top1_real_bounded_metric_lt_iff_abs_lt:
  fixes a b e :: real
  assumes he: "0 < e"
  assumes he1: "e \<le> 1"
  shows "top1_real_bounded_metric a b < e \<longleftrightarrow> abs (a - b) < e"
proof (rule iffI)
  assume hlt: "top1_real_bounded_metric a b < e"
  have hmin: "min (abs (a - b)) 1 < e"
    using hlt unfolding top1_real_bounded_metric_def .
  show "abs (a - b) < e"
  proof (cases "abs (a - b) \<le> 1")
    case True
    have "min (abs (a - b)) 1 = abs (a - b)"
      using True by simp
    thus ?thesis
      using hmin by simp
  next
    case False
    have "min (abs (a - b)) 1 = 1"
      using False by simp
    then have "1 < e"
      using hmin by simp
    thus ?thesis
      using he1 by simp
  qed
next
  assume habs: "abs (a - b) < e"
  have habs1: "abs (a - b) < 1"
    by (rule less_le_trans[OF habs he1])
  have "min (abs (a - b)) 1 = abs (a - b)"
    using habs1 by simp
  thus "top1_real_bounded_metric a b < e"
    unfolding top1_real_bounded_metric_def using habs by simp
qed

lemma open_interval_in_bounded_metric_topology:
  fixes a b :: real
  assumes hab: "a < b"
  shows "open_interval a b \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
proof -
  let ?T = "top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
  let ?B = "top1_metric_basis_on (UNIV::real set) top1_real_bounded_metric"

  show ?thesis
    unfolding top1_metric_topology_on_def topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "open_interval a b \<subseteq> (UNIV::real set)"
      by simp
    show "\<forall>x\<in>open_interval a b. \<exists>ba\<in>?B. x \<in> ba \<and> ba \<subseteq> open_interval a b"
    proof (intro ballI)
      fix x :: real
      assume hx: "x \<in> open_interval a b"
      have hax_hxb: "a < x \<and> x < b"
        using hx unfolding open_interval_def by simp
      have hax: "a < x"
        using hax_hxb by (rule conjunct1)
      have hxb: "x < b"
        using hax_hxb by (rule conjunct2)

      define e0 where "e0 = min ((x - a) / 2) ((b - x) / 2)"
      define e where "e = min e0 (1/2)"

      have he0: "0 < e0"
        unfolding e0_def using hax hxb by simp
      have he: "0 < e"
        unfolding e_def using he0 by simp
      have he1: "e \<le> 1"
        unfolding e_def by simp

      have hball_basis: "top1_ball_on UNIV top1_real_bounded_metric x e \<in> ?B"
        unfolding top1_metric_basis_on_def
        apply (rule CollectI)
        apply (rule exI[where x=x])
        apply (rule exI[where x=e])
        using he by simp

      have hxball: "x \<in> top1_ball_on UNIV top1_real_bounded_metric x e"
        unfolding top1_ball_on_def top1_real_bounded_metric_def using he by simp

      have hsub: "top1_ball_on UNIV top1_real_bounded_metric x e \<subseteq> open_interval a b"
      proof (rule subsetI)
        fix y :: real
        assume hy: "y \<in> top1_ball_on UNIV top1_real_bounded_metric x e"
        have hxy: "top1_real_bounded_metric x y < e"
          using hy unfolding top1_ball_on_def by simp
        have habs: "abs (x - y) < e"
          by (rule iffD1[OF top1_real_bounded_metric_lt_iff_abs_lt[OF he _] hxy]) (rule he1)

        have habs': "abs (y - x) < e"
          using habs by (simp add: abs_minus_commute)
        have hboth: "x - e < y \<and> y < x + e"
          using habs' by (simp add: abs_diff_less_iff)
        have hy_lt: "x - e < y"
          using hboth by blast
        have hy_gt: "y < x + e"
          using hboth by blast

        have he_le0: "e \<le> e0"
          unfolding e_def by simp
        have he_le_left: "e0 \<le> (x - a) / 2"
          unfolding e0_def by (rule min.cobounded1)
        have he_le_right: "e0 \<le> (b - x) / 2"
          unfolding e0_def by (rule min.cobounded2)
        have he_le_left': "e \<le> (x - a) / 2"
          by (rule order_trans[OF he_le0 he_le_left])
        have he_le_right': "e \<le> (b - x) / 2"
          by (rule order_trans[OF he_le0 he_le_right])

        have hxap: "0 < x - a"
          using hax by simp
        have hxap_half: "(x - a) / 2 < x - a"
        proof -
          have "(1 / 2 :: real) < 1"
            by simp
          have "(x - a) * (1 / 2) < (x - a) * 1"
            by (rule mult_strict_left_mono[OF \<open>(1 / 2 :: real) < 1\<close> hxap])
          thus ?thesis
            by simp
        qed
        have helt: "e < x - a"
        proof -
          have he_le: "e \<le> (x - a) / 2"
            using he_le_left' .
          show ?thesis
            by (rule order_le_less_trans[OF he_le hxap_half])
        qed
        have ha_lt: "a < x - e"
          using helt by linarith

        have hbpx: "0 < b - x"
          using hxb by simp
        have hbpx_half: "(b - x) / 2 < b - x"
        proof -
          have "(1 / 2 :: real) < 1"
            by simp
          have "(b - x) * (1 / 2) < (b - x) * 1"
            by (rule mult_strict_left_mono[OF \<open>(1 / 2 :: real) < 1\<close> hbpx])
          thus ?thesis
            by simp
        qed
        have herlt: "e < b - x"
        proof -
          have he_le: "e \<le> (b - x) / 2"
            using he_le_right' .
          show ?thesis
            by (rule order_le_less_trans[OF he_le hbpx_half])
        qed
        have hb_gt: "x + e < b"
          using herlt by linarith

        have "a < y"
          using ha_lt hy_lt by linarith
        moreover have "y < b"
          using hy_gt hb_gt by linarith
        ultimately show "y \<in> open_interval a b"
          unfolding open_interval_def by simp
      qed

      show "\<exists>ba\<in>?B. x \<in> ba \<and> ba \<subseteq> open_interval a b"
        apply (rule bexI[where x="top1_ball_on UNIV top1_real_bounded_metric x e"])
         apply (intro conjI)
          apply (rule hxball)
         apply (rule hsub)
        apply (rule hball_basis)
        done
    qed
  qed
qed

lemma open_ray_gt_in_bounded_metric_topology:
  fixes a :: real
  shows "open_ray_gt a \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
proof -
  let ?T = "top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
  let ?B = "top1_metric_basis_on (UNIV::real set) top1_real_bounded_metric"
  show ?thesis
    unfolding top1_metric_topology_on_def topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "open_ray_gt a \<subseteq> (UNIV::real set)"
      by simp
    show "\<forall>x\<in>open_ray_gt a. \<exists>ba\<in>?B. x \<in> ba \<and> ba \<subseteq> open_ray_gt a"
    proof (intro ballI)
      fix x :: real
      assume hx: "x \<in> open_ray_gt a"
      have hax: "a < x"
        using hx unfolding open_ray_gt_def by simp

      define e0 where "e0 = (x - a) / 2"
      define e where "e = min e0 (1/2)"

      have he0: "0 < e0"
        unfolding e0_def using hax by simp
      have he: "0 < e"
        unfolding e_def using he0 by simp
      have he1: "e \<le> 1"
        unfolding e_def by simp

      have hball_basis: "top1_ball_on UNIV top1_real_bounded_metric x e \<in> ?B"
        unfolding top1_metric_basis_on_def
        apply (rule CollectI)
        apply (rule exI[where x=x])
        apply (rule exI[where x=e])
        using he by simp

      have hxball: "x \<in> top1_ball_on UNIV top1_real_bounded_metric x e"
        unfolding top1_ball_on_def top1_real_bounded_metric_def using he by simp

      have hsub: "top1_ball_on UNIV top1_real_bounded_metric x e \<subseteq> open_ray_gt a"
      proof (rule subsetI)
        fix y :: real
        assume hy: "y \<in> top1_ball_on UNIV top1_real_bounded_metric x e"
        have hxy: "top1_real_bounded_metric x y < e"
          using hy unfolding top1_ball_on_def by simp
        have habs: "abs (x - y) < e"
          by (rule iffD1[OF top1_real_bounded_metric_lt_iff_abs_lt[OF he _] hxy]) (rule he1)
        have habs': "abs (y - x) < e"
          using habs by (simp add: abs_minus_commute)
        have hboth: "x - e < y \<and> y < x + e"
          using habs' by (simp add: abs_diff_less_iff)
        have hy_lb: "x - e < y"
          using hboth by blast

        have he_le0: "e \<le> e0"
          unfolding e_def by simp
        have hxap: "0 < x - a"
          using hax by simp
        have hxap_half: "(x - a) / 2 < x - a"
        proof -
          have "(1 / 2 :: real) < 1"
            by simp
          have "(x - a) * (1 / 2) < (x - a) * 1"
            by (rule mult_strict_left_mono[OF \<open>(1 / 2 :: real) < 1\<close> hxap])
          thus ?thesis
            by simp
        qed
        have helt: "e < x - a"
        proof -
          have he_le: "e \<le> (x - a) / 2"
            unfolding e_def e0_def
            by (rule min.cobounded1)
          show ?thesis
            by (rule order_le_less_trans[OF he_le hxap_half])
        qed
        have "a < x - e"
          using helt by linarith
        hence "a < y"
          using hy_lb by linarith
        thus "y \<in> open_ray_gt a"
          unfolding open_ray_gt_def by simp
      qed

      show "\<exists>ba\<in>?B. x \<in> ba \<and> ba \<subseteq> open_ray_gt a"
        apply (rule bexI[where x="top1_ball_on UNIV top1_real_bounded_metric x e"])
         apply (intro conjI)
          apply (rule hxball)
         apply (rule hsub)
        apply (rule hball_basis)
        done
    qed
  qed
qed

lemma open_ray_lt_in_bounded_metric_topology:
  fixes a :: real
  shows "open_ray_lt a \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
proof -
  let ?T = "top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
  let ?B = "top1_metric_basis_on (UNIV::real set) top1_real_bounded_metric"
  show ?thesis
    unfolding top1_metric_topology_on_def topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "open_ray_lt a \<subseteq> (UNIV::real set)"
      by simp
    show "\<forall>x\<in>open_ray_lt a. \<exists>ba\<in>?B. x \<in> ba \<and> ba \<subseteq> open_ray_lt a"
    proof (intro ballI)
      fix x :: real
      assume hx: "x \<in> open_ray_lt a"
      have hxa: "x < a"
        using hx unfolding open_ray_lt_def by simp

      define e0 where "e0 = (a - x) / 2"
      define e where "e = min e0 (1/2)"

      have he0: "0 < e0"
        unfolding e0_def using hxa by simp
      have he: "0 < e"
        unfolding e_def using he0 by simp
      have he1: "e \<le> 1"
        unfolding e_def by simp

      have hball_basis: "top1_ball_on UNIV top1_real_bounded_metric x e \<in> ?B"
        unfolding top1_metric_basis_on_def
        apply (rule CollectI)
        apply (rule exI[where x=x])
        apply (rule exI[where x=e])
        using he by simp

      have hxball: "x \<in> top1_ball_on UNIV top1_real_bounded_metric x e"
        unfolding top1_ball_on_def top1_real_bounded_metric_def using he by simp

      have hsub: "top1_ball_on UNIV top1_real_bounded_metric x e \<subseteq> open_ray_lt a"
      proof (rule subsetI)
        fix y :: real
        assume hy: "y \<in> top1_ball_on UNIV top1_real_bounded_metric x e"
        have hxy: "top1_real_bounded_metric x y < e"
          using hy unfolding top1_ball_on_def by simp
        have habs: "abs (x - y) < e"
          by (rule iffD1[OF top1_real_bounded_metric_lt_iff_abs_lt[OF he _] hxy]) (rule he1)
        have habs': "abs (y - x) < e"
          using habs by (simp add: abs_minus_commute)
        have hboth: "x - e < y \<and> y < x + e"
          using habs' by (simp add: abs_diff_less_iff)
        have hy_ub: "y < x + e"
          using hboth by blast

        have he_le0: "e \<le> e0"
          unfolding e_def by simp
        have haxp: "0 < a - x"
          using hxa by simp
        have haxp_half: "(a - x) / 2 < a - x"
        proof -
          have "(1 / 2 :: real) < 1"
            by simp
          have "(a - x) * (1 / 2) < (a - x) * 1"
            by (rule mult_strict_left_mono[OF \<open>(1 / 2 :: real) < 1\<close> haxp])
          thus ?thesis
            by simp
        qed
        have hlt: "e < a - x"
        proof -
          have he_le: "e \<le> (a - x) / 2"
            unfolding e_def e0_def
            by (rule min.cobounded1)
          show ?thesis
            by (rule order_le_less_trans[OF he_le haxp_half])
        qed
        have "x + e < a"
          using hlt by linarith
        hence "y < a"
          using hy_ub by linarith
        thus "y \<in> open_ray_lt a"
          unfolding open_ray_lt_def by simp
      qed

      show "\<exists>ba\<in>?B. x \<in> ba \<and> ba \<subseteq> open_ray_lt a"
        apply (rule bexI[where x="top1_ball_on UNIV top1_real_bounded_metric x e"])
         apply (intro conjI)
          apply (rule hxball)
         apply (rule hsub)
        apply (rule hball_basis)
        done
    qed
  qed
qed

lemma order_topology_on_UNIV_eq_bounded_metric_topology_real:
  shows "(order_topology_on_UNIV::real set set) =
    top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
proof (rule subset_antisym)
  have hTopOrd: "is_topology_on (UNIV::real set) (order_topology_on_UNIV::real set set)"
    by (rule order_topology_on_UNIV_is_topology_on)

  have hTopMet: "is_topology_on (UNIV::real set) (top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric)"
  proof -
    have hBasis: "is_basis_on (UNIV::real set) (top1_metric_basis_on (UNIV::real set) top1_real_bounded_metric)"
      by (rule top1_metric_basis_is_basis_on[OF top1_real_bounded_metric_metric_on])
    show ?thesis
      unfolding top1_metric_topology_on_def
      by (rule topology_generated_by_basis_is_topology_on[OF hBasis])
  qed

  show "(order_topology_on_UNIV::real set set) \<subseteq> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
  proof -
    have hBsub:
      "basis_order_topology \<subseteq> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
    proof (rule subsetI)
      fix U :: "real set"
      assume hU: "U \<in> basis_order_topology"
      have hcases:
        "(\<exists>a b. a < b \<and> U = open_interval a b)
         \<or> (\<exists>a. U = open_ray_gt a)
         \<or> (\<exists>a. U = open_ray_lt a)
         \<or> (U = UNIV)"
        using hU unfolding basis_order_topology_def by blast
      show "U \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
        using hcases
      proof (elim disjE)
        assume "\<exists>a b. a < b \<and> U = open_interval a b"
        then obtain a b where hab: "a < b" and hUeq: "U = open_interval a b"
          by blast
        show ?thesis
          unfolding hUeq by (rule open_interval_in_bounded_metric_topology[OF hab])
      next
        assume "\<exists>a. U = open_ray_gt a"
        then obtain a where hUeq: "U = open_ray_gt a"
          by blast
        show ?thesis
          unfolding hUeq by (rule open_ray_gt_in_bounded_metric_topology)
      next
        assume "\<exists>a. U = open_ray_lt a"
        then obtain a where hUeq: "U = open_ray_lt a"
          by blast
        show ?thesis
          unfolding hUeq by (rule open_ray_lt_in_bounded_metric_topology)
      next
        assume hUeq: "U = UNIV"
        have "UNIV \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
          using hTopMet unfolding is_topology_on_def by blast
        thus ?thesis
          using hUeq by simp
      qed
    qed
    have hInc:
      "topology_generated_by_basis (UNIV::real set) basis_order_topology
        \<subseteq> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
      by (rule topology_generated_by_basis_subset[OF hTopMet hBsub])
    show ?thesis
      unfolding order_topology_on_UNIV_def
      using hInc by simp
  qed

  show "top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric \<subseteq> (order_topology_on_UNIV::real set set)"
  proof -
    have hBsub:
      "top1_metric_basis_on (UNIV::real set) top1_real_bounded_metric \<subseteq> (order_topology_on_UNIV::real set set)"
    proof (rule subsetI)
      fix U :: "real set"
      assume hU: "U \<in> top1_metric_basis_on (UNIV::real set) top1_real_bounded_metric"
      then obtain x e where he: "0 < e" and hUeq: "U = top1_ball_on UNIV top1_real_bounded_metric x e"
        unfolding top1_metric_basis_on_def by blast
      show "U \<in> (order_topology_on_UNIV::real set set)"
        unfolding hUeq
        by (rule top1_real_bounded_metric_ball_in_order_topology[OF he])
    qed

    have hInc:
      "topology_generated_by_basis (UNIV::real set) (top1_metric_basis_on (UNIV::real set) top1_real_bounded_metric)
        \<subseteq> (order_topology_on_UNIV::real set set)"
      by (rule topology_generated_by_basis_subset[OF hTopOrd hBsub])

    show ?thesis
      unfolding top1_metric_topology_on_def
      using hInc by simp
  qed
qed

(** Euclidean metric on finite products of reals, written on function-spaces \<open>top1_PiE I (\<lambda>_. UNIV)\<close>. **)
definition top1_euclidean_metric_real_on :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> real" where
  "top1_euclidean_metric_real_on I x y = sqrt (\<Sum>i\<in>I. (x i - y i)\<^sup>2)"

(** Square/sup metric on finite products of reals: \<open>\<rho>(x,y) = sup_i |x_i-y_i|\<close>. **)
definition top1_square_metric_real_on :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> real" where
  "top1_square_metric_real_on I x y = Sup ((\<lambda>i. abs (x i - y i)) ` I)"

(** Uniform metric on \<open>\<real>^J\<close>: \<open>\<bar>\<rho>(x,y) = sup_{\<alpha>\<in>J} \<bar>d(x_\alpha,y_\alpha)\<close>. **)
definition top1_uniform_metric_real_on :: "'i set \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> real) \<Rightarrow> real" where
  "top1_uniform_metric_real_on I x y = Sup ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"

(** The uniform metric on \<open>\<real>^I\<close> is a metric as soon as the index set is nonempty. **)
lemma top1_uniform_metric_real_on_metric_on:
  fixes I :: "'i set"
  assumes hne: "I \<noteq> {}"
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "X\<^sub>R \<equiv> top1_PiE I XR"
  shows "top1_metric_on X\<^sub>R (top1_uniform_metric_real_on I)"
proof -
  obtain i0 where hi0: "i0 \<in> I"
    using hne by blast

  have h0iff: "\<And>u v. top1_real_bounded_metric u v = 0 \<longleftrightarrow> u = v"
  proof -
    fix u v :: real
    have "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. top1_real_bounded_metric x y = 0 \<longleftrightarrow> x = y"
      using top1_real_bounded_metric_metric_on unfolding top1_metric_on_def by blast
    thus "top1_real_bounded_metric u v = 0 \<longleftrightarrow> u = v"
      by simp
  qed

  have hSbdd:
    "\<And>x y. bdd_above ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
  proof -
    fix x y :: "'i \<Rightarrow> real"
    show "bdd_above ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
      unfolding bdd_above_def
    proof (rule exI[where x="1::real"], intro ballI)
      fix r
      assume hr: "r \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
      then obtain i where hi: "i \<in> I" and hr_eq: "r = top1_real_bounded_metric (x i) (y i)"
        by blast
      show "r \<le> (1::real)"
        unfolding hr_eq top1_real_bounded_metric_def by simp
    qed
  qed

  show ?thesis
    unfolding top1_metric_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X\<^sub>R. 0 \<le> top1_uniform_metric_real_on I x x"
    proof (intro ballI)
      fix x :: "'i \<Rightarrow> real"
      assume hx: "x \<in> X\<^sub>R"
      have hmem0:
        "top1_real_bounded_metric (x i0) (x i0) \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (x i)) ` I)"
        using hi0 by blast
      have "top1_real_bounded_metric (x i0) (x i0) \<le> top1_uniform_metric_real_on I x x"
        unfolding top1_uniform_metric_real_on_def
        by (rule cSup_upper[OF hmem0 hSbdd])
      thus "0 \<le> top1_uniform_metric_real_on I x x"
        unfolding top1_real_bounded_metric_def by simp
    qed

    show "\<forall>x\<in>X\<^sub>R. \<forall>y\<in>X\<^sub>R. 0 \<le> top1_uniform_metric_real_on I x y"
    proof (intro ballI)
      fix x :: "'i \<Rightarrow> real"
      fix y :: "'i \<Rightarrow> real"
      assume hx: "x \<in> X\<^sub>R"
      assume hy: "y \<in> X\<^sub>R"
      have hmem:
        "top1_real_bounded_metric (x i0) (y i0) \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
        using hi0 by blast
      have hle:
        "top1_real_bounded_metric (x i0) (y i0) \<le> top1_uniform_metric_real_on I x y"
        unfolding top1_uniform_metric_real_on_def
        by (rule cSup_upper[OF hmem hSbdd])
      have "0 \<le> top1_real_bounded_metric (x i0) (y i0)"
        unfolding top1_real_bounded_metric_def by simp
      thus "0 \<le> top1_uniform_metric_real_on I x y"
        using hle by linarith
    qed

    show "\<forall>x\<in>X\<^sub>R. \<forall>y\<in>X\<^sub>R. top1_uniform_metric_real_on I x y = 0 \<longleftrightarrow> x = y"
    proof (intro ballI)
      fix x :: "'i \<Rightarrow> real"
      fix y :: "'i \<Rightarrow> real"
      assume hx: "x \<in> X\<^sub>R"
      assume hy: "y \<in> X\<^sub>R"
      show "top1_uniform_metric_real_on I x y = 0 \<longleftrightarrow> x = y"
      proof (rule iffI)
        assume h0: "top1_uniform_metric_real_on I x y = 0"
        have hxext: "\<forall>i. i \<notin> I \<longrightarrow> x i = undefined"
          using hx unfolding X\<^sub>R_def XR_def top1_PiE_iff by blast
        have hyext: "\<forall>i. i \<notin> I \<longrightarrow> y i = undefined"
          using hy unfolding X\<^sub>R_def XR_def top1_PiE_iff by blast

        have hI: "\<forall>i\<in>I. x i = y i"
        proof (intro ballI)
          fix i assume hi: "i \<in> I"
          have hmem:
            "top1_real_bounded_metric (x i) (y i) \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
            using hi by blast
          have hle:
            "top1_real_bounded_metric (x i) (y i) \<le> top1_uniform_metric_real_on I x y"
            unfolding top1_uniform_metric_real_on_def
            by (rule cSup_upper[OF hmem hSbdd])
          have "0 \<le> top1_real_bounded_metric (x i) (y i)"
            unfolding top1_real_bounded_metric_def by simp
          have "top1_real_bounded_metric (x i) (y i) = 0"
            using h0 hle \<open>0 \<le> top1_real_bounded_metric (x i) (y i)\<close> by linarith
          thus "x i = y i"
            using h0iff by simp
        qed

        show "x = y"
        proof (rule ext)
          fix j
          show "x j = y j"
          proof (cases "j \<in> I")
            case True
            show ?thesis
              using hI True by blast
          next
            case False
            have "x j = undefined"
              using hxext False by blast
            moreover have "y j = undefined"
              using hyext False by blast
            ultimately show ?thesis
              by simp
          qed
        qed
      next
        assume hxy: "x = y"
        have hSne:
          "((\<lambda>i. top1_real_bounded_metric (x i) (x i)) ` I) \<noteq> {}"
          using hi0 by blast
        have hall0: "\<forall>r\<in>((\<lambda>i. top1_real_bounded_metric (x i) (x i)) ` I). r \<le> 0"
        proof (intro ballI)
          fix r
          assume hr: "r \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (x i)) ` I)"
          then obtain i where hi: "i \<in> I" and hr_eq: "r = top1_real_bounded_metric (x i) (x i)"
            by blast
          show "r \<le> 0"
            unfolding hr_eq top1_real_bounded_metric_def by simp
        qed
        have "top1_uniform_metric_real_on I x x \<le> 0"
          unfolding top1_uniform_metric_real_on_def
        proof (rule cSup_least[OF hSne])
          fix r
          assume hr: "r \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (x i)) ` I)"
          show "r \<le> 0"
            using hall0 hr by (rule bspec)
        qed
        moreover have "0 \<le> top1_uniform_metric_real_on I x x"
        proof -
          have hmem0:
            "top1_real_bounded_metric (x i0) (x i0) \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (x i)) ` I)"
            using hi0 by blast
          have "top1_real_bounded_metric (x i0) (x i0) \<le> top1_uniform_metric_real_on I x x"
            unfolding top1_uniform_metric_real_on_def
            by (rule cSup_upper[OF hmem0 hSbdd])
          thus ?thesis
            unfolding top1_real_bounded_metric_def by simp
        qed
        ultimately have "top1_uniform_metric_real_on I x x = 0"
          by linarith
        thus "top1_uniform_metric_real_on I x y = 0"
          using hxy by simp
      qed
    qed

    show "\<forall>x\<in>X\<^sub>R. \<forall>y\<in>X\<^sub>R. top1_uniform_metric_real_on I x y = top1_uniform_metric_real_on I y x"
    proof (intro ballI)
      fix x :: "'i \<Rightarrow> real"
      fix y :: "'i \<Rightarrow> real"
      assume hx: "x \<in> X\<^sub>R"
      assume hy: "y \<in> X\<^sub>R"
      have himg:
        "((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)
           = ((\<lambda>i. top1_real_bounded_metric (y i) (x i)) ` I)"
      proof (rule image_cong)
        show "I = I"
          by simp
        fix i assume "i \<in> I"
        show "top1_real_bounded_metric (x i) (y i) = top1_real_bounded_metric (y i) (x i)"
          unfolding top1_real_bounded_metric_def by (simp add: abs_minus_commute)
      qed
      show "top1_uniform_metric_real_on I x y = top1_uniform_metric_real_on I y x"
        unfolding top1_uniform_metric_real_on_def
        using himg by simp
    qed

    show "\<forall>x\<in>X\<^sub>R. \<forall>y\<in>X\<^sub>R. \<forall>z\<in>X\<^sub>R.
          top1_uniform_metric_real_on I x z \<le> top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I y z"
    proof (intro ballI)
      fix x :: "'i \<Rightarrow> real"
      fix y :: "'i \<Rightarrow> real"
      fix z :: "'i \<Rightarrow> real"
      assume hx: "x \<in> X\<^sub>R"
      assume hy: "y \<in> X\<^sub>R"
      assume hz: "z \<in> X\<^sub>R"

      define Sxz where "Sxz = ((\<lambda>i. top1_real_bounded_metric (x i) (z i)) ` I)"
      define Sxy where "Sxy = ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
      define Syz where "Syz = ((\<lambda>i. top1_real_bounded_metric (y i) (z i)) ` I)"

      have hSxz_ne: "Sxz \<noteq> {}"
        unfolding Sxz_def using hi0 by blast
      have hSxz_bdd: "bdd_above Sxz"
        unfolding Sxz_def by (rule hSbdd)

      have hall:
        "\<forall>r\<in>Sxz. r \<le> top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I y z"
      proof (intro ballI)
        fix r
        assume hr: "r \<in> Sxz"
        then obtain i where hi: "i \<in> I" and hr_eq: "r = top1_real_bounded_metric (x i) (z i)"
          unfolding Sxz_def by blast

        have htri:
          "top1_real_bounded_metric (x i) (z i)
            \<le> top1_real_bounded_metric (x i) (y i) + top1_real_bounded_metric (y i) (z i)"
          by (rule top1_real_bounded_metric_triangle)

        have hmem_xy:
          "top1_real_bounded_metric (x i) (y i) \<in> Sxy"
          unfolding Sxy_def using hi by blast
        have hmem_yz:
          "top1_real_bounded_metric (y i) (z i) \<in> Syz"
          unfolding Syz_def using hi by blast
        have hle_xy:
          "top1_real_bounded_metric (x i) (y i) \<le> top1_uniform_metric_real_on I x y"
        proof -
          have hbdd:
            "bdd_above ((\<lambda>j. top1_real_bounded_metric (x j) (y j)) ` I)"
            by (rule hSbdd)
          have "top1_real_bounded_metric (x i) (y i)
              \<le> (SUP j\<in>I. top1_real_bounded_metric (x j) (y j))"
            by (rule cSUP_upper[OF hi hbdd])
          thus ?thesis
            unfolding top1_uniform_metric_real_on_def by simp
        qed
        have hle_yz:
          "top1_real_bounded_metric (y i) (z i) \<le> top1_uniform_metric_real_on I y z"
        proof -
          have hbdd:
            "bdd_above ((\<lambda>j. top1_real_bounded_metric (y j) (z j)) ` I)"
            by (rule hSbdd)
          have "top1_real_bounded_metric (y i) (z i)
              \<le> (SUP j\<in>I. top1_real_bounded_metric (y j) (z j))"
            by (rule cSUP_upper[OF hi hbdd])
          thus ?thesis
            unfolding top1_uniform_metric_real_on_def by simp
        qed

        have "top1_real_bounded_metric (x i) (z i)
            \<le> top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I y z"
          using htri hle_xy hle_yz by linarith
        thus "r \<le> top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I y z"
          unfolding hr_eq by simp
      qed

      have "Sup Sxz \<le> top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I y z"
      proof (rule cSup_least[OF hSxz_ne])
        fix r
        assume hr: "r \<in> Sxz"
        show "r \<le> top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I y z"
          using hall hr by (rule bspec)
      qed
      thus "top1_uniform_metric_real_on I x z \<le> top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I y z"
        unfolding top1_uniform_metric_real_on_def Sxz_def by simp
    qed
  qed
qed

(** Uniform-coordinate metrics are uniformly bounded above (by 1), hence their images are bounded above. **)
lemma top1_uniform_metric_real_on_bdd_above:
  shows "bdd_above ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
proof -
  show ?thesis
    unfolding bdd_above_def
  proof (rule exI[where x="1::real"], intro ballI)
    fix r
    assume hr: "r \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (y i)) ` I)"
    then obtain i where hi: "i \<in> I" and hr_eq: "r = top1_real_bounded_metric (x i) (y i)"
      by blast
    show "r \<le> (1::real)"
      unfolding hr_eq top1_real_bounded_metric_def by simp
  qed
qed

(** Each coordinate distance is bounded by the uniform metric. **)
lemma top1_uniform_metric_real_on_coord_le:
  assumes hi: "i \<in> I"
  shows "top1_real_bounded_metric (x i) (y i) \<le> top1_uniform_metric_real_on I x y"
proof -
  have hmem:
    "top1_real_bounded_metric (x i) (y i) \<in> ((\<lambda>j. top1_real_bounded_metric (x j) (y j)) ` I)"
    using hi by blast
  have hbdd:
    "bdd_above ((\<lambda>j. top1_real_bounded_metric (x j) (y j)) ` I)"
    by (rule top1_uniform_metric_real_on_bdd_above)
  show ?thesis
    unfolding top1_uniform_metric_real_on_def
    by (rule cSup_upper[OF hmem hbdd])
qed

(** Specialized form of @{thm top1_uniform_metric_real_on_metric_on} without the auxiliary abbreviations. **)
lemma top1_uniform_metric_real_on_metric_on_PiE_UNIV:
  fixes I :: "'i set"
  assumes "I \<noteq> {}"
  shows "top1_metric_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_uniform_metric_real_on I)"
  using top1_uniform_metric_real_on_metric_on[OF assms] by simp

(** Reflexivity of the uniform metric on the carrier. **)
lemma top1_uniform_metric_real_on_refl:
  fixes I :: "'i set"
  assumes hne: "I \<noteq> {}"
  assumes hx: "x \<in> top1_PiE I (\<lambda>_. (UNIV::real set))"
  shows "top1_uniform_metric_real_on I x x = 0"
proof -
  have hmet:
    "top1_metric_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_uniform_metric_real_on I)"
    by (rule top1_uniform_metric_real_on_metric_on_PiE_UNIV[OF hne])
  have h0iff:
    "\<forall>u\<in>top1_PiE I (\<lambda>_. (UNIV::real set)). \<forall>v\<in>top1_PiE I (\<lambda>_. (UNIV::real set)).
        top1_uniform_metric_real_on I u v = 0 \<longleftrightarrow> u = v"
    using hmet unfolding top1_metric_on_def by blast
  have "top1_uniform_metric_real_on I x x = 0 \<longleftrightarrow> x = x"
    using h0iff hx by blast
  thus ?thesis
    by simp
qed

(** Munkres' metric inducing the product topology on \<open>\<real>^\<omega>\<close>.  We use \<open>Suc n\<close> in the denominator
    to match the intended indexing by the positive integers. **)
definition top1_D_metric_real_omega :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "top1_D_metric_real_omega x y =
     Sup ((\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) ` (UNIV::nat set))"

(** Each coordinate term of Munkres' \<open>D\<close>-metric is bounded above by 1. **)
lemma top1_D_metric_real_omega_term_le_1:
  shows "top1_real_bounded_metric (x n) (y n) / real (Suc n) \<le> (1::real)"
proof -
  have hpos: "0 < (real (Suc n) :: real)"
    by simp
  have hle1: "top1_real_bounded_metric (x n) (y n) \<le> (1::real)"
    unfolding top1_real_bounded_metric_def by simp
  have hle_den: "top1_real_bounded_metric (x n) (y n) \<le> real (Suc n)"
  proof -
    have h1le: "(1::real) \<le> real (Suc n)"
      by simp
    show ?thesis
      using hle1 h1le by linarith
  qed
  show ?thesis
    using hpos hle_den by (simp add: divide_le_eq)
qed

(** The defining set in \<open>top1_D_metric_real_omega\<close> is bounded above. **)
lemma top1_D_metric_real_omega_bdd_above:
  shows "bdd_above ((\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) ` (UNIV::nat set))"
  unfolding bdd_above_def
proof (rule exI[where x="1::real"], intro ballI)
  fix r
  assume hr: "r \<in> ((\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) ` (UNIV::nat set))"
  then obtain n where hn: "r = top1_real_bounded_metric (x n) (y n) / real (Suc n)"
    by blast
  show "r \<le> (1::real)"
    unfolding hn by (rule top1_D_metric_real_omega_term_le_1)
qed

(** Munkres' \<open>D\<close>-metric is always nonnegative. **)
lemma top1_D_metric_real_omega_nonneg:
  shows "0 \<le> top1_D_metric_real_omega x y"
proof -
  let ?S = "((\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) ` (UNIV::nat set))"
  have hmem: "(\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) 0 \<in> ?S"
  proof -
    have "(0::nat) \<in> (UNIV::nat set)"
      by simp
    then show ?thesis
      by (rule imageI)
  qed
  have hbdd: "bdd_above ?S"
    by (rule top1_D_metric_real_omega_bdd_above)
  have hle: "top1_real_bounded_metric (x 0) (y 0) / real (Suc 0) \<le> Sup ?S"
    by (rule cSup_upper[OF hmem hbdd])
  have h0le: "0 \<le> top1_real_bounded_metric (x 0) (y 0) / real (Suc 0)"
  proof -
    have h0: "0 \<le> top1_real_bounded_metric (x 0) (y 0)"
      unfolding top1_real_bounded_metric_def by simp
    have hpos: "0 < (real (Suc 0) :: real)"
      by simp
    show ?thesis
      using h0 hpos by simp
  qed
  have "0 \<le> Sup ?S"
    using h0le hle by linarith
  thus ?thesis
    unfolding top1_D_metric_real_omega_def by simp
qed

(** Munkres' \<open>D\<close>-metric is always bounded above by 1. **)
lemma top1_D_metric_real_omega_le_1:
  shows "top1_D_metric_real_omega x y \<le> (1::real)"
proof -
  let ?S = "((\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) ` (UNIV::nat set))"
  have hSne: "?S \<noteq> {}"
    by simp
  have hbdd: "bdd_above ?S"
    by (rule top1_D_metric_real_omega_bdd_above)
  have "Sup ?S \<le> (1::real)"
  proof (rule cSup_least[OF hSne])
    fix xa
    assume hxa: "xa \<in> ?S"
    then obtain n where hn: "xa = top1_real_bounded_metric (x n) (y n) / real (Suc n)"
      by blast
    show "xa \<le> (1::real)"
      unfolding hn by (rule top1_D_metric_real_omega_term_le_1)
  qed
  thus ?thesis
    unfolding top1_D_metric_real_omega_def by simp
qed

(** Munkres' \<open>D\<close>-metric is reflexive. **)
lemma top1_D_metric_real_omega_refl:
  shows "top1_D_metric_real_omega x x = 0"
proof -
  let ?S = "((\<lambda>n. top1_real_bounded_metric (x n) (x n) / real (Suc n)) ` (UNIV::nat set))"

  have hSeq: "?S = {0}"
  proof (rule set_eqI)
    fix r
    show "r \<in> ?S \<longleftrightarrow> r \<in> {0}"
    proof
      assume hr: "r \<in> ?S"
      then obtain n where hn: "r = top1_real_bounded_metric (x n) (x n) / real (Suc n)"
        by blast
      have h0: "top1_real_bounded_metric (x n) (x n) = 0"
        unfolding top1_real_bounded_metric_def by simp
      have "r = 0"
        unfolding hn h0 by simp
      then show "r \<in> {0}"
        by simp
    next
      assume "r \<in> {0}"
      then have hr0: "r = 0"
        by simp
      have h0: "top1_real_bounded_metric (x 0) (x 0) = 0"
        unfolding top1_real_bounded_metric_def by simp
      have hmem0: "0 \<in> ?S"
      proof -
        have "(0::nat) \<in> (UNIV::nat set)"
          by simp
        then have "(\<lambda>n. top1_real_bounded_metric (x n) (x n) / real (Suc n)) 0 \<in> ?S"
          by (rule imageI)
        then show ?thesis
          unfolding h0 by simp
      qed
      show "r \<in> ?S"
        unfolding hr0 using hmem0 by simp
    qed
  qed

  show ?thesis
    unfolding top1_D_metric_real_omega_def
    unfolding hSeq
    by simp
qed

(** Munkres' \<open>D\<close>-metric is symmetric. **)
lemma top1_D_metric_real_omega_sym:
  shows "top1_D_metric_real_omega x y = top1_D_metric_real_omega y x"
proof -
  let ?Sxy = "((\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) ` (UNIV::nat set))"
  let ?Syx = "((\<lambda>n. top1_real_bounded_metric (y n) (x n) / real (Suc n)) ` (UNIV::nat set))"

  have hsets: "?Sxy = ?Syx"
  proof (rule set_eqI)
    fix r
    show "r \<in> ?Sxy \<longleftrightarrow> r \<in> ?Syx"
    proof
      assume hr: "r \<in> ?Sxy"
      then obtain n where hn: "r = top1_real_bounded_metric (x n) (y n) / real (Suc n)"
        by blast
      have hsym: "top1_real_bounded_metric (x n) (y n) = top1_real_bounded_metric (y n) (x n)"
        unfolding top1_real_bounded_metric_def by (simp add: abs_minus_commute algebra_simps)
      have "r = top1_real_bounded_metric (y n) (x n) / real (Suc n)"
        unfolding hn hsym by simp
      then show "r \<in> ?Syx"
        by blast
    next
      assume hr: "r \<in> ?Syx"
      then obtain n where hn: "r = top1_real_bounded_metric (y n) (x n) / real (Suc n)"
        by blast
      have hsym: "top1_real_bounded_metric (y n) (x n) = top1_real_bounded_metric (x n) (y n)"
        unfolding top1_real_bounded_metric_def by (simp add: abs_minus_commute algebra_simps)
      have "r = top1_real_bounded_metric (x n) (y n) / real (Suc n)"
        unfolding hn hsym by simp
      then show "r \<in> ?Sxy"
        by blast
    qed
  qed

  show ?thesis
    unfolding top1_D_metric_real_omega_def
    unfolding hsets
    by simp
qed

(** Munkres' \<open>D\<close>-metric vanishes iff the arguments are equal (pointwise). **)
lemma top1_D_metric_real_omega_0_iff:
  shows "top1_D_metric_real_omega x y = 0 \<longleftrightarrow> x = y"
proof (rule iffI)
  assume h0: "top1_D_metric_real_omega x y = 0"
  show "x = y"
  proof (rule ext)
    fix n :: nat
    let ?S = "((\<lambda>k. top1_real_bounded_metric (x k) (y k) / real (Suc k)) ` (UNIV::nat set))"
    have hbdd: "bdd_above ?S"
      by (rule top1_D_metric_real_omega_bdd_above)
    have hmem: "top1_real_bounded_metric (x n) (y n) / real (Suc n) \<in> ?S"
      by simp
    have hle: "top1_real_bounded_metric (x n) (y n) / real (Suc n) \<le> Sup ?S"
      by (rule cSup_upper[OF hmem hbdd])
    have hSup0: "Sup ?S = 0"
      using h0 unfolding top1_D_metric_real_omega_def by simp
    have hle0: "top1_real_bounded_metric (x n) (y n) / real (Suc n) \<le> 0"
      using hle unfolding hSup0 by simp

    have hge0: "0 \<le> top1_real_bounded_metric (x n) (y n) / real (Suc n)"
    proof -
      have hnonneg: "0 \<le> top1_real_bounded_metric (x n) (y n)"
        unfolding top1_real_bounded_metric_def by simp
      have hpos: "0 < (real (Suc n) :: real)"
        by simp
      show ?thesis
        using hnonneg hpos by simp
    qed

    have hterm0: "top1_real_bounded_metric (x n) (y n) / real (Suc n) = 0"
      using hge0 hle0 by linarith
    have hden_ne: "(real (Suc n) :: real) \<noteq> 0"
      by simp
    have hbm0: "top1_real_bounded_metric (x n) (y n) = 0"
      using hterm0 hden_ne by simp

    have h0iff: "\<forall>u\<in>UNIV. \<forall>v\<in>UNIV. top1_real_bounded_metric u v = 0 \<longleftrightarrow> u = v"
      using top1_real_bounded_metric_metric_on unfolding top1_metric_on_def by blast
    show "x n = y n"
      using h0iff hbm0 by blast
  qed
next
  assume hxy: "x = y"
  show "top1_D_metric_real_omega x y = 0"
    using hxy by (simp add: top1_D_metric_real_omega_refl)
qed

(** Triangle inequality for Munkres' \<open>D\<close>-metric (proof deferred). **)
lemma top1_D_metric_real_omega_triangle:
  shows "top1_D_metric_real_omega x z \<le> top1_D_metric_real_omega x y + top1_D_metric_real_omega y z"
proof -
  let ?Sxz = "((\<lambda>n. top1_real_bounded_metric (x n) (z n) / real (Suc n)) ` (UNIV::nat set))"
  let ?Sxy = "((\<lambda>n. top1_real_bounded_metric (x n) (y n) / real (Suc n)) ` (UNIV::nat set))"
  let ?Syz = "((\<lambda>n. top1_real_bounded_metric (y n) (z n) / real (Suc n)) ` (UNIV::nat set))"

  have hSne_xz: "?Sxz \<noteq> {}"
    by simp
  have hbdd_xz: "bdd_above ?Sxz"
    by (rule top1_D_metric_real_omega_bdd_above)
  have hbdd_xy: "bdd_above ?Sxy"
    by (rule top1_D_metric_real_omega_bdd_above)
  have hbdd_yz: "bdd_above ?Syz"
    by (rule top1_D_metric_real_omega_bdd_above)

  have hall: "\<forall>xa\<in>?Sxz. xa \<le> Sup ?Sxy + Sup ?Syz"
  proof (intro ballI)
    fix xa
    assume hxa: "xa \<in> ?Sxz"
    then obtain n where hn:
      "xa = top1_real_bounded_metric (x n) (z n) / real (Suc n)"
      by blast

    have hpos: "0 < (real (Suc n) :: real)"
      by simp
    have htri:
      "top1_real_bounded_metric (x n) (z n)
        \<le> top1_real_bounded_metric (x n) (y n) + top1_real_bounded_metric (y n) (z n)"
      by (rule top1_real_bounded_metric_triangle)
    have hdiv:
      "top1_real_bounded_metric (x n) (z n) / real (Suc n)
        \<le> (top1_real_bounded_metric (x n) (y n) + top1_real_bounded_metric (y n) (z n)) / real (Suc n)"
    proof -
      have hnonneg: "0 \<le> (real (Suc n) :: real)"
        by simp
      show ?thesis
        by (rule divide_right_mono[OF htri hnonneg])
    qed
    have hsplit:
      "(top1_real_bounded_metric (x n) (y n) + top1_real_bounded_metric (y n) (z n)) / real (Suc n)
        = top1_real_bounded_metric (x n) (y n) / real (Suc n)
          + top1_real_bounded_metric (y n) (z n) / real (Suc n)"
      by (simp add: add_divide_distrib)

    have hmem_xy:
      "top1_real_bounded_metric (x n) (y n) / real (Suc n) \<in> ?Sxy"
      by simp
    have hmem_yz:
      "top1_real_bounded_metric (y n) (z n) / real (Suc n) \<in> ?Syz"
      by simp

    have hle_xy: "top1_real_bounded_metric (x n) (y n) / real (Suc n) \<le> Sup ?Sxy"
      by (rule cSup_upper[OF hmem_xy hbdd_xy])
    have hle_yz: "top1_real_bounded_metric (y n) (z n) / real (Suc n) \<le> Sup ?Syz"
      by (rule cSup_upper[OF hmem_yz hbdd_yz])

    have hsum_le: "top1_real_bounded_metric (x n) (y n) / real (Suc n)
        + top1_real_bounded_metric (y n) (z n) / real (Suc n) \<le> Sup ?Sxy + Sup ?Syz"
      using hle_xy hle_yz by linarith

    show "xa \<le> Sup ?Sxy + Sup ?Syz"
    proof -
      have hxa0: "xa = top1_real_bounded_metric (x n) (z n) / real (Suc n)"
        by (rule hn)
      have hxa1: "xa \<le> (top1_real_bounded_metric (x n) (y n) + top1_real_bounded_metric (y n) (z n)) / real (Suc n)"
        using hdiv unfolding hxa0 by simp
      have hxa2: "xa \<le> top1_real_bounded_metric (x n) (y n) / real (Suc n)
          + top1_real_bounded_metric (y n) (z n) / real (Suc n)"
      proof -
        have hEq:
          "(top1_real_bounded_metric (x n) (y n) + top1_real_bounded_metric (y n) (z n)) / real (Suc n)
            = top1_real_bounded_metric (x n) (y n) / real (Suc n)
              + top1_real_bounded_metric (y n) (z n) / real (Suc n)"
          by (simp add: add_divide_distrib)
        show ?thesis
          using hxa1 unfolding hEq by simp
      qed
      show ?thesis
      proof -
        have "xa \<le> Sup ?Sxy + Sup ?Syz"
          using hxa2 hsum_le by linarith
        then show ?thesis
          by simp
      qed
    qed
  qed

  have hSup_le: "Sup ?Sxz \<le> Sup ?Sxy + Sup ?Syz"
  proof (rule cSup_least[OF hSne_xz])
    fix xa
    assume hxa: "xa \<in> ?Sxz"
    show "xa \<le> Sup ?Sxy + Sup ?Syz"
      by (rule bspec[OF hall hxa])
  qed

  have hfinal1: "top1_D_metric_real_omega x z \<le> Sup ?Sxy + Sup ?Syz"
    unfolding top1_D_metric_real_omega_def using hSup_le by simp
  have hfinal2: "Sup ?Sxy + Sup ?Syz = top1_D_metric_real_omega x y + top1_D_metric_real_omega y z"
    unfolding top1_D_metric_real_omega_def by simp
  show ?thesis
    using hfinal1 unfolding hfinal2 by simp
qed

(** Each coordinate contribution is bounded above by the \<open>D\<close>-distance. **)
lemma top1_D_metric_real_omega_term_le:
  shows "top1_real_bounded_metric (x n) (y n) / real (Suc n) \<le> top1_D_metric_real_omega x y"
proof -
  let ?S = "((\<lambda>k. top1_real_bounded_metric (x k) (y k) / real (Suc k)) ` (UNIV::nat set))"
  have hmem: "(\<lambda>k. top1_real_bounded_metric (x k) (y k) / real (Suc k)) n \<in> ?S"
    by (rule imageI) simp
  have hbdd: "bdd_above ?S"
    by (rule top1_D_metric_real_omega_bdd_above)
  show ?thesis
    unfolding top1_D_metric_real_omega_def
    by (rule cSup_upper[OF hmem hbdd])
qed

(** If every basis element in \<open>B\<^sub>1\<close> is open in the topology generated by \<open>B\<^sub>2\<close>,
    then the topology generated by \<open>B\<^sub>1\<close> is included in that generated by \<open>B\<^sub>2\<close>. **)
lemma topology_generated_by_basis_mono_via_basis_elems:
  assumes hmem: "\<And>b. b \<in> B1 \<Longrightarrow> b \<in> topology_generated_by_basis X B2"
  shows "topology_generated_by_basis X B1 \<subseteq> topology_generated_by_basis X B2"
proof (rule subsetI)
  fix U
  assume hU: "U \<in> topology_generated_by_basis X B1"

  have hUsub: "U \<subseteq> X"
    using hU unfolding topology_generated_by_basis_def by blast
  have hUcov: "\<forall>x\<in>U. \<exists>b1\<in>B1. x \<in> b1 \<and> b1 \<subseteq> U"
    using hU unfolding topology_generated_by_basis_def by blast

  show "U \<in> topology_generated_by_basis X B2"
    unfolding topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "U \<subseteq> X"
      by (rule hUsub)

    show "\<forall>x\<in>U. \<exists>b\<in>B2. x \<in> b \<and> b \<subseteq> U"
    proof (intro ballI)
      fix x
      assume hxU: "x \<in> U"
      obtain b1 where hb1: "b1 \<in> B1" and hxb1: "x \<in> b1" and hb1sub: "b1 \<subseteq> U"
        using hUcov hxU by blast

      have hb1_open: "b1 \<in> topology_generated_by_basis X B2"
        by (rule hmem[OF hb1])
      have hb1_cov: "\<forall>y\<in>b1. \<exists>b2\<in>B2. y \<in> b2 \<and> b2 \<subseteq> b1"
        using hb1_open unfolding topology_generated_by_basis_def by blast
      obtain b2 where hb2: "b2 \<in> B2" and hxb2: "x \<in> b2" and hb2sub: "b2 \<subseteq> b1"
        using hb1_cov hxb1 by blast

      have hb2subU: "b2 \<subseteq> U"
        using hb2sub hb1sub by blast
      show "\<exists>b\<in>B2. x \<in> b \<and> b \<subseteq> U"
        using hb2 hxb2 hb2subU by blast
    qed
  qed
qed

(** On \<open>\<real>\<close>, every order-open set contains a symmetric open interval around each of its points. **)
lemma order_topology_on_UNIV_open_interval_subset_real:
  fixes U :: "real set"
  assumes hU: "U \<in> (order_topology_on_UNIV::real set set)"
  assumes hy: "y \<in> U"
  shows "\<exists>e>0. open_interval (y - e) (y + e) \<subseteq> U"
proof -
  have hUgen:
    "U \<in> topology_generated_by_basis (UNIV::real set) basis_order_topology"
    using hU unfolding order_topology_on_UNIV_def by simp
  have hUpt: "\<forall>x\<in>U. \<exists>b\<in>basis_order_topology. x \<in> b \<and> b \<subseteq> U"
    using hUgen unfolding topology_generated_by_basis_def by blast
  obtain b where hbB: "b \<in> basis_order_topology" and hyb: "y \<in> b" and hbsub: "b \<subseteq> U"
    using hUpt hy by blast

  have hb_cases:
      "b = (UNIV::real set)
      \<or> (\<exists>a c. a < c \<and> b = open_interval a c)
      \<or> (\<exists>a. b = open_ray_gt a)
      \<or> (\<exists>a. b = open_ray_lt a)"
    using hbB unfolding basis_order_topology_def by blast

  from hb_cases consider
      (univ) "b = (UNIV::real set)"
    | (int) a c where "a < c" and "b = open_interval a c"
    | (gt) a where "b = open_ray_gt a"
    | (lt) a where "b = open_ray_lt a"
    by blast
  then show ?thesis
  proof cases
    case univ
    have hUuniv: "(UNIV::real set) \<subseteq> U"
      using hbsub univ by simp
    have hsub_univ: "open_interval (y - 1) (y + 1) \<subseteq> (UNIV::real set)"
      by simp
    have hsub1: "open_interval (y - 1) (y + 1) \<subseteq> U"
      by (rule subset_trans[OF hsub_univ hUuniv])
    show ?thesis
      apply (rule exI[where x=1])
      apply (intro conjI)
       apply simp
      apply (rule hsub1)
      done
  next
    case (int a c)
    have hac: "a < c"
      by (rule int(1))
    have hb: "b = open_interval a c"
      by (rule int(2))
    have hay: "a < y" and hyc: "y < c"
      using hyb unfolding hb open_interval_def by blast+
    define e where "e = min (y - a) (c - y) / 2"
    have he_pos: "e > 0"
      unfolding e_def using hay hyc by simp
    have hsubb: "open_interval (y - e) (y + e) \<subseteq> b"
    proof
      fix t
      assume ht: "t \<in> open_interval (y - e) (y + e)"
      have h1: "y - e < t"
        using ht unfolding open_interval_def by auto
      have h2: "t < y + e"
        using ht unfolding open_interval_def by auto
      have he_conj: "e \<le> (y - a) / 2 \<and> e \<le> (c - y) / 2"
        unfolding e_def by simp
      have he1: "e \<le> (y - a) / 2"
        using he_conj by (rule conjunct1)
      have he2: "e \<le> (c - y) / 2"
        using he_conj by (rule conjunct2)
		  have hae: "a < y - e"
			  proof -
			    have hyapos: "0 < y - a"
			      using hay by linarith
		        have hhalf: "(y - a) / 2 \<le> y - a"
	        proof -
	          have hnonneg: "0 \<le> y - a"
	            using hyapos by linarith
	          have "(1/2::real) \<le> 1"
	            by simp
	          hence "(1/2::real) * (y - a) \<le> 1 * (y - a)"
	            by (rule mult_right_mono[OF _ hnonneg])
		          thus ?thesis
		            by simp
		        qed
	        have hhalf_lt: "(y - a) / 2 < y - a"
	        proof -
	          have hcoef: "(1/2::real) < 1"
	            by simp
	          have "(1/2::real) * (y - a) < 1 * (y - a)"
	            by (rule mult_strict_right_mono[OF hcoef hyapos])
	          thus ?thesis
	            by simp
	        qed
		        have "e < y - a"
		          using he1 hhalf_lt by linarith
		        thus ?thesis
		          by linarith
	      qed
		      have hec: "y + e < c"
		      proof -
		        have hepos: "0 < e"
		          using he_pos .
		        have h2e: "2 * e \<le> c - y"
		        proof -
		          have hnonneg2: "0 \<le> (2::real)"
		            by simp
		          have "2 * e \<le> 2 * ((c - y) / 2)"
		            using mult_left_mono[OF he2 hnonneg2] by simp
		          thus ?thesis
		            by (simp add: field_simps)
		        qed
		        have "y + 2 * e \<le> c"
		          using h2e by linarith
		        moreover have "y + e < y + 2 * e"
		          using hepos by linarith
		        ultimately show ?thesis
		          by linarith
		      qed
      have "a < t"
        using hae h1 by linarith
      moreover have "t < c"
        using h2 hec by linarith
      ultimately show "t \<in> b"
        unfolding hb open_interval_def by blast
    qed
    have "open_interval (y - e) (y + e) \<subseteq> U"
      using hsubb hbsub by blast
    thus ?thesis
      using he_pos by blast
  next
    case (gt a)
    have hb: "b = open_ray_gt a"
      by (rule gt)
    have hay: "a < y"
      using hyb unfolding hb open_ray_gt_def by blast
    define e where "e = (y - a) / 2"
    have he_pos: "e > 0"
      using hay unfolding e_def by simp
    have hsubb: "open_interval (y - e) (y + e) \<subseteq> b"
    proof
      fix t
      assume ht: "t \<in> open_interval (y - e) (y + e)"
      have h1: "y - e < t"
        using ht unfolding open_interval_def by blast
      have "a < y - e"
      proof -
        have h2pos: "0 < (2::real)"
          by simp
        have hmul: "a * 2 < y + a"
          using hay by linarith
        have hahalf: "a < (y + a) / 2"
          using h2pos hmul by (simp add: less_divide_eq)
        show ?thesis
          using hahalf by (simp add: e_def field_simps)
      qed
      hence "a < t"
        using h1 by linarith
      thus "t \<in> b"
        unfolding hb open_ray_gt_def by blast
    qed
    have "open_interval (y - e) (y + e) \<subseteq> U"
      using hsubb hbsub by blast
    thus ?thesis
      using he_pos by blast
  next
    case (lt a)
    have hb: "b = open_ray_lt a"
      by (rule lt)
    have hya: "y < a"
      using hyb unfolding hb open_ray_lt_def by blast
    define e where "e = (a - y) / 2"
    have he_pos: "e > 0"
      using hya unfolding e_def by simp
    have hsubb: "open_interval (y - e) (y + e) \<subseteq> b"
    proof
      fix t
      assume ht: "t \<in> open_interval (y - e) (y + e)"
      have h2: "t < y + e"
        using ht unfolding open_interval_def by blast
      have "y + e < a"
      proof -
        have h2pos: "0 < (2::real)"
          by simp
        have hsum: "y + a < a * 2"
          using hya by linarith
        have hhalf: "(y + a) / 2 < a"
          using h2pos hsum by (simp add: less_divide_eq)
        show ?thesis
          using hhalf by (simp add: e_def field_simps)
      qed
      hence "t < a"
        using h2 by linarith
      thus "t \<in> b"
        unfolding hb open_ray_lt_def by blast
    qed
    have "open_interval (y - e) (y + e) \<subseteq> U"
      using hsubb hbsub by blast
    thus ?thesis
      using he_pos by blast
  qed
qed

(** For a finite, nonempty index set, the sup-metric inequality can be read coordinatewise. **)
lemma top1_square_metric_real_on_lt_iff:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  shows "top1_square_metric_real_on I x y < e \<longleftrightarrow> (\<forall>i\<in>I. abs (x i - y i) < e)"
proof -
  let ?S = "(\<lambda>i. abs (x i - y i)) ` I"
  have hfinS: "finite ?S"
    using hfin by simp
  have hneS: "?S \<noteq> {}"
    using hne by simp
  have hSup: "Sup ?S = Max ?S"
    by (rule cSup_eq_Max[OF hfinS hneS])
  show ?thesis
  proof (rule iffI)
    assume hlt: "top1_square_metric_real_on I x y < e"
    have hMaxlt: "Max ?S < e"
      using hlt unfolding top1_square_metric_real_on_def hSup by simp
    show "\<forall>i\<in>I. abs (x i - y i) < e"
    proof (intro ballI)
      fix i
      assume hi: "i \<in> I"
      have hmem: "abs (x i - y i) \<in> ?S"
        using hi by simp
      have hle: "abs (x i - y i) \<le> Max ?S"
        by (rule Max_ge[OF hfinS hmem])
      show "abs (x i - y i) < e"
        using hle hMaxlt by linarith
    qed
  next
    assume hall: "\<forall>i\<in>I. abs (x i - y i) < e"
    have hMaxin: "Max ?S \<in> ?S"
      by (rule Max_in[OF hfinS hneS])
    then obtain i where hi: "i \<in> I" and hMax: "Max ?S = abs (x i - y i)"
      by blast
    have hMaxlt: "Max ?S < e"
      using hall[rule_format, OF hi] unfolding hMax by simp
    have "Sup ?S < e"
      unfolding hSup using hMaxlt by simp
    thus "top1_square_metric_real_on I x y < e"
      unfolding top1_square_metric_real_on_def by simp
  qed
qed

(** Absolute-value inequality as an open-interval condition. **)
lemma abs_diff_lt_iff_mem_open_interval:
  fixes a b e :: real
  shows "abs (a - b) < e \<longleftrightarrow> b \<in> open_interval (a - e) (a + e)"
proof (rule iffI)
  assume habs: "abs (a - b) < e"
  have h12: "- e < a - b \<and> a - b < e"
    using habs by (simp add: abs_less_iff)
  have h1: "- e < a - b"
    using h12 by simp
  have h2: "a - b < e"
    using h12 by simp
  have hab1: "a - e < b"
    using h2 by linarith
  have hab2: "b < a + e"
    using h1 by linarith
  show "b \<in> open_interval (a - e) (a + e)"
    unfolding open_interval_def using hab1 hab2 by simp
next
  assume hb: "b \<in> open_interval (a - e) (a + e)"
  have hab1: "a - e < b"
    using hb unfolding open_interval_def by simp
  have hab2: "b < a + e"
    using hb unfolding open_interval_def by simp
  have h1: "- e < a - b"
    using hab2 by linarith
  have h2: "a - b < e"
    using hab1 by linarith
  have "- e < a - b \<and> a - b < e"
    using h1 h2 by simp
  thus "abs (a - b) < e"
    by (simp add: abs_less_iff)
qed

(** Coordinate differences are bounded above by the Euclidean distance. **)
lemma top1_euclidean_metric_real_on_coord_le:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hi: "i \<in> I"
  shows "abs (x i - y i) \<le> top1_euclidean_metric_real_on I x y"
proof -
  let ?S = "(\<Sum>j\<in>I. (x j - y j)\<^sup>2)"
  have hS_nonneg: "0 \<le> ?S"
    by (rule sum_nonneg) simp
  have hrest_nonneg: "0 \<le> (\<Sum>j\<in>I - {i}. (x j - y j)\<^sup>2)"
    by (rule sum_nonneg) simp
  have hdecomp: "?S = (x i - y i)\<^sup>2 + (\<Sum>j\<in>I - {i}. (x j - y j)\<^sup>2)"
    using hfin hi by (simp add: sum.remove)
  have hterm_le: "(x i - y i)\<^sup>2 \<le> ?S"
    using hdecomp hrest_nonneg by linarith
  have "sqrt ((x i - y i)\<^sup>2) \<le> sqrt ?S"
    by (rule real_sqrt_le_mono[OF hterm_le])
  thus ?thesis
    unfolding top1_euclidean_metric_real_on_def
    by (simp add: hS_nonneg)
qed

(** On finite products, the sup metric is bounded above by the Euclidean metric. **)
lemma top1_square_metric_real_on_le_euclidean:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  shows "top1_square_metric_real_on I x y \<le> top1_euclidean_metric_real_on I x y"
proof -
  let ?S = "(\<lambda>i. abs (x i - y i)) ` I"
  have hfinS: "finite ?S"
    using hfin by simp
  have hneS: "?S \<noteq> {}"
    using hne by simp
  have hSup: "Sup ?S = Max ?S"
    by (rule cSup_eq_Max[OF hfinS hneS])

  have hall: "\<forall>r\<in>?S. r \<le> top1_euclidean_metric_real_on I x y"
  proof (intro ballI)
    fix r
    assume hr: "r \<in> ?S"
    then obtain i where hi: "i \<in> I" and hr_eq: "r = abs (x i - y i)"
      by blast
    show "r \<le> top1_euclidean_metric_real_on I x y"
      unfolding hr_eq by (rule top1_euclidean_metric_real_on_coord_le[OF hfin hi])
  qed

  have hMaxin: "Max ?S \<in> ?S"
    by (rule Max_in[OF hfinS hneS])
  have "Max ?S \<le> top1_euclidean_metric_real_on I x y"
    by (rule bspec[OF hall hMaxin])
  thus ?thesis
    unfolding top1_square_metric_real_on_def hSup by simp
qed

(** Triangle inequality for the sup metric on finite products. **)
lemma top1_square_metric_real_on_triangle:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  shows "top1_square_metric_real_on I x z
    \<le> top1_square_metric_real_on I x y + top1_square_metric_real_on I y z"
proof -
  let ?Sxz = "(\<lambda>i. abs (x i - z i)) ` I"
  let ?Sxy = "(\<lambda>i. abs (x i - y i)) ` I"
  let ?Syz = "(\<lambda>i. abs (y i - z i)) ` I"
  have hfinS: "finite ?Sxz" "finite ?Sxy" "finite ?Syz"
  proof -
    show "finite ?Sxz"
      using hfin by simp
    show "finite ?Sxy"
      using hfin by simp
    show "finite ?Syz"
      using hfin by simp
  qed
  have hneS: "?Sxz \<noteq> {}" "?Sxy \<noteq> {}" "?Syz \<noteq> {}"
  proof -
    show "?Sxz \<noteq> {}"
      using hne by simp
    show "?Sxy \<noteq> {}"
      using hne by simp
    show "?Syz \<noteq> {}"
      using hne by simp
  qed

  have hSupxz: "top1_square_metric_real_on I x z = Max ?Sxz"
    unfolding top1_square_metric_real_on_def by (simp add: cSup_eq_Max[OF hfinS(1) hneS(1)])
  have hSupxy: "top1_square_metric_real_on I x y = Max ?Sxy"
    unfolding top1_square_metric_real_on_def by (simp add: cSup_eq_Max[OF hfinS(2) hneS(2)])
  have hSupyz: "top1_square_metric_real_on I y z = Max ?Syz"
    unfolding top1_square_metric_real_on_def by (simp add: cSup_eq_Max[OF hfinS(3) hneS(3)])

  have hall: "\<forall>r\<in>?Sxz. r \<le> top1_square_metric_real_on I x y + top1_square_metric_real_on I y z"
  proof (intro ballI)
    fix r
    assume hr: "r \<in> ?Sxz"
    then obtain i where hi: "i \<in> I" and hr_eq: "r = abs (x i - z i)"
      by blast
    have htri: "abs (x i - z i) \<le> abs (x i - y i) + abs (y i - z i)"
      by (simp add: abs_triangle_ineq4)
    have hxy: "abs (x i - y i) \<le> top1_square_metric_real_on I x y"
    proof -
      have "abs (x i - y i) \<in> ?Sxy"
        using hi by simp
      hence "abs (x i - y i) \<le> Max ?Sxy"
        using Max_ge[OF hfinS(2)] by blast
      thus ?thesis
        unfolding hSupxy by simp
    qed
    have hyz: "abs (y i - z i) \<le> top1_square_metric_real_on I y z"
    proof -
      have "abs (y i - z i) \<in> ?Syz"
        using hi by simp
      hence "abs (y i - z i) \<le> Max ?Syz"
        using Max_ge[OF hfinS(3)] by blast
      thus ?thesis
        unfolding hSupyz by simp
    qed
    show "r \<le> top1_square_metric_real_on I x y + top1_square_metric_real_on I y z"
      unfolding hr_eq using htri hxy hyz by linarith
  qed

  have hMaxin: "Max ?Sxz \<in> ?Sxz"
    by (rule Max_in[OF hfinS(1) hneS(1)])
  have "Max ?Sxz \<le> top1_square_metric_real_on I x y + top1_square_metric_real_on I y z"
    by (rule bspec[OF hall hMaxin])
  thus ?thesis
    unfolding hSupxz by simp
qed

(** Coordinate differences are bounded above by the square/sup distance (finite, nonempty index set). **)
lemma top1_square_metric_real_on_coord_le:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  assumes hi: "i \<in> I"
  shows "abs (x i - y i) \<le> top1_square_metric_real_on I x y"
proof -
  let ?S = "(\<lambda>j. abs (x j - y j)) ` I"
  have hfinS: "finite ?S"
    using hfin by simp
  have hneS: "?S \<noteq> {}"
    using hne by simp
  have hSup: "Sup ?S = Max ?S"
    by (rule cSup_eq_Max[OF hfinS hneS])
  have hmem: "abs (x i - y i) \<in> ?S"
    using hi by simp
  have "abs (x i - y i) \<le> Max ?S"
    by (rule Max_ge[OF hfinS hmem])
  thus ?thesis
    unfolding top1_square_metric_real_on_def hSup by simp
qed

(** On finite products, the Euclidean metric is bounded above by a constant multiple of the sup metric. **)
lemma top1_euclidean_metric_real_on_le_sqrt_card_mul_square:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  shows "top1_euclidean_metric_real_on I x y
    \<le> sqrt (real (card I)) * top1_square_metric_real_on I x y"
proof -
  obtain i0 where hi0: "i0 \<in> I"
    using hne by blast
  let ?M = "top1_square_metric_real_on I x y"
  have hM_nonneg: "0 \<le> ?M"
  proof -
    have "0 \<le> abs (x i0 - y i0)"
      by simp
    moreover have "abs (x i0 - y i0) \<le> ?M"
      by (rule top1_square_metric_real_on_coord_le[OF hfin hne hi0])
    ultimately show ?thesis
      by linarith
  qed

  have hsum_le:
    "(\<Sum>i\<in>I. (x i - y i)\<^sup>2) \<le> real (card I) * ?M\<^sup>2"
  proof -
    have hpt: "\<And>i. i \<in> I \<Longrightarrow> (x i - y i)\<^sup>2 \<le> ?M\<^sup>2"
    proof -
      fix i
      assume hi: "i \<in> I"
	      have habs_le: "abs (x i - y i) \<le> ?M"
	        by (rule top1_square_metric_real_on_coord_le[OF hfin hne hi])
		      have habs_nonneg: "0 \<le> abs (x i - y i)"
		        by simp
		      have hsq: "(abs (x i - y i))\<^sup>2 \<le> ?M\<^sup>2"
		        using habs_le habs_nonneg hM_nonneg
		        apply (intro power_mono; simp)
		        done
		      show "(x i - y i)\<^sup>2 \<le> ?M\<^sup>2"
		        using hsq by simp
		    qed
	    have "(\<Sum>i\<in>I. (x i - y i)\<^sup>2) \<le> (\<Sum>i\<in>I. ?M\<^sup>2)"
	    proof (rule sum_mono)
	      fix i
	      assume hi: "i \<in> I"
	      show "(x i - y i)\<^sup>2 \<le> ?M\<^sup>2"
	        by (rule hpt[OF hi])
	    qed
	    also have "... = real (card I) * ?M\<^sup>2"
	      by simp
	    finally show ?thesis
	      .
  qed

  have hsum_nonneg: "0 \<le> (\<Sum>i\<in>I. (x i - y i)\<^sup>2)"
    by (rule sum_nonneg) simp
  have hcard_nonneg: "0 \<le> real (card I)"
    by simp

  have "top1_euclidean_metric_real_on I x y = sqrt (\<Sum>i\<in>I. (x i - y i)\<^sup>2)"
    unfolding top1_euclidean_metric_real_on_def by simp
  also have "... \<le> sqrt (real (card I) * ?M\<^sup>2)"
    by (rule real_sqrt_le_mono[OF hsum_le])
  also have "... = sqrt (real (card I)) * abs ?M"
    by (simp add: real_sqrt_mult)
  also have "... = sqrt (real (card I)) * ?M"
    using hM_nonneg by simp
  finally show ?thesis
    by simp
qed

(** Triangle inequality for the Euclidean metric on finite products. **)
lemma top1_euclidean_metric_real_on_triangle:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  shows "top1_euclidean_metric_real_on I x z
    \<le> top1_euclidean_metric_real_on I x y + top1_euclidean_metric_real_on I y z"
using hfin
proof (induction I rule: finite_induct)
  case empty
  show ?case
    by (simp add: top1_euclidean_metric_real_on_def)
next
  case (insert i F)
  have hfinF: "finite F"
    using insert.hyps(1) .
  have hiF: "i \<notin> F"
    using insert.hyps(2) .
  have ih:
    "top1_euclidean_metric_real_on F x z
      \<le> top1_euclidean_metric_real_on F x y + top1_euclidean_metric_real_on F y z"
    using insert.IH .

  let ?Sxy = "(\<Sum>j\<in>F. (x j - y j)\<^sup>2)"
  let ?Syz = "(\<Sum>j\<in>F. (y j - z j)\<^sup>2)"
  let ?Sxz = "(\<Sum>j\<in>F. (x j - z j)\<^sup>2)"
  let ?a = "sqrt ?Sxy"
  let ?c = "sqrt ?Syz"
  let ?b = "x i - y i"
  let ?d = "y i - z i"

	  have hSxy_nonneg: "0 \<le> ?Sxy"
	  proof (rule sum_nonneg)
	    fix j
	    assume hj: "j \<in> F"
	    show "0 \<le> (x j - y j)\<^sup>2"
	      by simp
	  qed
	  have hSyz_nonneg: "0 \<le> ?Syz"
	  proof (rule sum_nonneg)
	    fix j
	    assume hj: "j \<in> F"
	    show "0 \<le> (y j - z j)\<^sup>2"
	      by simp
	  qed
	  have hSxz_nonneg: "0 \<le> ?Sxz"
	  proof (rule sum_nonneg)
	    fix j
	    assume hj: "j \<in> F"
	    show "0 \<le> (x j - z j)\<^sup>2"
	      by simp
	  qed

  have hrest_le:
    "sqrt ?Sxz \<le> sqrt ?Sxy + sqrt ?Syz"
  proof -
    have "sqrt ?Sxz = top1_euclidean_metric_real_on F x z"
      unfolding top1_euclidean_metric_real_on_def by simp
    also have "... \<le> top1_euclidean_metric_real_on F x y + top1_euclidean_metric_real_on F y z"
      using ih by simp
    also have "... = sqrt ?Sxy + sqrt ?Syz"
      unfolding top1_euclidean_metric_real_on_def by simp
    finally show ?thesis
      .
  qed

			  have hSxz_le: "?Sxz \<le> (?a + ?c)\<^sup>2"
			  proof -
			    have hsqrt_nonneg: "0 \<le> sqrt ?Sxz"
			      by (rule real_sqrt_ge_zero, rule hSxz_nonneg)
			    have hsq: "(sqrt ?Sxz)\<^sup>2 \<le> (?a + ?c)\<^sup>2"
			    proof -
			      have "(sqrt ?Sxz)\<^sup>2 \<le> (sqrt ?Sxy + sqrt ?Syz)\<^sup>2"
			        using hrest_le hsqrt_nonneg by (rule power_mono)
			      thus ?thesis
			        by simp
			    qed
			    have "(sqrt ?Sxz)\<^sup>2 = ?Sxz"
			      using hSxz_nonneg by simp
			    thus ?thesis
			      using hsq by simp
			  qed

  have hmono:
    "sqrt (?Sxz + (?b + ?d)\<^sup>2) \<le> sqrt ((?a + ?c)\<^sup>2 + (?b + ?d)\<^sup>2)"
  proof -
    have "?Sxz + (?b + ?d)\<^sup>2 \<le> (?a + ?c)\<^sup>2 + (?b + ?d)\<^sup>2"
      using hSxz_le by linarith
    thus ?thesis
      by (rule real_sqrt_le_mono)
  qed

  have h2d:
    "sqrt ((?a + ?c)\<^sup>2 + (?b + ?d)\<^sup>2) \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2) + sqrt (?c\<^sup>2 + ?d\<^sup>2)"
    by (rule real_sqrt_sum_squares_triangle_ineq)

  have hsqrt_a2: "?a\<^sup>2 = ?Sxy"
    using hSxy_nonneg by (simp add: power2_eq_square)
  have hsqrt_c2: "?c\<^sup>2 = ?Syz"
    using hSyz_nonneg by (simp add: power2_eq_square)

  have hbpd: "?b + ?d = x i - z i"
    by simp

  have hxy_ins:
    "top1_euclidean_metric_real_on (insert i F) x y = sqrt (?Sxy + ?b\<^sup>2)"
    unfolding top1_euclidean_metric_real_on_def using hfinF hiF by simp
  have hyz_ins:
    "top1_euclidean_metric_real_on (insert i F) y z = sqrt (?Syz + ?d\<^sup>2)"
    unfolding top1_euclidean_metric_real_on_def using hfinF hiF by simp
  have hxz_ins:
    "top1_euclidean_metric_real_on (insert i F) x z = sqrt (?Sxz + (?b + ?d)\<^sup>2)"
    unfolding top1_euclidean_metric_real_on_def using hfinF hiF hbpd by simp

  have "top1_euclidean_metric_real_on (insert i F) x z
      \<le> sqrt ((?a + ?c)\<^sup>2 + (?b + ?d)\<^sup>2)"
    unfolding hxz_ins using hmono by simp
  also have "... \<le> sqrt (?a\<^sup>2 + ?b\<^sup>2) + sqrt (?c\<^sup>2 + ?d\<^sup>2)"
    using h2d by simp
  also have "... = top1_euclidean_metric_real_on (insert i F) x y + top1_euclidean_metric_real_on (insert i F) y z"
  proof -
    have "sqrt (?a\<^sup>2 + ?b\<^sup>2) = sqrt (?Sxy + ?b\<^sup>2)"
      unfolding hsqrt_a2 by simp
    moreover have "sqrt (?c\<^sup>2 + ?d\<^sup>2) = sqrt (?Syz + ?d\<^sup>2)"
      unfolding hsqrt_c2 by simp
    ultimately show ?thesis
      unfolding hxy_ins hyz_ins by simp
  qed
  finally show ?case
    by simp
qed

(** A square/sup-metric ball is open in the Euclidean metric topology on finite products. **)
lemma top1_square_ball_open_in_euclidean_metric_topology_real:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "X\<^sub>R \<equiv> top1_PiE I XR"
  assumes hx: "x \<in> X\<^sub>R"
  assumes he: "0 < e"
  shows "top1_ball_on X\<^sub>R (top1_square_metric_real_on I) x e
    \<in> top1_metric_topology_on X\<^sub>R (top1_euclidean_metric_real_on I)"
proof -
  let ?X = "X\<^sub>R"
  let ?B = "top1_metric_basis_on ?X (top1_euclidean_metric_real_on I)"
  have hball_sub: "top1_ball_on ?X (top1_square_metric_real_on I) x e \<subseteq> ?X"
    unfolding top1_ball_on_def by blast

  show ?thesis
    unfolding top1_metric_topology_on_def topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "top1_ball_on ?X (top1_square_metric_real_on I) x e \<subseteq> ?X"
      by (rule hball_sub)

    show "\<forall>y\<in>top1_ball_on ?X (top1_square_metric_real_on I) x e.
            \<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> top1_ball_on ?X (top1_square_metric_real_on I) x e"
    proof (intro ballI)
      fix y
      assume hy: "y \<in> top1_ball_on ?X (top1_square_metric_real_on I) x e"
      have hyX: "y \<in> ?X" and hxy: "top1_square_metric_real_on I x y < e"
        using hy unfolding top1_ball_on_def by blast+

      define r where "r = e - top1_square_metric_real_on I x y"
      have hr: "r > 0"
        unfolding r_def using hxy by linarith

      have hbasis: "top1_ball_on ?X (top1_euclidean_metric_real_on I) y r \<in> ?B"
        unfolding top1_metric_basis_on_def
        apply (intro CollectI)
        apply (rule exI[where x=y])
        apply (rule exI[where x=r])
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply (rule hyX)
        apply (rule hr)
        done
      have hy_in: "y \<in> top1_ball_on ?X (top1_euclidean_metric_real_on I) y r"
      proof -
        have "top1_euclidean_metric_real_on I y y = 0"
          unfolding top1_euclidean_metric_real_on_def by simp
        thus ?thesis
          unfolding top1_ball_on_def using hyX hr by simp
      qed

      have hsub:
        "top1_ball_on ?X (top1_euclidean_metric_real_on I) y r
          \<subseteq> top1_ball_on ?X (top1_square_metric_real_on I) x e"
      proof (rule subsetI)
        fix z
        assume hz: "z \<in> top1_ball_on ?X (top1_euclidean_metric_real_on I) y r"
        have hzX: "z \<in> ?X" and hyz: "top1_euclidean_metric_real_on I y z < r"
          using hz unfolding top1_ball_on_def by blast+
        have hyz_sq: "top1_square_metric_real_on I y z < r"
        proof -
          have "top1_square_metric_real_on I y z \<le> top1_euclidean_metric_real_on I y z"
            by (rule top1_square_metric_real_on_le_euclidean[OF hfin hne])
          thus ?thesis
            using hyz by linarith
        qed
        have hxz: "top1_square_metric_real_on I x z < e"
        proof -
          have htri:
            "top1_square_metric_real_on I x z
              \<le> top1_square_metric_real_on I x y + top1_square_metric_real_on I y z"
            by (rule top1_square_metric_real_on_triangle[OF hfin hne])
          have "top1_square_metric_real_on I x z < top1_square_metric_real_on I x y + r"
            using htri hyz_sq by linarith
          thus ?thesis
            unfolding r_def by simp
        qed
        show "z \<in> top1_ball_on ?X (top1_square_metric_real_on I) x e"
          unfolding top1_ball_on_def using hzX hxz by blast
      qed

      show "\<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> top1_ball_on ?X (top1_square_metric_real_on I) x e"
        using hbasis hy_in hsub by blast
    qed
  qed
qed

(** A Euclidean ball is open in the square/sup metric topology on finite products. **)
lemma top1_euclidean_ball_open_in_square_metric_topology_real:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "X\<^sub>R \<equiv> top1_PiE I XR"
  assumes hx: "x \<in> X\<^sub>R"
  assumes he: "0 < e"
  shows "top1_ball_on X\<^sub>R (top1_euclidean_metric_real_on I) x e
    \<in> top1_metric_topology_on X\<^sub>R (top1_square_metric_real_on I)"
proof -
  let ?X = "X\<^sub>R"
  let ?B = "top1_metric_basis_on ?X (top1_square_metric_real_on I)"
  have hball_sub: "top1_ball_on ?X (top1_euclidean_metric_real_on I) x e \<subseteq> ?X"
    unfolding top1_ball_on_def by blast

  show ?thesis
    unfolding top1_metric_topology_on_def topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "top1_ball_on ?X (top1_euclidean_metric_real_on I) x e \<subseteq> ?X"
      by (rule hball_sub)

    show "\<forall>y\<in>top1_ball_on ?X (top1_euclidean_metric_real_on I) x e.
            \<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> top1_ball_on ?X (top1_euclidean_metric_real_on I) x e"
    proof (intro ballI)
      fix y
      assume hy: "y \<in> top1_ball_on ?X (top1_euclidean_metric_real_on I) x e"
      have hyX: "y \<in> ?X" and hxy: "top1_euclidean_metric_real_on I x y < e"
        using hy unfolding top1_ball_on_def by blast+

      have hcard_pos: "0 < card I"
        using hfin hne by (simp add: card_gt_0_iff)
      have hsqrt_card_pos: "0 < sqrt (real (card I))"
        by (rule real_sqrt_gt_zero, simp add: hcard_pos)

      define d where "d = e - top1_euclidean_metric_real_on I x y"
      have hd_pos: "0 < d"
        unfolding d_def using hxy by linarith
      define r where "r = d / sqrt (real (card I))"
      have hr_pos: "0 < r"
        unfolding r_def using hd_pos hsqrt_card_pos by simp

      have hbasis: "top1_ball_on ?X (top1_square_metric_real_on I) y r \<in> ?B"
        unfolding top1_metric_basis_on_def
        apply (intro CollectI)
        apply (rule exI[where x=y])
        apply (rule exI[where x=r])
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply (rule hyX)
        apply (rule hr_pos)
        done
      have hy_in: "y \<in> top1_ball_on ?X (top1_square_metric_real_on I) y r"
      proof -
        have "top1_square_metric_real_on I y y = 0"
          unfolding top1_square_metric_real_on_def using hne by simp
        thus ?thesis
          unfolding top1_ball_on_def using hyX hr_pos by simp
      qed

      have hsub:
        "top1_ball_on ?X (top1_square_metric_real_on I) y r
          \<subseteq> top1_ball_on ?X (top1_euclidean_metric_real_on I) x e"
      proof (rule subsetI)
        fix z
        assume hz: "z \<in> top1_ball_on ?X (top1_square_metric_real_on I) y r"
        have hzX: "z \<in> ?X" and hyz: "top1_square_metric_real_on I y z < r"
          using hz unfolding top1_ball_on_def by blast+

	        have hyz_euclid: "top1_euclidean_metric_real_on I y z < d"
	        proof -
	          have hle:
	            "top1_euclidean_metric_real_on I y z
	              \<le> sqrt (real (card I)) * top1_square_metric_real_on I y z"
	            by (rule top1_euclidean_metric_real_on_le_sqrt_card_mul_square[OF hfin hne])
	          have hslt:
	            "sqrt (real (card I)) * top1_square_metric_real_on I y z
	              < sqrt (real (card I)) * r"
	            using hyz hsqrt_card_pos by (rule mult_strict_left_mono)
	          have hlt: "top1_euclidean_metric_real_on I y z < sqrt (real (card I)) * r"
	            using hle hslt by linarith
	          have hsqrt_ne0: "sqrt (real (card I)) \<noteq> 0"
	            using hsqrt_card_pos by simp
	          have "sqrt (real (card I)) * r = d"
	            unfolding r_def using hsqrt_ne0 by (simp add: field_simps)
	          thus ?thesis
	            using hlt by simp
	        qed

        have hxz: "top1_euclidean_metric_real_on I x z < e"
        proof -
          have htri:
            "top1_euclidean_metric_real_on I x z
              \<le> top1_euclidean_metric_real_on I x y + top1_euclidean_metric_real_on I y z"
            by (rule top1_euclidean_metric_real_on_triangle[OF hfin])
          have "top1_euclidean_metric_real_on I x z
              < top1_euclidean_metric_real_on I x y + d"
            using htri hyz_euclid by linarith
          thus ?thesis
            unfolding d_def by simp
        qed
        show "z \<in> top1_ball_on ?X (top1_euclidean_metric_real_on I) x e"
          unfolding top1_ball_on_def using hzX hxz by blast
      qed

      show "\<exists>b\<in>?B. y \<in> b \<and> b \<subseteq> top1_ball_on ?X (top1_euclidean_metric_real_on I) x e"
        using hbasis hy_in hsub by blast
    qed
  qed
qed

(** from \S20 Theorem 20.3 [top1.tex:1684] **)
theorem Theorem_20_3:
  fixes I :: "'i set"
  assumes hfin: "finite I"
  assumes hne: "I \<noteq> {}"
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "TR \<equiv> (order_topology_on_UNIV::real set set)"
  defines "X\<^sub>R \<equiv> top1_PiE I XR"
  shows "top1_metric_topology_on X\<^sub>R (top1_euclidean_metric_real_on I) = top1_product_topology_on I XR (\<lambda>_. TR)"
    and "top1_metric_topology_on X\<^sub>R (top1_square_metric_real_on I) = top1_product_topology_on I XR (\<lambda>_. TR)"
text \<open>
  For finite, nonempty index set \<open>I\<close>, the square/sup metric topology agrees with the box topology since both
  have the same basic neighborhoods given by coordinatewise open intervals.  Since \<open>I\<close> is finite, box and product
  topologies coincide.  Finally, Euclidean and square metrics induce the same topology on finite products by mutual
  local refinement of balls.
\<close>
proof -
  let ?Tprod = "top1_product_topology_on I XR (\<lambda>_. TR)"
  let ?Tbox = "top1_box_topology_on I XR (\<lambda>_. TR)"
  let ?Te = "top1_metric_topology_on X\<^sub>R (top1_euclidean_metric_real_on I)"
  let ?Ts = "top1_metric_topology_on X\<^sub>R (top1_square_metric_real_on I)"

  have hprod_box: "?Tprod = ?Tbox"
    using top1_product_topology_eq_box_topology_if_finite[OF hfin]
    by (simp add: top1_product_topology_on_def top1_box_topology_on_def)

  have hsub1:
    "topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))
      \<subseteq> topology_generated_by_basis X\<^sub>R (top1_box_basis_on I XR (\<lambda>_. TR))"
  proof (rule topology_generated_by_basis_mono_via_basis_elems)
    fix b
    assume hb: "b \<in> top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I)"
    obtain x e where hxX: "x \<in> X\<^sub>R" and he: "0 < e"
        and hb_eq: "b = top1_ball_on X\<^sub>R (top1_square_metric_real_on I) x e"
      using hb unfolding top1_metric_basis_on_def by blast
    define U where "U = (\<lambda>i. open_interval (x i - e) (x i + e))"
    have hU: "\<forall>i\<in>I. U i \<in> TR \<and> U i \<subseteq> XR i"
    proof (intro ballI)
      fix i
      assume hi: "i \<in> I"
      have hab: "x i - e < x i + e"
        using he by linarith
      show "U i \<in> TR \<and> U i \<subseteq> XR i"
        unfolding U_def TR_def XR_def using open_interval_in_order_topology[OF hab] by simp
    qed
    have hb_basis: "b \<in> top1_box_basis_on I XR (\<lambda>_. TR)"
      unfolding top1_box_basis_on_def
    proof (rule CollectI, rule exI[where x=U], intro conjI)
      show "\<forall>i\<in>I. U i \<in> TR \<and> U i \<subseteq> XR i"
        by (rule hU)
      show "b = top1_PiE I U"
        unfolding hb_eq top1_ball_on_def
        apply (rule set_eqI)
        subgoal for y
          unfolding U_def X\<^sub>R_def XR_def
          by (simp add: top1_square_metric_real_on_lt_iff[OF hfin hne]
                        abs_diff_lt_iff_mem_open_interval top1_PiE_iff open_interval_def;
              blast)
        done
    qed
    show "b \<in> topology_generated_by_basis X\<^sub>R (top1_box_basis_on I XR (\<lambda>_. TR))"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> X\<^sub>R"
        unfolding hb_eq top1_ball_on_def by blast
      show "\<forall>y\<in>b. \<exists>ba\<in>top1_box_basis_on I XR (\<lambda>_. TR). y \<in> ba \<and> ba \<subseteq> b"
        using hb_basis by blast
    qed
  qed

  have hsub2:
    "topology_generated_by_basis X\<^sub>R (top1_box_basis_on I XR (\<lambda>_. TR))
      \<subseteq> topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))"
  proof (rule topology_generated_by_basis_mono_via_basis_elems)
    fix b
    assume hb: "b \<in> top1_box_basis_on I XR (\<lambda>_. TR)"
    obtain U where hU: "\<forall>i\<in>I. U i \<in> TR \<and> U i \<subseteq> XR i" and hb_eq: "b = top1_PiE I U"
      using hb unfolding top1_box_basis_on_def by blast

      show "b \<in> topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      have "top1_PiE I U \<subseteq> top1_PiE I XR"
        using hU unfolding XR_def
        apply (intro top1_PiE_mono)
        apply simp
        done
      thus "b \<subseteq> X\<^sub>R"
        unfolding hb_eq X\<^sub>R_def by simp

      show "\<forall>y\<in>b. \<exists>ba\<in>top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I).
              y \<in> ba \<and> ba \<subseteq> b"
      proof (intro ballI)
        fix y
        assume hy: "y \<in> b"
        have hyX: "y \<in> X\<^sub>R"
          using hy \<open>b \<subseteq> X\<^sub>R\<close> by blast

        have hcoord: "\<forall>i\<in>I. \<exists>ei>0. open_interval (y i - ei) (y i + ei) \<subseteq> U i"
        proof (intro ballI)
          fix i
          assume hi: "i \<in> I"
          have hyi: "y i \<in> U i"
            using hy unfolding hb_eq top1_PiE_iff using hi by blast
          have "U i \<in> (order_topology_on_UNIV::real set set)"
            using hU hi unfolding TR_def by blast
          then obtain ei where hei: "ei > 0" and hsub: "open_interval (y i - ei) (y i + ei) \<subseteq> U i"
            using order_topology_on_UNIV_open_interval_subset_real[OF _ hyi] by blast
          show "\<exists>ei>0. open_interval (y i - ei) (y i + ei) \<subseteq> U i"
            using hei hsub by blast
        qed

        have hex: "\<exists>efun. \<forall>i\<in>I. efun i > 0 \<and> open_interval (y i - efun i) (y i + efun i) \<subseteq> U i"
          using hcoord by (rule bchoice)
        then obtain efun where hef:
          "\<forall>i\<in>I. efun i > 0 \<and> open_interval (y i - efun i) (y i + efun i) \<subseteq> U i"
          by blast

        define r where "r = Min (efun ` I)"
        have hr_pos: "r > 0"
        proof -
          have hfinR: "finite (efun ` I)"
            using hfin by simp
          have hneR: "efun ` I \<noteq> {}"
            using hne by simp
          have hr_in: "r \<in> efun ` I"
            unfolding r_def using Min_in[OF hfinR hneR] by simp
          then obtain i0 where hi0: "i0 \<in> I" and hr_eq: "r = efun i0"
            by blast
          show ?thesis
            using hef[rule_format, OF hi0] unfolding hr_eq by blast
        qed

        have hball_sub:
          "top1_ball_on X\<^sub>R (top1_square_metric_real_on I) y r \<subseteq> b"
        proof (rule subsetI)
          fix z
          assume hz: "z \<in> top1_ball_on X\<^sub>R (top1_square_metric_real_on I) y r"
          have hzX: "z \<in> X\<^sub>R" and hyz: "top1_square_metric_real_on I y z < r"
            using hz unfolding top1_ball_on_def by blast+
          have hyz_coord: "\<forall>i\<in>I. abs (y i - z i) < r"
            using top1_square_metric_real_on_lt_iff[OF hfin hne] hyz by simp

          have hz_in: "\<forall>i\<in>I. z i \<in> U i"
          proof (intro ballI)
            fix i
            assume hi: "i \<in> I"
            have hr_le: "r \<le> efun i"
              unfolding r_def using hfin hi by simp

            have hzi: "abs (y i - z i) < r"
              using hyz_coord hi by blast
            have hz_int: "z i \<in> open_interval (y i - r) (y i + r)"
              unfolding open_interval_def using hzi by (simp add: abs_less_iff algebra_simps)
            have hint_mono:
              "open_interval (y i - r) (y i + r) \<subseteq> open_interval (y i - efun i) (y i + efun i)"
            proof
              fix t
              assume ht: "t \<in> open_interval (y i - r) (y i + r)"
              have ht1: "y i - r < t"
                using ht unfolding open_interval_def by auto
              have ht2: "t < y i + r"
                using ht unfolding open_interval_def by auto
              have "y i - efun i \<le> y i - r"
                using hr_le by linarith
              moreover have "y i + r \<le> y i + efun i"
                using hr_le by linarith
              hence "y i - efun i < t"
                using ht1 by linarith
              moreover from \<open>y i + r \<le> y i + efun i\<close> have "t < y i + efun i"
                using ht2 by linarith
              ultimately show "t \<in> open_interval (y i - efun i) (y i + efun i)"
                unfolding open_interval_def by blast
            qed
            have "open_interval (y i - efun i) (y i + efun i) \<subseteq> U i"
              using hef hi by blast
            have "z i \<in> open_interval (y i - efun i) (y i + efun i)"
              using hz_int hint_mono by blast
            thus "z i \<in> U i"
              using \<open>open_interval (y i - efun i) (y i + efun i) \<subseteq> U i\<close> by blast
          qed
          show "z \<in> b"
          proof -
            have hz_ext: "\<forall>i. i \<notin> I \<longrightarrow> z i = undefined"
              using hzX unfolding X\<^sub>R_def XR_def top1_PiE_iff by simp
            have "z \<in> top1_PiE I U"
              unfolding top1_PiE_iff using hz_in hz_ext by blast
            thus ?thesis
              unfolding hb_eq by simp
          qed
        qed

        have hbasis: "top1_ball_on X\<^sub>R (top1_square_metric_real_on I) y r \<in> top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I)"
          unfolding top1_metric_basis_on_def
          apply (intro CollectI)
          apply (rule exI[where x=y])
          apply (rule exI[where x=r])
          apply (rule conjI)
           apply simp
          apply (rule conjI)
           apply (rule hyX)
          apply (rule hr_pos)
          done
        have hy_in: "y \<in> top1_ball_on X\<^sub>R (top1_square_metric_real_on I) y r"
        proof -
          have "top1_square_metric_real_on I y y = 0"
            unfolding top1_square_metric_real_on_def using hne by simp
          thus ?thesis
            unfolding top1_ball_on_def using hyX hr_pos by simp
        qed

        show "\<exists>ba\<in>top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I).
                y \<in> ba \<and> ba \<subseteq> b"
          using hbasis hy_in hball_sub by blast
      qed
    qed
  qed

  have hsquare_box: "?Ts = ?Tbox"
  proof (rule antisym)
    have hsub1':
      "topology_generated_by_basis (top1_PiE I XR)
         (top1_metric_basis_on (top1_PiE I XR) (top1_square_metric_real_on I))
        \<subseteq> topology_generated_by_basis (top1_PiE I XR) (top1_box_basis_on I XR (\<lambda>_. TR))"
      using hsub1 unfolding X\<^sub>R_def .
    show "?Ts \<subseteq> ?Tbox"
      unfolding top1_metric_topology_on_def top1_box_topology_on_def X\<^sub>R_def
      by (rule hsub1')
  next
    have hsub2':
      "topology_generated_by_basis (top1_PiE I XR) (top1_box_basis_on I XR (\<lambda>_. TR))
        \<subseteq> topology_generated_by_basis (top1_PiE I XR)
           (top1_metric_basis_on (top1_PiE I XR) (top1_square_metric_real_on I))"
      using hsub2 unfolding X\<^sub>R_def .
    show "?Tbox \<subseteq> ?Ts"
      unfolding top1_metric_topology_on_def top1_box_topology_on_def X\<^sub>R_def
      by (rule hsub2')
  qed

  have hsquare_prod: "?Ts = ?Tprod"
    using hsquare_box hprod_box by simp

  have heuclid_square: "?Te = ?Ts"
  proof (rule antisym)
    have hsub:
      "topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_euclidean_metric_real_on I))
        \<subseteq> topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))"
    proof (rule topology_generated_by_basis_mono_via_basis_elems)
      fix b
      assume hb: "b \<in> top1_metric_basis_on X\<^sub>R (top1_euclidean_metric_real_on I)"
      obtain x e where hxX: "x \<in> X\<^sub>R" and he: "0 < e"
          and hb_eq: "b = top1_ball_on X\<^sub>R (top1_euclidean_metric_real_on I) x e"
        using hb unfolding top1_metric_basis_on_def by blast
	      show "b \<in> topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))"
	      proof (subst hb_eq)
	        have hx_univ: "x \<in> top1_PiE I (\<lambda>_. (UNIV::real set))"
	          using hxX unfolding X\<^sub>R_def XR_def .
		        have hopen:
		          "top1_ball_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_euclidean_metric_real_on I) x e
		            \<in> top1_metric_topology_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_square_metric_real_on I)"
		          using top1_euclidean_ball_open_in_square_metric_topology_real[OF hfin hne hx_univ he] .
		        have hopen_XR:
		          "top1_ball_on X\<^sub>R (top1_euclidean_metric_real_on I) x e
		            \<in> top1_metric_topology_on X\<^sub>R (top1_square_metric_real_on I)"
		          unfolding X\<^sub>R_def XR_def
		          by (rule hopen)
		        have hopen_basis:
		          "top1_ball_on X\<^sub>R (top1_euclidean_metric_real_on I) x e
		            \<in> topology_generated_by_basis X\<^sub>R
		                 (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))"
		          using hopen_XR unfolding top1_metric_topology_on_def .
		        show "top1_ball_on X\<^sub>R (top1_euclidean_metric_real_on I) x e
		          \<in> topology_generated_by_basis X\<^sub>R
		               (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))"
		          by (rule hopen_basis)
	      qed
	    qed
	    show "?Te \<subseteq> ?Ts"
	      unfolding top1_metric_topology_on_def using hsub by simp
	  next
    have hsub:
      "topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I))
        \<subseteq> topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_euclidean_metric_real_on I))"
    proof (rule topology_generated_by_basis_mono_via_basis_elems)
      fix b
      assume hb: "b \<in> top1_metric_basis_on X\<^sub>R (top1_square_metric_real_on I)"
      obtain x e where hxX: "x \<in> X\<^sub>R" and he: "0 < e"
          and hb_eq: "b = top1_ball_on X\<^sub>R (top1_square_metric_real_on I) x e"
        using hb unfolding top1_metric_basis_on_def by blast
	      show "b \<in> topology_generated_by_basis X\<^sub>R (top1_metric_basis_on X\<^sub>R (top1_euclidean_metric_real_on I))"
	      proof (subst hb_eq)
	        have hx_univ: "x \<in> top1_PiE I (\<lambda>_. (UNIV::real set))"
	          using hxX unfolding X\<^sub>R_def XR_def .
		        have hopen:
		          "top1_ball_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_square_metric_real_on I) x e
		            \<in> top1_metric_topology_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_euclidean_metric_real_on I)"
		          using top1_square_ball_open_in_euclidean_metric_topology_real[OF hfin hne hx_univ he] .
		        have hopen_XR:
		          "top1_ball_on X\<^sub>R (top1_square_metric_real_on I) x e
		            \<in> top1_metric_topology_on X\<^sub>R (top1_euclidean_metric_real_on I)"
		          unfolding X\<^sub>R_def XR_def
		          by (rule hopen)
		        have hopen_basis:
		          "top1_ball_on X\<^sub>R (top1_square_metric_real_on I) x e
		            \<in> topology_generated_by_basis X\<^sub>R
		                 (top1_metric_basis_on X\<^sub>R (top1_euclidean_metric_real_on I))"
		          using hopen_XR unfolding top1_metric_topology_on_def .
		        show "top1_ball_on X\<^sub>R (top1_square_metric_real_on I) x e
		          \<in> topology_generated_by_basis X\<^sub>R
		               (top1_metric_basis_on X\<^sub>R (top1_euclidean_metric_real_on I))"
		          by (rule hopen_basis)
	      qed
	    qed
	    show "?Ts \<subseteq> ?Te"
	      unfolding top1_metric_topology_on_def using hsub by simp
	  qed

  show "top1_metric_topology_on X\<^sub>R (top1_euclidean_metric_real_on I) = ?Tprod"
    using heuclid_square hsquare_prod by simp
  show "top1_metric_topology_on X\<^sub>R (top1_square_metric_real_on I) = ?Tprod"
    using hsquare_prod by simp
qed

(** Uniform metric topology is always coarser than the box topology on \<open>\<real>^I\<close>. **)
lemma top1_uniform_metric_topology_subset_box_topology_real:
  fixes I :: "'i set"
  shows "top1_metric_topology_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_uniform_metric_real_on I)
    \<subseteq> top1_box_topology_on I (\<lambda>_. (UNIV::real set)) (\<lambda>_. (order_topology_on_UNIV::real set set))"
proof (cases "I = {}")
  case True
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?TR = "(order_topology_on_UNIV::real set set)"
  let ?X = "top1_PiE I ?XR"

  have hXsingle: "?X = {(\<lambda>_. undefined)}"
  proof (rule set_eqI)
    fix f
    show "f \<in> ?X \<longleftrightarrow> f \<in> {(\<lambda>_. undefined)}"
    proof (rule iffI)
      assume hf: "f \<in> ?X"
      have hext: "\<forall>i. f i = undefined"
        using hf unfolding True top1_PiE_iff by simp
      have "f = (\<lambda>_. undefined)"
        by (rule ext, simp add: hext)
      thus "f \<in> {(\<lambda>_. undefined)}"
        by simp
    next
      assume hf: "f \<in> {(\<lambda>_. undefined)}"
      then show "f \<in> ?X"
        unfolding True top1_PiE_iff by simp
    qed
  qed

  have hTopCoord: "\<forall>i\<in>I. is_topology_on (?XR i) ?TR"
    by (simp add: order_topology_on_UNIV_is_topology_on)
  have hTopTbox: "is_topology_on ?X (top1_box_topology_on I ?XR (\<lambda>_. ?TR))"
    by (rule top1_box_topology_on_is_topology_on[OF hTopCoord])
  have hempty: "{} \<in> top1_box_topology_on I ?XR (\<lambda>_. ?TR)"
    using hTopTbox unfolding is_topology_on_def by blast
  have hwhole: "?X \<in> top1_box_topology_on I ?XR (\<lambda>_. ?TR)"
    using hTopTbox unfolding is_topology_on_def by blast

  show ?thesis
  proof (rule subsetI)
    fix U
    assume hU: "U \<in> top1_metric_topology_on ?X (top1_uniform_metric_real_on I)"
    have hUsub: "U \<subseteq> ?X"
      using hU unfolding top1_metric_topology_on_def topology_generated_by_basis_def by blast
    have "U = {} \<or> U = ?X"
      using hUsub unfolding hXsingle by auto
    thus "U \<in> top1_box_topology_on I ?XR (\<lambda>_. ?TR)"
      using hempty hwhole by blast
  qed
next
  case False
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?TR = "(order_topology_on_UNIV::real set set)"
  let ?X = "top1_PiE I ?XR"
  obtain i0 where hi0: "i0 \<in> I"
    using False by blast

  have hTopCoord: "\<forall>i\<in>I. is_topology_on (?XR i) ?TR"
    by (simp add: order_topology_on_UNIV_is_topology_on)
  have hTopTbox: "is_topology_on ?X (top1_box_topology_on I ?XR (\<lambda>_. ?TR))"
    by (rule top1_box_topology_on_is_topology_on[OF hTopCoord])

  have hBasisSub:
    "top1_metric_basis_on ?X (top1_uniform_metric_real_on I) \<subseteq> top1_box_topology_on I ?XR (\<lambda>_. ?TR)"
  proof (rule subsetI)
    fix b
    assume hb: "b \<in> top1_metric_basis_on ?X (top1_uniform_metric_real_on I)"
    obtain x e where hxX: "x \<in> ?X" and he: "0 < e"
        and hb_eq: "b = top1_ball_on ?X (top1_uniform_metric_real_on I) x e"
      using hb unfolding top1_metric_basis_on_def by blast

    have hball_in:
      "top1_ball_on ?X (top1_uniform_metric_real_on I) x e \<in> top1_box_topology_on I ?XR (\<lambda>_. ?TR)"
      unfolding top1_box_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "top1_ball_on ?X (top1_uniform_metric_real_on I) x e \<subseteq> top1_PiE I ?XR"
        unfolding top1_ball_on_def by blast

      show "\<forall>y\<in>top1_ball_on ?X (top1_uniform_metric_real_on I) x e.
              \<exists>ba\<in>top1_box_basis_on I ?XR (\<lambda>_. ?TR).
                y \<in> ba \<and> ba \<subseteq> top1_ball_on ?X (top1_uniform_metric_real_on I) x e"
      proof (intro ballI)
        fix y
        assume hy: "y \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x e"
        have hyX: "y \<in> ?X" and hdist: "top1_uniform_metric_real_on I x y < e"
          using hy unfolding top1_ball_on_def by blast+

        define r where "r = (top1_uniform_metric_real_on I x y + e) / 2"
        have hr_pos: "r > 0"
        proof -
          have hmet: "top1_metric_on ?X (top1_uniform_metric_real_on I)"
            by (rule top1_uniform_metric_real_on_metric_on_PiE_UNIV[OF False])
          have hxy_nonneg: "0 \<le> top1_uniform_metric_real_on I x y"
            using hmet hxX hyX unfolding top1_metric_on_def by blast
          have "0 < top1_uniform_metric_real_on I x y + e"
            using he hxy_nonneg by linarith
          hence "0 < (top1_uniform_metric_real_on I x y + e) / 2"
            by simp
          thus ?thesis
            unfolding r_def by simp
        qed
        have hr_lt: "r < e"
        proof -
          have "2 * top1_uniform_metric_real_on I x y < 2 * e"
            using hdist by (simp add: mult_strict_left_mono)
          hence "top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I x y < 2 * e"
            by (simp add: algebra_simps)
          hence "top1_uniform_metric_real_on I x y + e < 2 * e"
            using hdist by linarith
          hence "(top1_uniform_metric_real_on I x y + e) / 2 < e"
            by (simp add: field_simps)
          thus ?thesis
            unfolding r_def by simp
        qed
        have hdist_r: "top1_uniform_metric_real_on I x y < r"
        proof -
          have hmet: "top1_metric_on ?X (top1_uniform_metric_real_on I)"
            by (rule top1_uniform_metric_real_on_metric_on_PiE_UNIV[OF False])
          have hxy_nonneg: "0 \<le> top1_uniform_metric_real_on I x y"
            using hmet hxX hyX unfolding top1_metric_on_def by blast
          have "top1_uniform_metric_real_on I x y < e"
            by (rule hdist)
          hence "top1_uniform_metric_real_on I x y + top1_uniform_metric_real_on I x y
              < top1_uniform_metric_real_on I x y + e"
            by (simp add: add_strict_left_mono)
          hence "2 * top1_uniform_metric_real_on I x y < top1_uniform_metric_real_on I x y + e"
            by (simp add: algebra_simps)
          hence "top1_uniform_metric_real_on I x y < (top1_uniform_metric_real_on I x y + e) / 2"
            by (simp add: field_simps)
          thus ?thesis
            unfolding r_def by simp
        qed

        define U where "U = (\<lambda>i. top1_ball_on UNIV top1_real_bounded_metric (x i) r)"
        have hUbox: "\<forall>i\<in>I. U i \<in> ?TR \<and> U i \<subseteq> ?XR i"
        proof (intro ballI)
          fix i assume hi: "i \<in> I"
          have "top1_ball_on UNIV top1_real_bounded_metric (x i) r \<in> (order_topology_on_UNIV::real set set)"
            by (rule top1_real_bounded_metric_ball_in_order_topology[OF hr_pos])
          thus "U i \<in> ?TR \<and> U i \<subseteq> ?XR i"
            unfolding U_def by simp
        qed
        have hbox_basis: "top1_PiE I U \<in> top1_box_basis_on I ?XR (\<lambda>_. ?TR)"
          unfolding top1_box_basis_on_def using hUbox by blast

        have hPi_sub_X: "top1_PiE I U \<subseteq> ?X"
        proof -
          have hsub: "\<forall>i\<in>I. U i \<subseteq> ?XR i"
            using hUbox by blast
          have "top1_PiE I U \<subseteq> top1_PiE I ?XR"
            by (rule top1_PiE_mono[OF hsub])
          thus ?thesis
            by simp
        qed

        have hybox: "y \<in> top1_PiE I U"
        proof -
          have hyExt: "\<forall>j. j \<notin> I \<longrightarrow> y j = undefined"
            using hyX unfolding top1_PiE_iff by blast
          have hyU: "\<forall>i\<in>I. y i \<in> U i"
          proof (intro ballI)
            fix i assume hi: "i \<in> I"
            have hle_coord:
              "top1_real_bounded_metric (x i) (y i) \<le> top1_uniform_metric_real_on I x y"
              by (rule top1_uniform_metric_real_on_coord_le[OF hi])
            have "top1_real_bounded_metric (x i) (y i) < r"
              using hle_coord hdist_r by linarith
            thus "y i \<in> U i"
              unfolding U_def top1_ball_on_def by simp
          qed
          show ?thesis
            unfolding top1_PiE_iff using hyU hyExt by blast
        qed

        have hbox_sub_ball:
          "top1_PiE I U \<subseteq> top1_ball_on ?X (top1_uniform_metric_real_on I) x e"
        proof (rule subsetI)
          fix z
          assume hz: "z \<in> top1_PiE I U"
          have hzX: "z \<in> ?X"
            using hPi_sub_X hz by blast

          have hall_le:
            "\<forall>s\<in>((\<lambda>i. top1_real_bounded_metric (x i) (z i)) ` I). s \<le> r"
          proof (intro ballI)
            fix s
            assume hs: "s \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (z i)) ` I)"
            then obtain i where hi: "i \<in> I" and hs_eq: "s = top1_real_bounded_metric (x i) (z i)"
              by blast
            have "z i \<in> U i"
              using hz hi unfolding top1_PiE_iff by blast
            then have "top1_real_bounded_metric (x i) (z i) < r"
              unfolding U_def top1_ball_on_def by simp
            thus "s \<le> r"
              unfolding hs_eq by simp
          qed

          have hSne: "((\<lambda>i. top1_real_bounded_metric (x i) (z i)) ` I) \<noteq> {}"
            using hi0 by blast
          have hSup_le: "top1_uniform_metric_real_on I x z \<le> r"
            unfolding top1_uniform_metric_real_on_def
          proof (rule cSup_least[OF hSne])
            fix s
            assume hs: "s \<in> ((\<lambda>i. top1_real_bounded_metric (x i) (z i)) ` I)"
            show "s \<le> r"
              using hall_le hs by (rule bspec)
          qed
          have "top1_uniform_metric_real_on I x z < e"
            using hSup_le hr_lt by linarith
          thus "z \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x e"
            unfolding top1_ball_on_def using hzX by blast
        qed

        show "\<exists>ba\<in>top1_box_basis_on I ?XR (\<lambda>_. ?TR).
                y \<in> ba \<and> ba \<subseteq> top1_ball_on ?X (top1_uniform_metric_real_on I) x e"
          apply (rule bexI[where x="top1_PiE I U"])
           apply (intro conjI)
            apply (rule hybox)
           apply (rule hbox_sub_ball)
          apply (rule hbox_basis)
          done
      qed
    qed

    show "b \<in> top1_box_topology_on I ?XR (\<lambda>_. ?TR)"
      unfolding hb_eq using hball_in by simp
  qed

  have hGenSub:
    "topology_generated_by_basis ?X (top1_metric_basis_on ?X (top1_uniform_metric_real_on I))
      \<subseteq> top1_box_topology_on I ?XR (\<lambda>_. ?TR)"
    by (rule topology_generated_by_basis_subset[OF hTopTbox hBasisSub])
  show ?thesis
    unfolding top1_metric_topology_on_def using hGenSub by simp
qed

(** Product topology on \<open>\<real>^I\<close> is contained in the uniform metric topology. **)
lemma top1_product_topology_subset_uniform_metric_topology_real:
  fixes I :: "'i set"
  shows "top1_product_topology_on I (\<lambda>_. (UNIV::real set)) (\<lambda>_. (order_topology_on_UNIV::real set set))
    \<subseteq> top1_metric_topology_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_uniform_metric_real_on I)"
proof (cases "I = {}")
  case True
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?X = "top1_PiE I ?XR"
  let ?Tprod = "top1_product_topology_on I ?XR (\<lambda>_. (order_topology_on_UNIV::real set set))"
  let ?Tunif = "top1_metric_topology_on ?X (top1_uniform_metric_real_on I)"

  have hXsingle: "?X = {(\<lambda>_. undefined)}"
  proof (rule set_eqI)
    fix f
    show "f \<in> ?X \<longleftrightarrow> f \<in> {(\<lambda>_. undefined)}"
    proof (rule iffI)
      assume hf: "f \<in> ?X"
      have hext: "\<forall>i. f i = undefined"
        using hf unfolding True top1_PiE_iff by simp
      have "f = (\<lambda>_. undefined)"
        by (rule ext, simp add: hext)
      thus "f \<in> {(\<lambda>_. undefined)}"
        by simp
    next
      assume hf: "f \<in> {(\<lambda>_. undefined)}"
      then show "f \<in> ?X"
        unfolding True top1_PiE_iff by simp
    qed
  qed

  have hempty: "{} \<in> ?Tunif"
    unfolding top1_metric_topology_on_def topology_generated_by_basis_def by simp

	  have hwhole: "?X \<in> ?Tunif"
	  proof -
	    obtain x0 where hx0: "x0 \<in> ?X"
	      using hXsingle by auto
	    define e where "e = abs (top1_uniform_metric_real_on I x0 x0) + 1"
	    have he: "0 < e"
	      unfolding e_def by simp
	    have hdist_lt_e: "top1_uniform_metric_real_on I x0 x0 < e"
	    proof -
	      have hle: "top1_uniform_metric_real_on I x0 x0 \<le> abs (top1_uniform_metric_real_on I x0 x0)"
	        by (rule abs_ge_self)
	      have habs_lt: "abs (top1_uniform_metric_real_on I x0 x0)
	        < abs (top1_uniform_metric_real_on I x0 x0) + 1"
	        by linarith
	      have "top1_uniform_metric_real_on I x0 x0 < abs (top1_uniform_metric_real_on I x0 x0) + 1"
	        by (rule le_less_trans[OF hle habs_lt])
	      thus ?thesis
	        unfolding e_def by simp
	    qed
	    have hx0ball: "x0 \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e"
	      unfolding top1_ball_on_def using hx0 hdist_lt_e by simp
	    have hball_basis:
	      "top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e
	        \<in> top1_metric_basis_on ?X (top1_uniform_metric_real_on I)"
	      unfolding top1_metric_basis_on_def using hx0 he by blast

	    show ?thesis
	      unfolding top1_metric_topology_on_def topology_generated_by_basis_def
	    proof (rule CollectI, intro conjI)
	      show "?X \<subseteq> ?X"
	        by simp
	      show "\<forall>x\<in>?X. \<exists>ba\<in>top1_metric_basis_on ?X (top1_uniform_metric_real_on I).
	            x \<in> ba \<and> ba \<subseteq> ?X"
	      proof (intro ballI)
	        fix x
	        assume hx: "x \<in> ?X"
	        have hx_undef: "x = (\<lambda>_. undefined)"
	          using hx hXsingle by auto
	        have hx0_undef: "x0 = (\<lambda>_. undefined)"
	          using hx0 hXsingle by auto
	        have hx_eq_x0: "x = x0"
	          using hx_undef hx0_undef by simp

	        show "\<exists>ba\<in>top1_metric_basis_on ?X (top1_uniform_metric_real_on I).
	              x \<in> ba \<and> ba \<subseteq> ?X"
	        proof (rule bexI[where x="top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e"])
	          have "x \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e"
	            using hx_eq_x0 hx0ball by simp
	          thus "x \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e
	            \<and> top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e \<subseteq> ?X"
	          proof (intro conjI)
	            show "top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e \<subseteq> ?X"
	              unfolding top1_ball_on_def by blast
	          qed
	          show "top1_ball_on ?X (top1_uniform_metric_real_on I) x0 e
	            \<in> top1_metric_basis_on ?X (top1_uniform_metric_real_on I)"
	            by (rule hball_basis)
	        qed
	      qed
	    qed
	  qed

  show ?thesis
  proof (rule subsetI)
    fix U
    assume hU: "U \<in> ?Tprod"
    have hUsub: "U \<subseteq> ?X"
      using hU unfolding top1_product_topology_on_def topology_generated_by_basis_def by blast
    have "U = {} \<or> U = ?X"
      using hUsub unfolding hXsingle by auto
    thus "U \<in> ?Tunif"
      using hempty hwhole by blast
  qed
next
  case False
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?TR = "(order_topology_on_UNIV::real set set)"
  let ?X = "top1_PiE I ?XR"
  let ?Tprod = "top1_product_topology_on I ?XR (\<lambda>_. ?TR)"
  let ?Tunif = "top1_metric_topology_on ?X (top1_uniform_metric_real_on I)"

  have hIne: "I \<noteq> {}"
    using False .

  have hMetric: "top1_metric_on ?X (top1_uniform_metric_real_on I)"
    by (rule top1_uniform_metric_real_on_metric_on_PiE_UNIV[OF hIne])
  have hTopTunif: "is_topology_on ?X ?Tunif"
    unfolding top1_metric_topology_on_def
    by (rule topology_generated_by_basis_is_topology_on[OF top1_metric_basis_is_basis_on[OF hMetric]])

  have hBsub: "top1_product_basis_on I ?XR (\<lambda>_. ?TR) \<subseteq> ?Tunif"
  proof (rule subsetI)
    fix b
    assume hb: "b \<in> top1_product_basis_on I ?XR (\<lambda>_. ?TR)"
    obtain U where hbU: "b = top1_PiE I U"
        and hU: "(\<forall>i\<in>I. U i \<in> ?TR \<and> U i \<subseteq> ?XR i)"
        and hFfin: "finite {i \<in> I. U i \<noteq> ?XR i}"
      using hb unfolding top1_product_basis_on_def by blast

    have hbsubX: "b \<subseteq> ?X"
    proof -
      have hsub: "\<forall>i\<in>I. U i \<subseteq> ?XR i"
        using hU by blast
      have "top1_PiE I U \<subseteq> top1_PiE I ?XR"
        by (rule top1_PiE_mono[OF hsub])
      thus ?thesis
        unfolding hbU by simp
    qed

    show "b \<in> ?Tunif"
      unfolding top1_metric_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> ?X"
        by (rule hbsubX)
      show "\<forall>x\<in>b. \<exists>ba\<in>top1_metric_basis_on ?X (top1_uniform_metric_real_on I).
            x \<in> ba \<and> ba \<subseteq> b"
      proof (intro ballI)
        fix x
        assume hx: "x \<in> b"
        have hxX: "x \<in> ?X"
          using hbsubX hx by blast

        define F where "F = {i \<in> I. U i \<noteq> ?XR i}"
        have hFfin': "finite F"
          using hFfin unfolding F_def by simp

        have hUeq_XR: "\<And>i. i \<in> I \<Longrightarrow> i \<notin> F \<Longrightarrow> U i = ?XR i"
        proof -
          fix i assume hiI: "i \<in> I" and hin: "i \<notin> F"
          have "U i = ?XR i"
            using hiI hin unfolding F_def by blast
          thus "U i = ?XR i" .
        qed

        show "\<exists>ba\<in>top1_metric_basis_on ?X (top1_uniform_metric_real_on I).
              x \<in> ba \<and> ba \<subseteq> b"
        proof (cases "F = {}")
          case True
          have hUall: "\<forall>i\<in>I. U i = ?XR i"
          proof (intro ballI)
            fix i assume hiI: "i \<in> I"
            have "i \<notin> F"
              using True by simp
            thus "U i = ?XR i"
              using hUeq_XR hiI by blast
          qed

          have hb_eqX: "b = ?X"
          proof -
            have "top1_PiE I U = top1_PiE I ?XR"
              by (rule top1_PiE_cong_on[OF hUall])
            thus ?thesis
              unfolding hbU by simp
          qed

          define \<delta> where "\<delta> = (1::real)"
	          have hdel_pos: "\<delta> > 0"
	            unfolding \<delta>_def by simp
	          have hxx0: "top1_uniform_metric_real_on I x x = 0"
	            by (rule top1_uniform_metric_real_on_refl[OF hIne]) (use hxX in simp)
	          have hxball: "x \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta>"
	            unfolding top1_ball_on_def using hxX hdel_pos hxx0 by simp
	          have hball_basis:
	            "top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta>
              \<in> top1_metric_basis_on ?X (top1_uniform_metric_real_on I)"
            unfolding top1_metric_basis_on_def using hxX hdel_pos by blast
          have hball_sub: "top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta> \<subseteq> b"
            unfolding hb_eqX by (simp add: top1_ball_on_def)

          show ?thesis
            apply (rule bexI[where x="top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta>"])
             apply (intro conjI)
              apply (rule hxball)
             apply (rule hball_sub)
            apply (rule hball_basis)
            done
        next
          case False
          have hcoord:
            "\<forall>i\<in>F. \<exists>\<epsilon>>0. top1_ball_on UNIV top1_real_bounded_metric (x i) \<epsilon> \<subseteq> U i"
          proof (intro ballI)
            fix i
            assume hiF: "i \<in> F"
            have hiI: "i \<in> I"
              using hiF unfolding F_def by blast
	            have hUiTR: "U i \<in> ?TR"
	              using hU hiI by blast
	            have hxUi: "x i \<in> U i"
	            proof -
	              have hxPiE: "x \<in> top1_PiE I U"
	                using hx unfolding hbU by simp
	              have hxall: "\<forall>j\<in>I. x j \<in> U j"
	                using hxPiE unfolding top1_PiE_iff by simp
	              show ?thesis
	                using hxall hiI by simp
	            qed
	            have hUiMet: "U i \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
	              using hUiTR unfolding order_topology_on_UNIV_eq_bounded_metric_topology_real by simp
            obtain \<epsilon> where heps: "\<epsilon> > 0"
                and hball_sub: "top1_ball_on UNIV top1_real_bounded_metric (x i) \<epsilon> \<subseteq> U i"
              using top1_metric_open_contains_ball[OF top1_real_bounded_metric_metric_on hUiMet hxUi] by blast
            show "\<exists>\<epsilon>>0. top1_ball_on UNIV top1_real_bounded_metric (x i) \<epsilon> \<subseteq> U i"
              using heps hball_sub by blast
          qed

          obtain \<epsilon>fun where h\<epsilon>fun:
            "\<forall>i\<in>F. \<epsilon>fun i > 0 \<and> top1_ball_on UNIV top1_real_bounded_metric (x i) (\<epsilon>fun i) \<subseteq> U i"
            using bchoice[OF hcoord] by blast

          define \<delta> where "\<delta> = Min ((\<epsilon>fun) ` F)"
          have hdel_pos: "\<delta> > 0"
          proof -
            have hfin: "finite ((\<epsilon>fun) ` F)"
              using hFfin' by simp
            have hne: "((\<epsilon>fun) ` F) \<noteq> {}"
              using False by simp
            have hMin_in: "Min ((\<epsilon>fun) ` F) \<in> (\<epsilon>fun) ` F"
              by (rule Min_in[OF hfin hne])
            then obtain i0 where hi0: "i0 \<in> F" and hdel_eq: "\<delta> = \<epsilon>fun i0"
              unfolding \<delta>_def by blast
            have "\<epsilon>fun i0 > 0"
              using h\<epsilon>fun hi0 by blast
            thus ?thesis
              unfolding hdel_eq by simp
          qed

          have hdel_le: "\<And>i. i \<in> F \<Longrightarrow> \<delta> \<le> \<epsilon>fun i"
          proof -
            fix i assume hiF: "i \<in> F"
            have hfin: "finite ((\<epsilon>fun) ` F)"
              using hFfin' by simp
            have "\<epsilon>fun i \<in> (\<epsilon>fun) ` F"
              using hiF by blast
            hence "Min ((\<epsilon>fun) ` F) \<le> \<epsilon>fun i"
              by (rule Min_le[OF hfin])
            thus "\<delta> \<le> \<epsilon>fun i"
              unfolding \<delta>_def by simp
          qed

	          have hxx0: "top1_uniform_metric_real_on I x x = 0"
	            by (rule top1_uniform_metric_real_on_refl[OF hIne]) (use hxX in simp)
	          have hxball: "x \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta>"
	            unfolding top1_ball_on_def using hxX hdel_pos hxx0 by simp
	          have hball_basis:
	            "top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta>
              \<in> top1_metric_basis_on ?X (top1_uniform_metric_real_on I)"
            unfolding top1_metric_basis_on_def using hxX hdel_pos by blast

          have hball_sub: "top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta> \<subseteq> b"
          proof (rule subsetI)
            fix y
            assume hy: "y \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta>"
            have hyX: "y \<in> ?X" and hdist: "top1_uniform_metric_real_on I x y < \<delta>"
              using hy unfolding top1_ball_on_def by blast+
            have hyExt: "\<forall>j. j \<notin> I \<longrightarrow> y j = undefined"
              using hyX unfolding top1_PiE_iff by blast

            have hyU: "\<forall>i\<in>I. y i \<in> U i"
            proof (intro ballI)
              fix i assume hiI: "i \<in> I"
              show "y i \<in> U i"
              proof (cases "i \<in> F")
                case True
	                have hle_coord:
	                  "top1_real_bounded_metric (x i) (y i) \<le> top1_uniform_metric_real_on I x y"
	                  by (rule top1_uniform_metric_real_on_coord_le[OF hiI])
	                have hxy_lt: "top1_real_bounded_metric (x i) (y i) < \<delta>"
	                  by (rule le_less_trans[OF hle_coord hdist])
                have "\<delta> \<le> \<epsilon>fun i"
                  by (rule hdel_le[OF True])
	                hence hxy_lt_eps: "top1_real_bounded_metric (x i) (y i) < \<epsilon>fun i"
	                  by (rule less_le_trans[OF hxy_lt])
                have "y i \<in> top1_ball_on UNIV top1_real_bounded_metric (x i) (\<epsilon>fun i)"
                  unfolding top1_ball_on_def using hxy_lt_eps by simp
                moreover have "top1_ball_on UNIV top1_real_bounded_metric (x i) (\<epsilon>fun i) \<subseteq> U i"
                  using h\<epsilon>fun True by blast
                ultimately show ?thesis
                  by blast
              next
                case False
                have "U i = ?XR i"
                  using hUeq_XR hiI False by blast
                thus ?thesis
                  by simp
              qed
            qed

            show "y \<in> b"
              unfolding hbU top1_PiE_iff using hyU hyExt by blast
          qed

          show ?thesis
            apply (rule bexI[where x="top1_ball_on ?X (top1_uniform_metric_real_on I) x \<delta>"])
             apply (intro conjI)
              apply (rule hxball)
             apply (rule hball_sub)
            apply (rule hball_basis)
            done
        qed
      qed
    qed
  qed

  have "?Tprod \<subseteq> ?Tunif"
    unfolding top1_product_topology_on_def
    by (rule topology_generated_by_basis_subset[OF hTopTunif hBsub])
  thus ?thesis
    by simp
qed

(** For infinite index sets, the product topology on \<open>\<real>^I\<close> is strictly coarser than the uniform metric topology. **)
lemma top1_product_topology_ne_uniform_metric_topology_real:
  fixes I :: "'i set"
  assumes hInf: "infinite I"
  shows "top1_product_topology_on I (\<lambda>_. (UNIV::real set)) (\<lambda>_. (order_topology_on_UNIV::real set set))
    \<noteq> top1_metric_topology_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_uniform_metric_real_on I)"
proof (rule notI)
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?TR = "(order_topology_on_UNIV::real set set)"
  let ?X = "top1_PiE I ?XR"
  let ?Tprod = "top1_product_topology_on I ?XR (\<lambda>_. ?TR)"
  let ?Tunif = "top1_metric_topology_on ?X (top1_uniform_metric_real_on I)"

  assume hEq: "?Tprod = ?Tunif"

  have hIne: "I \<noteq> {}"
    using hInf by auto

  define x0 where "x0 = (\<lambda>i. if i \<in> I then (0::real) else undefined)"
  have hx0X: "x0 \<in> ?X"
    unfolding x0_def top1_PiE_iff by simp

  have hMetric: "top1_metric_on ?X (top1_uniform_metric_real_on I)"
    by (rule top1_uniform_metric_real_on_metric_on_PiE_UNIV[OF hIne])

  define B where "B = top1_ball_on ?X (top1_uniform_metric_real_on I) x0 (1/2)"
  have hB_Tunif: "B \<in> ?Tunif"
  proof -
    have "B \<in> top1_metric_topology_on ?X (top1_uniform_metric_real_on I)"
      unfolding B_def
      by (rule top1_ball_open_in_metric_topology[OF hMetric hx0X]) simp
    thus ?thesis
      by simp
  qed

  have hx0B: "x0 \<in> B"
  proof -
    have hxx0: "top1_uniform_metric_real_on I x0 x0 = 0"
      by (rule top1_uniform_metric_real_on_refl[OF hIne hx0X])
    show ?thesis
      unfolding B_def top1_ball_on_def using hx0X hxx0 by simp
  qed

  have hB_not_Tprod: "B \<notin> ?Tprod"
  proof
    assume hBprod: "B \<in> ?Tprod"

    have hBgen:
      "B \<subseteq> ?X
        \<and> (\<forall>x\<in>B. \<exists>ba\<in>top1_product_basis_on I ?XR (\<lambda>_. ?TR). x \<in> ba \<and> ba \<subseteq> B)"
      using hBprod unfolding top1_product_topology_on_def topology_generated_by_basis_def by simp
    have hBnbhd:
      "\<forall>x\<in>B. \<exists>ba\<in>top1_product_basis_on I ?XR (\<lambda>_. ?TR). x \<in> ba \<and> ba \<subseteq> B"
      using hBgen by blast

    obtain b where hbasis: "b \<in> top1_product_basis_on I ?XR (\<lambda>_. ?TR)"
        and hx0b: "x0 \<in> b"
        and hbsub: "b \<subseteq> B"
      using hBnbhd hx0B by blast

    obtain U where hbU: "b = top1_PiE I U"
        and hU: "(\<forall>i\<in>I. U i \<in> ?TR \<and> U i \<subseteq> ?XR i)"
        and hFfin: "finite {i \<in> I. U i \<noteq> ?XR i}"
      using hbasis unfolding top1_product_basis_on_def by blast

    define F where "F = {i \<in> I. U i \<noteq> ?XR i}"
    have hFfin': "finite F"
      using hFfin unfolding F_def by simp

    have hIFne: "I - F \<noteq> {}"
    proof
      assume hIF0: "I - F = {}"
      have hIsubF: "I \<subseteq> F"
        using hIF0 by blast
      have "finite I"
        by (rule finite_subset[OF hIsubF hFfin'])
      with hInf show False
        by simp
    qed
    obtain j where hj: "j \<in> I - F"
      using hIFne by blast
    have hjI: "j \<in> I" and hjnF: "j \<notin> F"
      using hj by blast+

    have hx0_in_U: "\<forall>i\<in>I. x0 i \<in> U i"
      using hx0b unfolding hbU top1_PiE_iff by simp

    have hUj_UNIV: "U j = (UNIV::real set)"
    proof -
      have "j \<in> I"
        by (rule hjI)
      moreover have "U j = ?XR j"
        using hjI hjnF unfolding F_def by blast
      ultimately show ?thesis
        by simp
    qed

    define y where "y = (\<lambda>i. if i \<in> I then (if i = j then (1::real) else x0 i) else undefined)"

    have hyX: "y \<in> ?X"
      unfolding y_def x0_def top1_PiE_iff by simp

    have hyb: "y \<in> b"
    proof -
      have hyU: "\<forall>i\<in>I. y i \<in> U i"
      proof (intro ballI)
        fix i assume hiI: "i \<in> I"
        show "y i \<in> U i"
        proof (cases "i = j")
          case True
          show ?thesis
            unfolding y_def using True hiI hjI hUj_UNIV by simp
        next
          case False
          have "y i = x0 i"
            unfolding y_def using hiI False by simp
          moreover have "x0 i \<in> U i"
            using hx0_in_U hiI by simp
          ultimately show ?thesis
            by simp
        qed
      qed
      show ?thesis
        unfolding hbU top1_PiE_iff
        apply (intro conjI)
         apply (rule hyU)
        unfolding y_def by simp
    qed

    have hyB: "y \<in> B"
      using hbsub hyb by blast

    have hcoord: "top1_real_bounded_metric (x0 j) (y j) = 1"
      using hjI unfolding x0_def y_def top1_real_bounded_metric_def by simp
    have hle_coord:
      "top1_real_bounded_metric (x0 j) (y j) \<le> top1_uniform_metric_real_on I x0 y"
      by (rule top1_uniform_metric_real_on_coord_le[OF hjI])
    have hdist_ge: "1 \<le> top1_uniform_metric_real_on I x0 y"
      using hcoord hle_coord by simp

    have hnot_ball: "y \<notin> B"
    proof -
      have "\<not> (top1_uniform_metric_real_on I x0 y < 1/2)"
        using hdist_ge by linarith
      thus ?thesis
        unfolding B_def top1_ball_on_def using hyX by simp
    qed

    show False
      using hyB hnot_ball by contradiction
  qed

  have "B \<in> ?Tprod"
    using hEq hB_Tunif by simp
  with hB_not_Tprod show False
    by contradiction
qed

(** For infinite index sets, the uniform metric topology on \<open>\<real>^I\<close> is strictly coarser than the box topology. **)
lemma top1_uniform_metric_topology_ne_box_topology_real:
  fixes I :: "'i set"
  assumes hInf: "infinite I"
  shows "top1_metric_topology_on (top1_PiE I (\<lambda>_. (UNIV::real set))) (top1_uniform_metric_real_on I)
    \<noteq> top1_box_topology_on I (\<lambda>_. (UNIV::real set)) (\<lambda>_. (order_topology_on_UNIV::real set set))"
proof (rule notI)
  let ?XR = "(\<lambda>_. (UNIV::real set))"
  let ?TR = "(order_topology_on_UNIV::real set set)"
  let ?X = "top1_PiE I ?XR"
  let ?Tunif = "top1_metric_topology_on ?X (top1_uniform_metric_real_on I)"
  let ?Tbox = "top1_box_topology_on I ?XR (\<lambda>_. ?TR)"

  assume hEq: "?Tunif = ?Tbox"

  have hIne: "I \<noteq> {}"
    using hInf by auto

  have hTopAll: "\<forall>i\<in>I. is_topology_on (?XR i) ?TR"
  proof (intro ballI)
    fix i assume "i \<in> I"
    show "is_topology_on (?XR i) ?TR"
      using order_topology_on_UNIV_is_topology_on by simp
  qed

  have hBasisBox: "is_basis_on ?X (top1_box_basis_on I ?XR (\<lambda>_. ?TR))"
    by (rule top1_box_basis_is_basis_on[OF hTopAll])

  have hNotFin: "\<not> finite I"
    using hInf by simp
  obtain f :: "nat \<Rightarrow> 'i" where hf_inj: "inj f" and hf_range: "range f \<subseteq> I"
    using infinite_countable_subset[OF hNotFin] by blast

  define g where "g = inv_into UNIV f"
  have hginv: "\<And>n. g (f n) = n"
    unfolding g_def using hf_inj by (simp add: inv_into_f_f)

  define U where
    "U = (\<lambda>i. if i \<in> range f
          then open_interval (- inverse (real (Suc (g i)))) (inverse (real (Suc (g i))))
          else (UNIV::real set))"
  define W where "W = top1_PiE I U"

  have hW_basis: "W \<in> top1_box_basis_on I ?XR (\<lambda>_. ?TR)"
  proof -
    have hUiTR: "\<forall>i\<in>I. U i \<in> ?TR \<and> U i \<subseteq> ?XR i"
    proof (intro ballI)
      fix i assume hiI: "i \<in> I"
      show "U i \<in> ?TR \<and> U i \<subseteq> ?XR i"
      proof (cases "i \<in> range f")
        case False
        have hUi: "U i = (UNIV::real set)"
          unfolding U_def using False by simp
        have hUNIV: "(UNIV::real set) \<in> ?TR"
        proof -
          have hTop: "is_topology_on (UNIV::real set) ?TR"
            by (rule order_topology_on_UNIV_is_topology_on)
          show ?thesis
            by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
        qed
        show ?thesis
          using hUi hUNIV by simp
      next
        case True
        define r where "r = inverse (real (Suc (g i)))"
        have hr: "0 < r"
          unfolding r_def by simp
        have hab: "(-r) < r"
          using hr by simp
        have hopen: "open_interval (-r) r \<in> ?TR"
          by (rule open_interval_in_order_topology[OF hab])
        have hUi: "U i = open_interval (-r) r"
          unfolding U_def r_def using True by simp
        have hsub: "U i \<subseteq> ?XR i"
          unfolding hUi by simp
        have "U i \<in> ?TR"
          unfolding hUi using hopen by simp
        thus ?thesis
          using hsub by simp
      qed
    qed
    show ?thesis
      unfolding W_def top1_box_basis_on_def
      apply (rule CollectI)
      apply (rule exI[where x=U])
      apply (intro conjI)
       apply simp
      apply (rule hUiTR)
      done
  qed

  have hW_Tbox: "W \<in> ?Tbox"
    unfolding top1_box_topology_on_def
    by (rule basis_elem_open_in_generated_topology[OF hBasisBox hW_basis])

  have hMetric: "top1_metric_on ?X (top1_uniform_metric_real_on I)"
    by (rule top1_uniform_metric_real_on_metric_on_PiE_UNIV[OF hIne])

  define x0 where "x0 = (\<lambda>i. if i \<in> I then (0::real) else undefined)"
  have hx0X: "x0 \<in> ?X"
    unfolding x0_def top1_PiE_iff by simp

  have hx0W: "x0 \<in> W"
  proof -
    have hx0U: "\<forall>i\<in>I. x0 i \<in> U i"
    proof (intro ballI)
      fix i assume hiI: "i \<in> I"
      show "x0 i \<in> U i"
      proof (cases "i \<in> range f")
        case False
        show ?thesis
          unfolding U_def x0_def using False hiI by simp
      next
        case True
        define r where "r = inverse (real (Suc (g i)))"
        have hr: "0 < r"
          unfolding r_def by simp
        have hab: "(-r) < (0::real)"
          using hr by simp
        have hbc: "(0::real) < r"
          using hr by simp
        have "x0 i = 0"
          unfolding x0_def using hiI by simp
        thus ?thesis
          unfolding U_def r_def open_interval_def using True hab hbc by simp
      qed
    qed
    show ?thesis
      unfolding W_def top1_PiE_iff using hx0U x0_def by simp
  qed
  
  have hW_not_Tunif: "W \<notin> ?Tunif"
  proof
    assume hWopen: "W \<in> ?Tunif"
    obtain \<epsilon> where heps: "0 < \<epsilon>"
        and hball_sub: "top1_ball_on ?X (top1_uniform_metric_real_on I) x0 \<epsilon> \<subseteq> W"
      using top1_metric_open_contains_ball[OF hMetric hWopen hx0W] by blast

    obtain N :: nat where hN: "inverse (of_nat (Suc N)) < \<epsilon>"
      using reals_Archimedean[OF heps] by blast
    define i0 where "i0 = f N"
    have hi0I: "i0 \<in> I"
    proof -
      have "f N \<in> range f"
        by blast
      then have "f N \<in> I"
        using hf_range by blast
      thus ?thesis
        unfolding i0_def .
    qed
    have hi0Range: "i0 \<in> range f"
      unfolding i0_def by blast

    define r where "r = inverse (real (Suc N))"
    have hr_pos: "0 < r"
      unfolding r_def by simp
    have hr_lt: "r < \<epsilon>"
      using hN unfolding r_def by simp

    define y where "y = (\<lambda>i. if i \<in> I then (if i = i0 then r else (0::real)) else undefined)"
    have hyX: "y \<in> ?X"
      unfolding y_def top1_PiE_iff by simp

    have hdist_le: "top1_uniform_metric_real_on I x0 y \<le> r"
    proof -
      define S where "S = ((\<lambda>i. top1_real_bounded_metric (x0 i) (y i)) ` I)"
      have hSne: "S \<noteq> {}"
      proof -
        have "top1_real_bounded_metric (x0 i0) (y i0) \<in> S"
          unfolding S_def using hi0I by blast
        thus ?thesis
          by blast
      qed

      have hall: "\<forall>s\<in>S. s \<le> r"
      proof (intro ballI)
        fix s
        assume hs: "s \<in> S"
        then obtain i where hiI: "i \<in> I" and hs_eq: "s = top1_real_bounded_metric (x0 i) (y i)"
          unfolding S_def by blast
        show "s \<le> r"
        proof (cases "i = i0")
          case True
          have hx0i: "x0 i = (0::real)"
            using hiI unfolding x0_def by simp
          have hyi: "y i = r"
            using hiI True unfolding y_def by simp
          have habs: "abs ((0::real) - r) = r"
            using hr_pos by simp
          have "top1_real_bounded_metric (x0 i) (y i) = min r 1"
            unfolding hx0i hyi top1_real_bounded_metric_def habs by simp
          moreover have "min r 1 = r"
          proof -
            have "r \<le> 1"
            proof -
              have h: "(1::real) \<le> 1 + real N"
                by simp
              have "inverse (1 + real N) \<le> inverse 1"
                by (rule le_imp_inverse_le[OF h]) simp
              thus ?thesis
                unfolding r_def by simp
            qed
            thus ?thesis
              by simp
          qed
          ultimately have "top1_real_bounded_metric (x0 i) (y i) = r"
            by simp
          thus ?thesis
            unfolding hs_eq by simp
        next
          case False
          have hx0i: "x0 i = (0::real)"
            using hiI unfolding x0_def by simp
          have hyi: "y i = (0::real)"
            using hiI False unfolding y_def by simp
          have "top1_real_bounded_metric (x0 i) (y i) = 0"
            unfolding hx0i hyi top1_real_bounded_metric_def by simp
          thus ?thesis
            unfolding hs_eq using hr_pos by simp
        qed
      qed

      have "Sup S \<le> r"
      proof (rule cSup_least[OF hSne])
        fix s
        assume hs: "s \<in> S"
        show "s \<le> r"
          using hall hs by blast
      qed
      thus ?thesis
        unfolding top1_uniform_metric_real_on_def S_def by simp
    qed

    have hdist_lt: "top1_uniform_metric_real_on I x0 y < \<epsilon>"
      using hdist_le hr_lt by linarith
    have hyball: "y \<in> top1_ball_on ?X (top1_uniform_metric_real_on I) x0 \<epsilon>"
      unfolding top1_ball_on_def using hyX hdist_lt by simp
    have hyW: "y \<in> W"
      using hball_sub hyball by blast

    have hyU0: "y i0 \<in> U i0"
    proof -
      have "\<forall>i\<in>I. y i \<in> U i"
        using hyW unfolding W_def top1_PiE_iff by simp
      thus ?thesis
        using hi0I by simp
    qed

    have hUi0: "U i0 = open_interval (-r) r"
      unfolding U_def r_def using hi0Range by (simp add: hginv i0_def)
    have "y i0 = r"
      using hi0I unfolding y_def by simp
    hence "y i0 \<notin> U i0"
      unfolding hUi0 open_interval_def by simp
    thus False
      using hyU0 by contradiction
  qed
  (* Proof idea: pick a box-basic neighborhood around the zero function with radii shrinking along an injected copy
     of \<open>\<nat>\<close>; any uniform ball includes a point violating one of those coordinate constraints.  A full draft of
     this argument previously caused `*** Timeout` under session option `timeout=120`. *)

  have "W \<in> ?Tunif"
    using hEq hW_Tbox by simp
  with hW_not_Tunif show False
    by contradiction
qed

(** from \S20 Theorem 20.4 [top1.tex:1761] **)
theorem Theorem_20_4:
  fixes I :: "'i set"
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "TR \<equiv> (order_topology_on_UNIV::real set set)"
  defines "X\<^sub>R \<equiv> top1_PiE I XR"
  defines "Tprod \<equiv> top1_product_topology_on I XR (\<lambda>_. TR)"
  defines "Tbox \<equiv> top1_box_topology_on I XR (\<lambda>_. TR)"
  defines "Tunif \<equiv> top1_metric_topology_on X\<^sub>R (top1_uniform_metric_real_on I)"
  shows "Tprod \<subseteq> Tunif \<and> Tunif \<subseteq> Tbox"
    and "infinite I \<longrightarrow> Tprod \<noteq> Tunif \<and> Tunif \<noteq> Tbox \<and> Tprod \<noteq> Tbox"
text \<open>
  Proof status: admitted for now.

  Intended proof plan: show the uniform metric topology is finer than the product topology (basic product rectangles
  contain a uniform-metric ball) and coarser than the box topology (uniform balls are boxes with a uniform radius
  bound).  For infinite \<open>I\<close>, provide standard strictness counterexamples (e.g. a box-open set requiring
  coordinatewise radii not bounded below, and a product-open set not containing any uniform ball).
\<close>
proof -
  have hTunifSub: "Tunif \<subseteq> Tbox"
    unfolding Tunif_def Tbox_def X\<^sub>R_def XR_def TR_def
    by (rule top1_uniform_metric_topology_subset_box_topology_real)
  have hTprodSub: "Tprod \<subseteq> Tunif"
    unfolding Tunif_def Tprod_def X\<^sub>R_def XR_def TR_def
    by (rule top1_product_topology_subset_uniform_metric_topology_real)
  show "Tprod \<subseteq> Tunif \<and> Tunif \<subseteq> Tbox"
    using hTprodSub hTunifSub by blast
next
  show "infinite I \<longrightarrow> Tprod \<noteq> Tunif \<and> Tunif \<noteq> Tbox \<and> Tprod \<noteq> Tbox"
  proof
    assume hInfI: "infinite I"

    have hTunifSub0: "Tunif \<subseteq> Tbox"
      unfolding Tunif_def Tbox_def X\<^sub>R_def XR_def TR_def
      by (rule top1_uniform_metric_topology_subset_box_topology_real)
    have hTprodSub0: "Tprod \<subseteq> Tunif"
      unfolding Tunif_def Tprod_def X\<^sub>R_def XR_def TR_def
      by (rule top1_product_topology_subset_uniform_metric_topology_real)

    have hprod_ne: "Tprod \<noteq> Tunif"
      unfolding Tprod_def Tunif_def X\<^sub>R_def XR_def TR_def
      using top1_product_topology_ne_uniform_metric_topology_real[OF hInfI] by simp

    have hunif_ne: "Tunif \<noteq> Tbox"
      unfolding Tunif_def Tbox_def X\<^sub>R_def XR_def TR_def
      using top1_uniform_metric_topology_ne_box_topology_real[OF hInfI] by simp

    have hprod_box_ne: "Tprod \<noteq> Tbox"
    proof
      assume hEq: "Tprod = Tbox"
      have hTunifSub': "Tunif \<subseteq> Tprod"
        using hTunifSub0 hEq by simp
      have "Tprod = Tunif"
        by (rule subset_antisym[OF hTprodSub0 hTunifSub'])
      thus False
        using hprod_ne by simp
    qed

    show "Tprod \<noteq> Tunif \<and> Tunif \<noteq> Tbox \<and> Tprod \<noteq> Tbox"
      using hprod_ne hunif_ne hprod_box_ne by blast
  qed
qed

(** A basic open ball for Munkres' \<open>D\<close>-metric is open in the product topology. **)
lemma top1_D_metric_real_omega_ball_in_product_topology:
  fixes x :: "nat \<Rightarrow> real"
  fixes e :: real
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "TR \<equiv> (order_topology_on_UNIV::real set set)"
  defines "X\<omega> \<equiv> top1_PiE (UNIV::nat set) XR"
  defines "Tprod \<equiv> top1_product_topology_on (UNIV::nat set) XR (\<lambda>_. TR)"
  assumes hx: "x \<in> X\<omega>"
  assumes he: "0 < e"
  shows "top1_ball_on X\<omega> top1_D_metric_real_omega x e \<in> Tprod"
proof -
  have hTopTR: "is_topology_on (UNIV::real set) TR"
    unfolding TR_def by (rule order_topology_on_UNIV_is_topology_on)

  show ?thesis
    unfolding Tprod_def X\<omega>_def top1_product_topology_on_def topology_generated_by_basis_def
  proof (rule CollectI, intro conjI)
    show "top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e \<subseteq>
          top1_PiE (UNIV::nat set) XR"
      unfolding top1_ball_on_def by simp

    show "\<forall>y\<in>top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e.
            \<exists>ba\<in>top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR).
              y \<in> ba \<and> ba \<subseteq> top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e"
    proof (intro ballI)
      fix y
      assume hy: "y \<in> top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e"
      have hyX: "y \<in> X\<omega>" and hDxy: "top1_D_metric_real_omega x y < e"
        using hy unfolding top1_ball_on_def X\<omega>_def by blast+

      define \<delta> where "\<delta> = (e - top1_D_metric_real_omega x y) / 2"
      have hdel_pos: "0 < \<delta>"
        using hDxy he unfolding \<delta>_def by simp

      obtain N :: nat where hN: "1 / real (Suc N) < \<delta>"
      proof -
        obtain N :: nat where hN': "inverse (of_nat (Suc N)) < \<delta>"
          using reals_Archimedean[OF hdel_pos] by blast
        have "1 / real (Suc N) < \<delta>"
          using hN' by (simp add: field_simps)
        thus ?thesis
          by (rule that)
      qed

      define U where
        "U = (\<lambda>n.
            if n < Suc N then top1_ball_on UNIV top1_real_bounded_metric (y n) (\<delta> * real (Suc n))
            else (UNIV::real set))"
      define ba where "ba = top1_PiE (UNIV::nat set) U"

      have hU_in: "\<forall>i\<in>(UNIV::nat set). U i \<in> TR \<and> U i \<subseteq> XR i"
      proof (intro ballI)
        fix i :: nat
        show "U i \<in> TR \<and> U i \<subseteq> XR i"
        proof (cases "i < Suc N")
          case True
          have hpos: "0 < \<delta> * real (Suc i)"
            using hdel_pos by simp
          have hUiTR:
            "top1_ball_on UNIV top1_real_bounded_metric (y i) (\<delta> * real (Suc i)) \<in> TR"
            unfolding TR_def by (rule top1_real_bounded_metric_ball_in_order_topology[OF hpos])
          show ?thesis
            unfolding U_def XR_def using True hUiTR by simp
        next
          case False
          have hUNIV: "UNIV \<in> TR"
            using hTopTR unfolding is_topology_on_def by blast
          show ?thesis
            unfolding U_def XR_def using False hUNIV by simp
        qed
      qed

      have hfin: "finite {i \<in> (UNIV::nat set). U i \<noteq> XR i}"
      proof -
        have hsub: "{i \<in> (UNIV::nat set). U i \<noteq> XR i} \<subseteq> {i. i < Suc N}"
          unfolding XR_def U_def by auto
        have hfin': "finite {i. i < Suc N}"
          by simp
        show ?thesis
          by (rule finite_subset[OF hsub hfin'])
      qed

      have hba_basis: "ba \<in> top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR)"
        unfolding ba_def top1_product_basis_on_def using hU_in hfin by blast

      have hy_in_ba: "y \<in> ba"
      proof -
        have hyU: "\<forall>i\<in>(UNIV::nat set). y i \<in> U i"
        proof (intro ballI)
          fix i :: nat
          show "y i \<in> U i"
          proof (cases "i < Suc N")
            case True
            have hpos: "0 < \<delta> * real (Suc i)"
              using hdel_pos by simp
            have "y i \<in> top1_ball_on UNIV top1_real_bounded_metric (y i) (\<delta> * real (Suc i))"
            proof -
              have h0: "top1_real_bounded_metric (y i) (y i) = 0"
                unfolding top1_real_bounded_metric_def by simp
              have "top1_real_bounded_metric (y i) (y i) < \<delta> * real (Suc i)"
                using hpos unfolding h0 by simp
              thus ?thesis
                unfolding top1_ball_on_def using hpos by simp
            qed
            thus ?thesis
              unfolding U_def using True by simp
          next
            case False
            show ?thesis
              unfolding U_def using False by simp
          qed
        qed
        show ?thesis
          unfolding ba_def top1_PiE_iff using hyU by simp
      qed

      have hba_sub_ball: "ba \<subseteq> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
      proof (rule subsetI)
        fix z
        assume hz: "z \<in> ba"
        have hzX: "z \<in> X\<omega>"
        proof -
          have hzU: "\<forall>i\<in>(UNIV::nat set). z i \<in> U i"
            using hz unfolding ba_def top1_PiE_iff by simp
          have hzXR: "\<forall>i\<in>(UNIV::nat set). z i \<in> XR i"
          proof (intro ballI)
            fix i :: nat
            have "U i \<subseteq> XR i"
              using hU_in by simp
            moreover have "z i \<in> U i"
              using hzU by simp
            ultimately show "z i \<in> XR i"
              by blast
          qed
          show ?thesis
          proof -
            have hzXR': "\<forall>i\<in>(UNIV::nat set). z i \<in> XR i"
              using hzXR by simp
            show ?thesis
              unfolding X\<omega>_def top1_PiE_iff using hzXR' by simp
          qed
        qed

        have hterm_le: "\<forall>n. top1_real_bounded_metric (y n) (z n) / real (Suc n) \<le> \<delta>"
        proof
          fix n
          show "top1_real_bounded_metric (y n) (z n) / real (Suc n) \<le> \<delta>"
          proof (cases "n < Suc N")
            case True
            have hzU: "z n \<in> U n"
              using hz unfolding ba_def top1_PiE_iff by simp
            have hpos: "0 < \<delta> * real (Suc n)"
              using hdel_pos by simp
            have "z n \<in> top1_ball_on UNIV top1_real_bounded_metric (y n) (\<delta> * real (Suc n))"
              using hzU True unfolding U_def by simp
            then have "top1_real_bounded_metric (y n) (z n) < \<delta> * real (Suc n)"
              unfolding top1_ball_on_def using hpos by simp
            then have "top1_real_bounded_metric (y n) (z n) / real (Suc n) < \<delta>"
              by (simp add: field_simps)
            thus ?thesis
              by simp
          next
            case False
            have hbd: "top1_real_bounded_metric (y n) (z n) \<le> 1"
              unfolding top1_real_bounded_metric_def by simp
            have hposn: "0 < (real (Suc n) :: real)"
              by simp
            have "top1_real_bounded_metric (y n) (z n) / real (Suc n) \<le> 1 / real (Suc n)"
              using hbd hposn by (simp add: divide_right_mono)
            also have "... \<le> 1 / real (Suc N)"
            proof -
              have hle: "real (Suc N) \<le> (real (Suc n) :: real)"
                using False by simp
              have "inverse (real (Suc n) :: real) \<le> inverse (real (Suc N) :: real)"
                using le_imp_inverse_le[OF hle] by simp
              thus ?thesis
                by (simp add: field_simps)
            qed
            also have "... < \<delta>"
              using hN by simp
            finally show ?thesis
              by simp
          qed
        qed

        have hDyz_le: "top1_D_metric_real_omega y z \<le> \<delta>"
        proof -
          let ?S = "((\<lambda>n. top1_real_bounded_metric (y n) (z n) / real (Suc n)) ` (UNIV::nat set))"
          have hSne: "?S \<noteq> {}"
            by simp
          have "Sup ?S \<le> \<delta>"
          proof (rule cSup_least[OF hSne])
            fix s
            assume hs: "s \<in> ?S"
            then obtain n where hn: "s = top1_real_bounded_metric (y n) (z n) / real (Suc n)"
              by blast
            show "s \<le> \<delta>"
              unfolding hn using hterm_le by simp
          qed
          thus ?thesis
            unfolding top1_D_metric_real_omega_def by simp
        qed

        have hDxz_le: "top1_D_metric_real_omega x z \<le> top1_D_metric_real_omega x y + top1_D_metric_real_omega y z"
          by (rule top1_D_metric_real_omega_triangle)
        have hDxz_lt: "top1_D_metric_real_omega x z < e"
        proof -
          have "top1_D_metric_real_omega x z \<le> top1_D_metric_real_omega x y + \<delta>"
            using hDxz_le hDyz_le by linarith
          also have "... = (top1_D_metric_real_omega x y + e) / 2"
            unfolding \<delta>_def by (simp add: field_simps)
          also have "... < e"
            using hDxy he by (simp add: field_simps)
          finally show ?thesis .
        qed

        show "z \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
          unfolding top1_ball_on_def using hzX hDxz_lt by simp
      qed

      show "\<exists>ba\<in>top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR).
              y \<in> ba \<and> ba \<subseteq> top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e"
      proof (rule bexI[where x=ba])
        show "ba \<in> top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR)"
          by (rule hba_basis)
        show "y \<in> ba \<and> ba \<subseteq> top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e"
        proof (intro conjI)
          show "y \<in> ba"
            by (rule hy_in_ba)
          show "ba \<subseteq> top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e"
          proof (rule subsetI)
            fix z
            assume hz: "z \<in> ba"
            have hz_in: "z \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
              using hz hba_sub_ball by blast
            have "z \<in> X\<omega>"
              using hz_in unfolding top1_ball_on_def by simp
            hence "z \<in> top1_PiE (UNIV::nat set) XR"
              unfolding X\<omega>_def .
            moreover have "top1_D_metric_real_omega x z < e"
              using hz_in unfolding top1_ball_on_def by simp
            ultimately show "z \<in> top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e"
              unfolding top1_ball_on_def by simp
          qed
        qed
      qed
    qed
  qed
qed

(** The product topology on \<open>\<real>^\<omega>\<close> is contained in the \<open>D\<close>-metric topology. **)
lemma top1_product_topology_subset_D_metric_topology_real_omega:
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "TR \<equiv> (order_topology_on_UNIV::real set set)"
  defines "X\<omega> \<equiv> top1_PiE (UNIV::nat set) XR"
  defines "Tprod \<equiv> top1_product_topology_on (UNIV::nat set) XR (\<lambda>_. TR)"
  assumes hmet: "top1_metric_on X\<omega> top1_D_metric_real_omega"
  shows "Tprod \<subseteq> top1_metric_topology_on X\<omega> top1_D_metric_real_omega"
proof -
  let ?Tm = "top1_metric_topology_on X\<omega> top1_D_metric_real_omega"

  have hTopMet: "is_topology_on X\<omega> ?Tm"
    by (rule top1_metric_topology_on_is_topology_on[OF hmet])

  have hBasisSub: "top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR) \<subseteq> ?Tm"
  proof (rule subsetI)
    fix b
    assume hb: "b \<in> top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR)"
    obtain U where hU:
        "\<forall>i\<in>(UNIV::nat set). U i \<in> TR \<and> U i \<subseteq> XR i"
      and hfin: "finite {i \<in> (UNIV::nat set). U i \<noteq> XR i}"
      and hb_eq: "b = top1_PiE (UNIV::nat set) U"
      using hb unfolding top1_product_basis_on_def by blast

    have hTopTR: "is_topology_on (UNIV::real set) TR"
      unfolding TR_def by (rule order_topology_on_UNIV_is_topology_on)

    have hb_sub_X: "b \<subseteq> X\<omega>"
    proof -
      have hsub: "\<forall>i\<in>(UNIV::nat set). U i \<subseteq> XR i"
        using hU by blast
      have "top1_PiE (UNIV::nat set) U \<subseteq> top1_PiE (UNIV::nat set) XR"
        by (rule top1_PiE_mono[OF hsub])
      thus ?thesis
        unfolding hb_eq X\<omega>_def by simp
    qed

    have hb_open: "b \<in> ?Tm"
      unfolding top1_metric_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> X\<omega>"
        by (rule hb_sub_X)

      show "\<forall>x\<in>b. \<exists>ba\<in>top1_metric_basis_on X\<omega> top1_D_metric_real_omega. x \<in> ba \<and> ba \<subseteq> b"
      proof (intro ballI)
        fix x
        assume hx: "x \<in> b"
        have hxX: "x \<in> X\<omega>"
          using hx hb_sub_X by blast

        let ?F = "{i \<in> (UNIV::nat set). U i \<noteq> XR i}"
        have hFfin: "finite ?F"
          using hfin by simp

        have hxU: "\<forall>i\<in>(UNIV::nat set). x i \<in> U i"
          using hx unfolding hb_eq top1_PiE_iff by simp

        have hcoord_ball:
          "\<forall>i\<in>?F. \<exists>\<epsilon>>0. top1_ball_on UNIV top1_real_bounded_metric (x i) \<epsilon> \<subseteq> U i"
        proof (intro ballI)
          fix i
          assume hiF: "i \<in> ?F"
          have hUiTR: "U i \<in> TR"
            using hU hiF by simp
          have hxi: "x i \<in> U i"
            using hxU hiF by simp
          have hUiMet: "U i \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
            using hUiTR unfolding TR_def order_topology_on_UNIV_eq_bounded_metric_topology_real by simp
          obtain \<epsilon> where heps: "0 < \<epsilon>"
              and hball_sub: "top1_ball_on UNIV top1_real_bounded_metric (x i) \<epsilon> \<subseteq> U i"
            using top1_metric_open_contains_ball[OF top1_real_bounded_metric_metric_on hUiMet hxi] by blast
          show "\<exists>\<epsilon>>0. top1_ball_on UNIV top1_real_bounded_metric (x i) \<epsilon> \<subseteq> U i"
            using heps hball_sub by blast
        qed

        obtain eps where heps:
          "\<forall>i\<in>?F. 0 < eps i \<and> top1_ball_on UNIV top1_real_bounded_metric (x i) (eps i) \<subseteq> U i"
          using bchoice[OF hcoord_ball] by blast

        define r where
          "r = (if ?F = {} then 1 else Min ((\<lambda>i. eps i / real (Suc i)) ` ?F))"

        have hr_pos: "0 < r"
        proof (cases "?F = {}")
          case True
          show ?thesis
            unfolding r_def using True by simp
        next
          case False
          have hImg_fin: "finite ((\<lambda>i. eps i / real (Suc i)) ` ?F)"
            using hFfin by blast
          have hImg_ne: "(\<lambda>i. eps i / real (Suc i)) ` ?F \<noteq> {}"
            using False by simp
          have hMin_in: "Min ((\<lambda>i. eps i / real (Suc i)) ` ?F) \<in> ((\<lambda>i. eps i / real (Suc i)) ` ?F)"
            by (rule Min_in[OF hImg_fin hImg_ne])
          then obtain i0 where hi0F: "i0 \<in> ?F"
              and hMin_eq: "Min ((\<lambda>i. eps i / real (Suc i)) ` ?F) = eps i0 / real (Suc i0)"
            by blast
          have "0 < eps i0 / real (Suc i0)"
            using heps hi0F by simp
          thus ?thesis
            unfolding r_def using False hMin_eq by simp
        qed

        have hball_sub: "top1_ball_on X\<omega> top1_D_metric_real_omega x r \<subseteq> b"
        proof (rule subsetI)
          fix z
          assume hz: "z \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x r"
          have hzX: "z \<in> X\<omega>" and hDxz: "top1_D_metric_real_omega x z < r"
            using hz unfolding top1_ball_on_def by blast+

          have hzU: "\<forall>i\<in>(UNIV::nat set). z i \<in> U i"
          proof (intro ballI)
            fix i :: nat
            show "z i \<in> U i"
            proof (cases "i \<in> ?F")
            case True
            have hr_le: "r \<le> eps i / real (Suc i)"
            proof -
              have hF_ne: "?F \<noteq> {}"
                using True by blast
              have hr: "r = Min ((\<lambda>i. eps i / real (Suc i)) ` ?F)"
                unfolding r_def using hF_ne by (rule if_not_P)
              have hImg_fin: "finite ((\<lambda>i. eps i / real (Suc i)) ` ?F)"
                using hFfin by blast
              have hMin_le: "Min ((\<lambda>i. eps i / real (Suc i)) ` ?F) \<le> eps i / real (Suc i)"
                using Min_le[OF hImg_fin] True by blast
              show ?thesis
                using hr hMin_le by simp
            qed

              have hterm_le: "top1_real_bounded_metric (x i) (z i) / real (Suc i) \<le> top1_D_metric_real_omega x z"
                by (rule top1_D_metric_real_omega_term_le)
              have hterm_lt: "top1_real_bounded_metric (x i) (z i) / real (Suc i) < r"
                using hDxz hterm_le by linarith
              have hmult: "top1_real_bounded_metric (x i) (z i) < r * real (Suc i)"
                using hterm_lt by (simp add: field_simps)
              have hbound: "r * real (Suc i) \<le> eps i"
                using hr_le by (simp add: field_simps)
              have hcoord: "top1_real_bounded_metric (x i) (z i) < eps i"
                using hmult hbound by linarith
              have hpos: "0 < eps i"
                using heps True by simp
              have hz_in_ball: "z i \<in> top1_ball_on UNIV top1_real_bounded_metric (x i) (eps i)"
                unfolding top1_ball_on_def using hcoord by simp
              have hsube: "top1_ball_on UNIV top1_real_bounded_metric (x i) (eps i) \<subseteq> U i"
                using heps True by simp
              show ?thesis
                using hsube hz_in_ball by blast
            next
              case False
              have hUi: "U i = XR i"
                using False by auto
              show ?thesis
                unfolding hUi XR_def by simp
            qed
          qed

          show "z \<in> b"
            unfolding hb_eq top1_PiE_iff using hzU by simp
        qed

        have hx_in_ball: "x \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x r"
          unfolding top1_ball_on_def using hxX top1_D_metric_real_omega_refl hr_pos by simp
        have hball_basis: "top1_ball_on X\<omega> top1_D_metric_real_omega x r \<in> top1_metric_basis_on X\<omega> top1_D_metric_real_omega"
          unfolding top1_metric_basis_on_def using hxX hr_pos by blast

        show "\<exists>ba\<in>top1_metric_basis_on X\<omega> top1_D_metric_real_omega. x \<in> ba \<and> ba \<subseteq> b"
          apply (rule bexI[where x="top1_ball_on X\<omega> top1_D_metric_real_omega x r"])
           apply (intro conjI)
            apply (rule hx_in_ball)
           apply (rule hball_sub)
          apply (rule hball_basis)
          done
      qed
    qed

    show "b \<in> ?Tm"
      using hb_open by simp
  qed

  have hInc:
    "topology_generated_by_basis X\<omega> (top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR)) \<subseteq> ?Tm"
    by (rule topology_generated_by_basis_subset[OF hTopMet hBasisSub])
  have hInc': "topology_generated_by_basis (top1_PiE (UNIV::nat set) XR)
      (top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR))
      \<subseteq> top1_metric_topology_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega"
    using hInc unfolding X\<omega>_def by simp
  show ?thesis
    unfolding Tprod_def top1_product_topology_on_def X\<omega>_def using hInc' by simp
qed

(** from \S20 Theorem 20.5 [top1.tex:1776] **)
theorem Theorem_20_5:
  defines "XR \<equiv> (\<lambda>_. (UNIV::real set))"
  defines "TR \<equiv> (order_topology_on_UNIV::real set set)"
  defines "X\<omega> \<equiv> top1_PiE (UNIV::nat set) XR"
  defines "Tprod \<equiv> top1_product_topology_on (UNIV::nat set) XR (\<lambda>_. TR)"
  shows "top1_metric_on X\<omega> top1_D_metric_real_omega
    \<and> top1_metric_topology_on X\<omega> top1_D_metric_real_omega = Tprod"
text \<open>
  Proof status: admitted for now.

  Intended proof plan: show \<open>top1_D_metric_real_omega\<close> is a metric (weighted sup of bounded coordinate metrics),
  then prove equality of topologies by comparing bases: a ball in the D-metric gives finitely many coordinate
  constraints, hence is product-open; conversely, a basic product neighborhood around a point contains a suitable
  D-metric ball by choosing a small enough radius governed by finitely many coordinates.
\<close>
proof -
  have hmetric: "top1_metric_on X\<omega> top1_D_metric_real_omega"
  proof (unfold top1_metric_on_def, intro conjI)
    show "\<forall>x\<in>X\<omega>. 0 \<le> top1_D_metric_real_omega x x"
      by (intro ballI) (rule top1_D_metric_real_omega_nonneg)
    show "\<forall>x\<in>X\<omega>. \<forall>y\<in>X\<omega>. 0 \<le> top1_D_metric_real_omega x y"
      by (intro ballI) (rule top1_D_metric_real_omega_nonneg)
    show "\<forall>x\<in>X\<omega>. \<forall>y\<in>X\<omega>. top1_D_metric_real_omega x y = 0 \<longleftrightarrow> x = y"
      by (intro ballI) (rule top1_D_metric_real_omega_0_iff)
    show "\<forall>x\<in>X\<omega>. \<forall>y\<in>X\<omega>. top1_D_metric_real_omega x y = top1_D_metric_real_omega y x"
      by (intro ballI) (simp add: top1_D_metric_real_omega_sym)
    show "\<forall>x\<in>X\<omega>. \<forall>y\<in>X\<omega>. \<forall>z\<in>X\<omega>.
        top1_D_metric_real_omega x z \<le> top1_D_metric_real_omega x y + top1_D_metric_real_omega y z"
      by (intro ballI) (rule top1_D_metric_real_omega_triangle)
  qed
  show ?thesis
  proof (intro conjI)
    show "top1_metric_on X\<omega> top1_D_metric_real_omega"
      by (rule hmetric)
    show "top1_metric_topology_on X\<omega> top1_D_metric_real_omega = Tprod"
    proof -
      have hSub: "top1_metric_topology_on X\<omega> top1_D_metric_real_omega \<subseteq> Tprod"
      proof -
        have hTopTR: "is_topology_on (UNIV::real set) TR"
          unfolding TR_def by (rule order_topology_on_UNIV_is_topology_on)
        have hAll: "\<forall>i\<in>(UNIV::nat set). is_topology_on (XR i) TR"
          unfolding XR_def using hTopTR by simp
        have hTopProd: "is_topology_on X\<omega> Tprod"
          unfolding Tprod_def X\<omega>_def by (rule top1_product_topology_on_is_topology_on[OF hAll])

        have hBasisSub:
          "top1_metric_basis_on X\<omega> top1_D_metric_real_omega \<subseteq> Tprod"
        proof (rule subsetI)
          fix b
          assume hb: "b \<in> top1_metric_basis_on X\<omega> top1_D_metric_real_omega"
          obtain x e where hx: "x \<in> X\<omega>" and he: "0 < e"
              and hb_eq: "b = top1_ball_on X\<omega> top1_D_metric_real_omega x e"
            using hb unfolding top1_metric_basis_on_def by blast
          have hx': "x \<in> top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set))"
            using hx unfolding X\<omega>_def XR_def by simp
          have hball_raw:
            "top1_ball_on (top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set)))
                top1_D_metric_real_omega x e
              \<in> top1_product_topology_on (UNIV::nat set) (\<lambda>_. (UNIV::real set))
                   (\<lambda>_. (order_topology_on_UNIV::real set set))"
            using top1_D_metric_real_omega_ball_in_product_topology[OF hx' he] .
          have "top1_ball_on X\<omega> top1_D_metric_real_omega x e \<in> Tprod"
            using hball_raw unfolding X\<omega>_def XR_def Tprod_def TR_def by simp
          thus "b \<in> Tprod"
            unfolding hb_eq by simp
        qed

        have hTopMet: "is_topology_on X\<omega> (top1_metric_topology_on X\<omega> top1_D_metric_real_omega)"
          by (rule top1_metric_topology_on_is_topology_on[OF hmetric])
        have hGenSub:
          "topology_generated_by_basis X\<omega> (top1_metric_basis_on X\<omega> top1_D_metric_real_omega) \<subseteq> Tprod"
          by (rule topology_generated_by_basis_subset[OF hTopProd hBasisSub])
        show ?thesis
          unfolding top1_metric_topology_on_def using hGenSub by simp
      qed
      show ?thesis
      proof (rule antisym)
        show "top1_metric_topology_on X\<omega> top1_D_metric_real_omega \<subseteq> Tprod"
          by (rule hSub)
        show "Tprod \<subseteq> top1_metric_topology_on X\<omega> top1_D_metric_real_omega"
        proof -
          have hraw:
            "top1_product_topology_on (UNIV::nat set) (\<lambda>_. (UNIV::real set))
               (\<lambda>_. (order_topology_on_UNIV::real set set))
             \<subseteq> top1_metric_topology_on (top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set)))
                  top1_D_metric_real_omega"
          proof -
            have "top1_metric_on (top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set))) top1_D_metric_real_omega"
              using hmetric unfolding X\<omega>_def XR_def by simp
            thus ?thesis
              using top1_product_topology_subset_D_metric_topology_real_omega
              unfolding XR_def TR_def X\<omega>_def Tprod_def by simp
          qed
          show ?thesis
            using hraw unfolding XR_def TR_def X\<omega>_def Tprod_def by simp
        qed
      qed
    qed
(*
    proof (rule subset_antisym)
      let ?Tm = "top1_metric_topology_on X\<omega> top1_D_metric_real_omega"

      have hTopTR: "is_topology_on (UNIV::real set) TR"
        unfolding TR_def by (rule order_topology_on_UNIV_is_topology_on)
      have hTopProd: "is_topology_on X\<omega> Tprod"
      proof -
        have hAll: "\<forall>i\<in>(UNIV::nat set). is_topology_on (XR i) TR"
          unfolding XR_def using hTopTR by simp
        show ?thesis
          unfolding Tprod_def X\<omega>_def
          by (rule top1_product_topology_on_is_topology_on[OF hAll])
      qed
      have hTopMet: "is_topology_on X\<omega> ?Tm"
        by (rule top1_metric_topology_on_is_topology_on[OF hmetric])

      show "?Tm \<subseteq> Tprod"
      proof -
        have hBasisSub: "top1_metric_basis_on X\<omega> top1_D_metric_real_omega \<subseteq> Tprod"
        proof (rule subsetI)
          fix b
          assume hb: "b \<in> top1_metric_basis_on X\<omega> top1_D_metric_real_omega"
          obtain x e where hxX: "x \<in> X\<omega>" and he: "0 < e"
              and hb_eq: "b = top1_ball_on X\<omega> top1_D_metric_real_omega x e"
            using hb unfolding top1_metric_basis_on_def by blast

          have hball_in: "top1_ball_on X\<omega> top1_D_metric_real_omega x e \<in> Tprod"
            unfolding Tprod_def X\<omega>_def top1_product_topology_on_def topology_generated_by_basis_def
          proof (rule CollectI, intro conjI)
            show "top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e \<subseteq>
                  top1_PiE (UNIV::nat set) XR"
            proof (rule subsetI)
              fix y
              assume hy: "y \<in> top1_ball_on (top1_PiE (UNIV::nat set) XR) top1_D_metric_real_omega x e"
              thus "y \<in> top1_PiE (UNIV::nat set) XR"
                unfolding top1_ball_on_def by simp
            qed

            show "\<forall>y\<in>top1_ball_on X\<omega> top1_D_metric_real_omega x e.
                    \<exists>ba\<in>top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR).
                      y \<in> ba \<and> ba \<subseteq> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
            proof (intro ballI)
              fix y
              assume hy: "y \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
              have hyX: "y \<in> X\<omega>" and hDxy: "top1_D_metric_real_omega x y < e"
                using hy unfolding top1_ball_on_def by blast+

              define \<delta> where "\<delta> = (e - top1_D_metric_real_omega x y) / 2"
              have hdel_pos: "0 < \<delta>"
                using hDxy he unfolding \<delta>_def by simp

              obtain N :: nat where hN: "1 / real (Suc N) < \<delta>"
              proof -
                obtain N :: nat where hN': "inverse (of_nat (Suc N)) < \<delta>"
                  using reals_Archimedean[OF hdel_pos] by blast
                have "1 / real (Suc N) < \<delta>"
                  using hN' by (simp add: field_simps)
                thus ?thesis
                  by (rule that)
              qed

              define U where
                "U = (\<lambda>n.
                    if n < Suc N then top1_ball_on UNIV top1_real_bounded_metric (y n) (\<delta> * real (Suc n))
                    else (UNIV::real set))"
              define ba where "ba = top1_PiE (UNIV::nat set) U"

              have hba_basis: "ba \<in> top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR)"
              proof -
                have hU_in: "\<forall>i\<in>(UNIV::nat set). U i \<in> TR \<and> U i \<subseteq> XR i"
                proof (intro ballI)
                  fix i :: nat
                  show "U i \<in> TR \<and> U i \<subseteq> XR i"
                  proof (cases "i < Suc N")
                    case True
                    have hpos: "0 < \<delta> * real (Suc i)"
                      using hdel_pos by simp
                    have hUiTR: "top1_ball_on UNIV top1_real_bounded_metric (y i) (\<delta> * real (Suc i)) \<in> TR"
                      unfolding TR_def by (rule top1_real_bounded_metric_ball_in_order_topology[OF hpos])
                    show ?thesis
                      unfolding U_def XR_def using True hUiTR by simp
                  next
                    case False
                    have hUNIV: "UNIV \<in> TR"
                      using hTopTR unfolding is_topology_on_def by blast
                    show ?thesis
                      unfolding U_def XR_def using False hUNIV by simp
                  qed
                qed

                have hfin: "finite {i \<in> (UNIV::nat set). U i \<noteq> XR i}"
                proof -
                  have hsub: "{i \<in> (UNIV::nat set). U i \<noteq> XR i} \<subseteq> {i. i < Suc N}"
                    unfolding XR_def U_def by auto
                  have hfin': "finite {i. i < Suc N}"
                    by simp
                  show ?thesis
                    by (rule finite_subset[OF hsub hfin'])
                qed

                have "ba = top1_PiE (UNIV::nat set) U"
                  unfolding ba_def by simp
                thus ?thesis
                  unfolding top1_product_basis_on_def
                  apply (rule CollectI)
                  apply (rule exI[where x=U])
                  using hU_in hfin by simp
              qed

              have hy_in_ba: "y \<in> ba"
              proof -
                have hyU: "\<forall>i\<in>(UNIV::nat set). y i \<in> U i"
                proof (intro ballI)
                  fix i :: nat
                  show "y i \<in> U i"
                  proof (cases "i < Suc N")
                    case True
                    have hpos: "0 < \<delta> * real (Suc i)"
                      using hdel_pos by simp
                    have "top1_real_bounded_metric (y i) (y i) = 0"
                      unfolding top1_real_bounded_metric_def by simp
                    then have "y i \<in> top1_ball_on UNIV top1_real_bounded_metric (y i) (\<delta> * real (Suc i))"
                      unfolding top1_ball_on_def using hpos by simp
                    thus ?thesis
                      unfolding U_def using True by simp
                  next
                    case False
                    show ?thesis
                      unfolding U_def using False by simp
                  qed
                qed
                show ?thesis
                  unfolding ba_def top1_PiE_iff
                  using hyU by simp
              qed

              have hba_sub_ball: "ba \<subseteq> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
              proof (rule subsetI)
                fix z
                assume hz: "z \<in> ba"

                have hzU: "\<forall>i\<in>(UNIV::nat set). z i \<in> U i"
                  using hz unfolding ba_def top1_PiE_iff by simp

                have hDyz_le: "top1_D_metric_real_omega y z \<le> \<delta>"
                proof -
                  let ?S = "((\<lambda>k. top1_real_bounded_metric (y k) (z k) / real (Suc k)) ` (UNIV::nat set))"
                  have hbdd: "bdd_above ?S"
                    by (rule top1_D_metric_real_omega_bdd_above)
                  have hSne: "?S \<noteq> {}"
                    by simp
                  have hall: "\<forall>r\<in>?S. r \<le> \<delta>"
                  proof (intro ballI)
                    fix r
                    assume hr: "r \<in> ?S"
                    then obtain n where hn: "r = top1_real_bounded_metric (y n) (z n) / real (Suc n)"
                      by blast
                    show "r \<le> \<delta>"
                    proof (cases "n < Suc N")
                      case True
                      have hz_in: "z n \<in> top1_ball_on UNIV top1_real_bounded_metric (y n) (\<delta> * real (Suc n))"
                        using hzU unfolding U_def using True by simp
                      have hpos: "0 < (real (Suc n) :: real)"
                        by simp
                      have hdist: "top1_real_bounded_metric (y n) (z n) < \<delta> * real (Suc n)"
                        using hz_in unfolding top1_ball_on_def by blast
                      have "top1_real_bounded_metric (y n) (z n) / real (Suc n) < \<delta>"
                        using hdist hpos by (simp add: divide_lt_eq)
                      thus ?thesis
                        unfolding hn by simp
                    next
                      case False
                      have hle1: "top1_real_bounded_metric (y n) (z n) \<le> (1::real)"
                        unfolding top1_real_bounded_metric_def by simp
                      have hpos: "0 < (real (Suc n) :: real)"
                        by simp
                      have hterm_le: "top1_real_bounded_metric (y n) (z n) / real (Suc n) \<le> 1 / real (Suc n)"
                        using hle1 hpos by (simp add: divide_right_mono)
                      have hSuc_le: "real (Suc N) \<le> (real (Suc n) :: real)"
                        using False by simp
                      have hposN: "0 < (real (Suc N) :: real)"
                        by simp
                      have hinv: "1 / real (Suc n) \<le> 1 / real (Suc N)"
                        using inv_le_inv_of_le[OF hposN hSuc_le] by (simp add: field_simps)
                      have htail: "top1_real_bounded_metric (y n) (z n) / real (Suc n) \<le> 1 / real (Suc N)"
                        by (rule le_trans[OF hterm_le le_trans[OF hinv le_rfl]])
                      have hlt: "1 / real (Suc N) < \<delta>"
                        using hN by simp
                      have "top1_real_bounded_metric (y n) (z n) / real (Suc n) < \<delta>"
                        by (rule le_less_trans[OF htail hlt])
                      thus ?thesis
                        unfolding hn by simp
                    qed
                  qed
                  have hSup: "Sup ?S \<le> \<delta>"
                    by (rule cSup_least[OF hSne hbdd]) (rule hall)
                  show ?thesis
                    unfolding top1_D_metric_real_omega_def using hSup by simp
                qed

                have hDxz_le: "top1_D_metric_real_omega x z \<le> top1_D_metric_real_omega x y + top1_D_metric_real_omega y z"
                  by (rule top1_D_metric_real_omega_triangle)
                have hDxz_lt: "top1_D_metric_real_omega x z < e"
                proof -
                  have hmid: "top1_D_metric_real_omega x y + \<delta> = (e + top1_D_metric_real_omega x y) / 2"
                    unfolding \<delta>_def by (simp add: field_simps algebra_simps)
                  have hlt: "(e + top1_D_metric_real_omega x y) / 2 < e"
                    using hDxy by simp
                  have "top1_D_metric_real_omega x z \<le> top1_D_metric_real_omega x y + \<delta>"
                    by (rule le_trans[OF hDxz_le add_left_mono[OF hDyz_le]])
                  then have "top1_D_metric_real_omega x z \<le> (e + top1_D_metric_real_omega x y) / 2"
                    using hmid by simp
                  then show ?thesis
                    by (rule le_less_trans[OF _ hlt])
                qed
                show "z \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
                  unfolding top1_ball_on_def using hDxz_lt by blast
              qed

              show "\<exists>ba\<in>top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR).
                      y \<in> ba \<and> ba \<subseteq> top1_ball_on X\<omega> top1_D_metric_real_omega x e"
                apply (rule bexI[where x=ba])
                 apply (intro conjI)
                  apply (rule hy_in_ba)
                 apply (rule hba_sub_ball)
                apply (rule hba_basis)
                done
            qed
          qed

          show "b \<in> Tprod"
            unfolding hb_eq using hball_in by simp
        qed

        have hInc: "topology_generated_by_basis X\<omega> (top1_metric_basis_on X\<omega> top1_D_metric_real_omega) \<subseteq> Tprod"
          by (rule topology_generated_by_basis_subset[OF hTopProd hBasisSub])
        show ?thesis
          unfolding top1_metric_topology_on_def using hInc by simp
      qed

      show "Tprod \<subseteq> ?Tm"
      proof -
        have hBasisSub: "top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR) \<subseteq> ?Tm"
        proof (rule subsetI)
          fix b
          assume hb: "b \<in> top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR)"
          obtain U where hUall: "\<forall>i\<in>(UNIV::nat set). U i \<in> TR \<and> U i \<subseteq> XR i"
              and hfin: "finite {i \<in> (UNIV::nat set). U i \<noteq> XR i}"
              and hb_eq: "b = top1_PiE (UNIV::nat set) U"
            using hb unfolding top1_product_basis_on_def by blast

          have hb_sub: "b \<subseteq> X\<omega>"
            unfolding hb_eq X\<omega>_def XR_def
            by (rule top1_PiE_mono) simp

          have hopen: "b \<in> ?Tm"
            unfolding top1_metric_topology_on_def topology_generated_by_basis_def
          proof (rule CollectI, intro conjI)
            show "b \<subseteq> X\<omega>"
              by (rule hb_sub)
            show "\<forall>x\<in>b. \<exists>ba\<in>top1_metric_basis_on X\<omega> top1_D_metric_real_omega. x \<in> ba \<and> ba \<subseteq> b"
            proof (intro ballI)
              fix x
              assume hx: "x \<in> b"

              define F where "F = {i \<in> (UNIV::nat set). U i \<noteq> XR i}"
              have hFfin: "finite F"
                unfolding F_def using hfin by simp

              show "\<exists>ba\<in>top1_metric_basis_on X\<omega> top1_D_metric_real_omega. x \<in> ba \<and> ba \<subseteq> b"
              proof (cases "F = {}")
                case True
                have hb_all: "b = X\<omega>"
                proof (rule set_eqI)
                  fix z
                  show "z \<in> b \<longleftrightarrow> z \<in> X\<omega>"
                  proof
                    assume "z \<in> b"
                    then show "z \<in> X\<omega>"
                      using hb_sub by blast
                  next
                    assume hzX: "z \<in> X\<omega>"
                    have hzU: "\<forall>i\<in>(UNIV::nat set). z i \<in> U i"
                    proof (intro ballI)
                      fix i :: nat
                      have hUi: "U i = XR i"
                        using True unfolding F_def by auto
                      show "z i \<in> U i"
                        unfolding hUi XR_def by simp
                    qed
                    show "z \<in> b"
                      unfolding hb_eq top1_PiE_iff using hzU by simp
                  qed
                qed
                have hxX: "x \<in> X\<omega>"
                  using hx hb_sub by blast
                have hxball: "x \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x 1"
                  unfolding top1_ball_on_def using hxX top1_D_metric_real_omega_refl by simp
                have hball_basis: "top1_ball_on X\<omega> top1_D_metric_real_omega x 1 \<in> top1_metric_basis_on X\<omega> top1_D_metric_real_omega"
                  unfolding top1_metric_basis_on_def using hxX by simp
                have hsub: "top1_ball_on X\<omega> top1_D_metric_real_omega x 1 \<subseteq> b"
                  unfolding hb_all by simp
                show ?thesis
                  apply (rule bexI[where x="top1_ball_on X\<omega> top1_D_metric_real_omega x 1"])
                   apply (intro conjI)
                    apply (rule hxball)
                   apply (rule hsub)
                  apply (rule hball_basis)
                  done
              next
                case False
                have hxX: "x \<in> X\<omega>"
                  using hx hb_sub by blast

                have hex: "\<forall>i\<in>F. \<exists>e. 0 < e \<and> top1_ball_on UNIV top1_real_bounded_metric (x i) e \<subseteq> U i"
                proof (intro ballI)
                  fix i :: nat
                  assume hi: "i \<in> F"
                  have hUiTR: "U i \<in> TR"
                    using hUall hi by blast
                  have hUiMet: "U i \<in> top1_metric_topology_on (UNIV::real set) top1_real_bounded_metric"
                    using hUiTR unfolding order_topology_on_UNIV_eq_bounded_metric_topology_real[unfolded TR_def] by simp
                  have hxi: "x i \<in> U i"
                    using hx unfolding hb_eq top1_PiE_iff using hi by simp
                  obtain e where hepos: "0 < e" and hsube: "top1_ball_on UNIV top1_real_bounded_metric (x i) e \<subseteq> U i"
                    using top1_metric_open_contains_ball[OF top1_real_bounded_metric_metric_on hUiMet hxi] by blast
                  show "\<exists>e. 0 < e \<and> top1_ball_on UNIV top1_real_bounded_metric (x i) e \<subseteq> U i"
                    by (rule exI[where x=e], intro conjI[OF hepos hsube])
                qed

                obtain eps where heps: "\<forall>i\<in>F. 0 < eps i \<and> top1_ball_on UNIV top1_real_bounded_metric (x i) (eps i) \<subseteq> U i"
                  using bchoice[OF hex] by blast

                define r where "r = Min ((\<lambda>i. eps i / real (Suc i)) ` F)"

                have hr_pos: "0 < r"
                proof -
                  have hpos_all: "\<forall>t\<in>((\<lambda>i. eps i / real (Suc i)) ` F). 0 < t"
                  proof (intro ballI)
                    fix t
                    assume ht: "t \<in> ((\<lambda>i. eps i / real (Suc i)) ` F)"
                    then obtain i where hiF: "i \<in> F" and ht_eq: "t = eps i / real (Suc i)"
                      by blast
                    have hepos: "0 < eps i"
                      using heps hiF by blast
                    show "0 < t"
                      unfolding ht_eq using hepos by simp
                  qed
                  have hMin_in: "r \<in> ((\<lambda>i. eps i / real (Suc i)) ` F)"
                    unfolding r_def
                    by (rule Min_in) (use hFfin False in auto)
                  show ?thesis
                    using hpos_all hMin_in by blast
                qed

                have hball_sub: "top1_ball_on X\<omega> top1_D_metric_real_omega x r \<subseteq> b"
                proof (rule subsetI)
                  fix z
                  assume hz: "z \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x r"
                  have hzX: "z \<in> X\<omega>" and hDxz: "top1_D_metric_real_omega x z < r"
                    using hz unfolding top1_ball_on_def by blast+
                  have hzU: "\<forall>i\<in>(UNIV::nat set). z i \<in> U i"
                  proof (intro ballI)
                    fix i :: nat
                    show "z i \<in> U i"
                    proof (cases "i \<in> F")
                      case True
                      have hterm_le: "top1_real_bounded_metric (x i) (z i) / real (Suc i) \<le> top1_D_metric_real_omega x z"
                        by (rule top1_D_metric_real_omega_term_le)
                      have hterm_lt: "top1_real_bounded_metric (x i) (z i) / real (Suc i) < r"
                        by (rule le_less_trans[OF hterm_le hDxz])
                      have hr_le: "r \<le> eps i / real (Suc i)"
                      proof -
                        have hmem: "eps i / real (Suc i) \<in> ((\<lambda>j. eps j / real (Suc j)) ` F)"
                          using True by blast
                        show ?thesis
                          unfolding r_def by (rule Min_le[OF hFfin hmem])
                      qed
                      have hterm_lt2: "top1_real_bounded_metric (x i) (z i) / real (Suc i) < eps i / real (Suc i)"
                        using hterm_lt hr_le by linarith
                      have hpos: "0 < (real (Suc i) :: real)"
                        by simp
                      have hcoord: "top1_real_bounded_metric (x i) (z i) < eps i"
                        using hterm_lt2 hpos by (simp add: divide_lt_eq)
                      have hz_in_ball: "z i \<in> top1_ball_on UNIV top1_real_bounded_metric (x i) (eps i)"
                        unfolding top1_ball_on_def using hcoord by simp
                      have hsube: "top1_ball_on UNIV top1_real_bounded_metric (x i) (eps i) \<subseteq> U i"
                        using heps True by blast
                      show ?thesis
                        using hsube hz_in_ball by blast
                    next
                      case False
                      have hUi: "U i = XR i"
                        using False unfolding F_def by auto
                      show ?thesis
                        unfolding hUi XR_def by simp
                    qed
                  qed
                  show "z \<in> b"
                    unfolding hb_eq top1_PiE_iff using hzU by simp
                qed

                have hx_in_ball: "x \<in> top1_ball_on X\<omega> top1_D_metric_real_omega x r"
                  unfolding top1_ball_on_def using hxX top1_D_metric_real_omega_refl hr_pos by simp
                have hball_basis: "top1_ball_on X\<omega> top1_D_metric_real_omega x r \<in> top1_metric_basis_on X\<omega> top1_D_metric_real_omega"
                  unfolding top1_metric_basis_on_def using hxX hr_pos by blast

                show ?thesis
                  apply (rule bexI[where x="top1_ball_on X\<omega> top1_D_metric_real_omega x r"])
                   apply (intro conjI)
                    apply (rule hx_in_ball)
                   apply (rule hball_sub)
                  apply (rule hball_basis)
                  done
              qed
            qed
          qed

          show "b \<in> ?Tm"
            using hopen by simp
        qed

        have hInc: "topology_generated_by_basis X\<omega> (top1_product_basis_on (UNIV::nat set) XR (\<lambda>_. TR)) \<subseteq> ?Tm"
          by (rule topology_generated_by_basis_subset[OF hTopMet hBasisSub])
        show ?thesis
          unfolding Tprod_def X\<omega>_def top1_product_topology_on_def using hInc by simp
      qed
    qed
*)
  qed
qed

section \<open>\<S>21 The Metric Topology (continued)\<close>

text \<open>
  Section \<S>21 of \<open>top1.tex\<close> develops the familiar \<open>\<epsilon>\<close>–\<open>\<delta>\<close> definition of continuity
  and the relation between continuity and sequences in metrizable spaces.
\<close>

(** from \S21 Theorem 21.1 (\<epsilon>–\<delta> continuity) [top1.tex:1984] **)
theorem Theorem_21_1:
  assumes hdX: "top1_metric_on X dX"
  assumes hdY: "top1_metric_on Y dY"
  shows "top1_continuous_map_on X (top1_metric_topology_on X dX) Y (top1_metric_topology_on Y dY) f
    \<longleftrightarrow>
      ((\<forall>x\<in>X. f x \<in> Y) \<and>
       (\<forall>x\<in>X. \<forall>\<epsilon>::real. \<epsilon> > 0 \<longrightarrow>
          (\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>))))"
proof (rule iffI)
  assume hcont: "top1_continuous_map_on X (top1_metric_topology_on X dX) Y (top1_metric_topology_on Y dY) f"
  have hmap: "\<forall>x\<in>X. f x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hpre: "\<forall>V\<in>(top1_metric_topology_on Y dY). {x\<in>X. f x \<in> V} \<in> top1_metric_topology_on X dX"
    using hcont unfolding top1_continuous_map_on_def by blast
  show "(\<forall>x\<in>X. f x \<in> Y) \<and>
       (\<forall>x\<in>X. \<forall>\<epsilon>::real. \<epsilon> > 0 \<longrightarrow>
          (\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>)))"
  proof (intro conjI)
    show "\<forall>x\<in>X. f x \<in> Y"
      by (rule hmap)
    show "\<forall>x\<in>X. \<forall>\<epsilon>::real. \<epsilon> > 0 \<longrightarrow>
          (\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>))"
    proof (intro ballI allI impI)
      fix x
      fix \<epsilon> :: real
      assume hxX: "x \<in> X"
      assume heps: "\<epsilon> > 0"
      have hfxY: "f x \<in> Y" using hmap hxX by blast
      have hopen_ball: "top1_ball_on Y dY (f x) \<epsilon> \<in> top1_metric_topology_on Y dY"
        by (rule top1_ball_open_in_metric_topology[OF hdY hfxY heps])
      have hpre_open: "{u\<in>X. f u \<in> top1_ball_on Y dY (f x) \<epsilon>} \<in> top1_metric_topology_on X dX"
        using hpre hopen_ball by blast
      have hxpre: "x \<in> {u\<in>X. f u \<in> top1_ball_on Y dY (f x) \<epsilon>}"
      proof -
        have hdx0: "dY (f x) (f x) = 0"
          using hdY hfxY unfolding top1_metric_on_def by blast
        show ?thesis
          unfolding top1_ball_on_def using hxX hfxY heps hdx0 by simp
      qed
      obtain \<delta> where hdel: "\<delta> > 0"
          and hball_sub: "top1_ball_on X dX x \<delta> \<subseteq> {u\<in>X. f u \<in> top1_ball_on Y dY (f x) \<epsilon>}"
        using top1_metric_open_contains_ball[OF hdX hpre_open hxpre] by blast
      show "\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>)"
      proof (rule exI[where x=\<delta>], intro conjI)
        show "\<delta> > 0" by (rule hdel)
        show "\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>"
        proof (intro ballI impI)
          fix y assume hyX: "y \<in> X" and hdist: "dX x y < \<delta>"
          have hyball: "y \<in> top1_ball_on X dX x \<delta>"
            unfolding top1_ball_on_def using hyX hdist by blast
          have hypre: "y \<in> {u\<in>X. f u \<in> top1_ball_on Y dY (f x) \<epsilon>}"
            using hball_sub hyball by blast
          have "f y \<in> top1_ball_on Y dY (f x) \<epsilon>"
            using hypre by simp
          thus "dY (f x) (f y) < \<epsilon>"
            unfolding top1_ball_on_def using hmap hxX hyX by blast
        qed
      qed
    qed
  qed
next
  assume h: "(\<forall>x\<in>X. f x \<in> Y) \<and>
       (\<forall>x\<in>X. \<forall>\<epsilon>::real. \<epsilon> > 0 \<longrightarrow>
          (\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>)))"
  have hmap: "\<forall>x\<in>X. f x \<in> Y"
    using h by blast
  have hepsdel:
    "\<forall>x\<in>X. \<forall>\<epsilon>::real. \<epsilon> > 0 \<longrightarrow>
        (\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>))"
    using h by blast

  have hTopX: "is_topology_on X (top1_metric_topology_on X dX)"
    by (rule top1_metric_topology_on_is_topology_on[OF hdX])

  have hBasisY:
    "basis_for Y (top1_metric_basis_on Y dY) (top1_metric_topology_on Y dY)"
    unfolding basis_for_def top1_metric_topology_on_def
    by (intro conjI, rule top1_metric_basis_is_basis_on[OF hdY], rule refl)

  have hpre_basis:
    "\<forall>b\<in>top1_metric_basis_on Y dY. {x\<in>X. f x \<in> b} \<in> top1_metric_topology_on X dX"
  proof (intro ballI)
    fix b assume hb: "b \<in> top1_metric_basis_on Y dY"
    obtain y0 \<epsilon> where hbdef: "b = top1_ball_on Y dY y0 \<epsilon>" and hy0: "y0 \<in> Y" and heps: "\<epsilon> > 0"
      using hb unfolding top1_metric_basis_on_def by blast

    let ?P = "{x\<in>X. f x \<in> b}"

    have hPX: "?P \<subseteq> X" by blast
    have hprop: "\<forall>x\<in>?P. \<exists>c\<in>top1_metric_basis_on X dX. x \<in> c \<and> c \<subseteq> ?P"
	    proof (intro ballI)
	      fix x assume hxP: "x \<in> ?P"
	      have hxX: "x \<in> X" and hfxb: "f x \<in> b"
	      proof -
	        have hx_conj: "x \<in> X \<and> f x \<in> b"
	          using hxP by simp
	        show "x \<in> X"
	          using hx_conj by (rule conjunct1)
	        show "f x \<in> b"
	          using hx_conj by (rule conjunct2)
	      qed
	      have hfxY: "f x \<in> Y"
	        using hmap hxX by blast
	      have hdist0: "dY y0 (f x) < \<epsilon>"
	        using hfxb unfolding hbdef top1_ball_on_def using hfxY by blast

      define \<epsilon>' where "\<epsilon>' = \<epsilon> - dY y0 (f x)"
      have heps': "\<epsilon>' > 0"
        unfolding \<epsilon>'_def using hdist0 by simp
      obtain \<delta> where hdel: "\<delta> > 0"
          and hdel_prop: "\<forall>y\<in>X. dX x y < \<delta> \<longrightarrow> dY (f x) (f y) < \<epsilon>'"
        using hepsdel hxX heps' by blast

      have hball_sub: "top1_ball_on X dX x \<delta> \<subseteq> ?P"
      proof (rule subsetI)
        fix y assume hy: "y \<in> top1_ball_on X dX x \<delta>"
        have hyX: "y \<in> X" and hdist: "dX x y < \<delta>"
          using hy unfolding top1_ball_on_def by blast+
        have hfyY: "f y \<in> Y"
          using hmap hyX by blast
        have hsmall: "dY (f x) (f y) < \<epsilon>'"
          using hdel_prop hyX hdist by blast
        have htri: "dY y0 (f y) \<le> dY y0 (f x) + dY (f x) (f y)"
          using hdY hy0 hfxY hfyY unfolding top1_metric_on_def by blast
        have "dY y0 (f y) < dY y0 (f x) + \<epsilon>'"
          using htri hsmall by simp
        also have "... = \<epsilon>"
          unfolding \<epsilon>'_def by simp
        finally have "dY y0 (f y) < \<epsilon>" .
        have "f y \<in> top1_ball_on Y dY y0 \<epsilon>"
          unfolding top1_ball_on_def using hfyY \<open>dY y0 (f y) < \<epsilon>\<close> by blast
        hence "f y \<in> b"
          unfolding hbdef by simp
        show "y \<in> ?P"
          using hyX \<open>f y \<in> b\<close> by simp
      qed

      have hxball: "x \<in> top1_ball_on X dX x \<delta>"
      proof -
        have "dX x x = 0"
          using hdX hxX unfolding top1_metric_on_def by blast
        thus ?thesis
          unfolding top1_ball_on_def using hxX hdel by simp
      qed

      have hball_basis: "top1_ball_on X dX x \<delta> \<in> top1_metric_basis_on X dX"
        unfolding top1_metric_basis_on_def using hxX hdel by blast

      show "\<exists>c\<in>top1_metric_basis_on X dX. x \<in> c \<and> c \<subseteq> ?P"
        by (rule bexI[where x="top1_ball_on X dX x \<delta>"], intro conjI, rule hxball, rule hball_sub, rule hball_basis)
    qed

    have "?P \<in> topology_generated_by_basis X (top1_metric_basis_on X dX)"
      unfolding topology_generated_by_basis_def using hPX hprop by blast
    thus "?P \<in> top1_metric_topology_on X dX"
      unfolding top1_metric_topology_on_def by simp
  qed

  show "top1_continuous_map_on X (top1_metric_topology_on X dX) Y (top1_metric_topology_on Y dY) f"
    by (rule top1_continuous_map_on_generated_by_basis[OF hTopX hBasisY hmap hpre_basis])
qed

(** from \S21 Lemma 21.2 (Sequence lemma) [top1.tex:~2000] **)
theorem Lemma_21_2_sequence:
  assumes hTX: "is_topology_on X TX"
  assumes hx: "seq_converges_to_on s x X TX"
  assumes hsA: "\<forall>n. s n \<in> A"
  assumes hAX: "A \<subseteq> X"
  shows "x \<in> closure_on X TX A"
proof -
  have hxX: "x \<in> X"
    using hx unfolding seq_converges_to_on_def by blast
  have hcl: "\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U A"
  proof (intro allI impI)
    fix U assume hU: "neighborhood_of x X TX U"
    obtain N where hN: "\<forall>n\<ge>N. s n \<in> U"
      using hx hU unfolding seq_converges_to_on_def by blast
    have "s N \<in> U"
      using hN by simp
    moreover have "s N \<in> A"
      using hsA by blast
    ultimately show "intersects U A"
      unfolding intersects_def by blast
  qed
  show ?thesis
    by (rule iffD2[OF Theorem_17_5a[OF hTX hxX hAX], OF hcl])
qed

theorem Lemma_21_2_sequence_converse:
  assumes hd: "top1_metric_on X d"
  assumes hxcl: "x \<in> closure_on X (top1_metric_topology_on X d) A"
  assumes hAX: "A \<subseteq> X"
  shows "\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X (top1_metric_topology_on X d)"
proof -
  have hTop: "is_topology_on X (top1_metric_topology_on X d)"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])

  have hxX: "x \<in> X"
    using hxcl closure_on_subset_carrier[OF hTop hAX] by blast

  have hnbhd_inter:
    "\<forall>U. neighborhood_of x X (top1_metric_topology_on X d) U \<longrightarrow> intersects U A"
    by (rule iffD1[OF Theorem_17_5a[OF hTop hxX hAX], OF hxcl])

  have hchoose: "\<forall>n. \<exists>a. a \<in> top1_ball_on X d x (inverse (of_nat (Suc n))) \<inter> A"
  proof (intro allI)
    fix n
    have hpos: "0 < inverse (of_nat (Suc n) :: real)"
      by simp
    have hopen: "top1_ball_on X d x (inverse (of_nat (Suc n))) \<in> top1_metric_topology_on X d"
      by (rule top1_ball_open_in_metric_topology[OF hd hxX hpos])
    have hxball: "x \<in> top1_ball_on X d x (inverse (of_nat (Suc n)))"
    proof -
      have "d x x = 0"
        using hd hxX unfolding top1_metric_on_def by blast
      thus ?thesis
        unfolding top1_ball_on_def using hxX hpos by simp
    qed
    have hnbhd: "neighborhood_of x X (top1_metric_topology_on X d) (top1_ball_on X d x (inverse (of_nat (Suc n))))"
      unfolding neighborhood_of_def using hopen hxball by blast
    have "intersects (top1_ball_on X d x (inverse (of_nat (Suc n)))) A"
      using hnbhd_inter hnbhd by blast
    thus "\<exists>a. a \<in> top1_ball_on X d x (inverse (of_nat (Suc n))) \<inter> A"
      unfolding intersects_def by blast
  qed

  obtain s0 where hs0: "\<forall>n. s0 n \<in> top1_ball_on X d x (inverse (of_nat (Suc n))) \<inter> A"
    using choice[OF hchoose] by blast

  define s where "s = s0"

  have hsA': "\<forall>n. s n \<in> A"
    unfolding s_def using hs0 by blast

  have hconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
  proof (unfold seq_converges_to_on_def, intro conjI)
    show "x \<in> X" by (rule hxX)
    show "\<forall>U. neighborhood_of x X (top1_metric_topology_on X d) U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> U)"
    proof (intro allI impI)
      fix U assume hU: "neighborhood_of x X (top1_metric_topology_on X d) U"
      have hUopen: "U \<in> top1_metric_topology_on X d" and hxU: "x \<in> U"
        using hU unfolding neighborhood_of_def by blast+
      obtain \<epsilon> where heps: "\<epsilon> > 0" and hball_sub: "top1_ball_on X d x \<epsilon> \<subseteq> U"
        using top1_metric_open_contains_ball[OF hd hUopen hxU] by blast

      obtain n where hnpos: "n > 0" and hinv: "inverse (of_nat n :: real) < \<epsilon>"
        using ex_inverse_of_nat_less[OF heps] by blast
      have hn': "\<exists>N. n = Suc N"
      proof (cases n)
        case 0
        show ?thesis
          using hnpos by (simp add: 0)
      next
        case (Suc N)
        show ?thesis
          by (intro exI[where x=N]) (simp add: Suc)
      qed
      obtain N where hn: "n = Suc N"
        using hn' by blast
      have hNpos: "inverse (of_nat (Suc N) :: real) < \<epsilon>"
        using hinv hn by simp

      have htail: "\<forall>n\<ge>N. s n \<in> top1_ball_on X d x \<epsilon>"
      proof (intro allI impI)
        fix n assume hn: "n \<ge> N"
        have hsball: "s n \<in> top1_ball_on X d x (inverse (of_nat (Suc n)))"
          unfolding s_def using hs0 by blast
        have hsX: "s n \<in> X"
          using hsball unfolding top1_ball_on_def by blast
        have hdist: "d x (s n) < inverse (of_nat (Suc n) :: real)"
          using hsball unfolding top1_ball_on_def by blast
        have hle: "(1 / of_nat (Suc n) :: real) \<le> (1 / of_nat (Suc N) :: real)"
          using inverse_of_nat_le[of "Suc N" "Suc n"] hn by simp
        have "d x (s n) < 1 / of_nat (Suc n)"
          using hdist by (simp add: inverse_eq_divide)
        also have "... \<le> 1 / of_nat (Suc N)"
          by (rule hle)
        also have "... < \<epsilon>"
        proof -
          have "1 / of_nat (Suc N) = inverse (of_nat (Suc N) :: real)"
            by (simp add: inverse_eq_divide)
          thus "1 / of_nat (Suc N) < \<epsilon>"
            using hNpos by simp
        qed
        finally have "d x (s n) < \<epsilon>" .
        show "s n \<in> top1_ball_on X d x \<epsilon>"
          unfolding top1_ball_on_def using hsX \<open>d x (s n) < \<epsilon>\<close> by blast
      qed

      show "\<exists>N. \<forall>n\<ge>N. s n \<in> U"
      proof (rule exI[where x=N])
        show "\<forall>n\<ge>N. s n \<in> U"
        proof (intro allI impI)
          fix n assume hn: "n \<ge> N"
          have "s n \<in> top1_ball_on X d x \<epsilon>"
            using htail hn by blast
          thus "s n \<in> U"
            using hball_sub by blast
        qed
      qed
    qed
  qed

  show ?thesis
    by (rule exI[where x=s], intro conjI, rule hsA', rule hconv)
qed

(** from \S21 Lemma 21.2 (The sequence lemma) [top1.tex:2002] **)
theorem Lemma_21_2:
  assumes hTX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  shows "(\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)
          \<longrightarrow> x \<in> closure_on X TX A"
    and "top1_metrizable_on X TX
          \<longrightarrow> x \<in> closure_on X TX A
          \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)"
proof -
  show "(\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)
          \<longrightarrow> x \<in> closure_on X TX A"
  proof
    assume hex: "\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX"
    obtain s where hsA: "\<forall>n. s n \<in> A" and hsconv: "seq_converges_to_on s x X TX"
      using hex by blast
    show "x \<in> closure_on X TX A"
      by (rule Lemma_21_2_sequence[OF hTX hsconv hsA hAX])
  qed

  show "top1_metrizable_on X TX
          \<longrightarrow> x \<in> closure_on X TX A
          \<longrightarrow> (\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX)"
  proof (intro impI)
    assume hmet: "top1_metrizable_on X TX"
    assume hxcl: "x \<in> closure_on X TX A"
    obtain d where hd: "top1_metric_on X d" and hTXeq: "TX = top1_metric_topology_on X d"
      using hmet unfolding top1_metrizable_on_def by blast
    have hxcl': "x \<in> closure_on X (top1_metric_topology_on X d) A"
      unfolding hTXeq[symmetric] by (rule hxcl)
    obtain s where hsA: "\<forall>n. s n \<in> A"
        and hsconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
      using Lemma_21_2_sequence_converse[OF hd hxcl' hAX] by blast
    show "\<exists>s. (\<forall>n. s n \<in> A) \<and> seq_converges_to_on s x X TX"
      apply (rule exI[where x=s])
      apply (intro conjI)
       apply (rule hsA)
      unfolding hTXeq
      apply (rule hsconv)
      done
  qed
qed

(** from \S21 Theorem 21.3 (Sequential characterization of continuity) [top1.tex:2006] **)
theorem Theorem_21_3_forward:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
  assumes hx: "seq_converges_to_on s x X TX"
  shows "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
proof -
  have hmap: "\<forall>x\<in>X. f x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hxX: "x \<in> X"
    using hx unfolding seq_converges_to_on_def by blast
  have hfxY: "f x \<in> Y"
    using hmap hxX by blast
  show ?thesis
    unfolding seq_converges_to_on_def
  proof (intro conjI)
    show "f x \<in> Y" by (rule hfxY)
    show "\<forall>V. neighborhood_of (f x) Y TY V \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. f (s n) \<in> V)"
    proof (intro allI impI)
      fix V assume hV: "neighborhood_of (f x) Y TY V"
      have hVTY: "V \<in> TY" and hfxV: "f x \<in> V"
        using hV unfolding neighborhood_of_def by blast+
      have hpre: "{u\<in>X. f u \<in> V} \<in> TX"
        using hcont hVTY unfolding top1_continuous_map_on_def by blast
      have hnbhd: "neighborhood_of x X TX {u\<in>X. f u \<in> V}"
        unfolding neighborhood_of_def using hpre hxX hfxV by simp
      obtain N where hN: "\<forall>n\<ge>N. s n \<in> {u\<in>X. f u \<in> V}"
        using hx hnbhd unfolding seq_converges_to_on_def by blast
      show "\<exists>N. \<forall>n\<ge>N. f (s n) \<in> V"
      proof (rule exI[where x=N])
        show "\<forall>n\<ge>N. f (s n) \<in> V"
        proof (intro allI impI)
          fix n assume hn: "n \<ge> N"
          have "s n \<in> {u\<in>X. f u \<in> V}"
            using hN hn by blast
          thus "f (s n) \<in> V"
            by simp
        qed
      qed
    qed
  qed
qed

theorem Theorem_21_3_converse_metric:
  assumes hd: "top1_metric_on X d"
  assumes hTY: "is_topology_on Y TY"
  assumes hmap: "\<forall>x\<in>X. f x \<in> Y"
  assumes hseq:
    "\<forall>s x. seq_converges_to_on s x X (top1_metric_topology_on X d)
          \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
  shows "top1_continuous_map_on X (top1_metric_topology_on X d) Y TY f"
proof -
  have hTX: "is_topology_on X (top1_metric_topology_on X d)"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])
  have hclosure:
    "\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X (top1_metric_topology_on X d) A \<subseteq> closure_on Y TY (f ` A)"
  proof (intro allI impI)
    fix A assume hAX: "A \<subseteq> X"
    show "f ` closure_on X (top1_metric_topology_on X d) A \<subseteq> closure_on Y TY (f ` A)"
    proof (rule subsetI)
      fix y assume hy: "y \<in> f ` closure_on X (top1_metric_topology_on X d) A"
      obtain x where hxcl: "x \<in> closure_on X (top1_metric_topology_on X d) A" and hyfx: "y = f x"
        using hy by blast
      obtain s where hsA: "\<forall>n. s n \<in> A"
          and hsconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
        using Lemma_21_2_sequence_converse[OF hd hxcl hAX] by blast
      have hconvY: "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
        using hseq hsconv by blast
      have hs_in: "\<forall>n. f (s n) \<in> f ` A"
      proof (intro allI)
        fix n
        have "s n \<in> A" using hsA by blast
        thus "f (s n) \<in> f ` A"
          by (rule imageI)
      qed
      have himg_sub: "f ` A \<subseteq> Y"
      proof (rule subsetI)
        fix y assume hy: "y \<in> f ` A"
        obtain a where haA: "a \<in> A" and hyfa: "y = f a"
          using hy by blast
        have haX: "a \<in> X" using hAX haA by blast
        have "f a \<in> Y" using hmap haX by blast
        thus "y \<in> Y" using hyfa by simp
      qed
      have hclY: "f x \<in> closure_on Y TY (f ` A)"
        by (rule Lemma_21_2_sequence[OF hTY hconvY hs_in himg_sub])
      show "y \<in> closure_on Y TY (f ` A)"
        using hclY hyfx by simp
    qed
  qed

  have "top1_continuous_map_on X (top1_metric_topology_on X d) Y TY f
        \<longleftrightarrow> ((\<forall>x\<in>X. f x \<in> Y) \<and>
             (\<forall>A. A \<subseteq> X \<longrightarrow> f ` closure_on X (top1_metric_topology_on X d) A \<subseteq> closure_on Y TY (f ` A)))"
    by (rule Theorem_18_1(1)[OF hTX hTY])
  thus ?thesis
    using hmap hclosure by blast
qed

(** from \S21 Theorem 21.3 (combined statement, with metrizable converse). **)
theorem Theorem_21_3:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hmap: "\<forall>x\<in>X. f x \<in> Y"
  shows "top1_continuous_map_on X TX Y TY f
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)"
    and "top1_metrizable_on X TX
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
          \<longrightarrow> top1_continuous_map_on X TX Y TY f"
proof -
  show "top1_continuous_map_on X TX Y TY f
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)"
  proof
    assume hcont: "top1_continuous_map_on X TX Y TY f"
    show "\<forall>s x. seq_converges_to_on s x X TX
            \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
    proof (intro allI impI)
      fix s x
      assume hx: "seq_converges_to_on s x X TX"
      show "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
        by (rule Theorem_21_3_forward[OF hTX hTY hcont hx])
    qed
  qed

  show "top1_metrizable_on X TX
          \<longrightarrow> (\<forall>s x. seq_converges_to_on s x X TX
                 \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY)
          \<longrightarrow> top1_continuous_map_on X TX Y TY f"
  proof (intro impI)
    assume hmet: "top1_metrizable_on X TX"
    assume hseq:
      "\<forall>s x. seq_converges_to_on s x X TX
            \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
    obtain d where hd: "top1_metric_on X d" and hTXeq: "TX = top1_metric_topology_on X d"
      using hmet unfolding top1_metrizable_on_def by blast
    have hseq': "\<forall>s x. seq_converges_to_on s x X (top1_metric_topology_on X d)
            \<longrightarrow> seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
    proof (intro allI impI)
      fix s x
      assume hs: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
      have hsTX: "seq_converges_to_on s x X TX"
        unfolding hTXeq by (rule hs)
      show "seq_converges_to_on (\<lambda>n. f (s n)) (f x) Y TY"
        using hseq hsTX by blast
    qed
    have hcont:
      "top1_continuous_map_on X (top1_metric_topology_on X d) Y TY f"
      by (rule Theorem_21_3_converse_metric[OF hd hTY hmap hseq'])
    show "top1_continuous_map_on X TX Y TY f"
      unfolding hTXeq using hcont by simp
  qed
qed

(** from \S21 Lemma 21.4 (Continuity of the arithmetic operations on \<open>\<real>\<close>) [top1.tex:2026] **)
theorem Lemma_21_4:
  defines "TR \<equiv> (order_topology_on_UNIV::real set set)"
  shows "top1_continuous_map_on (UNIV \<times> UNIV) (product_topology_on TR TR) UNIV TR (\<lambda>p. pi1 p + pi2 p)"
    and "top1_continuous_map_on (UNIV \<times> UNIV) (product_topology_on TR TR) UNIV TR (\<lambda>p. pi1 p - pi2 p)"
    and "top1_continuous_map_on (UNIV \<times> UNIV) (product_topology_on TR TR) UNIV TR (\<lambda>p. pi1 p * pi2 p)"
    and "top1_continuous_map_on (UNIV \<times> (UNIV - {0::real}))
           (subspace_topology (UNIV \<times> UNIV) (product_topology_on TR TR) (UNIV \<times> (UNIV - {0::real})))
           UNIV TR (\<lambda>p. pi1 p / pi2 p)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "TR"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?X = "?R \<times> ?R"

  have hTopR: "is_topology_on ?R ?TR"
    unfolding TR_def by (rule order_topology_on_UNIV_is_topology_on)
  have hTopX: "is_topology_on ?X ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopR hTopR])

  have hBasisR: "basis_for ?R (basis_order_topology::real set set) ?TR"
    unfolding TR_def by (rule basis_for_order_topology_on_UNIV)

  have cont_add:
    "top1_continuous_map_on ?X ?TP ?R ?TR (\<lambda>p::real \<times> real. pi1 p + pi2 p)"
  proof -
    let ?plus = "(\<lambda>p::real \<times> real. pi1 p + pi2 p)"
    have hpre: "\<forall>b\<in>(basis_order_topology::real set set). {p \<in> ?X. ?plus p \<in> b} \<in> ?TP"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      define P where "P = {p \<in> ?X. ?plus p \<in> b}"
      have hPsub: "P \<subseteq> ?X"
        unfolding P_def by simp
      have hlocal: "\<forall>p\<in>P. \<exists>W\<in>?TP. p \<in> W \<and> W \<subseteq> P"
      proof (intro ballI)
        fix p assume hpP: "p \<in> P"
        have hpb: "?plus p \<in> b"
          using hpP unfolding P_def by simp
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
            unfolding U_def TR_def by (rule open_interval_in_order_topology)
        qed
        have hV_TR: "V \<in> ?TR"
        proof -
          have "pi2 p - e/2 < pi2 p + e/2"
            using he2 by linarith
          thus ?thesis
            unfolding V_def TR_def by (rule open_interval_in_order_topology)
        qed
	        have hW_TP: "W \<in> ?TP"
	          unfolding W_def by (rule product_rect_open[OF hU_TR hV_TR])
	        have hpW: "p \<in> W"
	        proof -
	          have hpU: "pi1 p \<in> U"
	          proof -
	            have h1: "pi1 p - e/2 < pi1 p"
	              using he2 by linarith
	            have h2: "pi1 p < pi1 p + e/2"
	              using he2 by linarith
	            show ?thesis
	              unfolding U_def open_interval_def using h1 h2 by simp
	          qed
	          have hpV: "pi2 p \<in> V"
	          proof -
	            have h1: "pi2 p - e/2 < pi2 p"
	              using he2 by linarith
	            have h2: "pi2 p < pi2 p + e/2"
	              using he2 by linarith
	            show ?thesis
	              unfolding V_def open_interval_def using h1 h2 by simp
	          qed
		          show ?thesis
		          proof (cases p)
		            case (Pair a b)
		            have "a \<in> U"
		              using hpU unfolding Pair by (simp add: pi1_def)
		            moreover have "b \<in> V"
		              using hpV unfolding Pair by (simp add: pi2_def)
		            ultimately show ?thesis
		              unfolding W_def Pair by simp
		          qed
	        qed
        have hWsub: "W \<subseteq> P"
	        proof (rule subsetI)
	          fix q assume hqW: "q \<in> W"
	          have hqU: "fst q \<in> U"
	            using hqW unfolding W_def by auto
	          have hqV: "snd q \<in> V"
	            using hqW unfolding W_def by auto

	          have hqU_ineq: "pi1 p - e/2 < fst q \<and> fst q < pi1 p + e/2"
	            using hqU unfolding U_def open_interval_def by simp
	          have hqV_ineq: "pi2 p - e/2 < snd q \<and> snd q < pi2 p + e/2"
	            using hqV unfolding V_def open_interval_def by simp

	          have hq1: "pi1 p - e/2 < pi1 q"
	            using hqU_ineq by (simp add: pi1_def)
	          have hq2: "pi1 q < pi1 p + e/2"
	            using hqU_ineq by (simp add: pi1_def)
	          have hq3: "pi2 p - e/2 < pi2 q"
	            using hqV_ineq by (simp add: pi2_def)
	          have hq4: "pi2 q < pi2 p + e/2"
	            using hqV_ineq by (simp add: pi2_def)
          have hsum1: "?plus p - e < ?plus q"
          proof -
            have "pi1 p + pi2 p - e < pi1 q + pi2 q"
              using hq1 hq3 by linarith
            thus ?thesis
              by simp
          qed
          have hsum2: "?plus q < ?plus p + e"
          proof -
            have "pi1 q + pi2 q < pi1 p + pi2 p + e"
              using hq2 hq4 by linarith
            thus ?thesis
              by simp
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
          proof (intro conjI)
            show "p \<in> W"
              by (rule hpW)
            show "W \<subseteq> P"
              by (rule hWsub)
          qed
        qed
      qed
	      have hP_open: "P \<in> ?TP"
	        by (rule top1_open_set_from_local_opens[OF hTopX hPsub hlocal])
	      show "{p \<in> ?X. ?plus p \<in> b} \<in> ?TP"
	        unfolding P_def[symmetric] using hP_open .
    qed
    show ?thesis
      by (rule top1_continuous_map_on_generated_by_basis[OF hTopX hBasisR], simp, rule hpre)
  qed

  have cont_mul:
    "top1_continuous_map_on ?X ?TP ?R ?TR (\<lambda>p::real \<times> real. pi1 p * pi2 p)"
  proof -
    let ?mul = "(\<lambda>p::real \<times> real. pi1 p * pi2 p)"
    have hpre: "\<forall>b\<in>(basis_order_topology::real set set). {p \<in> ?X. ?mul p \<in> b} \<in> ?TP"
    proof (intro ballI)
      fix b :: "real set"
      assume hb: "b \<in> (basis_order_topology::real set set)"
      define P where "P = {p \<in> ?X. ?mul p \<in> b}"
      have hPsub: "P \<subseteq> ?X"
        unfolding P_def by simp
      have hlocal: "\<forall>p\<in>P. \<exists>W\<in>?TP. p \<in> W \<and> W \<subseteq> P"
      proof (intro ballI)
        fix p assume hpP: "p \<in> P"
        have hpb: "?mul p \<in> b"
          using hpP unfolding P_def by simp
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
            unfolding U_def TR_def by (rule open_interval_in_order_topology)
        qed
        have hV_TR: "V \<in> ?TR"
        proof -
          have "pi2 p - d < pi2 p + d"
            using hdpos by linarith
          thus ?thesis
            unfolding V_def TR_def by (rule open_interval_in_order_topology)
        qed
	        have hW_TP: "W \<in> ?TP"
	          unfolding W_def by (rule product_rect_open[OF hU_TR hV_TR])
	        have hpW: "p \<in> W"
	        proof -
	          have hpU: "pi1 p \<in> U"
	          proof -
	            have h1: "pi1 p - d < pi1 p"
	              using hdpos by linarith
	            have h2: "pi1 p < pi1 p + d"
	              using hdpos by linarith
	            show ?thesis
	              unfolding U_def open_interval_def using h1 h2 by simp
	          qed
	          have hpV: "pi2 p \<in> V"
	          proof -
	            have h1: "pi2 p - d < pi2 p"
	              using hdpos by linarith
	            have h2: "pi2 p < pi2 p + d"
	              using hdpos by linarith
	            show ?thesis
	              unfolding V_def open_interval_def using h1 h2 by simp
	          qed
		          show ?thesis
		          proof (cases p)
		            case (Pair a b)
		            have "a \<in> U"
		              using hpU unfolding Pair by (simp add: pi1_def)
		            moreover have "b \<in> V"
		              using hpV unfolding Pair by (simp add: pi2_def)
		            ultimately show ?thesis
		              unfolding W_def Pair by simp
		          qed
	        qed

        have hWsub: "W \<subseteq> P"
	        proof (rule subsetI)
	          fix q assume hqW: "q \<in> W"
	          have hqU: "fst q \<in> U"
	            using hqW unfolding W_def by auto
	          have hqV: "snd q \<in> V"
	            using hqW unfolding W_def by auto

	          have hqU_ineq: "pi1 p - d < fst q \<and> fst q < pi1 p + d"
	            using hqU unfolding U_def open_interval_def by simp
	          have hqV_ineq: "pi2 p - d < snd q \<and> snd q < pi2 p + d"
	            using hqV unfolding V_def open_interval_def by simp

	          have hq1: "pi1 p - d < pi1 q"
	            using hqU_ineq by (simp add: pi1_def)
	          have hq2: "pi1 q < pi1 p + d"
	            using hqU_ineq by (simp add: pi1_def)
	          have hq3: "pi2 p - d < pi2 q"
	            using hqV_ineq by (simp add: pi2_def)
	          have hq4: "pi2 q < pi2 p + d"
	            using hqV_ineq by (simp add: pi2_def)
          have habs1: "abs (pi1 q - pi1 p) < d"
          proof -
            have "-d < pi1 q - pi1 p \<and> pi1 q - pi1 p < d"
              using hq1 hq2 by linarith
            thus ?thesis
              by (simp add: abs_less_iff)
          qed
          have habs2: "abs (pi2 q - pi2 p) < d"
          proof -
            have "-d < pi2 q - pi2 p \<and> pi2 q - pi2 p < d"
              using hq3 hq4 by linarith
            thus ?thesis
              by (simp add: abs_less_iff)
          qed
          have hpi1q_le: "abs (pi1 q) \<le> abs (pi1 p) + 1"
          proof -
            have "abs (pi1 q) = abs (pi1 p + (pi1 q - pi1 p))"
              by simp
            also have "... \<le> abs (pi1 p) + abs (pi1 q - pi1 p)"
              by (rule abs_triangle_ineq)
            also have "... < abs (pi1 p) + d"
              using habs1 by linarith
            also have "... \<le> abs (pi1 p) + 1"
              using hd_le_1 by linarith
            finally show ?thesis
              by linarith
          qed
          have hdiff_le:
            "abs (?mul q - ?mul p) \<le> abs (pi1 q) * abs (pi2 q - pi2 p) + abs (pi2 p) * abs (pi1 q - pi1 p)"
	          proof -
	            have "?mul q - ?mul p = pi1 q * (pi2 q - pi2 p) + pi2 p * (pi1 q - pi1 p)"
	              by (simp add: algebra_simps)
	            then have hEq: "abs (?mul q - ?mul p) = abs (pi1 q * (pi2 q - pi2 p) + pi2 p * (pi1 q - pi1 p))"
	              by simp
	            have hTri:
	              "abs (pi1 q * (pi2 q - pi2 p) + pi2 p * (pi1 q - pi1 p))
	               \<le> abs (pi1 q * (pi2 q - pi2 p)) + abs (pi2 p * (pi1 q - pi1 p))"
	              by (rule abs_triangle_ineq)
	            have hMult1: "abs (pi1 q * (pi2 q - pi2 p)) = abs (pi1 q) * abs (pi2 q - pi2 p)"
	              by (simp add: abs_mult)
	            have hMult2: "abs (pi2 p * (pi1 q - pi1 p)) = abs (pi2 p) * abs (pi1 q - pi1 p)"
	              by (simp add: abs_mult)
	            show ?thesis
	              unfolding hEq using hTri unfolding hMult1 hMult2 .
	          qed
	          have hdiff_lt:
	            "abs (?mul q - ?mul p) < d * K"
	          proof -
	            have hstep1: "abs (?mul q - ?mul p) \<le> abs (pi1 q) * abs (pi2 q - pi2 p) + abs (pi2 p) * abs (pi1 q - pi1 p)"
	              by (rule hdiff_le)

	            have habs1_le: "abs (pi1 q - pi1 p) \<le> d"
	              using habs1 by linarith
	            have habs2_le: "abs (pi2 q - pi2 p) \<le> d"
	              using habs2 by linarith

	            have hstep2_le:
	              "abs (pi1 q) * abs (pi2 q - pi2 p) + abs (pi2 p) * abs (pi1 q - pi1 p)
	               \<le> abs (pi1 q) * d + abs (pi2 p) * d"
		            proof -
		              have hA: "abs (pi1 q) * abs (pi2 q - pi2 p) \<le> abs (pi1 q) * d"
		              proof (rule mult_left_mono)
		                show "abs (pi2 q - pi2 p) \<le> d"
		                  by (rule habs2_le)
		                show "0 \<le> abs (pi1 q)"
		                  by simp
		              qed
		              have hB: "abs (pi2 p) * abs (pi1 q - pi1 p) \<le> abs (pi2 p) * d"
		              proof (rule mult_left_mono)
		                show "abs (pi1 q - pi1 p) \<le> d"
		                  by (rule habs1_le)
		                show "0 \<le> abs (pi2 p)"
		                  by simp
		              qed
		              show ?thesis
		                using hA hB by (rule add_mono)
		            qed

	            have hpi1q_lt: "abs (pi1 q) < abs (pi1 p) + 1"
	            proof -
	              have "abs (pi1 q) = abs (pi1 p + (pi1 q - pi1 p))"
	                by simp
	              also have "... \<le> abs (pi1 p) + abs (pi1 q - pi1 p)"
	                by (rule abs_triangle_ineq)
	              also have "... < abs (pi1 p) + d"
	                using habs1 by linarith
	              also have "... \<le> abs (pi1 p) + 1"
	                using hd_le_1 by linarith
	              finally show ?thesis
	                by linarith
	            qed

	            have hC_strict: "abs (pi1 q) * d < (abs (pi1 p) + 1) * d"
	              by (rule mult_strict_right_mono[OF hpi1q_lt hdpos])
	            have hstep3_strict:
	              "abs (pi1 q) * d + abs (pi2 p) * d < (abs (pi1 p) + 1) * d + abs (pi2 p) * d"
	              using hC_strict by linarith

	            have habs_lt: "abs (?mul q - ?mul p) < (abs (pi1 p) + 1) * d + abs (pi2 p) * d"
	              using hstep1 hstep2_le hstep3_strict by linarith

	            show ?thesis
	              unfolding K_def using habs_lt by (simp add: algebra_simps)
	          qed
	          have hbound: "d * K \<le> e / 2"
	          proof -
	            have "d * K \<le> d0 * K"
	            proof -
	              have "d * K \<le> d0 * K \<longleftrightarrow> d * K \<le> K * d0"
	                by (simp add: mult_ac)
	              also have "... \<longleftrightarrow> d \<le> d0"
	                using hKpos by (simp add: mult_le_cancel_left_pos)
	              finally show ?thesis
	                using hd_le_d0 by simp
	            qed
	            also have "... = e / 2"
	              unfolding d0_def K_def by (simp add: field_simps)
	            finally show ?thesis .
	          qed
          have hdiff_lt2: "abs (?mul q - ?mul p) < e"
          proof -
            have "abs (?mul q - ?mul p) < e / 2"
              using hdiff_lt hbound by linarith
            thus ?thesis
              using he by linarith
          qed
          have hqI: "?mul q \<in> open_interval (?mul p - e) (?mul p + e)"
          proof -
            have "-e < ?mul q - ?mul p \<and> ?mul q - ?mul p < e"
              using hdiff_lt2 by (simp add: abs_less_iff)
            hence "?mul p - e < ?mul q" and "?mul q < ?mul p + e"
              by linarith+
            thus ?thesis
              unfolding open_interval_def by simp
          qed
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
          proof (intro conjI)
            show "p \<in> W"
              by (rule hpW)
            show "W \<subseteq> P"
              by (rule hWsub)
          qed
        qed
      qed
	      have hP_open: "P \<in> ?TP"
	        by (rule top1_open_set_from_local_opens[OF hTopX hPsub hlocal])
	      show "{p \<in> ?X. ?mul p \<in> b} \<in> ?TP"
	        unfolding P_def[symmetric] using hP_open .
    qed
    show ?thesis
      by (rule top1_continuous_map_on_generated_by_basis[OF hTopX hBasisR], simp, rule hpre)
  qed

  have cont_uminus:
    "top1_continuous_map_on ?R ?TR ?R ?TR (\<lambda>x::real. -x)"
  proof -
    let ?neg = "(\<lambda>x::real. -x)"
    have hpre: "\<forall>b\<in>(basis_order_topology::real set set). {x \<in> ?R. ?neg x \<in> b} \<in> ?TR"
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
          unfolding hbeq open_interval_def by auto
        have hOpen: "open_interval (-c) (-a) \<in> ?TR"
        proof -
          have "-c < -a"
            using hac by linarith
          thus ?thesis
            unfolding TR_def by (rule open_interval_in_order_topology)
        qed
        show ?thesis
          using hOpen hEq by simp
      next
        assume hrest: "(\<exists>a. b = open_ray_gt a) \<or> (\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
        show ?thesis
        proof (rule disjE[OF hrest])
          assume hbr: "\<exists>a. b = open_ray_gt a"
          then obtain a where hbeq: "b = open_ray_gt a"
            by blast
          have hEq: "{x \<in> ?R. -x \<in> b} = open_ray_lt (-a)"
            unfolding hbeq open_ray_gt_def open_ray_lt_def by auto
          have hOpen: "open_ray_lt (-a) \<in> ?TR"
            unfolding TR_def by (rule open_ray_lt_in_order_topology)
          show ?thesis
            using hOpen hEq by simp
        next
          assume hrest2: "(\<exists>a. b = open_ray_lt a) \<or> b = (UNIV::real set)"
          show ?thesis
          proof (rule disjE[OF hrest2])
            assume hbl: "\<exists>a. b = open_ray_lt a"
            then obtain a where hbeq: "b = open_ray_lt a"
              by blast
            have hEq: "{x \<in> ?R. -x \<in> b} = open_ray_gt (-a)"
              unfolding hbeq open_ray_gt_def open_ray_lt_def by auto
            have hOpen: "open_ray_gt (-a) \<in> ?TR"
              unfolding TR_def by (rule open_ray_gt_in_order_topology)
            show ?thesis
              using hOpen hEq by simp
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
    show ?thesis
      by (rule top1_continuous_map_on_generated_by_basis[OF hTopR hBasisR], simp, rule hpre)
  qed

  have cont_sub:
    "top1_continuous_map_on ?X ?TP ?R ?TR (\<lambda>p::real \<times> real. pi1 p - pi2 p)"
  proof -
    let ?minus = "(\<lambda>p::real \<times> real. pi1 p - pi2 p)"
    let ?pair = "(\<lambda>p::real \<times> real. (pi1 p, - (pi2 p)))"
    have hpi1: "top1_continuous_map_on ?X ?TP ?R ?TR pi1"
      by (rule top1_continuous_pi1[OF hTopR hTopR])
    have hpi2: "top1_continuous_map_on ?X ?TP ?R ?TR pi2"
      by (rule top1_continuous_pi2[OF hTopR hTopR])
    have hneg_pi2: "top1_continuous_map_on ?X ?TP ?R ?TR (\<lambda>p. - (pi2 p))"
    proof -
      have hEq: "(\<lambda>p. - (pi2 p)) = (\<lambda>x::real. -x) \<circ> pi2"
        by (rule ext, simp add: o_def)
      show ?thesis
        unfolding hEq by (rule top1_continuous_map_on_comp[OF hpi2 cont_uminus])
    qed
    have hpair: "top1_continuous_map_on ?X ?TP (?R \<times> ?R) ?TP ?pair"
    proof -
      have hiff:
        "top1_continuous_map_on ?X ?TP (?R \<times> ?R) ?TP ?pair
         \<longleftrightarrow>
           (top1_continuous_map_on ?X ?TP ?R ?TR (pi1 \<circ> ?pair)
            \<and> top1_continuous_map_on ?X ?TP ?R ?TR (pi2 \<circ> ?pair))"
        by (rule Theorem_18_4[OF hTopX hTopR hTopR])
      have hpi1pair: "top1_continuous_map_on ?X ?TP ?R ?TR (pi1 \<circ> ?pair)"
      proof -
        have hEq: "(pi1 \<circ> ?pair) = pi1"
          by (rule ext, simp add: o_def pi1_def)
        show ?thesis
          unfolding hEq by (rule hpi1)
      qed
      have hpi2pair: "top1_continuous_map_on ?X ?TP ?R ?TR (pi2 \<circ> ?pair)"
      proof -
        have hEq: "(pi2 \<circ> ?pair) = (\<lambda>p. - (pi2 p))"
          by (rule ext, simp add: o_def pi2_def)
        show ?thesis
          unfolding hEq by (rule hneg_pi2)
      qed
      show ?thesis
        apply (rule iffD2[OF hiff])
        apply (intro conjI)
         apply (rule hpi1pair)
        apply (rule hpi2pair)
        done
    qed
    have hEq: "?minus = (\<lambda>p::real \<times> real. pi1 p + pi2 p) \<circ> ?pair"
      by (rule ext, simp add: o_def pi1_def pi2_def)
    show ?thesis
      unfolding hEq by (rule top1_continuous_map_on_comp[OF hpair cont_add])
  qed

  have cont_div:
    "top1_continuous_map_on (?R \<times> (?R - {0::real}))
       (subspace_topology ?X ?TP (?R \<times> (?R - {0::real})))
       ?R ?TR (\<lambda>p::real \<times> real. pi1 p / pi2 p)"
  proof -
    let ?W = "?R - {0::real}"
    let ?A = "?R \<times> ?W"
    let ?TA = "subspace_topology ?X ?TP ?A"
    let ?inv = "(\<lambda>t::real. inverse t)"
    let ?mul = "(\<lambda>p::real \<times> real. pi1 p * pi2 p)"
    let ?pairinv = "(\<lambda>p::real \<times> real. (pi1 p, ?inv (pi2 p)))"
    let ?TW = "subspace_topology ?R ?TR ?W"

    have hTopA: "is_topology_on ?A ?TA"
      by (rule subspace_topology_is_topology_on[OF hTopX], simp)
    have hTopW: "is_topology_on ?W ?TW"
      by (rule subspace_topology_is_topology_on[OF hTopR], simp)

    have cont_inv_nonzero: "top1_continuous_map_on ?W ?TW ?R ?TR ?inv"
    proof -
      show ?thesis
      proof (rule top1_continuous_map_on_generated_by_basis)
        show "is_topology_on ?W ?TW"
          by (rule hTopW)
        show "basis_for ?R (basis_order_topology::real set set) ?TR"
          by (rule hBasisR)
        show "\<forall>t\<in>?W. ?inv t \<in> ?R"
          by simp
        show "\<forall>b\<in>(basis_order_topology::real set set). {t \<in> ?W. ?inv t \<in> b} \<in> ?TW"
        proof (intro ballI)
          fix b :: "real set"
          assume hb: "b \<in> (basis_order_topology::real set set)"
	          define P where "P = {t \<in> ?W. ?inv t \<in> b}"
	          have hPsub: "P \<subseteq> ?W"
	            unfolding P_def by blast
          have hlocal: "\<forall>p\<in>P. \<exists>U\<in>?TW. p \<in> U \<and> U \<subseteq> P"
	          proof (intro ballI)
	            fix p assume hpP: "p \<in> P"
	            have hp_conj: "p \<in> ?W \<and> ?inv p \<in> b"
	              using hpP unfolding P_def by simp
	            have hpW: "p \<in> ?W"
	              using hp_conj by (rule conjunct1)
	            have hpb: "?inv p \<in> b"
	              using hp_conj by (rule conjunct2)
	            have hp0: "p \<noteq> 0"
	              using hpW by simp
		            obtain e where he: "0 < e"
		              and hI_sub: "open_interval (?inv p - e) (?inv p + e) \<subseteq> b"
	              using basis_order_topology_contains_open_interval[OF hb hpb] by blast
            define d1 where "d1 = abs p / 2"
            define d2 where "d2 = e * (abs p)\<^sup>2 / 4"
            define d where "d = min d1 d2"
            have hd1: "0 < d1"
            proof -
              have "0 < abs p"
                using hp0 by simp
              thus ?thesis
                unfolding d1_def by linarith
            qed
            have hd2: "0 < d2"
            proof -
              have "0 < abs p"
                using hp0 by simp
              hence "0 < (abs p)\<^sup>2"
                by simp
              thus ?thesis
                unfolding d2_def using he by (simp add: divide_pos_pos)
            qed
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
                unfolding U_def TR_def by (rule open_interval_in_order_topology)
            qed

	            have hUsubW: "U \<subseteq> ?W"
	            proof (rule subsetI)
	              fix t assume htU: "t \<in> U"
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
		              have habs_p2: "abs (t - p) < abs p / 2"
		              proof -
	                have "abs (t - p) < d1"
	                  using habs_lt hd_le_d1 by linarith
	                thus ?thesis
	                  unfolding d1_def by simp
	              qed
              have habs_p_le: "abs p \<le> abs t + abs (t - p)"
              proof -
                have "abs p = abs (t + (p - t))"
                  by simp
                also have "... \<le> abs t + abs (p - t)"
                  by (rule abs_triangle_ineq)
                also have "... = abs t + abs (t - p)"
                  by (simp add: abs_minus_commute)
                finally show ?thesis
                  by simp
              qed
              have habs_lower: "abs p - abs (t - p) \<le> abs t"
                using habs_p_le by linarith
              have "abs p / 2 < abs p - abs (t - p)"
                using habs_p2 by linarith
              hence "abs p / 2 < abs t"
                using habs_lower by linarith
              hence "t \<noteq> 0"
                by auto
              thus "t \<in> ?W"
                by simp
            qed

		            have hU_TW: "U \<in> ?TW"
		            proof -
			              have hEq: "?W \<inter> U = U"
			                using hUsubW by blast
		              show ?thesis
			                unfolding subspace_topology_def
			                apply (rule CollectI)
			                apply (rule exI[where x=U])
			                apply (intro conjI)
			                 apply (rule sym[OF hEq])
			                apply (rule hU_TR)
			                done
		            qed
            have hpU: "p \<in> U"
              unfolding U_def open_interval_def using hd by simp

	            have hUsubP: "U \<subseteq> P"
	            proof (rule subsetI)
	              fix t assume htU: "t \<in> U"
	              have htW: "t \<in> ?W"
	                using hUsubW htU by blast
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
              have habs_t_ge: "abs p / 2 < abs t"
	              proof -
	                have habs_p2: "abs (t - p) < abs p / 2"
	                proof -
	                  have "abs (t - p) < d1"
	                    using habs_lt hd_le_d1 by linarith
	                  thus ?thesis
	                    unfolding d1_def by simp
	                qed
	                have habs_p_le: "abs p \<le> abs t + abs (t - p)"
	                proof -
	                  have "abs p = abs (t + (p - t))"
	                    by simp
                  also have "... \<le> abs t + abs (p - t)"
                    by (rule abs_triangle_ineq)
                  also have "... = abs t + abs (t - p)"
                    by (simp add: abs_minus_commute)
                  finally show ?thesis
                    by simp
                qed
                have habs_lower: "abs p - abs (t - p) \<le> abs t"
                  using habs_p_le by linarith
                have "abs p / 2 < abs p - abs (t - p)"
                  using habs_p2 by linarith
                thus ?thesis
                  using habs_lower by linarith
              qed

              have habs_den_lb: "(abs p) * (abs p / 2) \<le> abs (p * t)"
              proof -
                have "abs (p * t) = abs p * abs t"
                  by (simp add: abs_mult)
                also have "... \<ge> abs p * (abs p / 2)"
                  using habs_t_ge by (intro mult_left_mono, simp, linarith)
                finally show ?thesis
                  by simp
              qed

              have hinv_diff:
                "abs (?inv t - ?inv p) = abs (t - p) / abs (p * t)"
              proof -
                have ht0: "t \<noteq> 0"
                  using htW by simp
                have "?inv t - ?inv p = (p - t) / (p * t)"
                  using hp0 ht0 by (simp add: field_simps)
                hence "abs (?inv t - ?inv p) = abs (p - t) / abs (p * t)"
                  by (simp add: abs_divide)
                also have "abs (p - t) = abs (t - p)"
                  by simp
                finally show ?thesis .
              qed

		              have hden_pos: "0 < (abs p) * (abs p / 2)"
		              proof -
		                have "0 < abs p"
		                  using hp0 by simp
		                have h2pos: "0 < (2::real)"
		                  by simp
		                have habs_div2: "0 < abs p / 2"
		                  by (rule divide_pos_pos[OF \<open>0 < abs p\<close> h2pos])
		                show ?thesis
		                  using \<open>0 < abs p\<close> habs_div2 by (rule mult_pos_pos)
		              qed
              have hle_inv: "inverse (abs (p * t)) \<le> inverse ((abs p) * (abs p / 2))"
                using habs_den_lb hden_pos by (rule le_imp_inverse_le)

              have hdiff_le:
                "abs (?inv t - ?inv p) \<le> abs (t - p) / ((abs p) * (abs p / 2))"
              proof -
                have hnonneg: "0 \<le> abs (t - p)"
                  by simp
                have "abs (?inv t - ?inv p) = abs (t - p) * inverse (abs (p * t))"
                  unfolding hinv_diff by (simp only: divide_inverse)
                also have "... \<le> abs (t - p) * inverse ((abs p) * (abs p / 2))"
                  using hle_inv hnonneg by (rule mult_left_mono)
                also have "... = abs (t - p) / ((abs p) * (abs p / 2))"
                  by (simp only: divide_inverse)
                finally show ?thesis .
              qed

              have hdiff_le2: "abs (?inv t - ?inv p) \<le> 2 * d / (abs p)\<^sup>2"
              proof -
                have hp0': "abs p \<noteq> 0"
                  using hp0 by simp
                have hEq: "abs (t - p) / ((abs p) * (abs p / 2)) = 2 * abs (t - p) / (abs p)\<^sup>2"
                  using hp0' by (simp add: field_simps power2_eq_square)
                have "abs (?inv t - ?inv p) \<le> 2 * abs (t - p) / (abs p)\<^sup>2"
                  using hdiff_le unfolding hEq .
                also have "... \<le> 2 * d / (abs p)\<^sup>2"
                proof -
                  have hp2pos: "0 < (abs p)\<^sup>2"
                    using hp0' by simp
                  have hp2nonneg: "0 \<le> (abs p)\<^sup>2"
                    by (rule less_imp_le[OF hp2pos])
                  have "2 * abs (t - p) \<le> 2 * d"
                    using habs_le by (rule mult_left_mono, simp)
                  have "2 * abs (t - p) / (abs p)\<^sup>2 \<le> 2 * d / (abs p)\<^sup>2"
                  proof (rule divide_right_mono)
                    show "2 * abs (t - p) \<le> 2 * d"
                      by (rule \<open>2 * abs (t - p) \<le> 2 * d\<close>)
                    show "0 \<le> (abs p)\<^sup>2"
                      by (rule hp2nonneg)
                  qed
                  thus ?thesis .
                qed
                finally show ?thesis .
              qed

              have hbound: "2 * d / (abs p)\<^sup>2 \<le> e / 2"
              proof -
                have hp0': "abs p \<noteq> 0"
                  using hp0 by simp
                have hp2pos: "0 < (abs p)\<^sup>2"
                  using hp0' by simp
                have hp2nonneg: "0 \<le> (abs p)\<^sup>2"
                  by (rule less_imp_le[OF hp2pos])
                have hd_le: "d \<le> e * (abs p)\<^sup>2 / 4"
                  using hd_le_d2 unfolding d2_def by simp
                have hnum_le: "2 * d \<le> 2 * (e * (abs p)\<^sup>2 / 4)"
                  using hd_le by (rule mult_left_mono, simp)
                have "2 * d / (abs p)\<^sup>2 \<le> (2 * (e * (abs p)\<^sup>2 / 4)) / (abs p)\<^sup>2"
                proof (rule divide_right_mono)
                  show "2 * d \<le> 2 * (e * (abs p)\<^sup>2 / 4)"
                    by (rule hnum_le)
                  show "0 \<le> (abs p)\<^sup>2"
                    by (rule hp2nonneg)
                qed
                also have "... = e / 2"
                  using hp0' by (simp add: field_simps)
                finally show ?thesis .
              qed

              have hdiff_lt: "abs (?inv t - ?inv p) < e"
              proof -
                have he2: "e / 2 < e"
                  using he by linarith
                have hle: "abs (?inv t - ?inv p) \<le> e / 2"
                  by (rule order_trans[OF hdiff_le2 hbound])
                show ?thesis
                  by (rule le_less_trans[OF hle he2])
              qed

              have htI: "?inv t \<in> open_interval (?inv p - e) (?inv p + e)"
              proof -
                have "-e < ?inv t - ?inv p \<and> ?inv t - ?inv p < e"
                  using hdiff_lt by (simp add: abs_less_iff)
                hence "?inv p - e < ?inv t" and "?inv t < ?inv p + e"
                  by linarith+
                thus ?thesis
                  unfolding open_interval_def by simp
              qed
              have htB: "?inv t \<in> b"
                using hI_sub htI by blast
              show "t \<in> P"
                unfolding P_def using htW htB by simp
            qed

	            show "\<exists>U\<in>?TW. p \<in> U \<and> U \<subseteq> P"
	            proof (rule bexI[where x=U])
	              show "U \<in> ?TW"
	                by (rule hU_TW)
	              show "p \<in> U \<and> U \<subseteq> P"
	              proof (intro conjI)
	                show "p \<in> U"
	                  by (rule hpU)
	                show "U \<subseteq> P"
	                  by (rule hUsubP)
	              qed
	            qed
          qed
	          have hP_open: "P \<in> ?TW"
	            by (rule top1_open_set_from_local_opens[OF hTopW hPsub hlocal])
	          show "{t \<in> ?W. ?inv t \<in> b} \<in> ?TW"
	            unfolding P_def[symmetric] using hP_open .
        qed
      qed
    qed

    have cont_pi1A: "top1_continuous_map_on ?A ?TA ?R ?TR pi1"
    proof -
      have cont_pi1X: "top1_continuous_map_on ?X ?TP ?R ?TR pi1"
        by (rule top1_continuous_pi1[OF hTopR hTopR])
      have hRule:
        "\<forall>A f. top1_continuous_map_on ?X ?TP ?R ?TR f \<and> A \<subseteq> ?X
               \<longrightarrow> top1_continuous_map_on A (subspace_topology ?X ?TP A) ?R ?TR f"
        by (rule Theorem_18_2(4)[OF hTopX hTopR hTopR])
      show ?thesis
        using hRule cont_pi1X by simp
    qed

    have cont_pi2A_toW: "top1_continuous_map_on ?A ?TA ?W ?TW pi2"
    proof -
      have cont_pi2X: "top1_continuous_map_on ?X ?TP ?R ?TR pi2"
        by (rule top1_continuous_pi2[OF hTopR hTopR])
      have hRuleD:
        "\<forall>A f. top1_continuous_map_on ?X ?TP ?R ?TR f \<and> A \<subseteq> ?X
               \<longrightarrow> top1_continuous_map_on A (subspace_topology ?X ?TP A) ?R ?TR f"
        by (rule Theorem_18_2(4)[OF hTopX hTopR hTopR])
	      have cont_pi2A: "top1_continuous_map_on ?A ?TA ?R ?TR pi2"
	        using hRuleD cont_pi2X by simp
	      have hpi2img: "pi2 ` ?A \<subseteq> ?W"
	      proof (rule subsetI)
	        fix y assume hy: "y \<in> pi2 ` ?A"
	        then obtain p where hpA: "p \<in> ?A" and hyEq: "y = pi2 p"
	          by blast
	        obtain a b where hp: "p = (a,b)" and hb0: "b \<noteq> 0"
	          using hpA by auto
	        have "y = b"
	          unfolding hyEq hp by (simp add: pi2_def)
	        thus "y \<in> ?W"
	          using hb0 by simp
	      qed
      have hRuleR:
        "\<forall>W f. top1_continuous_map_on ?A ?TA ?R ?TR f \<and> W \<subseteq> ?R \<and> f ` ?A \<subseteq> W
               \<longrightarrow> top1_continuous_map_on ?A ?TA W (subspace_topology ?R ?TR W) f"
        by (rule Theorem_18_2(5)[OF hTopA hTopR hTopR])
      show ?thesis
        using hRuleR cont_pi2A hpi2img by simp
    qed

    have cont_inv_pi2A: "top1_continuous_map_on ?A ?TA ?R ?TR (?inv \<circ> pi2)"
      by (rule top1_continuous_map_on_comp[OF cont_pi2A_toW cont_inv_nonzero])

    have cont_pairinv:
      "top1_continuous_map_on ?A ?TA (?R \<times> ?R) ?TP ?pairinv"
    proof -
      have hiff:
        "top1_continuous_map_on ?A ?TA (?R \<times> ?R) ?TP ?pairinv
         \<longleftrightarrow>
           (top1_continuous_map_on ?A ?TA ?R ?TR (pi1 \<circ> ?pairinv)
            \<and> top1_continuous_map_on ?A ?TA ?R ?TR (pi2 \<circ> ?pairinv))"
        by (rule Theorem_18_4[OF hTopA hTopR hTopR])

      have hpi1pair: "top1_continuous_map_on ?A ?TA ?R ?TR (pi1 \<circ> ?pairinv)"
      proof -
        have hEq: "(pi1 \<circ> ?pairinv) = pi1"
          by (rule ext, simp add: o_def pi1_def)
        show ?thesis
          unfolding hEq by (rule cont_pi1A)
      qed
      have hpi2pair: "top1_continuous_map_on ?A ?TA ?R ?TR (pi2 \<circ> ?pairinv)"
      proof -
        have hEq: "(pi2 \<circ> ?pairinv) = ?inv \<circ> pi2"
          by (rule ext, simp add: o_def pi2_def)
        show ?thesis
          unfolding hEq by (rule cont_inv_pi2A)
      qed

      show ?thesis
        apply (rule iffD2[OF hiff])
        apply (intro conjI)
         apply (rule hpi1pair)
        apply (rule hpi2pair)
        done
    qed

	    have cont_mul_on_pair: "top1_continuous_map_on ?A ?TA ?R ?TR (?mul \<circ> ?pairinv)"
	      by (rule top1_continuous_map_on_comp[OF cont_pairinv cont_mul])

	    have hEq: "(\<lambda>p::real \<times> real. pi1 p / pi2 p) = ?mul \<circ> ?pairinv"
	    proof (rule ext)
	      fix p :: "real \<times> real"
	      show "pi1 p / pi2 p = (?mul \<circ> ?pairinv) p"
	        by (simp add: o_def pi1_def pi2_def divide_inverse)
	    qed
	    show ?thesis
	      unfolding hEq by (rule cont_mul_on_pair)
	  qed

  show "top1_continuous_map_on (UNIV \<times> UNIV) (product_topology_on TR TR) UNIV TR (\<lambda>p. pi1 p + pi2 p)"
    using cont_add .
  show "top1_continuous_map_on (UNIV \<times> UNIV) (product_topology_on TR TR) UNIV TR (\<lambda>p. pi1 p - pi2 p)"
    using cont_sub .
  show "top1_continuous_map_on (UNIV \<times> UNIV) (product_topology_on TR TR) UNIV TR (\<lambda>p. pi1 p * pi2 p)"
    using cont_mul .
  show "top1_continuous_map_on (UNIV \<times> (UNIV - {0::real}))
          (subspace_topology (UNIV \<times> UNIV) (product_topology_on TR TR) (UNIV \<times> (UNIV - {0::real})))
          UNIV TR (\<lambda>p. pi1 p / pi2 p)"
    using cont_div .
qed

(** from \S21 Theorem 21.5 (Algebra of continuous real-valued functions) [top1.tex:2030] **)
theorem Theorem_21_5:
  fixes f g :: "'a \<Rightarrow> real"
  defines "TR \<equiv> (order_topology_on_UNIV::real set set)"
  assumes hTX: "is_topology_on X TX"
  assumes hf: "top1_continuous_map_on X TX UNIV TR f"
  assumes hg: "top1_continuous_map_on X TX UNIV TR g"
  shows "top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x + g x)"
    and "top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x - g x)"
    and "top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x * g x)"
    and "(\<forall>x\<in>X. g x \<noteq> 0) \<longrightarrow> top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x / g x)"
proof -
  let ?R = "(UNIV::real set)"
  let ?TR = "TR"
  let ?TP = "product_topology_on ?TR ?TR"
  let ?X2 = "?R \<times> ?R"
  let ?W = "?R \<times> (?R - {0::real})"

  have hTopR: "is_topology_on ?R ?TR"
    unfolding TR_def by (rule order_topology_on_UNIV_is_topology_on)
  have hTopX2: "is_topology_on ?X2 ?TP"
    by (rule product_topology_on_is_topology_on[OF hTopR hTopR])

  define pairfg where "pairfg = (\<lambda>x. (f x, g x))"

  have cont_pairfg: "top1_continuous_map_on X TX ?X2 ?TP pairfg"
  proof -
    have hiff:
      "top1_continuous_map_on X TX ?X2 ?TP pairfg
       \<longleftrightarrow>
         (top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> pairfg)
          \<and> top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> pairfg))"
      by (rule Theorem_18_4[OF hTX hTopR hTopR])

    have hpi1: "top1_continuous_map_on X TX ?R ?TR (pi1 \<circ> pairfg)"
    proof -
      have hEq: "(pi1 \<circ> pairfg) = f"
        unfolding pairfg_def
        by (rule ext, simp add: o_def pi1_def)
      show ?thesis
        unfolding hEq by (rule hf)
    qed

    have hpi2: "top1_continuous_map_on X TX ?R ?TR (pi2 \<circ> pairfg)"
    proof -
      have hEq: "(pi2 \<circ> pairfg) = g"
        unfolding pairfg_def
        by (rule ext, simp add: o_def pi2_def)
      show ?thesis
        unfolding hEq by (rule hg)
    qed

    show ?thesis
      apply (rule iffD2[OF hiff])
      apply (intro conjI)
       apply (rule hpi1)
      apply (rule hpi2)
      done
  qed

  have cont_add_op:
    "top1_continuous_map_on ?X2 ?TP ?R ?TR (\<lambda>p. pi1 p + pi2 p)"
    unfolding TR_def
    using Lemma_21_4(1)[unfolded TR_def]
    by assumption
  have cont_sub_op:
    "top1_continuous_map_on ?X2 ?TP ?R ?TR (\<lambda>p. pi1 p - pi2 p)"
    unfolding TR_def
    using Lemma_21_4(2)[unfolded TR_def]
    by assumption
  have cont_mul_op:
    "top1_continuous_map_on ?X2 ?TP ?R ?TR (\<lambda>p. pi1 p * pi2 p)"
    unfolding TR_def
    using Lemma_21_4(3)[unfolded TR_def]
    by assumption

  have cont_add: "top1_continuous_map_on X TX ?R ?TR (\<lambda>x. f x + g x)"
  proof -
    have hEq: "(\<lambda>x. f x + g x) = (\<lambda>p. pi1 p + pi2 p) \<circ> pairfg"
      unfolding pairfg_def by (rule ext, simp add: o_def pi1_def pi2_def)
    show ?thesis
      unfolding hEq by (rule top1_continuous_map_on_comp[OF cont_pairfg cont_add_op])
  qed

  have cont_sub: "top1_continuous_map_on X TX ?R ?TR (\<lambda>x. f x - g x)"
  proof -
    have hEq: "(\<lambda>x. f x - g x) = (\<lambda>p. pi1 p - pi2 p) \<circ> pairfg"
      unfolding pairfg_def by (rule ext, simp add: o_def pi1_def pi2_def)
    show ?thesis
      unfolding hEq by (rule top1_continuous_map_on_comp[OF cont_pairfg cont_sub_op])
  qed

  have cont_mul: "top1_continuous_map_on X TX ?R ?TR (\<lambda>x. f x * g x)"
  proof -
    have hEq: "(\<lambda>x. f x * g x) = (\<lambda>p. pi1 p * pi2 p) \<circ> pairfg"
      unfolding pairfg_def by (rule ext, simp add: o_def pi1_def pi2_def)
    show ?thesis
      unfolding hEq by (rule top1_continuous_map_on_comp[OF cont_pairfg cont_mul_op])
  qed

  have cont_div_imp:
    "(\<forall>x\<in>X. g x \<noteq> 0) \<longrightarrow> top1_continuous_map_on X TX ?R ?TR (\<lambda>x. f x / g x)"
  proof (intro impI)
    assume hne: "\<forall>x\<in>X. g x \<noteq> 0"

    have hWsub: "?W \<subseteq> ?X2"
      by simp

    have himg: "pairfg ` X \<subseteq> ?W"
    proof (rule subsetI)
      fix y assume hy: "y \<in> pairfg ` X"
      then obtain x where hx: "x \<in> X" and hyEq: "y = pairfg x"
        by blast
      have hgx0: "g x \<noteq> 0"
        using hne hx by blast
      show "y \<in> ?W"
        unfolding hyEq pairfg_def using hgx0 by simp
    qed

    have cont_pairfg_toW:
      "top1_continuous_map_on X TX ?W (subspace_topology ?X2 ?TP ?W) pairfg"
    proof -
      have hRuleR:
        "\<forall>W f. top1_continuous_map_on X TX ?X2 ?TP f \<and> W \<subseteq> ?X2 \<and> f ` X \<subseteq> W
               \<longrightarrow> top1_continuous_map_on X TX W (subspace_topology ?X2 ?TP W) f"
        by (rule Theorem_18_2(5)[OF hTX hTopX2 hTopX2])
      show ?thesis
        using hRuleR cont_pairfg hWsub himg by simp
    qed

    have cont_div_op:
      "top1_continuous_map_on ?W (subspace_topology ?X2 ?TP ?W) ?R ?TR (\<lambda>p. pi1 p / pi2 p)"
      unfolding TR_def
      using Lemma_21_4(4)[unfolded TR_def]
      by assumption

    have hEq: "(\<lambda>x. f x / g x) = (\<lambda>p. pi1 p / pi2 p) \<circ> pairfg"
      unfolding pairfg_def by (rule ext, simp add: o_def pi1_def pi2_def)
    show "top1_continuous_map_on X TX ?R ?TR (\<lambda>x. f x / g x)"
      unfolding hEq by (rule top1_continuous_map_on_comp[OF cont_pairfg_toW cont_div_op])
  qed

  show "top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x + g x)"
    using cont_add .
  show "top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x - g x)"
    using cont_sub .
  show "top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x * g x)"
    using cont_mul .
  show "(\<forall>x\<in>X. g x \<noteq> 0) \<longrightarrow> top1_continuous_map_on X TX UNIV TR (\<lambda>x. f x / g x)"
    using cont_div_imp .
qed

(** Uniform convergence on a set (metric-valued targets). **)
definition top1_uniformly_convergent_on ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
  "top1_uniformly_convergent_on X Y d fn f \<longleftrightarrow>
     (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>X. d (fn n x) (f x) < \<epsilon>)"

(** from \S21 Theorem 21.6 (Uniform limit theorem) [top1.tex:2054] **)
theorem Theorem_21_6:
  assumes hTX: "is_topology_on X TX"
  assumes hdY: "top1_metric_on Y dY"
  assumes hfn: "\<forall>n. top1_continuous_map_on X TX Y (top1_metric_topology_on Y dY) (fn n)"
  assumes hunif: "top1_uniformly_convergent_on X Y dY fn f"
  assumes hmap: "\<forall>x\<in>X. f x \<in> Y"
  shows "top1_continuous_map_on X TX Y (top1_metric_topology_on Y dY) f"
proof -
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> (\<Union>U) \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])
  have empty_TX: "{} \<in> TX"
    using hTX unfolding is_topology_on_def by blast

  have hBasisY: "basis_for Y (top1_metric_basis_on Y dY) (top1_metric_topology_on Y dY)"
    unfolding basis_for_def top1_metric_topology_on_def
    by (intro conjI, rule top1_metric_basis_is_basis_on[OF hdY], rule refl)

  have hpre: "\<forall>b\<in>top1_metric_basis_on Y dY. {x\<in>X. f x \<in> b} \<in> TX"
  proof (intro ballI)
    fix b assume hb: "b \<in> top1_metric_basis_on Y dY"
    obtain y0 e where hbdef: "b = top1_ball_on Y dY y0 e" and hy0: "y0 \<in> Y" and he: "0 < e"
      using hb unfolding top1_metric_basis_on_def by blast

    define P where "P = {x\<in>X. f x \<in> b}"
    have hPsub: "P \<subseteq> X"
      unfolding P_def by blast

    have hlocal: "\<forall>x\<in>P. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> P"
	    proof (intro ballI)
	      fix x assume hxP: "x \<in> P"
	      have hxX: "x \<in> X" and hfxb: "f x \<in> b"
	      proof -
	        have hx_conj: "x \<in> X \<and> f x \<in> b"
	          using hxP unfolding P_def by simp
	        show "x \<in> X"
	          using hx_conj by (rule conjunct1)
	        show "f x \<in> b"
	          using hx_conj by (rule conjunct2)
	      qed
	      have hfxY: "f x \<in> Y"
	        using hmap hxX by blast
	      have hdist_fx: "dY y0 (f x) < e"
	        using hfxb unfolding hbdef top1_ball_on_def by simp

      define m where "m = e - dY y0 (f x)"
      have hmpos: "0 < m"
        using hdist_fx unfolding m_def by linarith
      define eps where "eps = m / 3"
      have hepspos: "0 < eps"
        using hmpos unfolding eps_def by (simp add: divide_pos_pos)

      obtain N where hN: "\<forall>n\<ge>N. \<forall>z\<in>X. dY (fn n z) (f z) < eps"
        using hunif hepspos unfolding top1_uniformly_convergent_on_def by blast
      have hNspec: "\<forall>z\<in>X. dY (fn N z) (f z) < eps"
        using hN by simp

      have hfnN: "top1_continuous_map_on X TX Y (top1_metric_topology_on Y dY) (fn N)"
        using hfn by simp
      have hfnN_map: "\<forall>z\<in>X. fn N z \<in> Y"
        using hfnN unfolding top1_continuous_map_on_def by blast

      have hfnNxY: "fn N x \<in> Y"
        using hfnN_map hxX by blast

      define W where "W = top1_ball_on Y dY (fn N x) eps"
      have hW_open: "W \<in> top1_metric_topology_on Y dY"
        unfolding W_def by (rule top1_ball_open_in_metric_topology[OF hdY hfnNxY hepspos])

      define U where "U = {z\<in>X. fn N z \<in> W}"
      have hU_TX: "U \<in> TX"
      proof -
        have hpreN: "\<forall>V\<in>top1_metric_topology_on Y dY. {z\<in>X. fn N z \<in> V} \<in> TX"
          using hfnN unfolding top1_continuous_map_on_def by blast
        show ?thesis
          unfolding U_def using hpreN hW_open by blast
      qed

      have hxU: "x \<in> U"
      proof -
        have h0: "dY (fn N x) (fn N x) = 0"
        proof -
          have h0iff: "dY (fn N x) (fn N x) = 0 \<longleftrightarrow> (fn N x) = (fn N x)"
            using hdY hfnNxY unfolding top1_metric_on_def by blast
          show ?thesis
            using h0iff by simp
        qed
        have hdist0: "dY (fn N x) (fn N x) < eps"
          using hepspos h0 by simp
        have hfnNxW: "fn N x \<in> W"
          unfolding W_def top1_ball_on_def using hfnNxY hdist0 by simp
        show ?thesis
          unfolding U_def using hxX hfnNxW by simp
      qed

      have hUsubP: "U \<subseteq> P"
	      proof (rule subsetI)
	        fix u assume huU: "u \<in> U"
	        have huX: "u \<in> X" and hfnNuW: "fn N u \<in> W"
	        proof -
	          have hu_conj: "u \<in> X \<and> fn N u \<in> W"
	            using huU unfolding U_def by simp
	          show "u \<in> X"
	            using hu_conj by (rule conjunct1)
	          show "fn N u \<in> W"
	            using hu_conj by (rule conjunct2)
	        qed
	        have hfuY: "f u \<in> Y"
	          using hmap huX by blast
	        have hfnNuY: "fn N u \<in> Y"
	          using hfnN_map huX by blast

        have hdist_u: "dY (fn N u) (f u) < eps"
          using hNspec huX by blast
        have hdist_x: "dY (fn N x) (f x) < eps"
          using hNspec hxX by blast
        have hdist_fn: "dY (fn N x) (fn N u) < eps"
          using hfnNuW unfolding W_def top1_ball_on_def by simp

        have hsym_x: "dY (f x) (fn N x) = dY (fn N x) (f x)"
          using hdY hfxY hfnNxY unfolding top1_metric_on_def by blast
        have hsym_u: "dY (fn N u) (f u) = dY (f u) (fn N u)"
          using hdY hfnNuY hfuY unfolding top1_metric_on_def by blast
        have hsym_fn: "dY (fn N x) (fn N u) = dY (fn N u) (fn N x)"
          using hdY hfnNxY hfnNuY unfolding top1_metric_on_def by blast

        have htri_y0: "dY y0 (f u) \<le> dY y0 (f x) + dY (f x) (f u)"
          using hdY hy0 hfxY hfuY unfolding top1_metric_on_def by blast
        have htri_fx: "dY (f x) (f u) \<le> dY (f x) (fn N x) + dY (fn N x) (f u)"
          using hdY hfxY hfnNxY hfuY unfolding top1_metric_on_def by blast
        have htri_mid: "dY (fn N x) (f u) \<le> dY (fn N x) (fn N u) + dY (fn N u) (f u)"
          using hdY hfnNxY hfnNuY hfuY unfolding top1_metric_on_def by blast

	        have hbound_fx_fu: "dY (f x) (f u) < eps + eps + eps"
	        proof -
	          have h1: "dY (f x) (f u) \<le> dY (f x) (fn N x) + (dY (fn N x) (fn N u) + dY (fn N u) (f u))"
	          proof -
	            have "dY (f x) (f u) \<le> dY (f x) (fn N x) + dY (fn N x) (f u)"
	              by (rule htri_fx)
	            also have "... \<le> dY (f x) (fn N x) + (dY (fn N x) (fn N u) + dY (fn N u) (f u))"
	              by (rule add_left_mono[OF htri_mid])
	            finally show ?thesis
	              by (simp add: add.assoc)
	          qed
	          have h2: "dY (f x) (fn N x) < eps"
	            using hdist_x hsym_x by simp
	          have h3: "dY (fn N x) (fn N u) < eps"
	            using hdist_fn by simp
	          have h4: "dY (fn N u) (f u) < eps"
	            using hdist_u by simp
	          have hsum: "dY (f x) (fn N x) + (dY (fn N x) (fn N u) + dY (fn N u) (f u)) < eps + eps + eps"
	            using h2 h3 h4 by linarith
	          show ?thesis
	            by (rule le_less_trans[OF h1 hsum])
	        qed

	        have hdist_y0_fu: "dY y0 (f u) < e"
	        proof -
	          have hstep:
	            "dY y0 (f x) + dY (f x) (f u) < dY y0 (f x) + (eps + eps + eps)"
	            by (rule add_strict_left_mono[OF hbound_fx_fu])
	          have "dY y0 (f u) < dY y0 (f x) + (eps + eps + eps)"
	            by (rule le_less_trans[OF htri_y0 hstep])
	          also have "... = dY y0 (f x) + m"
	            unfolding eps_def by simp
	          also have "... = e"
	            unfolding m_def by simp
	          finally show ?thesis .
	        qed

        have hfu_in_b: "f u \<in> b"
          unfolding hbdef top1_ball_on_def using hfuY hdist_y0_fu by simp
        show "u \<in> P"
          unfolding P_def using huX hfu_in_b by simp
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
      unfolding UP_def by blast
    have hUnionUP: "\<Union>UP \<in> TX"
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

    show "{x\<in>X. f x \<in> b} \<in> TX"
      unfolding P_def[symmetric] hEq using hUnionUP by simp
  qed

  show ?thesis
    by (rule top1_continuous_map_on_generated_by_basis[OF hTX hBasisY hmap hpre])
qed

section \<open>\<S>22 The Quotient Topology\<close>

text \<open>
  Section \<S>22 of \<open>top1.tex\<close> introduces the quotient topology and its universal property.
  We formalize quotient maps in a way compatible with the set-based topological framework used
  throughout this theory.
\<close>

(** from \S22 Definition (Quotient map) [top1.tex:~2320] **)
definition top1_quotient_map_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_quotient_map_on X TX Y TY p \<longleftrightarrow>
     is_topology_on X TX \<and>
     is_topology_on Y TY \<and>
     top1_continuous_map_on X TX Y TY p \<and>
     (p ` X = Y) \<and>
     (\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. p x \<in> V} \<in> TX \<longrightarrow> V \<in> TY))"

(** from \S22 Definition (Saturated set w.r.t. a map) [top1.tex:~2380] **)
definition top1_saturated_with_respect_to_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_saturated_with_respect_to_on X p A \<longleftrightarrow>
     A \<subseteq> X \<and> (\<forall>x\<in>A. \<forall>y\<in>X. p y = p x \<longrightarrow> y \<in> A)"

(** Open / closed maps (restricted to the carrier). **)
definition top1_open_map_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_open_map_on X TX Y TY f \<longleftrightarrow>
     (\<forall>x\<in>X. f x \<in> Y) \<and> (\<forall>U. U \<in> TX \<and> U \<subseteq> X \<longrightarrow> f ` U \<in> TY)"

definition top1_closed_map_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_closed_map_on X TX Y TY f \<longleftrightarrow>
     (\<forall>x\<in>X. f x \<in> Y) \<and> (\<forall>A. closedin_on X TX A \<longrightarrow> closedin_on Y TY (f ` A))"

lemma top1_saturated_preimage_subset:
  assumes hsat: "top1_saturated_with_respect_to_on X p A"
  assumes hV: "V \<subseteq> p ` A"
  shows "{x\<in>X. p x \<in> V} \<subseteq> A"
proof (rule subsetI)
  fix x assume hx: "x \<in> {x \<in> X. p x \<in> V}"
  have hx_conj: "x \<in> X \<and> p x \<in> V"
    using hx by simp
  have hxX: "x \<in> X"
    using hx_conj by (rule conjunct1)
  have hpxV: "p x \<in> V"
    using hx_conj by (rule conjunct2)
  have hAX: "A \<subseteq> X"
    using hsat unfolding top1_saturated_with_respect_to_on_def by blast
  have hprop: "\<forall>a\<in>A. \<forall>y\<in>X. p y = p a \<longrightarrow> y \<in> A"
    using hsat unfolding top1_saturated_with_respect_to_on_def by blast
  have "p x \<in> p ` A"
    using hV hpxV by blast
  then obtain a where haA: "a \<in> A" and hpa: "p x = p a"
    by blast
  show "x \<in> A"
    using hprop haA hxX hpa by blast
qed

lemma top1_saturated_restrict_preimage_eq:
  assumes hsat: "top1_saturated_with_respect_to_on X p A"
  assumes hV: "V \<subseteq> p ` A"
  shows "{x\<in>A. p x \<in> V} = {x\<in>X. p x \<in> V}"
proof (rule equalityI)
  show "{x \<in> A. p x \<in> V} \<subseteq> {x \<in> X. p x \<in> V}"
  proof (rule subsetI)
    fix x assume hx: "x \<in> {x \<in> A. p x \<in> V}"
    have hx_conj: "x \<in> A \<and> p x \<in> V"
      using hx by simp
    have hxA: "x \<in> A"
      using hx_conj by (rule conjunct1)
    have hpxV: "p x \<in> V"
      using hx_conj by (rule conjunct2)
    have hAX: "A \<subseteq> X"
      using hsat unfolding top1_saturated_with_respect_to_on_def by blast
    have hxX: "x \<in> X"
      using hAX hxA by blast
    show "x \<in> {x \<in> X. p x \<in> V}"
      using hxX hpxV by simp
  qed
  show "{x \<in> X. p x \<in> V} \<subseteq> {x \<in> A. p x \<in> V}"
  proof (rule subsetI)
    fix x assume hx: "x \<in> {x \<in> X. p x \<in> V}"
    have hx_conj: "x \<in> X \<and> p x \<in> V"
      using hx by simp
    have hxX: "x \<in> X"
      using hx_conj by (rule conjunct1)
    have hpxV: "p x \<in> V"
      using hx_conj by (rule conjunct2)
    have hxA: "x \<in> A"
      using top1_saturated_preimage_subset[OF hsat hV] hx by blast
    show "x \<in> {x \<in> A. p x \<in> V}"
      using hxA hpxV by simp
  qed
qed

lemma top1_saturated_image_inter_eq:
  assumes hsat: "top1_saturated_with_respect_to_on X p A"
  assumes hU: "U \<subseteq> X"
  shows "p ` (U \<inter> A) = (p ` U) \<inter> (p ` A)"
proof (rule equalityI)
  show "p ` (U \<inter> A) \<subseteq> p ` U \<inter> p ` A"
    by blast
  show "p ` U \<inter> p ` A \<subseteq> p ` (U \<inter> A)"
  proof (rule subsetI)
    fix y assume hy: "y \<in> p ` U \<inter> p ` A"
    obtain u where huU: "u \<in> U" and hyu: "y = p u"
      using hy by blast
    obtain a where haA: "a \<in> A" and hya: "y = p a"
      using hy by blast
    have huX: "u \<in> X"
      using hU huU by blast
    have hAX: "A \<subseteq> X"
      using hsat unfolding top1_saturated_with_respect_to_on_def by blast
    have hprop: "\<forall>x\<in>A. \<forall>z\<in>X. p z = p x \<longrightarrow> z \<in> A"
      using hsat unfolding top1_saturated_with_respect_to_on_def by blast
    have "p u = p a"
      using hyu hya by simp
    have huA: "u \<in> A"
      using hprop haA huX \<open>p u = p a\<close> by blast
    have "u \<in> U \<inter> A"
      using huU huA by blast
    thus "y \<in> p ` (U \<inter> A)"
      using hyu by blast
  qed
qed

lemma top1_quotient_map_closed_iff_preimage_closed:
  assumes hp: "top1_quotient_map_on X TX Y TY p"
  assumes hC: "C \<subseteq> Y"
  shows "closedin_on Y TY C \<longleftrightarrow> closedin_on X TX {x\<in>X. p x \<in> C}"
proof (rule iffI)
  assume hclY: "closedin_on Y TY C"
  have hTopX: "is_topology_on X TX"
    using hp unfolding top1_quotient_map_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hp unfolding top1_quotient_map_on_def by blast
  have hcont: "top1_continuous_map_on X TX Y TY p"
    using hp unfolding top1_quotient_map_on_def by blast
  have hmap: "\<forall>x\<in>X. p x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hopenY: "Y - C \<in> TY"
    using hclY unfolding closedin_on_def by blast
  have hopenX: "{x \<in> X. p x \<in> Y - C} \<in> TX"
    using hcont hopenY unfolding top1_continuous_map_on_def by blast
  have hEq: "X - {x \<in> X. p x \<in> C} = {x \<in> X. p x \<in> Y - C}"
  proof (rule set_eqI)
    fix x
    show "x \<in> X - {x \<in> X. p x \<in> C} \<longleftrightarrow> x \<in> {x \<in> X. p x \<in> Y - C}"
    proof
      assume hx: "x \<in> X - {x \<in> X. p x \<in> C}"
      have hxX: "x \<in> X" and hpxnC: "p x \<notin> C"
        using hx by blast+
      have hpxY: "p x \<in> Y"
        using hmap hxX by blast
      show "x \<in> {x \<in> X. p x \<in> Y - C}"
        using hxX hpxY hpxnC by blast
    next
      assume hx: "x \<in> {x \<in> X. p x \<in> Y - C}"
      have hxX: "x \<in> X" and hpxY: "p x \<in> Y" and hpxnC: "p x \<notin> C"
        using hx by blast+
      show "x \<in> X - {x \<in> X. p x \<in> C}"
        using hxX hpxnC by blast
    qed
  qed
  show "closedin_on X TX {x \<in> X. p x \<in> C}"
    unfolding closedin_on_def
    apply (intro conjI)
     apply blast
    apply (subst hEq)
    apply (rule hopenX)
    done
next
  assume hclX: "closedin_on X TX {x \<in> X. p x \<in> C}"
  have hTopX: "is_topology_on X TX"
    using hp unfolding top1_quotient_map_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hp unfolding top1_quotient_map_on_def by blast
  have hcont: "top1_continuous_map_on X TX Y TY p"
    using hp unfolding top1_quotient_map_on_def by blast
  have hmap: "\<forall>x\<in>X. p x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast

  have hpre_open: "{x \<in> X. p x \<in> Y - C} \<in> TX"
  proof -
    have hcomp: "X - {x \<in> X. p x \<in> C} \<in> TX"
      using hclX unfolding closedin_on_def by blast
    have hEq: "{x \<in> X. p x \<in> Y - C} = X - {x \<in> X. p x \<in> C}"
    proof (rule set_eqI)
      fix x
      show "x \<in> {x \<in> X. p x \<in> Y - C} \<longleftrightarrow> x \<in> X - {x \<in> X. p x \<in> C}"
      proof
        assume hx: "x \<in> {x \<in> X. p x \<in> Y - C}"
        have hxX: "x \<in> X" and hpxY: "p x \<in> Y" and hpxnC: "p x \<notin> C"
          using hx by blast+
        show "x \<in> X - {x \<in> X. p x \<in> C}"
          using hxX hpxnC by blast
      next
        assume hx: "x \<in> X - {x \<in> X. p x \<in> C}"
        have hxX: "x \<in> X" and hpxnC: "p x \<notin> C"
          using hx by blast+
        have hpxY: "p x \<in> Y"
          using hmap hxX by blast
        show "x \<in> {x \<in> X. p x \<in> Y - C}"
          using hxX hpxY hpxnC by blast
      qed
    qed
    show ?thesis
      by (subst hEq) (rule hcomp)
  qed

  have hQ: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. p x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
    using hp unfolding top1_quotient_map_on_def by blast
  have hopenY: "Y - C \<in> TY"
    using hQ hC hpre_open by blast
  show "closedin_on Y TY C"
    unfolding closedin_on_def
    using hC hopenY by blast
qed

lemma top1_quotient_map_open_iff_preimage_open:
  assumes hp: "top1_quotient_map_on X TX Y TY p"
  assumes hV: "V \<subseteq> Y"
  shows "V \<in> TY \<longleftrightarrow> {x\<in>X. p x \<in> V} \<in> TX"
proof (rule iffI)
  assume hVT: "V \<in> TY"
  have hcont: "top1_continuous_map_on X TX Y TY p"
    using hp unfolding top1_quotient_map_on_def by blast
  show "{x\<in>X. p x \<in> V} \<in> TX"
    using hcont hVT unfolding top1_continuous_map_on_def by blast
next
  assume hpre: "{x\<in>X. p x \<in> V} \<in> TX"
  have hQ: "\<forall>W. W \<subseteq> Y \<longrightarrow> ({x\<in>X. p x \<in> W} \<in> TX \<longrightarrow> W \<in> TY)"
    using hp unfolding top1_quotient_map_on_def by blast
  show "V \<in> TY"
    using hQ hV hpre by blast
qed

lemma top1_saturated_preimage_image_eq:
  assumes hsat: "top1_saturated_with_respect_to_on X p A"
  shows "{x\<in>X. p x \<in> p ` A} = A"
proof (rule equalityI)
  have hAX: "A \<subseteq> X"
    using hsat unfolding top1_saturated_with_respect_to_on_def by blast
  show "{x \<in> X. p x \<in> p ` A} \<subseteq> A"
  proof (rule subsetI)
    fix x assume hx: "x \<in> {x \<in> X. p x \<in> p ` A}"
    have hxX: "x \<in> X" and hpx: "p x \<in> p ` A"
    proof -
      have hx_conj: "x \<in> X \<and> p x \<in> p ` A"
        using hx by simp
      show "x \<in> X"
        using hx_conj by (rule conjunct1)
      show "p x \<in> p ` A"
        using hx_conj by (rule conjunct2)
    qed
    obtain a where haA: "a \<in> A" and hpa: "p x = p a"
      using hpx by blast
    have hprop: "\<forall>x\<in>A. \<forall>y\<in>X. p y = p x \<longrightarrow> y \<in> A"
      using hsat unfolding top1_saturated_with_respect_to_on_def by blast
    show "x \<in> A"
      using hprop haA hxX hpa by blast
  qed
  show "A \<subseteq> {x \<in> X. p x \<in> p ` A}"
  proof (rule subsetI)
    fix a assume haA: "a \<in> A"
    have haX: "a \<in> X"
      using hAX haA by blast
    have "p a \<in> p ` A"
      using haA by blast
    show "a \<in> {x \<in> X. p x \<in> p ` A}"
      using haX \<open>p a \<in> p ` A\<close> by simp
  qed
qed

(** from \S22 Theorem 22.1 (Restriction to saturated subspace) [top1.tex:2395] **)
theorem Theorem_22_1:
  assumes hp: "top1_quotient_map_on X TX Y TY p"
  assumes hsat: "top1_saturated_with_respect_to_on X p A"
  shows
    "(openin_on X TX A \<or> closedin_on X TX A)
        \<longrightarrow> top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
    and
    "((top1_open_map_on X TX Y TY p \<or> top1_closed_map_on X TX Y TY p)
        \<longrightarrow> top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p)"
proof -
  have hTopX: "is_topology_on X TX"
    using hp unfolding top1_quotient_map_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hp unfolding top1_quotient_map_on_def by blast
  have hcont: "top1_continuous_map_on X TX Y TY p"
    using hp unfolding top1_quotient_map_on_def by blast
  have hsurj: "p ` X = Y"
    using hp unfolding top1_quotient_map_on_def by blast
  have hQ: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. p x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
    using hp unfolding top1_quotient_map_on_def by blast
  have hmap: "\<forall>x\<in>X. p x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hAX: "A \<subseteq> X"
    using hsat unfolding top1_saturated_with_respect_to_on_def by blast
  have hpA_sub: "p ` A \<subseteq> Y"
    using hmap hAX by blast

  have hTopA: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF hTopX hAX])
  have hToppA: "is_topology_on (p ` A) (subspace_topology Y TY (p ` A))"
    by (rule subspace_topology_is_topology_on[OF hTopY hpA_sub])

  have hcont_restrict:
    "top1_continuous_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
  proof -
    have hRestrDom:
      "\<forall>A' f. top1_continuous_map_on X TX Y TY f \<and> A' \<subseteq> X
             \<longrightarrow> top1_continuous_map_on A' (subspace_topology X TX A') Y TY f"
      by (rule Theorem_18_2(4)[OF hTopX hTopY hTopY])
    have hRestrRan:
      "\<forall>W f. top1_continuous_map_on A (subspace_topology X TX A) Y TY f \<and> W \<subseteq> Y \<and> f ` A \<subseteq> W
             \<longrightarrow> top1_continuous_map_on A (subspace_topology X TX A) W (subspace_topology Y TY W) f"
      by (rule Theorem_18_2(5)[OF hTopA hTopY hTopY])

    have hcontA_Y: "top1_continuous_map_on A (subspace_topology X TX A) Y TY p"
      using hRestrDom hcont hAX by blast
    have "top1_continuous_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
      using hRestrRan hcontA_Y hpA_sub by blast
    thus ?thesis .
  qed

  have hquotient_core:
    "(\<And>V. V \<subseteq> p ` A \<Longrightarrow> {x\<in>A. p x \<in> V} \<in> subspace_topology X TX A \<Longrightarrow> V \<in> subspace_topology Y TY (p ` A))
      \<Longrightarrow> top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
  proof -
    assume hQuot: "\<And>V. V \<subseteq> p ` A \<Longrightarrow> {x\<in>A. p x \<in> V} \<in> subspace_topology X TX A \<Longrightarrow> V \<in> subspace_topology Y TY (p ` A)"
    show "top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
      unfolding top1_quotient_map_on_def
    proof (intro conjI)
      show "is_topology_on A (subspace_topology X TX A)"
        by (rule hTopA)
      show "is_topology_on (p ` A) (subspace_topology Y TY (p ` A))"
        by (rule hToppA)
      show "top1_continuous_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
        by (rule hcont_restrict)
      show "p ` A = p ` A"
        by simp
      show "\<forall>V. V \<subseteq> p ` A \<longrightarrow> ({x \<in> A. p x \<in> V} \<in> subspace_topology X TX A \<longrightarrow> V \<in> subspace_topology Y TY (p ` A))"
        using hQuot by blast
    qed
  qed

  show "(openin_on X TX A \<or> closedin_on X TX A)
        \<longrightarrow> top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
  proof (intro impI)
    assume hA: "openin_on X TX A \<or> closedin_on X TX A"
    show "top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
    proof (rule hquotient_core)
      fix V assume hV: "V \<subseteq> p ` A"
      assume hpreA: "{x \<in> A. p x \<in> V} \<in> subspace_topology X TX A"

      show "V \<in> subspace_topology Y TY (p ` A)"
      proof (cases "openin_on X TX A")
        case True
        have hAopen: "A \<in> TX"
          using True unfolding openin_on_def by simp
        obtain U where hU: "U \<in> TX" and hEq: "{x \<in> A. p x \<in> V} = A \<inter> U"
          using hpreA unfolding subspace_topology_def by blast
        have hpreX_eq': "{x \<in> A. p x \<in> V} = {x \<in> X. p x \<in> V}"
          by (rule top1_saturated_restrict_preimage_eq[OF hsat hV])
        have hpreX_eq: "{x \<in> X. p x \<in> V} = {x \<in> A. p x \<in> V}"
          using hpreX_eq' by simp
        have hpreX_open: "{x \<in> X. p x \<in> V} \<in> TX"
        proof -
          have "A \<inter> U \<in> TX"
            by (rule topology_inter2[OF hTopX hAopen hU])
          thus ?thesis
            using hpreX_eq hEq by simp
        qed
        have hVY: "V \<subseteq> Y"
          using hV hpA_sub by blast
        have hV_open_Y: "V \<in> TY"
          using hQ hVY hpreX_open by blast
        show ?thesis
          unfolding subspace_topology_def
        proof -
          have hInt: "V = (p ` A) \<inter> V"
          proof (rule subset_antisym)
            show "V \<subseteq> (p ` A) \<inter> V"
              using hV by blast
            show "(p ` A) \<inter> V \<subseteq> V"
              by blast
          qed
	          show "V \<in> {p ` A \<inter> U |U. U \<in> TY}"
	            apply (rule CollectI)
	            apply (rule exI[where x=V])
	            apply (intro conjI)
	             apply (rule hInt)
	            apply (rule hV_open_Y)
	            done
	        qed
	      next
	        case False
        have hAcl: "closedin_on X TX A"
          using hA False by blast
        have hXAmem: "X - A \<in> TX"
          using hAcl unfolding closedin_on_def by blast

        obtain U where hU: "U \<in> TX" and hEq: "{x \<in> A. p x \<in> V} = A \<inter> U"
          using hpreA unfolding subspace_topology_def by blast
        define W where "W = (p ` A) - V"

        have hWsub: "W \<subseteq> p ` A"
          unfolding W_def by blast
        have hpreA_W: "{x \<in> A. p x \<in> W} = A - {x \<in> A. p x \<in> V}"
        proof (rule set_eqI)
          fix x
          show "x \<in> {x \<in> A. p x \<in> W} \<longleftrightarrow> x \<in> A - {x \<in> A. p x \<in> V}"
            unfolding W_def by blast
        qed
        have hpreX_W_eq': "{x \<in> A. p x \<in> W} = {x \<in> X. p x \<in> W}"
          by (rule top1_saturated_restrict_preimage_eq[OF hsat hWsub])
        have hpreX_W_eq: "{x \<in> X. p x \<in> W} = {x \<in> A. p x \<in> W}"
          using hpreX_W_eq' by simp

        have hpreX_W_closed: "closedin_on X TX {x \<in> X. p x \<in> W}"
        proof -
          have hCeq: "{x \<in> X. p x \<in> W} = A - {x \<in> A. p x \<in> V}"
            using hpreX_W_eq hpreA_W by simp
          have hCeq2: "{x \<in> A. p x \<in> V} = A \<inter> U"
            using hEq by simp
	          have hCeq3: "{x \<in> X. p x \<in> W} = A \<inter> (X - U)"
	          proof -
	            have hId: "A - (A \<inter> U) = A \<inter> (X - U)"
	            proof (rule set_eqI)
	              fix x
	              show "x \<in> A - (A \<inter> U) \<longleftrightarrow> x \<in> A \<inter> (X - U)"
	              proof
	                assume hx: "x \<in> A - (A \<inter> U)"
	                have hxA: "x \<in> A" and hxnot: "x \<notin> A \<inter> U"
	                  using hx by blast+
	                have hxX: "x \<in> X"
	                  using hAX hxA by blast
	                have hxnotU: "x \<notin> U"
	                  using hxA hxnot by blast
	                show "x \<in> A \<inter> (X - U)"
	                  using hxA hxX hxnotU by blast
	              next
	                assume hx: "x \<in> A \<inter> (X - U)"
	                have hxA: "x \<in> A" and hxX: "x \<in> X" and hxnotU: "x \<notin> U"
	                  using hx by blast+
	                have hxnot: "x \<notin> A \<inter> U"
	                  using hxA hxnotU by blast
	                show "x \<in> A - (A \<inter> U)"
	                  using hxA hxnot by blast
	              qed
	            qed
	            thus ?thesis
	              using hCeq hCeq2 by simp
	          qed
	          show ?thesis
	            unfolding closedin_on_def
		          proof (intro conjI)
		            show "{x \<in> X. p x \<in> W} \<subseteq> X"
		              by blast
		            have hXminus: "X - (A \<inter> (X - U)) = (X - A) \<union> (X \<inter> U)"
		            proof (rule set_eqI)
		              fix x
		              show "x \<in> X - (A \<inter> (X - U)) \<longleftrightarrow> x \<in> (X - A) \<union> (X \<inter> U)"
		                by blast
		            qed
		            have hXmem: "X \<in> TX"
		              using hTopX unfolding is_topology_on_def by blast
		            have hXintU: "X \<inter> U \<in> TX"
		              by (rule topology_inter2[OF hTopX hXmem hU])
		            have hUn_open: "(X - A) \<union> (X \<inter> U) \<in> TX"
		              by (rule topology_union2[OF hTopX hXAmem hXintU])
		            have hDiff1: "X - {x \<in> X. p x \<in> W} = X - (A \<inter> (X - U))"
		              by (subst hCeq3) simp
		            have hDiffEq: "X - {x \<in> X. p x \<in> W} = (X - A) \<union> (X \<inter> U)"
		              using hDiff1 hXminus by simp
		            show "X - {x \<in> X. p x \<in> W} \<in> TX"
		              by (subst hDiffEq) (rule hUn_open)
		          qed
	        qed

        have hWsubY: "W \<subseteq> Y"
          unfolding W_def using hpA_sub by blast
        have hW_closed_Y: "closedin_on Y TY W"
          using top1_quotient_map_closed_iff_preimage_closed[OF hp hWsubY] hpreX_W_closed by blast
        have hYminusW_open: "Y - W \<in> TY"
          using hW_closed_Y unfolding closedin_on_def by blast

        have hV_eq: "V = (p ` A) \<inter> (Y - W)"
        proof (rule equalityI)
          show "V \<subseteq> p ` A \<inter> (Y - W)"
            unfolding W_def using hV hpA_sub by blast
          show "p ` A \<inter> (Y - W) \<subseteq> V"
            unfolding W_def by blast
        qed

        show ?thesis
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[where x="Y - W"])
          apply (intro conjI)
           apply (simp add: hV_eq)
          apply (rule hYminusW_open)
          done
      qed
    qed
  qed

  show "(top1_open_map_on X TX Y TY p \<or> top1_closed_map_on X TX Y TY p)
        \<longrightarrow> top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
  proof (intro impI)
    assume hpoc: "top1_open_map_on X TX Y TY p \<or> top1_closed_map_on X TX Y TY p"
    show "top1_quotient_map_on A (subspace_topology X TX A) (p ` A) (subspace_topology Y TY (p ` A)) p"
    proof (rule hquotient_core)
      fix V assume hV: "V \<subseteq> p ` A"
      assume hpreA: "{x \<in> A. p x \<in> V} \<in> subspace_topology X TX A"
	      obtain U0 where hU0: "U0 \<in> TX" and hEq0: "{x \<in> A. p x \<in> V} = A \<inter> U0"
	        using hpreA unfolding subspace_topology_def by blast
	      define U where "U = U0 \<inter> X"
	      have hU: "U \<in> TX"
	      proof -
	        have hXmem: "X \<in> TX"
	          using hTopX unfolding is_topology_on_def by blast
	        show ?thesis
	          unfolding U_def by (rule topology_inter2[OF hTopX hU0 hXmem])
	      qed
      have hUsub: "U \<subseteq> X"
        unfolding U_def by blast
      have hEq: "{x \<in> A. p x \<in> V} = A \<inter> U"
      proof -
        have "A \<inter> U0 = A \<inter> (U0 \<inter> X)"
          using hAX by blast
        thus ?thesis
          using hEq0 unfolding U_def by simp
      qed

      have hpreX_eq: "{x \<in> X. p x \<in> V} = A \<inter> U"
        using top1_saturated_restrict_preimage_eq[OF hsat hV] hEq by simp
      have hV_eq_img: "V = (p ` U) \<inter> (p ` A)"
      proof -
        have hpreX: "{x \<in> X. p x \<in> V} = U \<inter> A"
          using hpreX_eq by (simp add: Int_commute Int_left_commute Int_assoc)
        have "p ` {x \<in> X. p x \<in> V} = V"
        proof (rule equalityI)
          show "p ` {x \<in> X. p x \<in> V} \<subseteq> V"
            by blast
          show "V \<subseteq> p ` {x \<in> X. p x \<in> V}"
          proof (rule subsetI)
            fix y assume hyV: "y \<in> V"
            have hyY: "y \<in> Y"
              using hV hpA_sub hyV by blast
            have "y \<in> Y"
              by (rule hyY)
            have "y \<in> p ` X"
              using hsurj hyY by simp
            then obtain x where hxX: "x \<in> X" and hy: "y = p x"
              by blast
            have "p x \<in> V"
              using hyV hy by simp
            have "x \<in> {x \<in> X. p x \<in> V}"
              using hxX \<open>p x \<in> V\<close> by simp
            thus "y \<in> p ` {x \<in> X. p x \<in> V}"
              using hy by blast
          qed
        qed
        have "V = p ` (U \<inter> A)"
          using hpreX hsurj \<open>p ` {x \<in> X. p x \<in> V} = V\<close> by simp
        also have "... = (p ` U) \<inter> (p ` A)"
          by (rule top1_saturated_image_inter_eq[OF hsat hUsub])
        finally show ?thesis .
      qed

      show "V \<in> subspace_topology Y TY (p ` A)"
	      proof (cases "top1_open_map_on X TX Y TY p")
	        case True
	        have hopen: "\<forall>U. U \<in> TX \<and> U \<subseteq> X \<longrightarrow> p ` U \<in> TY"
	          using True unfolding top1_open_map_on_def by blast
	        have hPU: "p ` U \<in> TY"
	          using hopen hU hUsub by blast
	        have hVeq: "V = (p ` A) \<inter> (p ` U)"
	        proof -
	          have "V = (p ` U) \<inter> (p ` A)"
	            by (rule hV_eq_img)
	          also have "... = (p ` A) \<inter> (p ` U)"
	            by (rule Int_commute)
	          finally show ?thesis .
	        qed
	        show ?thesis
	          unfolding subspace_topology_def
	          apply (rule CollectI)
	          apply (rule exI[where x="p ` U"])
	          apply (intro conjI)
	           apply (rule hVeq)
	          apply (rule hPU)
	          done
	      next
	        case False
	        have hclosed: "top1_closed_map_on X TX Y TY p"
	          using hpoc False by blast
	        have hCprop: "\<forall>A. closedin_on X TX A \<longrightarrow> closedin_on Y TY (p ` A)"
	          using hclosed unfolding top1_closed_map_on_def by blast
	        have hC: "closedin_on X TX (X - U)"
	        proof -
	          have hXmem: "X \<in> TX"
	            using hTopX unfolding is_topology_on_def by blast
	          have hXintU: "X \<inter> U \<in> TX"
	            by (rule topology_inter2[OF hTopX hXmem hU])
	          have hEq: "X - (X - U) = X \<inter> U"
	            by blast
	          show ?thesis
	            unfolding closedin_on_def
	          proof (intro conjI)
	            show "X - U \<subseteq> X"
	              by blast
	            show "X - (X - U) \<in> TX"
	              by (subst hEq) (rule hXintU)
	          qed
	        qed
	        have hCpU: "closedin_on Y TY (p ` (X - U))"
	          using hCprop hC by blast
	        have hOpU: "Y - p ` (X - U) \<in> TY"
	          using hCpU unfolding closedin_on_def by blast

        have hV_eq2: "V = (p ` A) \<inter> (Y - p ` (X - U))"
        proof (rule equalityI)
          show "V \<subseteq> p ` A \<inter> (Y - p ` (X - U))"
          proof (rule subsetI)
            fix y assume hyV: "y \<in> V"
            have hyPA: "y \<in> p ` A"
              using hV hyV by blast
            have "y \<notin> p ` (X - U)"
            proof
              assume hy: "y \<in> p ` (X - U)"
              obtain x where hxXU: "x \<in> X - U" and hyx: "y = p x"
                using hy by blast
              have hxX: "x \<in> X" and hxnotU: "x \<notin> U"
                using hxXU by blast+
              have "p x \<in> V"
                using hyV hyx by simp
              have hxpre: "x \<in> {x \<in> X. p x \<in> V}"
                using hxX \<open>p x \<in> V\<close> by simp
              have hxAU: "x \<in> A \<inter> U"
                using hpreX_eq hxpre by simp
              hence "x \<in> U"
                by blast
              thus False
                using hxnotU by blast
            qed
            have hyY: "y \<in> Y"
              using hpA_sub hyPA by blast
            show "y \<in> p ` A \<inter> (Y - p ` (X - U))"
              using hyPA hyY \<open>y \<notin> p ` (X - U)\<close> by blast
          qed
          show "p ` A \<inter> (Y - p ` (X - U)) \<subseteq> V"
          proof (rule subsetI)
            fix y assume hy: "y \<in> p ` A \<inter> (Y - p ` (X - U))"
            have hyPA: "y \<in> p ` A" and hynot: "y \<notin> p ` (X - U)"
              using hy by blast+
            obtain a where haA: "a \<in> A" and hyA: "y = p a"
              using hyPA by blast
            have haX: "a \<in> X"
              using hAX haA by blast
            have "a \<in> U"
            proof (rule classical)
              assume "a \<notin> U"
              have "a \<in> X - U"
                using haX \<open>a \<notin> U\<close> by blast
              have "y \<in> p ` (X - U)"
                using hyA \<open>a \<in> X - U\<close> by blast
              thus "a \<in> U"
                using hynot by blast
            qed
            have "a \<in> A \<inter> U"
              using haA \<open>a \<in> U\<close> by blast
	            have "y \<in> p ` (A \<inter> U)"
	              using hyA \<open>a \<in> A \<inter> U\<close> by blast
	            thus "y \<in> V"
	            proof -
	              have "y \<in> (p ` U) \<inter> (p ` A)"
	                using \<open>y \<in> p ` (A \<inter> U)\<close> by blast
	              thus ?thesis
	                using hV_eq_img by simp
	            qed
	          qed
	        qed

        show ?thesis
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[where x="Y - p ` (X - U)"])
          apply (intro conjI)
           apply (simp add: hV_eq2)
          apply (rule hOpU)
          done
      qed
    qed
  qed
qed

(** from \S22 Theorem 22.2 (Universal property of quotient maps) [top1.tex:2441] **)

(** Congruence lemmas: continuity / quotientness depend only on values on the carrier. **)
lemma top1_preimage_on_cong:
  assumes heq: "\<forall>x\<in>X. f x = g x"
  shows "{x\<in>X. f x \<in> V} = {x\<in>X. g x \<in> V}"
proof (rule set_eqI)
  fix x
  show "x \<in> {x \<in> X. f x \<in> V} \<longleftrightarrow> x \<in> {x \<in> X. g x \<in> V}"
  proof
    assume hx: "x \<in> {x \<in> X. f x \<in> V}"
    have hxX: "x \<in> X" and hfx: "f x \<in> V"
      using hx by blast+
    have hfg: "f x = g x"
      using heq hxX by blast
    have "g x = f x"
      using hfg by simp
    hence "g x \<in> V"
      using hfx by simp
    thus "x \<in> {x \<in> X. g x \<in> V}"
      using hxX by blast
  next
    assume hx: "x \<in> {x \<in> X. g x \<in> V}"
    have hxX: "x \<in> X" and hgx: "g x \<in> V"
      using hx by blast+
    have "f x = g x"
      using heq hxX by blast
    hence "f x \<in> V"
      using hgx by simp
    thus "x \<in> {x \<in> X. f x \<in> V}"
      using hxX by blast
  qed
qed

lemma top1_image_on_cong:
  assumes heq: "\<forall>x\<in>X. f x = g x"
  shows "f ` X = g ` X"
proof (rule subset_antisym)
  show "f ` X \<subseteq> g ` X"
  proof (rule subsetI)
    fix y assume hy: "y \<in> f ` X"
    then obtain x where hxX: "x \<in> X" and hyx: "y = f x"
      by blast
    have "y = g x"
      using heq hxX hyx by simp
    thus "y \<in> g ` X"
      using hxX by blast
  qed
  show "g ` X \<subseteq> f ` X"
  proof (rule subsetI)
    fix y assume hy: "y \<in> g ` X"
    then obtain x where hxX: "x \<in> X" and hyx: "y = g x"
      by blast
    have "y = f x"
      using heq hxX hyx by simp
    thus "y \<in> f ` X"
      using hxX by blast
  qed
qed

lemma top1_continuous_map_on_cong:
  assumes heq: "\<forall>x\<in>X. f x = g x"
  shows "top1_continuous_map_on X TX Y TY f \<longleftrightarrow> top1_continuous_map_on X TX Y TY g"
proof (rule iffI)
  assume hf: "top1_continuous_map_on X TX Y TY f"
  have hfmap: "\<forall>x\<in>X. f x \<in> Y"
    using hf unfolding top1_continuous_map_on_def by blast
  have hfpre: "\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX"
    using hf unfolding top1_continuous_map_on_def by blast
  show "top1_continuous_map_on X TX Y TY g"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. g x \<in> Y"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have hfg: "f x = g x"
        using heq hxX by blast
      have "g x = f x"
        using hfg by simp
      also have "... \<in> Y"
        using hfmap hxX by blast
      finally show "g x \<in> Y"
        by simp
    qed
    show "\<forall>V\<in>TY. {x \<in> X. g x \<in> V} \<in> TX"
	    proof (intro ballI)
	      fix V assume hV: "V \<in> TY"
	      have hEq: "{x\<in>X. f x \<in> V} = {x\<in>X. g x \<in> V}"
	        by (rule top1_preimage_on_cong[OF heq])
	      have "{x\<in>X. g x \<in> V} = {x\<in>X. f x \<in> V}"
	        using hEq by simp
	      thus "{x \<in> X. g x \<in> V} \<in> TX"
	        using hfpre hV by simp
	    qed
	  qed
next
  assume hg: "top1_continuous_map_on X TX Y TY g"
  have hgmap: "\<forall>x\<in>X. g x \<in> Y"
    using hg unfolding top1_continuous_map_on_def by blast
  have hgpre: "\<forall>V\<in>TY. {x\<in>X. g x \<in> V} \<in> TX"
    using hg unfolding top1_continuous_map_on_def by blast
  show "top1_continuous_map_on X TX Y TY f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. f x \<in> Y"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have "f x = g x"
        using heq hxX by blast
      also have "... \<in> Y"
        using hgmap hxX by blast
      finally show "f x \<in> Y"
        by simp
    qed
    show "\<forall>V\<in>TY. {x \<in> X. f x \<in> V} \<in> TX"
    proof (intro ballI)
      fix V assume hV: "V \<in> TY"
      have "{x\<in>X. f x \<in> V} = {x\<in>X. g x \<in> V}"
        by (rule top1_preimage_on_cong[OF heq])
      thus "{x \<in> X. f x \<in> V} \<in> TX"
        using hgpre hV by simp
    qed
  qed
qed

lemma top1_quotient_map_on_cong:
  assumes heq: "\<forall>x\<in>X. f x = g x"
  shows "top1_quotient_map_on X TX Y TY f \<longleftrightarrow> top1_quotient_map_on X TX Y TY g"
proof (rule iffI)
  assume hf: "top1_quotient_map_on X TX Y TY f"
  have hTopX: "is_topology_on X TX"
    using hf unfolding top1_quotient_map_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hf unfolding top1_quotient_map_on_def by blast
  have hcontf: "top1_continuous_map_on X TX Y TY f"
    using hf unfolding top1_quotient_map_on_def by blast
  have hsurjf: "f ` X = Y"
    using hf unfolding top1_quotient_map_on_def by blast
  have hQf: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. f x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
    using hf unfolding top1_quotient_map_on_def by blast

  have hsurjg: "g ` X = Y"
    using top1_image_on_cong[OF heq] hsurjf by simp
  have hcontg: "top1_continuous_map_on X TX Y TY g"
    using top1_continuous_map_on_cong[OF heq] hcontf by blast
  have hQg: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. g x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
  proof (intro allI impI)
    fix V assume hV: "V \<subseteq> Y"
    assume hpre: "{x\<in>X. g x \<in> V} \<in> TX"
    have hpre': "{x\<in>X. f x \<in> V} \<in> TX"
    proof -
      have "{x\<in>X. f x \<in> V} = {x\<in>X. g x \<in> V}"
        by (rule top1_preimage_on_cong[OF heq])
      thus ?thesis
        using hpre by simp
    qed
    show "V \<in> TY"
      using hQf hV hpre' by blast
  qed

  show "top1_quotient_map_on X TX Y TY g"
    unfolding top1_quotient_map_on_def
    apply (intro conjI)
        apply (rule hTopX)
       apply (rule hTopY)
      apply (rule hcontg)
     apply (rule hsurjg)
    apply (rule hQg)
    done
next
  assume hg: "top1_quotient_map_on X TX Y TY g"
  have hTopX: "is_topology_on X TX"
    using hg unfolding top1_quotient_map_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hg unfolding top1_quotient_map_on_def by blast
  have hcontg: "top1_continuous_map_on X TX Y TY g"
    using hg unfolding top1_quotient_map_on_def by blast
  have hsurjg: "g ` X = Y"
    using hg unfolding top1_quotient_map_on_def by blast
  have hQg: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. g x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
    using hg unfolding top1_quotient_map_on_def by blast

  have hsurjf: "f ` X = Y"
    using top1_image_on_cong[OF heq] hsurjg by simp
  have hcontf: "top1_continuous_map_on X TX Y TY f"
    using top1_continuous_map_on_cong[OF heq] hcontg by blast
  have hQf: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. f x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
  proof (intro allI impI)
    fix V assume hV: "V \<subseteq> Y"
    assume hpre: "{x\<in>X. f x \<in> V} \<in> TX"
    have hpre': "{x\<in>X. g x \<in> V} \<in> TX"
    proof -
      have hEq: "{x\<in>X. f x \<in> V} = {x\<in>X. g x \<in> V}"
        by (rule top1_preimage_on_cong[OF heq])
      have "{x\<in>X. g x \<in> V} = {x\<in>X. f x \<in> V}"
        using hEq by simp
      thus ?thesis
        using hpre by simp
    qed
    show "V \<in> TY"
      using hQg hV hpre' by blast
  qed

  show "top1_quotient_map_on X TX Y TY f"
    unfolding top1_quotient_map_on_def
    apply (intro conjI)
        apply (rule hTopX)
       apply (rule hTopY)
      apply (rule hcontf)
     apply (rule hsurjf)
    apply (rule hQf)
    done
qed

(** Composite of quotient maps is a quotient map [top1.tex:2428–2432]. **)
lemma top1_quotient_map_on_comp:
  assumes hp: "top1_quotient_map_on X TX Y TY p"
  assumes hq: "top1_quotient_map_on Y TY Z TZ q"
  shows "top1_quotient_map_on X TX Z TZ (q \<circ> p)"
proof -
  have hTopX: "is_topology_on X TX"
    using hp unfolding top1_quotient_map_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hp unfolding top1_quotient_map_on_def by blast
  have hTopZ: "is_topology_on Z TZ"
    using hq unfolding top1_quotient_map_on_def by blast
  have hcontp: "top1_continuous_map_on X TX Y TY p"
    using hp unfolding top1_quotient_map_on_def by blast
  have hcontq: "top1_continuous_map_on Y TY Z TZ q"
    using hq unfolding top1_quotient_map_on_def by blast
  have hsurjp: "p ` X = Y"
    using hp unfolding top1_quotient_map_on_def by blast
  have hsurjq: "q ` Y = Z"
    using hq unfolding top1_quotient_map_on_def by blast
  have hQp: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. p x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
    using hp unfolding top1_quotient_map_on_def by blast
  have hQq: "\<forall>V. V \<subseteq> Z \<longrightarrow> ({y\<in>Y. q y \<in> V} \<in> TY \<longrightarrow> V \<in> TZ)"
    using hq unfolding top1_quotient_map_on_def by blast

  have hpmap: "\<forall>x\<in>X. p x \<in> Y"
    using hcontp unfolding top1_continuous_map_on_def by blast
  have hqmap: "\<forall>y\<in>Y. q y \<in> Z"
    using hcontq unfolding top1_continuous_map_on_def by blast
  have hpreq_cont: "\<forall>V\<in>TZ. {y\<in>Y. q y \<in> V} \<in> TY"
    using hcontq unfolding top1_continuous_map_on_def by blast
  have hprep_cont: "\<forall>W\<in>TY. {x\<in>X. p x \<in> W} \<in> TX"
    using hcontp unfolding top1_continuous_map_on_def by blast

  have hcontqp: "top1_continuous_map_on X TX Z TZ (q \<circ> p)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. (q \<circ> p) x \<in> Z"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have "p x \<in> Y"
        using hpmap hxX by blast
      hence "q (p x) \<in> Z"
        using hqmap by blast
      thus "(q \<circ> p) x \<in> Z"
        by simp
    qed
    show "\<forall>V\<in>TZ. {x \<in> X. (q \<circ> p) x \<in> V} \<in> TX"
    proof (intro ballI)
      fix V assume hV: "V \<in> TZ"
      have hpreY: "{y\<in>Y. q y \<in> V} \<in> TY"
        using hpreq_cont hV by blast
      have hpreX: "{x\<in>X. p x \<in> {y\<in>Y. q y \<in> V}} \<in> TX"
        using hprep_cont hpreY by blast
      have hEq: "{x\<in>X. (q \<circ> p) x \<in> V} = {x\<in>X. p x \<in> {y\<in>Y. q y \<in> V}}"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x \<in> X. (q \<circ> p) x \<in> V} \<longleftrightarrow> x \<in> {x \<in> X. p x \<in> {y \<in> Y. q y \<in> V}}"
	        proof
	          assume hx: "x \<in> {x \<in> X. (q \<circ> p) x \<in> V}"
	          have hxX: "x \<in> X" and hqpx: "q (p x) \<in> V"
	          proof -
	            have hx_conj: "x \<in> X \<and> q (p x) \<in> V"
	              using hx by simp
	            show "x \<in> X"
	              using hx_conj by (rule conjunct1)
	            show "q (p x) \<in> V"
	              using hx_conj by (rule conjunct2)
	          qed
	          have hpxY: "p x \<in> Y"
	            using hpmap hxX by blast
	          have "p x \<in> {y \<in> Y. q y \<in> V}"
	            using hpxY hqpx by blast
          thus "x \<in> {x \<in> X. p x \<in> {y \<in> Y. q y \<in> V}}"
            using hxX by simp
	        next
	          assume hx: "x \<in> {x \<in> X. p x \<in> {y \<in> Y. q y \<in> V}}"
	          have hxX: "x \<in> X" and hpx: "p x \<in> {y \<in> Y. q y \<in> V}"
	          proof -
	            have hx_conj: "x \<in> X \<and> p x \<in> {y \<in> Y. q y \<in> V}"
	              using hx by simp
	            show "x \<in> X"
	              using hx_conj by (rule conjunct1)
	            show "p x \<in> {y \<in> Y. q y \<in> V}"
	              using hx_conj by (rule conjunct2)
	          qed
	          have "q (p x) \<in> V"
	            using hpx by blast
	          thus "x \<in> {x \<in> X. (q \<circ> p) x \<in> V}"
	            using hxX by simp
        qed
      qed
      show "{x \<in> X. (q \<circ> p) x \<in> V} \<in> TX"
        by (subst hEq) (rule hpreX)
    qed
  qed

  have hsurjqp: "(q \<circ> p) ` X = Z"
  proof -
    have "(q \<circ> p) ` X = q ` (p ` X)"
      by (simp add: image_image)
    also have "... = q ` Y"
      using hsurjp by simp
    also have "... = Z"
      using hsurjq by simp
    finally show ?thesis .
  qed

  have hQqp: "\<forall>V. V \<subseteq> Z \<longrightarrow> ({x\<in>X. (q \<circ> p) x \<in> V} \<in> TX \<longrightarrow> V \<in> TZ)"
  proof (intro allI impI)
    fix V assume hVsub: "V \<subseteq> Z"
    assume hpre: "{x\<in>X. (q \<circ> p) x \<in> V} \<in> TX"
    define W where "W = {y\<in>Y. q y \<in> V}"
    have hWsub: "W \<subseteq> Y"
      unfolding W_def by blast
	    have hpreW: "{x\<in>X. p x \<in> W} \<in> TX"
		    proof -
		      have hEq: "{x\<in>X. p x \<in> W} = {x\<in>X. (q \<circ> p) x \<in> V}"
		      proof (rule set_eqI)
		        fix x
		        show "x \<in> {x \<in> X. p x \<in> W} \<longleftrightarrow> x \<in> {x \<in> X. (q \<circ> p) x \<in> V}"
			        proof
			          assume hx: "x \<in> {x \<in> X. p x \<in> W}"
			          have hxX: "x \<in> X" and hpx: "p x \<in> W"
			          proof -
			            have hx_conj: "x \<in> X \<and> p x \<in> W"
			              using hx by simp
			            show "x \<in> X"
			              using hx_conj by (rule conjunct1)
			            show "p x \<in> W"
			              using hx_conj by (rule conjunct2)
			          qed
			          have hpxY: "p x \<in> Y"
			            using hpmap hxX by blast
			          have hqpx: "q (p x) \<in> V"
			            using hpx unfolding W_def by blast
		          show "x \<in> {x \<in> X. (q \<circ> p) x \<in> V}"
		            using hxX hqpx by simp
			        next
			          assume hx: "x \<in> {x \<in> X. (q \<circ> p) x \<in> V}"
			          have hxX: "x \<in> X" and hqpx: "q (p x) \<in> V"
			          proof -
			            have hx_conj: "x \<in> X \<and> q (p x) \<in> V"
			              using hx by simp
			            show "x \<in> X"
			              using hx_conj by (rule conjunct1)
			            show "q (p x) \<in> V"
			              using hx_conj by (rule conjunct2)
			          qed
			          have hpxY: "p x \<in> Y"
			            using hpmap hxX by blast
			          have "p x \<in> W"
			            unfolding W_def using hpxY hqpx by blast
		          thus "x \<in> {x \<in> X. p x \<in> W}"
		            using hxX by simp
		        qed
		      qed
		      show ?thesis
		        by (subst hEq) (rule hpre)
		    qed
    have hWopen: "W \<in> TY"
      using hQp hWsub hpreW by blast
    show "V \<in> TZ"
      using hQq hVsub hWopen unfolding W_def by blast
  qed

  show ?thesis
    unfolding top1_quotient_map_on_def
    apply (intro conjI)
        apply (rule hTopX)
       apply (rule hTopZ)
      apply (rule hcontqp)
     apply (rule hsurjqp)
    apply (rule hQqp)
    done
qed

theorem Theorem_22_2:
  assumes hp: "top1_quotient_map_on X TX Y TY p"
  assumes hgmap: "\<forall>x\<in>X. g x \<in> Z"
  assumes hconst: "\<forall>x\<in>X. \<forall>y\<in>X. p x = p y \<longrightarrow> g x = g y"
  shows "\<exists>f.
    (\<forall>y\<in>Y. f y \<in> Z)
    \<and> (\<forall>x\<in>X. f (p x) = g x)
    \<and> (top1_continuous_map_on Y TY Z TZ f \<longleftrightarrow> top1_continuous_map_on X TX Z TZ g)
    \<and> (top1_quotient_map_on Y TY Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g)"
proof -
  have hcontp: "top1_continuous_map_on X TX Y TY p"
    using hp unfolding top1_quotient_map_on_def by blast
  have hsurj: "p ` X = Y"
    using hp unfolding top1_quotient_map_on_def by blast
  have hQp: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. p x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
    using hp unfolding top1_quotient_map_on_def by blast
  have hpmap: "\<forall>x\<in>X. p x \<in> Y"
    using hcontp unfolding top1_continuous_map_on_def by blast
  have hprep_cont: "\<forall>W\<in>TY. {x\<in>X. p x \<in> W} \<in> TX"
    using hcontp unfolding top1_continuous_map_on_def by blast

  define f where "f y = g (SOME x. x \<in> X \<and> p x = y)" for y

  have hf_map: "\<forall>y\<in>Y. f y \<in> Z"
  proof (intro ballI)
    fix y assume hyY: "y \<in> Y"
    have "y \<in> p ` X"
      using hsurj hyY by simp
    then obtain x where hxX: "x \<in> X" and hpx: "p x = y"
      by blast
    have hex: "\<exists>x. x \<in> X \<and> p x = y"
      using hxX hpx by blast
    have hsome: "(SOME x. x \<in> X \<and> p x = y) \<in> X"
      using someI_ex[OF hex] by blast
    have "g (SOME x. x \<in> X \<and> p x = y) \<in> Z"
      using hgmap hsome by blast
    thus "f y \<in> Z"
      unfolding f_def by simp
  qed

  have hf_factor: "\<forall>x\<in>X. f (p x) = g x"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hex: "\<exists>u. u \<in> X \<and> p u = p x"
      using hxX by blast
    have hsome: "(SOME u. u \<in> X \<and> p u = p x) \<in> X \<and> p (SOME u. u \<in> X \<and> p u = p x) = p x"
      using someI_ex[OF hex] by blast
    have huX: "(SOME u. u \<in> X \<and> p u = p x) \<in> X"
      using hsome by blast
    have hpeq: "p (SOME u. u \<in> X \<and> p u = p x) = p x"
      using hsome by blast
    have "g (SOME u. u \<in> X \<and> p u = p x) = g x"
      using hconst huX hxX hpeq by blast
    thus "f (p x) = g x"
      unfolding f_def by simp
  qed

  have hcont_equiv: "top1_continuous_map_on Y TY Z TZ f \<longleftrightarrow> top1_continuous_map_on X TX Z TZ g"
  proof (rule iffI)
    assume hfcont: "top1_continuous_map_on Y TY Z TZ f"
    have hfpre: "\<forall>V\<in>TZ. {y\<in>Y. f y \<in> V} \<in> TY"
      using hfcont unfolding top1_continuous_map_on_def by blast
    show "top1_continuous_map_on X TX Z TZ g"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>x\<in>X. g x \<in> Z"
        by (rule hgmap)
      show "\<forall>V\<in>TZ. {x \<in> X. g x \<in> V} \<in> TX"
      proof (intro ballI)
        fix V assume hV: "V \<in> TZ"
        have hW: "{y\<in>Y. f y \<in> V} \<in> TY"
          using hfpre hV by blast
        have hpreX: "{x\<in>X. p x \<in> {y\<in>Y. f y \<in> V}} \<in> TX"
          using hprep_cont hW by blast
        have hEq: "{x\<in>X. g x \<in> V} = {x\<in>X. p x \<in> {y\<in>Y. f y \<in> V}}"
        proof (rule set_eqI)
          fix x
          show "x \<in> {x \<in> X. g x \<in> V} \<longleftrightarrow> x \<in> {x \<in> X. p x \<in> {y \<in> Y. f y \<in> V}}"
          proof
            assume hx: "x \<in> {x \<in> X. g x \<in> V}"
            have hxX: "x \<in> X" and hgx: "g x \<in> V"
              using hx by blast+
            have "f (p x) = g x"
              using hf_factor hxX by blast
            hence "f (p x) \<in> V"
              using hgx by simp
            have "p x \<in> {y\<in>Y. f y \<in> V}"
              using hpmap hxX \<open>f (p x) \<in> V\<close> by blast
            thus "x \<in> {x \<in> X. p x \<in> {y\<in>Y. f y \<in> V}}"
              using hxX by blast
          next
            assume hx: "x \<in> {x \<in> X. p x \<in> {y\<in>Y. f y \<in> V}}"
            have hxX: "x \<in> X" and hpx: "p x \<in> {y\<in>Y. f y \<in> V}"
              using hx by blast+
            have "f (p x) \<in> V"
              using hpx by blast
            have hfg: "f (p x) = g x"
              using hf_factor hxX by blast
            have "g x = f (p x)"
              using hfg by simp
            hence "g x \<in> V"
              using \<open>f (p x) \<in> V\<close> by simp
            thus "x \<in> {x \<in> X. g x \<in> V}"
              using hxX by blast
          qed
        qed
        show "{x \<in> X. g x \<in> V} \<in> TX"
          by (subst hEq) (rule hpreX)
      qed
    qed
  next
    assume hgcont: "top1_continuous_map_on X TX Z TZ g"
    have hgpre: "\<forall>V\<in>TZ. {x\<in>X. g x \<in> V} \<in> TX"
      using hgcont unfolding top1_continuous_map_on_def by blast
    show "top1_continuous_map_on Y TY Z TZ f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>y\<in>Y. f y \<in> Z"
        by (rule hf_map)
      show "\<forall>V\<in>TZ. {y \<in> Y. f y \<in> V} \<in> TY"
      proof (intro ballI)
        fix V assume hV: "V \<in> TZ"
        have hpreX: "{x\<in>X. g x \<in> V} \<in> TX"
          using hgpre hV by blast
        have hWsub: "{y\<in>Y. f y \<in> V} \<subseteq> Y"
          by blast
        have hpreW: "{x\<in>X. p x \<in> {y\<in>Y. f y \<in> V}} \<in> TX"
        proof -
          have hEq: "{x\<in>X. p x \<in> {y\<in>Y. f y \<in> V}} = {x\<in>X. g x \<in> V}"
          proof (rule set_eqI)
            fix x
            show "x \<in> {x \<in> X. p x \<in> {y \<in> Y. f y \<in> V}} \<longleftrightarrow> x \<in> {x \<in> X. g x \<in> V}"
            proof
              assume hx: "x \<in> {x \<in> X. p x \<in> {y \<in> Y. f y \<in> V}}"
              have hxX: "x \<in> X" and hpx: "p x \<in> {y \<in> Y. f y \<in> V}"
                using hx by blast+
	            have "f (p x) \<in> V"
	              using hpx by blast
	            have hfg: "f (p x) = g x"
	              using hf_factor hxX by blast
	            have "g x = f (p x)"
	              using hfg by simp
	            hence "g x \<in> V"
	              using \<open>f (p x) \<in> V\<close> by simp
	            thus "x \<in> {x \<in> X. g x \<in> V}"
	              using hxX by blast
            next
              assume hx: "x \<in> {x \<in> X. g x \<in> V}"
              have hxX: "x \<in> X" and hgx: "g x \<in> V"
                using hx by blast+
              have "f (p x) = g x"
                using hf_factor hxX by blast
              hence "f (p x) \<in> V"
                using hgx by simp
              have "p x \<in> {y\<in>Y. f y \<in> V}"
                using hpmap hxX \<open>f (p x) \<in> V\<close> by blast
              thus "x \<in> {x \<in> X. p x \<in> {y \<in> Y. f y \<in> V}}"
                using hxX by blast
            qed
          qed
          show ?thesis
            by (subst hEq) (rule hpreX)
        qed
        show "{y \<in> Y. f y \<in> V} \<in> TY"
          using hQp hWsub hpreW by blast
      qed
    qed
  qed

  have hquot_equiv: "top1_quotient_map_on Y TY Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g"
  proof (rule iffI)
    assume hfq: "top1_quotient_map_on Y TY Z TZ f"
    have hcomp: "top1_quotient_map_on X TX Z TZ (f \<circ> p)"
      by (rule top1_quotient_map_on_comp[OF hp hfq])
    have heq: "\<forall>x\<in>X. (f \<circ> p) x = g x"
      using hf_factor by simp
    show "top1_quotient_map_on X TX Z TZ g"
      using top1_quotient_map_on_cong[OF heq] hcomp by blast
  next
    assume hgq: "top1_quotient_map_on X TX Z TZ g"
    have hTopY: "is_topology_on Y TY"
      using hp unfolding top1_quotient_map_on_def by blast
    have hTopZ: "is_topology_on Z TZ"
      using hgq unfolding top1_quotient_map_on_def by blast
    have hgcont: "top1_continuous_map_on X TX Z TZ g"
      using hgq unfolding top1_quotient_map_on_def by blast
    have hfcont: "top1_continuous_map_on Y TY Z TZ f"
      using hcont_equiv hgcont by blast
    have hsurjg: "g ` X = Z"
      using hgq unfolding top1_quotient_map_on_def by blast
    have hsurjf: "f ` Y = Z"
    proof (rule subset_antisym)
      show "f ` Y \<subseteq> Z"
      proof (rule subsetI)
        fix z assume hz: "z \<in> f ` Y"
        then obtain y where hyY: "y \<in> Y" and hzy: "z = f y"
          by blast
        have "f y \<in> Z"
          using hf_map hyY by blast
        thus "z \<in> Z"
          using hzy by simp
      qed
      show "Z \<subseteq> f ` Y"
      proof (rule subsetI)
        fix z assume hzZ: "z \<in> Z"
        have "z \<in> g ` X"
          using hsurjg hzZ by simp
        then obtain x where hxX: "x \<in> X" and hzx: "z = g x"
          by blast
	        have "p x \<in> Y"
	          using hpmap hxX by blast
	        moreover have "f (p x) = g x"
	          using hf_factor hxX by blast
	        ultimately show "z \<in> f ` Y"
	        proof -
	          have "z = f (p x)"
	            using hzx \<open>f (p x) = g x\<close> by simp
	          thus ?thesis
	            using \<open>p x \<in> Y\<close> by blast
	        qed
	      qed
    qed
    have hQg: "\<forall>V. V \<subseteq> Z \<longrightarrow> ({x\<in>X. g x \<in> V} \<in> TX \<longrightarrow> V \<in> TZ)"
      using hgq unfolding top1_quotient_map_on_def by blast

    have hQf: "\<forall>V. V \<subseteq> Z \<longrightarrow> ({y\<in>Y. f y \<in> V} \<in> TY \<longrightarrow> V \<in> TZ)"
    proof (intro allI impI)
      fix V assume hVsub: "V \<subseteq> Z"
      assume hpreY: "{y\<in>Y. f y \<in> V} \<in> TY"
      have hpreX: "{x\<in>X. p x \<in> {y\<in>Y. f y \<in> V}} \<in> TX"
        using hprep_cont hpreY by blast
      have hEq: "{x\<in>X. p x \<in> {y\<in>Y. f y \<in> V}} = {x\<in>X. g x \<in> V}"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x \<in> X. p x \<in> {y \<in> Y. f y \<in> V}} \<longleftrightarrow> x \<in> {x \<in> X. g x \<in> V}"
        proof
          assume hx: "x \<in> {x \<in> X. p x \<in> {y \<in> Y. f y \<in> V}}"
          have hxX: "x \<in> X" and hpx: "p x \<in> {y \<in> Y. f y \<in> V}"
            using hx by blast+
	          have "f (p x) \<in> V"
	            using hpx by blast
	          have hfg: "f (p x) = g x"
	            using hf_factor hxX by blast
	          have "g x = f (p x)"
	            using hfg by simp
	          hence "g x \<in> V"
	            using \<open>f (p x) \<in> V\<close> by simp
	          thus "x \<in> {x \<in> X. g x \<in> V}"
	            using hxX by blast
        next
          assume hx: "x \<in> {x \<in> X. g x \<in> V}"
          have hxX: "x \<in> X" and hgx: "g x \<in> V"
            using hx by blast+
          have "f (p x) = g x"
            using hf_factor hxX by blast
          hence "f (p x) \<in> V"
            using hgx by simp
          have "p x \<in> {y\<in>Y. f y \<in> V}"
            using hpmap hxX \<open>f (p x) \<in> V\<close> by blast
          thus "x \<in> {x \<in> X. p x \<in> {y \<in> Y. f y \<in> V}}"
            using hxX by blast
        qed
	      qed
	      have hEq': "{x\<in>X. g x \<in> V} = {x\<in>X. p x \<in> {y\<in>Y. f y \<in> V}}"
	        using hEq by simp
	      have "{x\<in>X. g x \<in> V} \<in> TX"
	        by (subst hEq') (rule hpreX)
	      show "V \<in> TZ"
	        using hQg hVsub \<open>{x\<in>X. g x \<in> V} \<in> TX\<close> by blast
	    qed

    show "top1_quotient_map_on Y TY Z TZ f"
      unfolding top1_quotient_map_on_def
      apply (intro conjI)
          apply (rule hTopY)
         apply (rule hTopZ)
        apply (rule hfcont)
       apply (rule hsurjf)
      apply (rule hQf)
      done
  qed

  show "\<exists>f.
    (\<forall>y\<in>Y. f y \<in> Z)
    \<and> (\<forall>x\<in>X. f (p x) = g x)
    \<and> (top1_continuous_map_on Y TY Z TZ f \<longleftrightarrow> top1_continuous_map_on X TX Z TZ g)
    \<and> (top1_quotient_map_on Y TY Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g)"
    apply (rule exI[where x=f])
    apply (intro conjI)
       apply (rule hf_map)
      apply (rule hf_factor)
     apply (rule hcont_equiv)
    apply (rule hquot_equiv)
    done
qed

(** Quotient topology induced by a surjective map (used for Corollary 22.3). **)
definition top1_quotient_topology_by_map_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set set" where
  "top1_quotient_topology_by_map_on X TX Y p =
     {V. V \<subseteq> Y \<and> {x\<in>X. p x \<in> V} \<in> TX}"

(** The quotient topology induced by a surjective map \<open>p : X \<rightarrow> Y\<close> is a topology on \<open>Y\<close>. **)
lemma top1_quotient_topology_by_map_on_is_topology_on:
  assumes hTX: "is_topology_on X TX"
  assumes hpmap: "\<forall>x\<in>X. p x \<in> Y"
  shows "is_topology_on Y (top1_quotient_topology_by_map_on X TX Y p)"
proof -
  let ?TY = "top1_quotient_topology_by_map_on X TX Y p"

  have empty_TX: "{} \<in> TX"
    by (rule conjunct1[OF hTX[unfolded is_topology_on_def]])
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])
  have inter_TX: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])

  have preY_eq: "{x\<in>X. p x \<in> Y} = X"
  proof (rule equalityI)
    show "{x\<in>X. p x \<in> Y} \<subseteq> X" by simp
    show "X \<subseteq> {x\<in>X. p x \<in> Y}"
    proof (rule subsetI)
      fix x assume hxX: "x \<in> X"
      have "p x \<in> Y"
        using hpmap hxX by blast
      thus "x \<in> {x\<in>X. p x \<in> Y}"
        using hxX by simp
    qed
  qed

  have pre_empty_eq: "{x\<in>X. p x \<in> {}} = {}"
    by blast

  have empty_TY: "{} \<in> ?TY"
    unfolding top1_quotient_topology_by_map_on_def
    apply (intro CollectI conjI)
     apply simp
    apply (simp add: pre_empty_eq)
    apply (rule empty_TX)
    done

  have Y_TY: "Y \<in> ?TY"
    unfolding top1_quotient_topology_by_map_on_def
    apply (intro CollectI conjI)
     apply (rule subset_refl)
    apply (subst preY_eq)
    apply (rule X_TX)
    done

  have union_TY: "\<forall>U. U \<subseteq> ?TY \<longrightarrow> \<Union>U \<in> ?TY"
  proof (intro allI impI)
    fix U assume hU: "U \<subseteq> ?TY"
    have hUsubY: "\<And>V. V \<in> U \<Longrightarrow> V \<subseteq> Y"
    proof -
      fix V assume hV: "V \<in> U"
      have "V \<in> ?TY"
        using hU hV by (rule subsetD)
      thus "V \<subseteq> Y"
        unfolding top1_quotient_topology_by_map_on_def by simp
    qed

    have union_sub: "\<Union>U \<subseteq> Y"
    proof (rule subsetI)
      fix y assume hy: "y \<in> \<Union>U"
      then obtain V where hV: "V \<in> U" and hyV: "y \<in> V"
        by blast
      have "V \<subseteq> Y"
        by (rule hUsubY[OF hV])
      thus "y \<in> Y"
        using hyV by blast
    qed

    have hpre_subTX: "(\<lambda>V. {x\<in>X. p x \<in> V}) ` U \<subseteq> TX"
    proof (rule subsetI)
      fix A assume hA: "A \<in> (\<lambda>V. {x\<in>X. p x \<in> V}) ` U"
      obtain V where hV: "V \<in> U" and hAeq: "A = {x\<in>X. p x \<in> V}"
        using hA by (elim imageE)
      have "V \<in> ?TY"
        using hU hV by (rule subsetD)
      have "{x\<in>X. p x \<in> V} \<in> TX"
        using \<open>V \<in> ?TY\<close> unfolding top1_quotient_topology_by_map_on_def by simp
      thus "A \<in> TX"
        using hAeq by simp
    qed

    have pre_union_eq: "{x\<in>X. p x \<in> \<Union>U} = \<Union>((\<lambda>V. {x\<in>X. p x \<in> V}) ` U)"
    proof (rule set_eqI)
      fix x
      show "x \<in> {x \<in> X. p x \<in> \<Union>U} \<longleftrightarrow> x \<in> \<Union>((\<lambda>V. {x\<in>X. p x \<in> V}) ` U)"
        apply blast
        done
    qed

    have pre_open: "{x\<in>X. p x \<in> \<Union>U} \<in> TX"
      apply (subst pre_union_eq)
      apply (rule union_TX[rule_format, OF hpre_subTX])
      done

    show "\<Union>U \<in> ?TY"
      unfolding top1_quotient_topology_by_map_on_def
      apply (intro CollectI conjI)
       apply (rule union_sub)
      apply (rule pre_open)
      done
  qed

  have inter_TY: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TY \<longrightarrow> \<Inter>F \<in> ?TY"
  proof (intro allI impI)
    fix F assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> ?TY"
    have hfin: "finite F" and hne: "F \<noteq> {}" and hFsub: "F \<subseteq> ?TY"
      using hF by blast+
    have hFsubY: "\<forall>V\<in>F. V \<subseteq> Y"
      using hFsub unfolding top1_quotient_topology_by_map_on_def by blast

    have inter_sub: "\<Inter>F \<subseteq> Y"
    proof (rule subsetI)
      fix y assume hy: "y \<in> \<Inter>F"
      obtain V where hV: "V \<in> F"
        using hne by blast
      have hyV: "y \<in> V"
        using hy hV by blast
      have "V \<subseteq> Y"
        using hFsubY hV by blast
      thus "y \<in> Y"
        using hyV by blast
    qed

    have hpre_subTX: "(\<lambda>V. {x\<in>X. p x \<in> V}) ` F \<subseteq> TX"
    proof (rule subsetI)
      fix A assume hA: "A \<in> (\<lambda>V. {x\<in>X. p x \<in> V}) ` F"
      obtain V where hV: "V \<in> F" and hAeq: "A = {x\<in>X. p x \<in> V}"
        using hA by (elim imageE)
      have "V \<in> ?TY"
        using hFsub hV by (rule subsetD)
      have "{x\<in>X. p x \<in> V} \<in> TX"
        using \<open>V \<in> ?TY\<close> unfolding top1_quotient_topology_by_map_on_def by simp
      thus "A \<in> TX"
        using hAeq by simp
    qed

    have pre_inter_eq: "{x\<in>X. p x \<in> \<Inter>F} = \<Inter>((\<lambda>V. {x\<in>X. p x \<in> V}) ` F)"
    proof (rule equalityI)
      show "{x\<in>X. p x \<in> \<Inter>F} \<subseteq> \<Inter>((\<lambda>V. {x\<in>X. p x \<in> V}) ` F)"
      proof (rule subsetI)
        fix x assume hx: "x \<in> {x\<in>X. p x \<in> \<Inter>F}"
        have hxX: "x \<in> X" and hpx: "p x \<in> \<Inter>F"
        proof -
          have hx_conj: "x \<in> X \<and> p x \<in> \<Inter>F"
            using hx by simp
          show "x \<in> X"
            using hx_conj by (rule conjunct1)
          show "p x \<in> \<Inter>F"
            using hx_conj by (rule conjunct2)
        qed
        show "x \<in> \<Inter>((\<lambda>V. {x\<in>X. p x \<in> V}) ` F)"
        proof (rule InterI)
          fix A assume hA: "A \<in> (\<lambda>V. {x\<in>X. p x \<in> V}) ` F"
          obtain V where hV: "V \<in> F" and hAeq: "A = {x\<in>X. p x \<in> V}"
            using hA by (elim imageE)
          have "p x \<in> V"
            using hpx hV by blast
          thus "x \<in> A"
            using hxX hAeq by simp
        qed
      qed
      show "\<Inter>((\<lambda>V. {x\<in>X. p x \<in> V}) ` F) \<subseteq> {x\<in>X. p x \<in> \<Inter>F}"
      proof (rule subsetI)
        fix x assume hx: "x \<in> \<Inter>((\<lambda>V. {x\<in>X. p x \<in> V}) ` F)"
        have hxX: "x \<in> X"
        proof -
          obtain V where hV: "V \<in> F"
            using hne by blast
          have hA: "{u\<in>X. p u \<in> V} \<in> (\<lambda>W. {u\<in>X. p u \<in> W}) ` F"
            using hV by blast
          have "x \<in> {u\<in>X. p u \<in> V}"
            using hx hA by blast
          thus "x \<in> X"
            by simp
        qed
        have hpx: "p x \<in> \<Inter>F"
        proof (rule InterI)
          fix V assume hV: "V \<in> F"
          have hA: "{u\<in>X. p u \<in> V} \<in> (\<lambda>W. {u\<in>X. p u \<in> W}) ` F"
            using hV by blast
          have "x \<in> {u\<in>X. p u \<in> V}"
            using hx hA by blast
          thus "p x \<in> V"
            by simp
        qed
        show "x \<in> {x\<in>X. p x \<in> \<Inter>F}"
          using hxX hpx by simp
      qed
    qed

    have pre_open_img: "\<Inter>((\<lambda>V. {x\<in>X. p x \<in> V}) ` F) \<in> TX"
    proof -
      have hfin_img: "finite ((\<lambda>V. {x\<in>X. p x \<in> V}) ` F)"
        using hfin by simp
      have hne_img: "((\<lambda>V. {x\<in>X. p x \<in> V}) ` F) \<noteq> {}"
        using hne by simp
      have hImp: "finite ((\<lambda>V. {x\<in>X. p x \<in> V}) ` F) \<and>
          (\<lambda>V. {x\<in>X. p x \<in> V}) ` F \<noteq> {} \<and>
          (\<lambda>V. {x\<in>X. p x \<in> V}) ` F \<subseteq> TX"
        using hfin_img hne_img hpre_subTX by simp
      have hStep:
        "finite ((\<lambda>V. {x\<in>X. p x \<in> V}) ` F) \<and>
          (\<lambda>V. {x\<in>X. p x \<in> V}) ` F \<noteq> {} \<and>
          (\<lambda>V. {x\<in>X. p x \<in> V}) ` F \<subseteq> TX \<longrightarrow>
          \<Inter>((\<lambda>V. {x\<in>X. p x \<in> V}) ` F) \<in> TX"
        by (rule allE[OF inter_TX, where x="(\<lambda>V. {x\<in>X. p x \<in> V}) ` F"])
      show ?thesis
        by (rule mp[OF hStep hImp])
    qed

    have pre_open: "{x\<in>X. p x \<in> \<Inter>F} \<in> TX"
      by (subst pre_inter_eq) (rule pre_open_img)

    show "\<Inter>F \<in> ?TY"
      unfolding top1_quotient_topology_by_map_on_def
      apply (intro CollectI conjI)
       apply (rule inter_sub)
      apply (rule pre_open)
      done
  qed

  show ?thesis
    unfolding is_topology_on_def
    apply (intro conjI)
       apply (rule empty_TY)
      apply (rule Y_TY)
     apply (rule union_TY)
    apply (rule inter_TY)
    done
qed

(** A map equipped with its induced quotient topology is a quotient map. **)
lemma top1_quotient_map_on_from_quotient_topology_by_map_on:
  assumes hTX: "is_topology_on X TX"
  assumes hpmap: "\<forall>x\<in>X. p x \<in> Y"
  assumes hsurj: "p ` X = Y"
  shows "top1_quotient_map_on X TX Y (top1_quotient_topology_by_map_on X TX Y p) p"
proof -
  let ?TY = "top1_quotient_topology_by_map_on X TX Y p"

  have hTY: "is_topology_on Y ?TY"
    by (rule top1_quotient_topology_by_map_on_is_topology_on[OF hTX hpmap])

  have hpcont: "top1_continuous_map_on X TX Y ?TY p"
    unfolding top1_continuous_map_on_def
    apply (intro conjI)
     apply (rule hpmap)
    unfolding top1_quotient_topology_by_map_on_def
    apply (intro ballI)
    apply (drule CollectD)
    apply (erule conjunct2)
    done

  have hQ: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. p x \<in> V} \<in> TX \<longrightarrow> V \<in> ?TY)"
  proof (intro allI impI)
    fix V assume hVsub: "V \<subseteq> Y"
    assume hpre: "{x\<in>X. p x \<in> V} \<in> TX"
    show "V \<in> ?TY"
      unfolding top1_quotient_topology_by_map_on_def
      using hVsub hpre by simp
  qed

  show ?thesis
    unfolding top1_quotient_map_on_def
    apply (intro conjI)
        apply (rule hTX)
       apply (rule hTY)
      apply (rule hpcont)
     apply (rule hsurj)
    apply (rule hQ)
    done
qed

(** A homeomorphism is a quotient map (in the sense of \<S>22). **)
lemma top1_homeomorphism_on_imp_quotient_map_on:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
  shows "top1_quotient_map_on X TX Y TY f"
proof -
  have hTopX: "is_topology_on X TX"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hbij: "bij_betw f X Y"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hfcont: "top1_continuous_map_on X TX Y TY f"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hinvcont: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    using hhomeo unfolding top1_homeomorphism_on_def by blast

  have hsurj: "f ` X = Y"
    using hbij unfolding bij_betw_def by simp

  have hQ: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. f x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
  proof (intro allI impI)
    fix V assume hVsub: "V \<subseteq> Y"
    assume hpre: "{x\<in>X. f x \<in> V} \<in> TX"

    have hinv_pre: "\<forall>U\<in>TX. {y\<in>Y. inv_into X f y \<in> U} \<in> TY"
      using hinvcont unfolding top1_continuous_map_on_def by blast
    have hpreY: "{y\<in>Y. inv_into X f y \<in> {x\<in>X. f x \<in> V}} \<in> TY"
      using hinv_pre hpre by blast

    have hEq: "{y\<in>Y. inv_into X f y \<in> {x\<in>X. f x \<in> V}} = V"
    proof (rule set_eqI)
      fix y
      show "y \<in> {y \<in> Y. inv_into X f y \<in> {x \<in> X. f x \<in> V}} \<longleftrightarrow> y \<in> V"
      proof (rule iffI)
        assume hy: "y \<in> {y \<in> Y. inv_into X f y \<in> {x \<in> X. f x \<in> V}}"
        have hyY: "y \<in> Y" and hinv: "inv_into X f y \<in> {x \<in> X. f x \<in> V}"
        proof -
          have hy_conj: "y \<in> Y \<and> inv_into X f y \<in> {x \<in> X. f x \<in> V}"
            using hy by simp
          show "y \<in> Y"
            using hy_conj by (rule conjunct1)
          show "inv_into X f y \<in> {x \<in> X. f x \<in> V}"
            using hy_conj by (rule conjunct2)
        qed
        have hyIm: "y \<in> f ` X"
          using hsurj hyY by simp
        have hfy: "f (inv_into X f y) = y"
          using f_inv_into_f[OF hyIm] by simp
        have "f (inv_into X f y) \<in> V"
          using hinv by simp
        thus "y \<in> V"
          using hfy by simp
      next
        assume hyV: "y \<in> V"
        have hyY: "y \<in> Y"
          using hVsub hyV by blast
        have hyIm: "y \<in> f ` X"
          using hsurj hyY by simp
        have hinvX: "inv_into X f y \<in> X"
          by (rule inv_into_into[OF hyIm])
        have hfy: "f (inv_into X f y) = y"
          using f_inv_into_f[OF hyIm] by simp
        have "f (inv_into X f y) \<in> V"
          using hyV hfy by simp
        have "inv_into X f y \<in> {x\<in>X. f x \<in> V}"
          using hinvX \<open>f (inv_into X f y) \<in> V\<close> by simp
        thus "y \<in> {y\<in>Y. inv_into X f y \<in> {x\<in>X. f x \<in> V}}"
          using hyY by simp
      qed
    qed

    show "V \<in> TY"
      using hpreY unfolding hEq by simp
  qed

  show ?thesis
    unfolding top1_quotient_map_on_def
    apply (intro conjI)
        apply (rule hTopX)
       apply (rule hTopY)
      apply (rule hfcont)
     apply (rule hsurj)
    apply (rule hQ)
    done
qed

(** A bijective quotient map is a homeomorphism. **)
lemma top1_bij_quotient_map_on_imp_homeomorphism_on:
  assumes hquot: "top1_quotient_map_on X TX Y TY f"
  assumes hbij: "bij_betw f X Y"
  shows "top1_homeomorphism_on X TX Y TY f"
proof -
  have hTopX: "is_topology_on X TX"
    using hquot unfolding top1_quotient_map_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hquot unfolding top1_quotient_map_on_def by blast
  have hfcont: "top1_continuous_map_on X TX Y TY f"
    using hquot unfolding top1_quotient_map_on_def by blast
  have hsurj: "f ` X = Y"
    using hbij unfolding bij_betw_def by simp
  have hinj: "inj_on f X"
    using hbij unfolding bij_betw_def by simp
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]])
  have hQ: "\<forall>V. V \<subseteq> Y \<longrightarrow> ({x\<in>X. f x \<in> V} \<in> TX \<longrightarrow> V \<in> TY)"
    using hquot unfolding top1_quotient_map_on_def by blast

  have hinvcont: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>y\<in>Y. inv_into X f y \<in> X"
    proof (intro ballI)
      fix y assume hyY: "y \<in> Y"
      have hyIm: "y \<in> f ` X"
        using hsurj hyY by simp
      show "inv_into X f y \<in> X"
        by (rule inv_into_into[OF hyIm])
    qed
    show "\<forall>U\<in>TX. {y\<in>Y. inv_into X f y \<in> U} \<in> TY"
    proof (intro ballI)
      fix U assume hU: "U \<in> TX"
      define W where "W = U \<inter> X"

      have hW: "W \<in> TX"
        unfolding W_def by (rule topology_inter2[OF hTopX hU X_TX])
      have hWsubX: "W \<subseteq> X"
        unfolding W_def by simp

      have hWsubY: "f ` W \<subseteq> Y"
      proof (rule subsetI)
        fix y assume hy: "y \<in> f ` W"
        then obtain x where hxW: "x \<in> W" and hyx: "y = f x"
          by blast
        have hxX: "x \<in> X"
          using hxW unfolding W_def by simp
        have "f x \<in> Y"
          using hfcont hxX unfolding top1_continuous_map_on_def by blast
        thus "y \<in> Y"
          using hyx by simp
      qed

      have hpreEq: "{x\<in>X. f x \<in> f ` W} = W"
      proof (rule equalityI)
        show "{x\<in>X. f x \<in> f ` W} \<subseteq> W"
        proof (rule subsetI)
          fix x assume hx: "x \<in> {x\<in>X. f x \<in> f ` W}"
          have hxX: "x \<in> X" and hfx: "f x \<in> f ` W"
          proof -
            have hx_conj: "x \<in> X \<and> f x \<in> f ` W"
              using hx by simp
            show "x \<in> X"
              using hx_conj by (rule conjunct1)
            show "f x \<in> f ` W"
              using hx_conj by (rule conjunct2)
          qed
          obtain w where hwW: "w \<in> W" and hfw: "f x = f w"
            using hfx by blast
          have hwX: "w \<in> X"
            using hwW hWsubX by blast
          have "x = w"
          proof -
            have hinjD: "\<And>a b. a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> f a = f b \<Longrightarrow> a = b"
            proof -
              fix a b assume haX: "a \<in> X" and hbX: "b \<in> X" and hab: "f a = f b"
              have "\<forall>a\<in>X. \<forall>b\<in>X. f a = f b \<longrightarrow> a = b"
                using hinj unfolding inj_on_def by blast
              thus "a = b"
                using haX hbX hab by blast
            qed
            show "x = w"
              by (rule hinjD[OF hxX hwX hfw])
          qed
          thus "x \<in> W"
            using hwW by simp
        qed
        show "W \<subseteq> {x\<in>X. f x \<in> f ` W}"
        proof (rule subsetI)
          fix x assume hxW: "x \<in> W"
          have hxX: "x \<in> X"
            using hWsubX hxW by blast
          have "f x \<in> f ` W"
            using hxW by blast
          thus "x \<in> {x\<in>X. f x \<in> f ` W}"
            using hxX by simp
        qed
      qed

      have hImgOpen: "f ` W \<in> TY"
      proof -
        have hStep: "{x\<in>X. f x \<in> f ` W} \<in> TX \<longrightarrow> f ` W \<in> TY"
          using hQ hWsubY by blast
        have hpre: "{x\<in>X. f x \<in> f ` W} \<in> TX"
          by (subst hpreEq) (rule hW)
        show ?thesis
          using hStep hpre by blast
      qed

      have hEqInv: "{y\<in>Y. inv_into X f y \<in> U} = f ` W"
      proof (rule set_eqI)
        fix y
        show "y \<in> {y\<in>Y. inv_into X f y \<in> U} \<longleftrightarrow> y \<in> f ` W"
      proof (rule iffI)
        assume hy: "y \<in> {y\<in>Y. inv_into X f y \<in> U}"
        have hyY: "y \<in> Y" and hinvU: "inv_into X f y \<in> U"
        proof -
          have hy_conj: "y \<in> Y \<and> inv_into X f y \<in> U"
            using hy by simp
          show "y \<in> Y"
            using hy_conj by (rule conjunct1)
          show "inv_into X f y \<in> U"
            using hy_conj by (rule conjunct2)
        qed
        have hyIm: "y \<in> f ` X"
          using hsurj hyY by simp
        have hinvX: "inv_into X f y \<in> X"
          by (rule inv_into_into[OF hyIm])
          have hfy: "f (inv_into X f y) = y"
            using f_inv_into_f[OF hyIm] by simp
          have "inv_into X f y \<in> W"
            unfolding W_def using hinvU hinvX by simp
          thus "y \<in> f ` W"
          proof -
            have "f (inv_into X f y) \<in> f ` W"
              using \<open>inv_into X f y \<in> W\<close> by blast
            thus "y \<in> f ` W"
              using hfy by simp
          qed
        next
          assume hy: "y \<in> f ` W"
          then obtain x where hxW: "x \<in> W" and hyx: "y = f x"
            by blast
          have hxX: "x \<in> X"
            using hxW hWsubX by blast
          have hyIm: "y \<in> f ` X"
            using hxX hyx by blast
          have hinv: "inv_into X f y = x"
            using inv_into_f_eq[OF hinj hxX] hyx by simp
          have hyY: "y \<in> Y"
            using hWsubY hy by blast
          have "x \<in> U"
          proof -
            have "x \<in> U \<and> x \<in> X"
              using hxW unfolding W_def by simp
            thus "x \<in> U"
              by simp
          qed
          thus "y \<in> {y\<in>Y. inv_into X f y \<in> U}"
            using hyY hinv by simp
        qed
      qed

      show "{y\<in>Y. inv_into X f y \<in> U} \<in> TY"
        using hImgOpen unfolding hEqInv by simp
    qed
  qed

  show ?thesis
    unfolding top1_homeomorphism_on_def
    apply (intro conjI)
        apply (rule hTopX)
       apply (rule hTopY)
      apply (rule hbij)
     apply (rule hfcont)
    apply (rule hinvcont)
    done
qed

(** Fiber partition determined by a map \<open>g\<close>: the collection \<open>{g^{-1}({z}) | z\<in>Z}\<close> (restricted to \<open>X\<close>). **)
definition top1_fiber_partition_on :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set set" where
  "top1_fiber_partition_on X Z g = (\<lambda>z. {x\<in>X. g x = z}) ` Z"

(** Projection to the fiber through \<open>x\<close>. **)
definition top1_fiber_projection_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "top1_fiber_projection_on X g x = {u\<in>X. g u = g x}"

(** from \S22 Corollary 22.3 [top1.tex:2448] **)
text \<open>
  Intended proof strategy (Munkres \S22, Corollary 22.3):

  - Equip the fiber-partition space \<open>Xstar\<close> with the quotient topology induced by the fiber projection \<open>p\<close>.
    Then \<open>p\<close> is a quotient map (lemma \<open>top1_quotient_map_on_from_quotient_topology_by_map_on\<close>).
  - Apply Theorem 22.2 to factor \<open>g\<close> through \<open>p\<close>, obtaining \<open>f : Xstar \<rightarrow> Z\<close> with
    continuity equivalence and quotient-map equivalence.
  - Use surjectivity of \<open>g\<close> to show \<open>f\<close> is bijective; then relate homeomorphism/quotient-map status via
    auxiliary lemmas about bijective quotient maps and homeomorphisms.
  - For Hausdorff transfer, use injectivity of \<open>f\<close> and pull back disjoint neighborhoods along \<open>f\<close>.
\<close>
corollary Corollary_22_3:
  fixes X :: "'a set"
  fixes TX :: "'a set set"
  fixes Z :: "'b set"
  fixes TZ :: "'b set set"
  fixes g :: "'a \<Rightarrow> 'b"
  defines "Xstar \<equiv> top1_fiber_partition_on X Z g"
  defines "p \<equiv> top1_fiber_projection_on X g"
  defines "Tstar \<equiv> top1_quotient_topology_by_map_on X TX Xstar p"
  assumes hTX: "is_topology_on X TX"
  assumes hTZ: "is_topology_on Z TZ"
  assumes hcont: "top1_continuous_map_on X TX Z TZ g"
  assumes hsurj: "g ` X = Z"
  shows
    "\<exists>f.
      bij_betw f Xstar Z
      \<and> top1_continuous_map_on Xstar Tstar Z TZ f
      \<and> (top1_homeomorphism_on Xstar Tstar Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g)"
    and "is_hausdorff_on Z TZ \<longrightarrow> is_hausdorff_on Xstar Tstar"
proof -
  have hgmap: "\<forall>x\<in>X. g x \<in> Z"
    using hcont unfolding top1_continuous_map_on_def by (rule conjunct1)

  have hpmap: "\<forall>x\<in>X. p x \<in> Xstar"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    have hgxZ: "g x \<in> Z"
      by (rule hgmap[rule_format, OF hxX])
    show "p x \<in> Xstar"
      unfolding Xstar_def p_def top1_fiber_partition_on_def top1_fiber_projection_on_def
      by (rule imageI[OF hgxZ])
  qed

  have hsurjp: "p ` X = Xstar"
  proof (rule subset_antisym)
    show "p ` X \<subseteq> Xstar"
    proof (rule subsetI)
      fix y assume hy: "y \<in> p ` X"
      obtain x where hxX: "x \<in> X" and hyx: "y = p x"
        using hy by (elim imageE)
      show "y \<in> Xstar"
        using hpmap hxX hyx by simp
    qed
    show "Xstar \<subseteq> p ` X"
    proof (rule subsetI)
      fix A assume hA: "A \<in> Xstar"
      obtain z where hzZ: "z \<in> Z" and hAeq: "A = {u\<in>X. g u = z}"
        using hA unfolding Xstar_def top1_fiber_partition_on_def by (elim imageE)
      have hzIm: "z \<in> g ` X"
        using hsurj hzZ by simp
      obtain x where hxX: "x \<in> X" and hz: "z = g x"
        using hzIm by (elim imageE)
      have hgx: "g x = z"
        using hz by simp
      have hpx: "p x = {u\<in>X. g u = z}"
        unfolding p_def top1_fiber_projection_on_def using hgx by simp
      have "A = p x"
        using hAeq hpx by simp
      thus "A \<in> p ` X"
        using hxX by blast
    qed
  qed

  have hpquot: "top1_quotient_map_on X TX Xstar Tstar p"
    unfolding Tstar_def
    by (rule top1_quotient_map_on_from_quotient_topology_by_map_on[OF hTX hpmap hsurjp])

  have hconst: "\<forall>x\<in>X. \<forall>y\<in>X. p x = p y \<longrightarrow> g x = g y"
  proof (rule ballI)
    fix x assume hxX: "x \<in> X"
    show "\<forall>y\<in>X. p x = p y \<longrightarrow> g x = g y"
    proof (rule ballI)
      fix y assume hyX: "y \<in> X"
      show "p x = p y \<longrightarrow> g x = g y"
      proof (rule impI)
        assume hpxy: "p x = p y"
        have hy_py: "y \<in> p y"
          unfolding p_def top1_fiber_projection_on_def using hyX by simp
        have hy_px: "y \<in> p x"
          using hy_py hpxy by simp
        have "g y = g x"
          using hy_px unfolding p_def top1_fiber_projection_on_def by simp
        thus "g x = g y"
          by simp
      qed
    qed
  qed

  have hex_f:
    "\<exists>f.
      (\<forall>y\<in>Xstar. f y \<in> Z)
      \<and> (\<forall>x\<in>X. f (p x) = g x)
      \<and> (top1_continuous_map_on Xstar Tstar Z TZ f \<longleftrightarrow> top1_continuous_map_on X TX Z TZ g)
      \<and> (top1_quotient_map_on Xstar Tstar Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g)"
    by (rule Theorem_22_2[OF hpquot hgmap hconst])

  obtain f where
      hf_map: "\<forall>y\<in>Xstar. f y \<in> Z"
    and hf_factor: "\<forall>x\<in>X. f (p x) = g x"
    and hcont_equiv: "top1_continuous_map_on Xstar Tstar Z TZ f \<longleftrightarrow> top1_continuous_map_on X TX Z TZ g"
    and hquot_equiv: "top1_quotient_map_on Xstar Tstar Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g"
    using hex_f by (elim exE conjE)

  have hfcont: "top1_continuous_map_on Xstar Tstar Z TZ f"
    by (rule iffD2[OF hcont_equiv hcont])

  have hf_image: "f ` Xstar = Z"
  proof (rule subset_antisym)
    show "f ` Xstar \<subseteq> Z"
    proof (rule subsetI)
      fix z assume hz: "z \<in> f ` Xstar"
      then obtain A where hA: "A \<in> Xstar" and hzA: "z = f A"
        by blast
      have "f A \<in> Z"
        using hf_map hA by blast
      thus "z \<in> Z"
        using hzA by simp
    qed
    show "Z \<subseteq> f ` Xstar"
    proof (rule subsetI)
      fix z assume hzZ: "z \<in> Z"
      have hzIm: "z \<in> g ` X"
        using hsurj hzZ by simp
      obtain x where hxX: "x \<in> X" and hz: "z = g x"
        using hzIm by (elim imageE)
      have hgx: "g x = z"
        using hz by simp
      have hpx: "p x \<in> Xstar"
        using hpmap hxX by blast
      have "f (p x) = z"
        using hf_factor hxX hgx by simp
      thus "z \<in> f ` Xstar"
        using hpx by blast
    qed
  qed

  have hf_inj: "inj_on f Xstar"
  proof (rule inj_onI)
    fix A B assume hA: "A \<in> Xstar" and hB: "B \<in> Xstar"
    assume hEq: "f A = f B"
    have hAIm: "A \<in> p ` X"
      using hsurjp hA by simp
    obtain xA where hxAX: "xA \<in> X" and hAeq: "A = p xA"
      using hAIm by (elim imageE)
    have hBIm: "B \<in> p ` X"
      using hsurjp hB by simp
    obtain xB where hxBX: "xB \<in> X" and hBeq: "B = p xB"
      using hBIm by (elim imageE)

    have "g xA = g xB"
    proof -
      have hfxA: "f (p xA) = g xA"
        by (rule bspec[OF hf_factor hxAX])
      have hfxB: "f (p xB) = g xB"
        by (rule bspec[OF hf_factor hxBX])
      have "f (p xA) = f (p xB)"
        using hEq hAeq hBeq by simp
      thus "g xA = g xB"
        using hfxA hfxB by simp
    qed
    hence "p xA = p xB"
      unfolding p_def top1_fiber_projection_on_def by simp
    thus "A = B"
      using hAeq hBeq by simp
  qed

  have hbij: "bij_betw f Xstar Z"
    unfolding bij_betw_def
    apply (intro conjI)
     apply (rule hf_inj)
    apply (rule hf_image)
    done

  have hhomeo_iff_gquot:
    "top1_homeomorphism_on Xstar Tstar Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g"
  proof (rule iffI)
    assume hhomeo: "top1_homeomorphism_on Xstar Tstar Z TZ f"
    have hquotf: "top1_quotient_map_on Xstar Tstar Z TZ f"
      by (rule top1_homeomorphism_on_imp_quotient_map_on[OF hhomeo])
    show "top1_quotient_map_on X TX Z TZ g"
      using hquot_equiv hquotf by simp
  next
    assume hquotg: "top1_quotient_map_on X TX Z TZ g"
    have hquotf: "top1_quotient_map_on Xstar Tstar Z TZ f"
      using hquot_equiv hquotg by simp
    show "top1_homeomorphism_on Xstar Tstar Z TZ f"
      by (rule top1_bij_quotient_map_on_imp_homeomorphism_on[OF hquotf hbij])
  qed

  show "\<exists>f.
      bij_betw f Xstar Z
      \<and> top1_continuous_map_on Xstar Tstar Z TZ f
      \<and> (top1_homeomorphism_on Xstar Tstar Z TZ f \<longleftrightarrow> top1_quotient_map_on X TX Z TZ g)"
    apply (rule exI[where x=f])
    apply (intro conjI)
      apply (rule hbij)
     apply (rule hfcont)
    apply (rule hhomeo_iff_gquot)
    done

  show "is_hausdorff_on Z TZ \<longrightarrow> is_hausdorff_on Xstar Tstar"
  proof (intro impI)
    assume hHausZ: "is_hausdorff_on Z TZ"

    have hTopXstar: "is_topology_on Xstar Tstar"
      unfolding Tstar_def
      by (rule top1_quotient_topology_by_map_on_is_topology_on[OF hTX hpmap])
    show "is_hausdorff_on Xstar Tstar"
      by (rule hausdorff_on_of_inj_continuous_map[OF hTopXstar hHausZ hfcont hf_inj])
  qed
qed


end
