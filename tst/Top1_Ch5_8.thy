theory Top1_Ch5_8
  imports Top1_Ch4
begin

section \<open>\<S>37 The Tychonoff Theorem\<close>

text \<open>
  Status note (2026-03-24):
  Fully proved major results:
    \<open>\<S>37\<close> Tychonoff (Thm 37.3)
    \<open>\<S>41\<close> Paracompact Hausdorff \<open>\<Rightarrow>\<close> Normal (Thm 41.1)
    \<open>\<S>48\<close> Baire category (Thm 48.2, both parts)
  Remaining admits (46 total) in \<open>\<S>38\<close>--\<open>\<S>50\<close>:
  \<open>\<S>38\<close>: 3, \<open>\<S>39\<close>: 1, \<open>\<S>40\<close>: 3, \<open>\<S>41\<close>: 7, \<open>\<S>42\<close>: 1, \<open>\<S>43\<close>: 4, \<open>\<S>44\<close>: 1,
  \<open>\<S>45\<close>: 5, \<open>\<S>46\<close>: 4, \<open>\<S>47\<close>: 4, \<open>\<S>48\<close>: 1, \<open>\<S>49\<close>: 4, \<open>\<S>50\<close>: 8.
\<close>

text \<open>
  Chapter 5 of \<open>top1.tex\<close> begins with the Tychonoff theorem. We start by isolating
  the finite-intersection-property (FIP) combinatorics used in the standard closed-set proof.
\<close>

definition top1_FIP_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_FIP_on X \<A> \<longleftrightarrow>
     (\<forall>A\<in>\<A>. A \<subseteq> X) \<and> (\<forall>F. finite F \<and> F \<subseteq> \<A> \<longrightarrow> \<Inter>F \<noteq> {})"

definition top1_FIP_maximal_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_FIP_maximal_on X \<D> \<longleftrightarrow>
     top1_FIP_on X \<D> \<and> (\<forall>\<E>. \<D> \<subset> \<E> \<and> (\<forall>A\<in>\<E>. A \<subseteq> X) \<longrightarrow> \<not> top1_FIP_on X \<E>)"

(** from \S37 Lemma 37.1 (Maximal families with the finite intersection property) [top1.tex:5210] **)
lemma Lemma_37_1:
  assumes hFIP: "top1_FIP_on X \<A>"
  shows "\<exists>\<D>. \<A> \<subseteq> \<D> \<and> top1_FIP_maximal_on X \<D>"
proof -
  let ?Z = "{\<B>. \<A> \<subseteq> \<B> \<and> top1_FIP_on X \<B>}"

  have hAinZ: "\<A> \<in> ?Z"
    using hFIP by simp

  have hChainUB: "\<forall>\<C>\<in>chains ?Z. \<exists>U\<in>?Z. \<forall>\<B>\<in>\<C>. \<B> \<subseteq> U"
  proof (intro ballI)
    fix \<C>
    assume hC: "\<C> \<in> chains ?Z"

    show "\<exists>U\<in>?Z. \<forall>\<B>\<in>\<C>. \<B> \<subseteq> U"
    proof (cases "\<C> = {}")
      case True
      show ?thesis
        using hAinZ True by blast
    next
      case False
      let ?U = "\<Union>\<C>"

      have hU_ub: "\<forall>\<B>\<in>\<C>. \<B> \<subseteq> ?U"
        by blast

      have hCsubZ: "\<C> \<subseteq> ?Z"
        using hC by (rule chainsD2)

      obtain \<B>0 where hB0: "\<B>0 \<in> \<C>"
        using False by blast

      have hAsubU: "\<A> \<subseteq> ?U"
      proof -
        have hB0inZ: "\<B>0 \<in> ?Z"
          using hCsubZ hB0 by blast
        have hAsubB0: "\<A> \<subseteq> \<B>0"
          using hB0inZ by simp
        have hB0subU: "\<B>0 \<subseteq> ?U"
          using hU_ub hB0 by blast
        show ?thesis
          using hAsubB0 hB0subU by blast
      qed

      have hFIPU: "top1_FIP_on X ?U"
      proof -
        have hSubX: "\<forall>A\<in>?U. A \<subseteq> X"
        proof (intro ballI)
          fix A
          assume hA: "A \<in> ?U"
          then obtain \<B> where hB: "\<B> \<in> \<C>" and hAB: "A \<in> \<B>"
            by blast
          have hBinZ: "\<B> \<in> ?Z"
            using hCsubZ hB by blast
          have hFIPB: "top1_FIP_on X \<B>"
            using hBinZ by simp
          have "\<forall>A0\<in>\<B>. A0 \<subseteq> X"
            using hFIPB unfolding top1_FIP_on_def by (rule conjunct1)
          then show "A \<subseteq> X"
            using hAB by blast
        qed

        have hFinInter: "\<forall>F. finite F \<and> F \<subseteq> ?U \<longrightarrow> \<Inter>F \<noteq> {}"
        proof (intro allI impI)
          fix F
          assume hF: "finite F \<and> F \<subseteq> ?U"
          have hFfin: "finite F"
            using hF by simp
          have hFsubU: "F \<subseteq> ?U"
            using hF by simp

          have hFindInC: "\<exists>\<B>\<in>\<C>. F \<subseteq> \<B>"
            using hFfin hFsubU
          proof (induction rule: finite_induct)
            case empty
            show ?case
              apply (rule bexI[where x=\<B>0])
               apply simp
              apply (rule hB0)
              done
          next
            case (insert a F)
            have hFsubU': "F \<subseteq> ?U"
              using insert.prems by simp
            obtain \<B>1 where hB1: "\<B>1 \<in> \<C>" and hFsubB1: "F \<subseteq> \<B>1"
              using insert.IH hFsubU' by blast
            have haU: "a \<in> ?U"
              using insert.prems by simp
            then obtain \<B>2 where hB2: "\<B>2 \<in> \<C>" and haB2: "a \<in> \<B>2"
              by blast
            have hChain: "\<B>1 \<subseteq> \<B>2 \<or> \<B>2 \<subseteq> \<B>1"
              using hC hB1 hB2 by (rule chainsD)
            show ?case
            proof (cases "\<B>1 \<subseteq> \<B>2")
              case True
              have hIns: "insert a F \<subseteq> \<B>2"
              proof
                fix y
                assume hy: "y \<in> insert a F"
                show "y \<in> \<B>2"
                proof (cases "y = a")
                  case True
                  then show ?thesis
                    using haB2 by simp
                next
                  case False
                  have "y \<in> F"
                    using hy False by simp
                  then have "y \<in> \<B>1"
                    using hFsubB1 by blast
                  then show ?thesis
                    using True by blast
                qed
              qed
              show ?thesis
                using hB2 hIns by blast
            next
              case False
              have hB2subB1: "\<B>2 \<subseteq> \<B>1"
                using hChain False by blast
              have hIns: "insert a F \<subseteq> \<B>1"
              proof
                fix y
                assume hy: "y \<in> insert a F"
                show "y \<in> \<B>1"
                proof (cases "y = a")
                  case True
                  have "a \<in> \<B>1"
                    using haB2 hB2subB1 by blast
                  then show ?thesis
                    using True by simp
                next
                  case False
                  have "y \<in> F"
                    using hy False by simp
                  then show ?thesis
                    using hFsubB1 by blast
                qed
              qed
              show ?thesis
                using hB1 hIns by blast
            qed
          qed

          then obtain \<B> where hB: "\<B> \<in> \<C>" and hFsubB: "F \<subseteq> \<B>"
            by blast
          have hBinZ: "\<B> \<in> ?Z"
            using hCsubZ hB by blast
          have hFIPB: "top1_FIP_on X \<B>"
            using hBinZ by simp
          have hFIPB': "\<forall>G. finite G \<and> G \<subseteq> \<B> \<longrightarrow> \<Inter>G \<noteq> {}"
            using hFIPB unfolding top1_FIP_on_def by (rule conjunct2)
          show "\<Inter>F \<noteq> {}"
            using hFIPB' hFfin hFsubB by blast
        qed

        show ?thesis
          unfolding top1_FIP_on_def
          apply (intro conjI)
           apply (rule hSubX)
          apply (rule hFinInter)
          done
      qed

      have hUinZ: "?U \<in> ?Z"
        using hAsubU hFIPU by simp

      show ?thesis
        using hUinZ hU_ub by blast
    qed
  qed

  obtain \<D> where hDinZ: "\<D> \<in> ?Z"
    and hDmax: "\<forall>\<B>\<in>?Z. \<D> \<subseteq> \<B> \<longrightarrow> \<B> = \<D>"
    using Zorn_Lemma2[OF hChainUB] by blast

  have hAsubD: "\<A> \<subseteq> \<D>"
    using hDinZ by simp
  have hFIPD: "top1_FIP_on X \<D>"
    using hDinZ by simp

  have hMaxFIP: "\<forall>\<E>. \<D> \<subset> \<E> \<and> (\<forall>A\<in>\<E>. A \<subseteq> X) \<longrightarrow> \<not> top1_FIP_on X \<E>"
  proof (intro allI impI)
    fix \<E>
    assume hE: "\<D> \<subset> \<E> \<and> (\<forall>A\<in>\<E>. A \<subseteq> X)"
    have hpsub: "\<D> \<subset> \<E>"
      using hE by (rule conjunct1)
    have hDsubE: "\<D> \<subseteq> \<E>"
      using hpsub by (rule psubset_imp_subset)

    show "\<not> top1_FIP_on X \<E>"
    proof (rule ccontr)
      assume hFIP_E: "\<not> (\<not> top1_FIP_on X \<E>)"
      have hFIP_E': "top1_FIP_on X \<E>"
        using hFIP_E by simp

      have hA_subE: "\<A> \<subseteq> \<E>"
        using hAsubD hDsubE by blast

      have hEinZ: "\<E> \<in> ?Z"
        using hA_subE hFIP_E' by simp

      have hEq: "\<E> = \<D>"
        using hDmax hEinZ hDsubE by blast

      have "\<D> \<subset> \<D>"
        using hE hEq by simp
      then show False
        by simp
    qed
  qed

  show "\<exists>\<D>. \<A> \<subseteq> \<D> \<and> top1_FIP_maximal_on X \<D>"
  proof (rule exI[where x=\<D>], intro conjI)
    show "\<A> \<subseteq> \<D>"
      by (rule hAsubD)
    show "top1_FIP_maximal_on X \<D>"
      unfolding top1_FIP_maximal_on_def
      apply (intro conjI)
       apply (rule hFIPD)
      apply (rule hMaxFIP)
      done
  qed
qed

(** from \S37 Lemma 37.2 (Properties of maximal FIP families) [top1.tex:5232] **)
lemma Lemma_37_2:
  assumes hmax: "top1_FIP_maximal_on X \<D>"
  assumes hXne: "X \<noteq> {}"
  shows "(\<forall>F. finite F \<and> F \<subseteq> \<D> \<and> F \<noteq> {} \<longrightarrow> \<Inter>F \<in> \<D>)"
    and "(\<forall>A. A \<subseteq> X \<and> (\<forall>D0\<in>\<D>. intersects A D0) \<longrightarrow> A \<in> \<D>)"
proof -
  have hFIP: "top1_FIP_on X \<D>"
    using hmax unfolding top1_FIP_maximal_on_def by simp

  have hDsubX: "\<forall>D0\<in>\<D>. D0 \<subseteq> X"
    using hFIP unfolding top1_FIP_on_def by simp

  have hMax:
    "\<forall>\<E>. \<D> \<subset> \<E> \<and> (\<forall>A\<in>\<E>. A \<subseteq> X) \<longrightarrow> \<not> top1_FIP_on X \<E>"
    using hmax unfolding top1_FIP_maximal_on_def by simp

  have hFIP_D:
    "\<forall>F. finite F \<and> F \<subseteq> \<D> \<longrightarrow> \<Inter>F \<noteq> {}"
    using hFIP unfolding top1_FIP_on_def by simp

  have hInter_inD: "(\<forall>F. finite F \<and> F \<subseteq> \<D> \<and> F \<noteq> {} \<longrightarrow> \<Inter>F \<in> \<D>)"
  proof (intro allI impI)
    fix F
    assume hF: "finite F \<and> F \<subseteq> \<D> \<and> F \<noteq> {}"
    have hFfin: "finite F"
      using hF by simp
    have hFsub: "F \<subseteq> \<D>"
      using hF by simp
    have hFne: "F \<noteq> {}"
      using hF by simp

    have hInter_subX: "\<Inter>F \<subseteq> X"
    proof (rule subsetI)
      fix x
      assume hx: "x \<in> \<Inter>F"
      have hxF: "\<forall>A\<in>F. x \<in> A"
        using hx by simp
      obtain A0 where hA0: "A0 \<in> F"
        using hFne by blast
      have hA0subX: "A0 \<subseteq> X"
        using hDsubX hFsub hA0 by blast
      have hxA0: "x \<in> A0"
        using hxF hA0 by blast
      show "x \<in> X"
        using hA0subX hxA0 by blast
    qed

    show "\<Inter>F \<in> \<D>"
    proof (rule ccontr)
      assume hNot: "\<Inter>F \<notin> \<D>"
      let ?\<E> = "insert (\<Inter>F) \<D>"

      have hDsubE: "\<D> \<subset> ?\<E>"
        using hNot by auto

      have hEsubX: "\<forall>A\<in>?\<E>. A \<subseteq> X"
      proof
        fix A
        assume hA: "A \<in> ?\<E>"
        show "A \<subseteq> X"
        proof (cases "A = \<Inter>F")
          case True
          show ?thesis
            using True hInter_subX by simp
        next
          case False
          have "A \<in> \<D>"
            using hA False by simp
          then show ?thesis
            using hDsubX by blast
        qed
      qed

      have hFIP_E: "top1_FIP_on X ?\<E>"
      proof -
        have hAllSub: "(\<forall>A\<in>?\<E>. A \<subseteq> X)"
          using hEsubX .

        have hInterNE: "\<forall>G. finite G \<and> G \<subseteq> ?\<E> \<longrightarrow> \<Inter>G \<noteq> {}"
        proof (intro allI impI)
          fix G
          assume hG: "finite G \<and> G \<subseteq> ?\<E>"
          have hGfin: "finite G"
            using hG by simp
          have hGsub: "G \<subseteq> ?\<E>"
            using hG by simp

          show "\<Inter>G \<noteq> {}"
          proof (cases "\<Inter>F \<in> G")
            case False
            have hGsubD: "G \<subseteq> \<D>"
              using hGsub False by auto
            show ?thesis
              using hFIP_D hGfin hGsubD by blast
          next
            case True
            define H where "H = G - {\<Inter>F}"
            have hHfin: "finite H"
              using hGfin unfolding H_def by simp
            have hHsubD: "H \<subseteq> \<D>"
              using hGsub unfolding H_def by auto

            have hFUfin: "finite (F \<union> H)"
              using hFfin hHfin by simp
            have hFUsubD: "F \<union> H \<subseteq> \<D>"
              using hFsub hHsubD by auto

            have hInterFU: "\<Inter>(F \<union> H) \<noteq> {}"
              using hFIP_D hFUfin hFUsubD by blast

            have hInterG: "\<Inter>G = (\<Inter>F) \<inter> \<Inter>H"
            proof -
              have hGeq: "G = insert (\<Inter>F) H"
              proof (rule subset_antisym)
                show "G \<subseteq> insert (\<Inter>F) H"
                proof
                  fix y
                  assume hy: "y \<in> G"
                  show "y \<in> insert (\<Inter>F) H"
                  proof (cases "y = \<Inter>F")
                    case True
                    then show ?thesis by simp
                  next
                    case False
                    have "y \<in> H"
                      using hy False unfolding H_def by simp
                    then show ?thesis by simp
                  qed
                qed
              next
                show "insert (\<Inter>F) H \<subseteq> G"
                proof
                  fix y
                  assume hy: "y \<in> insert (\<Inter>F) H"
                  show "y \<in> G"
                  proof (cases "y = \<Inter>F")
                    case True
                    then show ?thesis
                      using \<open>\<Inter>F \<in> G\<close> by simp
                  next
                    case False
                    have "y \<in> H"
                      using hy False by simp
                    then show ?thesis
                      unfolding H_def by simp
                  qed
                qed
              qed
              show ?thesis
                unfolding hGeq by simp
            qed

            have hInterFU_eq: "\<Inter>(F \<union> H) = (\<Inter>F) \<inter> \<Inter>H"
            proof (rule subset_antisym)
              show "\<Inter>(F \<union> H) \<subseteq> (\<Inter>F) \<inter> \<Inter>H"
              proof
                fix x
                assume hx: "x \<in> \<Inter>(F \<union> H)"
                have hxAll: "\<forall>A\<in>F \<union> H. x \<in> A"
                  using hx by simp
                have hxF: "\<forall>A\<in>F. x \<in> A"
                  using hxAll by blast
                have hxH: "\<forall>A\<in>H. x \<in> A"
                  using hxAll by blast
                show "x \<in> (\<Inter>F) \<inter> \<Inter>H"
                  using hxF hxH by simp
              qed
              show "(\<Inter>F) \<inter> \<Inter>H \<subseteq> \<Inter>(F \<union> H)"
              proof
                fix x
                assume hx: "x \<in> (\<Inter>F) \<inter> \<Inter>H"
                have hxF: "\<forall>A\<in>F. x \<in> A"
                  using hx by simp
                have hxH: "\<forall>A\<in>H. x \<in> A"
                  using hx by simp
                have hxAll: "\<forall>A\<in>F \<union> H. x \<in> A"
                  using hxF hxH by blast
                show "x \<in> \<Inter>(F \<union> H)"
                  using hxAll by simp
              qed
            qed

            show ?thesis
              using hInterFU hInterG hInterFU_eq by simp
          qed
        qed

        show ?thesis
          unfolding top1_FIP_on_def
          apply (intro conjI)
           apply (rule hAllSub)
          apply (rule hInterNE)
          done
      qed

      have hNoFIP: "\<not> top1_FIP_on X ?\<E>"
      proof -
        have hImp: "(\<D> \<subset> ?\<E> \<and> (\<forall>A\<in>?\<E>. A \<subseteq> X)) \<longrightarrow> \<not> top1_FIP_on X ?\<E>"
          using hMax by (rule allE[where x="?\<E>"])
        have hPrem: "\<D> \<subset> ?\<E> \<and> (\<forall>A\<in>?\<E>. A \<subseteq> X)"
          using hDsubE hEsubX by simp
        show ?thesis
          using hImp hPrem by simp
      qed

      show False
        using hNoFIP hFIP_E by contradiction
    qed
  qed

  show "(\<forall>F. finite F \<and> F \<subseteq> \<D> \<and> F \<noteq> {} \<longrightarrow> \<Inter>F \<in> \<D>)"
    using hInter_inD .

  have hX_inD: "X \<in> \<D>"
  proof (rule ccontr)
    assume hNot: "X \<notin> \<D>"
    let ?\<E> = "insert X \<D>"

    have hDsubE: "\<D> \<subset> ?\<E>"
      using hNot by auto

    have hEsubX: "\<forall>A\<in>?\<E>. A \<subseteq> X"
      using hDsubX by auto

    have hFIP_E: "top1_FIP_on X ?\<E>"
    proof -
      have hInterNE: "\<forall>G. finite G \<and> G \<subseteq> ?\<E> \<longrightarrow> \<Inter>G \<noteq> {}"
      proof (intro allI impI)
        fix G
        assume hG: "finite G \<and> G \<subseteq> ?\<E>"
        have hGfin: "finite G"
          using hG by simp
        have hGsub: "G \<subseteq> ?\<E>"
          using hG by simp

        show "\<Inter>G \<noteq> {}"
        proof (cases "X \<in> G")
          case False
          have hGsubD: "G \<subseteq> \<D>"
            using hGsub False by auto
          show ?thesis
            using hFIP_D hGfin hGsubD by blast
        next
          case True
          define H where "H = G - {X}"
          have hHfin: "finite H"
            using hGfin unfolding H_def by simp
          have hHsubD: "H \<subseteq> \<D>"
            using hGsub unfolding H_def by auto

          have hInterH: "\<Inter>H \<noteq> {}"
            using hFIP_D hHfin hHsubD by blast

          have hInterG: "\<Inter>G = X \<inter> \<Inter>H"
          proof -
            have hGeq: "G = insert X H"
            proof (rule subset_antisym)
              show "G \<subseteq> insert X H"
              proof
                fix y
                assume hy: "y \<in> G"
                show "y \<in> insert X H"
                proof (cases "y = X")
                  case True
                  then show ?thesis by simp
                next
                  case False
                  have "y \<in> H"
                    using hy False unfolding H_def by simp
                  then show ?thesis by simp
                qed
              qed
            next
              show "insert X H \<subseteq> G"
              proof
                fix y
                assume hy: "y \<in> insert X H"
                show "y \<in> G"
                proof (cases "y = X")
                  case True
                  then show ?thesis
                    using \<open>X \<in> G\<close> by simp
                next
                  case False
                  have "y \<in> H"
                    using hy False by simp
                  then show ?thesis
                    unfolding H_def by simp
                qed
              qed
            qed
            show ?thesis
              unfolding hGeq by simp
          qed

          show ?thesis
          proof (cases "H = {}")
            case True
            have "\<Inter>G = X"
              using hInterG unfolding True by simp
            then show ?thesis
              using hXne by simp
          next
            case False
            have hInterH_subX: "\<Inter>H \<subseteq> X"
            proof (rule subsetI)
              fix x
              assume hx: "x \<in> \<Inter>H"
              have hxH: "\<forall>A\<in>H. x \<in> A"
                using hx by simp
              obtain A0 where hA0: "A0 \<in> H"
                using False by blast
              have hA0subX: "A0 \<subseteq> X"
                using hDsubX hHsubD hA0 by blast
              have hxA0: "x \<in> A0"
                using hxH hA0 by blast
              show "x \<in> X"
                using hA0subX hxA0 by blast
            qed

            have "\<Inter>G = \<Inter>H"
              using hInterG hInterH_subX by auto
            then show ?thesis
              using hInterH by simp
          qed
        qed
      qed

      show ?thesis
        unfolding top1_FIP_on_def
        apply (intro conjI)
         apply (rule hEsubX)
        apply (rule hInterNE)
        done
    qed

    have hNoFIP: "\<not> top1_FIP_on X ?\<E>"
    proof -
      have hImp: "(\<D> \<subset> ?\<E> \<and> (\<forall>A\<in>?\<E>. A \<subseteq> X)) \<longrightarrow> \<not> top1_FIP_on X ?\<E>"
        using hMax by (rule allE[where x="?\<E>"])
      have hPrem: "\<D> \<subset> ?\<E> \<and> (\<forall>A\<in>?\<E>. A \<subseteq> X)"
        using hDsubE hEsubX by simp
      show ?thesis
        using hImp hPrem by simp
    qed

    show False
      using hNoFIP hFIP_E by contradiction
  qed

  show "(\<forall>A. A \<subseteq> X \<and> (\<forall>D0\<in>\<D>. intersects A D0) \<longrightarrow> A \<in> \<D>)"
  proof (intro allI impI)
    fix A
    assume hA: "A \<subseteq> X \<and> (\<forall>D0\<in>\<D>. intersects A D0)"
    have hAsubX: "A \<subseteq> X"
      using hA by simp
    have hIntAll: "\<forall>D0\<in>\<D>. intersects A D0"
      using hA by simp

    have hAne: "A \<noteq> {}"
    proof -
      have "intersects A X"
        using hIntAll hX_inD by blast
      then have "A \<inter> X \<noteq> {}"
        unfolding intersects_def .
      then show ?thesis
        using hAsubX by auto
    qed

    show "A \<in> \<D>"
    proof (rule ccontr)
      assume hNot: "A \<notin> \<D>"
      let ?\<E> = "insert A \<D>"

      have hDsubE: "\<D> \<subset> ?\<E>"
        using hNot by auto

      have hEsubX: "\<forall>U\<in>?\<E>. U \<subseteq> X"
        using hDsubX hAsubX by auto

      have hFIP_E: "top1_FIP_on X ?\<E>"
      proof -
        have hInterNE: "\<forall>G. finite G \<and> G \<subseteq> ?\<E> \<longrightarrow> \<Inter>G \<noteq> {}"
        proof (intro allI impI)
          fix G
          assume hG: "finite G \<and> G \<subseteq> ?\<E>"
          have hGfin: "finite G"
            using hG by simp
          have hGsub: "G \<subseteq> ?\<E>"
            using hG by simp

          show "\<Inter>G \<noteq> {}"
          proof (cases "A \<in> G")
            case False
            have hGsubD: "G \<subseteq> \<D>"
              using hGsub False by auto
            show ?thesis
              using hFIP_D hGfin hGsubD by blast
          next
            case True
            define H where "H = G - {A}"
            have hHfin: "finite H"
              using hGfin unfolding H_def by simp
            have hHsubD: "H \<subseteq> \<D>"
              using hGsub unfolding H_def by auto

            have hInterG: "\<Inter>G = A \<inter> \<Inter>H"
            proof -
              have hGeq: "G = insert A H"
              proof (rule subset_antisym)
                show "G \<subseteq> insert A H"
                proof
                  fix y
                  assume hy: "y \<in> G"
                  show "y \<in> insert A H"
                  proof (cases "y = A")
                    case True
                    then show ?thesis by simp
                  next
                    case False
                    have "y \<in> H"
                      using hy False unfolding H_def by simp
                    then show ?thesis by simp
                  qed
                qed
              next
                show "insert A H \<subseteq> G"
                proof
                  fix y
                  assume hy: "y \<in> insert A H"
                  show "y \<in> G"
                  proof (cases "y = A")
                    case True
                    then show ?thesis
                      using \<open>A \<in> G\<close> by simp
                  next
                    case False
                    have "y \<in> H"
                      using hy False by simp
                    then show ?thesis
                      unfolding H_def by simp
                  qed
                qed
              qed
              show ?thesis
                unfolding hGeq by simp
            qed

            show ?thesis
            proof (cases "H = {}")
              case True
              show ?thesis
                using hAne hInterG unfolding True by simp
            next
              case False
              have hInterH_inD: "\<Inter>H \<in> \<D>"
              proof -
                have hH: "finite H \<and> H \<subseteq> \<D> \<and> H \<noteq> {}"
                  using hHfin hHsubD False by simp
                show ?thesis
                  using hInter_inD hH by blast
              qed

              have hIntAH: "intersects A (\<Inter>H)"
                using hIntAll hInterH_inD by blast
              have hInterAH: "A \<inter> \<Inter>H \<noteq> {}"
                using hIntAH unfolding intersects_def .

              show ?thesis
                using hInterAH hInterG by simp
            qed
          qed
        qed

        show ?thesis
          unfolding top1_FIP_on_def
          apply (intro conjI)
           apply (rule hEsubX)
          apply (rule hInterNE)
          done
      qed

      have hNoFIP: "\<not> top1_FIP_on X ?\<E>"
      proof -
        have hImp: "(\<D> \<subset> ?\<E> \<and> (\<forall>A\<in>?\<E>. A \<subseteq> X)) \<longrightarrow> \<not> top1_FIP_on X ?\<E>"
          using hMax by (rule allE[where x="?\<E>"])
        have hPrem: "\<D> \<subset> ?\<E> \<and> (\<forall>A\<in>?\<E>. A \<subseteq> X)"
          using hDsubE hEsubX by simp
        show ?thesis
          using hImp hPrem by simp
      qed

      show False
        using hNoFIP hFIP_E by contradiction
    qed
  qed
qed

text \<open>Extract the forward direction of the FIP characterization of compactness
  as a standalone lemma, to avoid tactic explosions when using Theorem 26.9 inline.\<close>
lemma compact_closed_FIP_inter_ne:
  assumes hTop: "is_topology_on X TX"
  assumes hComp: "top1_compact_on X TX"
  assumes hClosed: "\<forall>C\<in>\<C>. closedin_on X TX C"
  assumes hFIP: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {}"
  shows "\<Inter>\<C> \<noteq> {}"
proof -
  have hiff: "top1_compact_on X TX \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
         (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})
         \<longrightarrow> \<Inter>\<C> \<noteq> {})"
    by (rule Theorem_26_9[OF hTop])
  have hall: "\<forall>\<C>. (\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
       (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})
       \<longrightarrow> \<Inter>\<C> \<noteq> {}"
    by (rule iffD1[OF hiff hComp])
  have hprem: "(\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
       (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})"
    using hClosed hFIP by blast
  show ?thesis
    using spec[OF hall, of \<C>] hprem by (rule mp)
qed

lemma mem_of_eq: "x \<in> A \<Longrightarrow> A = B \<Longrightarrow> x \<in> B" by simp
lemma mem_of_eq_sym: "x \<in> A \<Longrightarrow> y = x \<Longrightarrow> y \<in> A" by simp
lemma mem_of_elem_eq: "x \<in> A \<Longrightarrow> x = y \<Longrightarrow> y \<in> A" by simp

text \<open>Minimal test: project FIP and show intersection of closures is nonempty for one coord.\<close>
lemma tychonoff_coord_point:
  assumes hFIP: "top1_FIP_on (top1_PiE I X) \<D>"
  assumes hDne: "\<D> \<noteq> {}"
  assumes hTopi: "is_topology_on (Xi) (TXi)"
  assumes hCompi: "top1_compact_on (Xi) (TXi)"
  assumes hi: "i \<in> I"
  assumes hDsub: "\<forall>D\<in>\<D>. D \<subseteq> top1_PiE I X"
  assumes hproj_sub: "\<forall>D\<in>\<D>. (\<lambda>f. f i) ` D \<subseteq> Xi"
  shows "\<exists>xi. xi \<in> Xi \<and> (\<forall>D\<in>\<D>. xi \<in> closure_on Xi TXi ((\<lambda>f. f i) ` D))"
proof -
  have hCclosed: "\<forall>C\<in>((\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>). closedin_on Xi TXi C"
  proof (intro ballI)
    fix C assume "C \<in> (\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>"
    then obtain D where hD: "D \<in> \<D>" and hCdef: "C = closure_on Xi TXi ((\<lambda>f. f i) ` D)" by blast
    show "closedin_on Xi TXi C"
      unfolding hCdef
      by (rule closure_on_closed[OF hTopi hproj_sub[rule_format, OF hD]])
  qed
  have hFIP_D: "\<forall>G. finite G \<and> G \<subseteq> \<D> \<longrightarrow> \<Inter>G \<noteq> {}"
    using hFIP unfolding top1_FIP_on_def by simp
  have hCfip: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> ((\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>) \<longrightarrow> \<Inter>F \<noteq> {}"
  proof (intro allI impI)
    fix F
    assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> ((\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>)"
    have hFfin: "finite F" using hF by simp
    have hFsub: "F \<subseteq> ((\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>)" using hF by simp
    have hsel: "\<forall>C\<in>F. \<exists>D\<in>\<D>. C = closure_on Xi TXi ((\<lambda>f. f i) ` D)"
      using hFsub by blast
    then obtain g where hg: "\<forall>C\<in>F. g C \<in> \<D> \<and> C = closure_on Xi TXi ((\<lambda>f. f i) ` (g C))"
      by metis
    have hGfin: "finite (g ` F)" using hFfin by simp
    have hGsub: "g ` F \<subseteq> \<D>" using hg by blast
    have "finite (g ` F) \<and> g ` F \<subseteq> \<D>" using hGfin hGsub by simp
    then have "\<Inter>(g ` F) \<noteq> {}" using hFIP_D by blast
    then obtain z where hz: "\<forall>D\<in>(g ` F). z \<in> D" by blast
    have "\<forall>C\<in>F. z i \<in> C"
    proof
      fix C assume hC: "C \<in> F"
      have hzgC: "z \<in> g C" using hz hC by blast
      have hzi_proj: "z i \<in> (\<lambda>f. f i) ` (g C)" using hzgC by blast
      have hproj_sub_cl: "(\<lambda>f. f i) ` (g C) \<subseteq> closure_on Xi TXi ((\<lambda>f. f i) ` (g C))"
        by (rule subset_closure_on)
      have hzi_cl: "z i \<in> closure_on Xi TXi ((\<lambda>f. f i) ` (g C))"
        by (rule subsetD[OF hproj_sub_cl hzi_proj])
      have hCeq: "closure_on Xi TXi ((\<lambda>f. f i) ` (g C)) = C"
        using hg hC by blast
      show "z i \<in> C"
        by (rule mem_of_eq[OF hzi_cl hCeq])
    qed
    then show "\<Inter>F \<noteq> {}" by blast
  qed
  have hne: "\<Inter>((\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>) \<noteq> {}"
    by (rule compact_closed_FIP_inter_ne[OF hTopi hCompi hCclosed hCfip])
  then obtain xi where hxi: "xi \<in> \<Inter>((\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>)" by blast
  have "xi \<in> Xi"
  proof -
    obtain D0 where hD0: "D0 \<in> \<D>" using hDne by blast
    have "closure_on Xi TXi ((\<lambda>f. f i) ` D0) \<in> (\<lambda>D. closure_on Xi TXi ((\<lambda>f. f i) ` D)) ` \<D>"
      using hD0 by blast
    then have hxi0: "xi \<in> closure_on Xi TXi ((\<lambda>f. f i) ` D0)"
      using hxi by blast
    have hsub: "closure_on Xi TXi ((\<lambda>f. f i) ` D0) \<subseteq> Xi"
      by (rule closure_on_subset_carrier[OF hTopi hproj_sub[rule_format, OF hD0]])
    show ?thesis
      using hsub hxi0 by (rule subsetD)
  qed
  moreover have "\<forall>D\<in>\<D>. xi \<in> closure_on Xi TXi ((\<lambda>f. f i) ` D)"
    using hxi by blast
  ultimately show ?thesis by blast
qed

text \<open>Product basis element equals finite intersection of cylinders.\<close>
lemma top1_PiE_as_Inter_cylinders:
  assumes hUsub: "\<forall>i\<in>I. U i \<subseteq> X i"
  assumes hJdef: "J = {i \<in> I. U i \<noteq> X i}"
  assumes hJne: "J \<noteq> {}"
  defines "cyl i \<equiv> top1_PiE I (\<lambda>j. if j = i then U i else X j)"
  shows "top1_PiE I U = \<Inter>(cyl ` J)"
proof (rule equalityI)
  show "top1_PiE I U \<subseteq> \<Inter>(cyl ` J)"
  proof (rule subsetI)
    fix f assume hf: "f \<in> top1_PiE I U"
    show "f \<in> \<Inter>(cyl ` J)"
    proof (rule InterI)
      fix C assume "C \<in> cyl ` J"
      then obtain i where hiJ: "i \<in> J" and hCeq: "C = cyl i" by blast
      have hi: "i \<in> I" using hiJ hJdef by blast
      show "f \<in> C"
        unfolding hCeq cyl_def top1_PiE_iff
      proof (intro conjI ballI impI allI)
        fix j assume "j \<in> I"
        show "f j \<in> (if j = i then U i else X j)"
        proof (cases "j = i")
          case True
          have "f i \<in> U i" using hf hi by (simp add: top1_PiE_iff)
          then show ?thesis using True by simp
        next
          case False
          have "f j \<in> U j" using hf \<open>j \<in> I\<close> by (simp add: top1_PiE_iff)
          then have "f j \<in> X j" using hUsub \<open>j \<in> I\<close> by blast
          then show ?thesis using False by simp
        qed
      next
        fix j assume "j \<notin> I"
        then show "f j = undefined" using hf by (simp add: top1_PiE_iff)
      qed
    qed
  qed
next
  show "\<Inter>(cyl ` J) \<subseteq> top1_PiE I U"
  proof (rule subsetI)
    fix f assume hf: "f \<in> \<Inter>(cyl ` J)"
    show "f \<in> top1_PiE I U"
      unfolding top1_PiE_iff
    proof (intro conjI ballI impI allI)
      fix i assume hiI: "i \<in> I"
      show "f i \<in> U i"
      proof (cases "i \<in> J")
        case True
        have "cyl i \<in> cyl ` J" using True by blast
        then have hfcyl: "f \<in> cyl i" using hf by blast
        have hfcyl': "f \<in> top1_PiE I (\<lambda>j. if j = i then U i else X j)"
          using hfcyl unfolding cyl_def by simp
        have "\<forall>j\<in>I. f j \<in> (if j = i then U i else X j)"
          using hfcyl' by (simp add: top1_PiE_iff)
        then have "f i \<in> (if i = i then U i else X i)"
          using hiI by blast
        then show ?thesis by simp
      next
        case False
        have hUiXi: "U i = X i" using False hiI hJdef by blast
        obtain i0 where hi0J: "i0 \<in> J" using hJne by blast
        have "cyl i0 \<in> cyl ` J" using hi0J by blast
        then have hfi0: "f \<in> cyl i0" using hf by blast
        have hfi0': "f \<in> top1_PiE I (\<lambda>j. if j = i0 then U i0 else X j)"
          using hfi0 unfolding cyl_def by simp
        have "\<forall>j\<in>I. f j \<in> (if j = i0 then U i0 else X j)"
          using hfi0' by (simp add: top1_PiE_iff)
        then have "f i \<in> (if i = i0 then U i0 else X i)"
          using hiI by blast
        then have "f i \<in> X i"
        proof (cases "i = i0")
          case True
          have hi0I: "i0 \<in> I" using hi0J hJdef by blast
          have "U i0 \<subseteq> X i0" using hUsub hi0I by blast
          then show ?thesis
            using \<open>f i \<in> (if i = i0 then U i0 else X i)\<close> True by (simp, blast)
        next
          case False
          then show ?thesis
            using \<open>f i \<in> (if i = i0 then U i0 else X i)\<close> by simp
        qed
        then show "f i \<in> U i" using hUiXi by simp
      qed
    next
      fix i assume "i \<notin> I"
      obtain i0 where hi0J: "i0 \<in> J" using hJne by blast
      have "cyl i0 \<in> cyl ` J" using hi0J by blast
      then have "f \<in> cyl i0" using hf by blast
      then show "f i = undefined"
        using \<open>i \<notin> I\<close> unfolding cyl_def by (simp add: top1_PiE_iff)
    qed
  qed
qed

text \<open>Key step: every subbasis element (cylinder) containing x belongs to the maximal FIP family.\<close>
lemma tychonoff_subbasis_in_maxFIP:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (TX i)"
  assumes hmax: "top1_FIP_maximal_on (top1_PiE I X) \<D>"
  assumes hProdNe: "top1_PiE I X \<noteq> {}"
  assumes hi: "i \<in> I"
  assumes hU: "U \<in> TX i"
  assumes hxU: "x i \<in> U"
  assumes hxProd: "x \<in> top1_PiE I X"
  assumes hxcl: "\<forall>D\<in>\<D>. x i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D)"
  shows "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<in> \<D>"
proof -
  let ?cyl = "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j)"
  have hTi: "is_topology_on (X i) (TX i)" using hTop hi by blast

  have hFIP_D: "top1_FIP_on (top1_PiE I X) \<D>"
    using hmax unfolding top1_FIP_maximal_on_def by simp
  have hDsub: "\<forall>D0\<in>\<D>. D0 \<subseteq> top1_PiE I X"
    using hFIP_D unfolding top1_FIP_on_def by simp

  text \<open>The cylinder is a subset of the product.\<close>
  have hcyl_sub: "?cyl \<subseteq> top1_PiE I X"
    by (rule top1_PiE_mono) (simp add: le_infI1)

  text \<open>The cylinder intersects every D in D.\<close>
  have hcyl_inter: "\<forall>D0\<in>\<D>. intersects ?cyl D0"
  proof (intro ballI)
    fix D0 assume hD0: "D0 \<in> \<D>"
    have hxicl: "x i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D0)"
      using hxcl hD0 by blast
    have hproj_sub: "(\<lambda>f. f i) ` D0 \<subseteq> X i"
    proof (rule image_subsetI)
      fix f assume "f \<in> D0"
      then have "f \<in> top1_PiE I X" using hDsub hD0 by blast
      then show "f i \<in> X i" using hi by (simp add: top1_PiE_iff)
    qed
    have hU_nbhd: "neighborhood_of (x i) (X i) (TX i) U"
      unfolding neighborhood_of_def using hU hxU by simp
    have hxiX: "x i \<in> X i"
      using hxProd hi by (simp add: top1_PiE_iff)
    have hclchar: "x i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D0) \<longleftrightarrow>
        (\<forall>V. neighborhood_of (x i) (X i) (TX i) V \<longrightarrow> intersects V ((\<lambda>f. f i) ` D0))"
      by (rule Theorem_17_5a[OF hTi hxiX hproj_sub])
    have hU_inter_proj: "intersects U ((\<lambda>f. f i) ` D0)"
      using iffD1[OF hclchar hxicl] hU_nbhd by blast
    then obtain z where hzU: "z \<in> U" and hzproj: "z \<in> (\<lambda>f. f i) ` D0"
      unfolding intersects_def by blast
    obtain f where hfD: "f \<in> D0" and hfi: "f i = z" using hzproj by blast
    have hfProd: "f \<in> top1_PiE I X" using hDsub hD0 hfD by blast
    have "f \<in> ?cyl"
      unfolding top1_PiE_iff
    proof (intro conjI ballI impI allI)
      fix j
      show "j \<in> I \<Longrightarrow> f j \<in> (if j = i then U \<inter> X i else X j)"
      proof (cases "j = i")
        case True
        have "f i \<in> X i" using hfProd hi by (simp add: top1_PiE_iff)
        then have "z \<in> X i" using hfi by simp
        then show ?thesis using True hfi hzU by simp
      next
        case False
        assume hjI: "j \<in> I"
        have "f j \<in> X j" using hfProd hjI by (simp add: top1_PiE_iff)
        then show ?thesis using False by simp
      qed
    next
      fix j
      show "j \<notin> I \<Longrightarrow> f j = undefined"
        using hfProd by (simp add: top1_PiE_iff)
    qed
    then have "f \<in> ?cyl \<inter> D0" using hfD by blast
    then show "intersects ?cyl D0" unfolding intersects_def by blast
  qed

  text \<open>By Lemma 37.2(b), the cylinder belongs to D.\<close>
  show "?cyl \<in> \<D>"
    using Lemma_37_2(2)[OF hmax hProdNe, THEN spec, of ?cyl] hcyl_sub hcyl_inter
    by blast
qed

text \<open>Key step: x is in the closure of every D, using the fact that every basis element
  containing x belongs to D and D has FIP.\<close>
lemma tychonoff_point_in_all_closures:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (TX i)"
  assumes hmax: "top1_FIP_maximal_on (top1_PiE I X) \<D>"
  assumes hProdNe: "top1_PiE I X \<noteq> {}"
  assumes hxProd: "x \<in> top1_PiE I X"
  assumes hxcl: "\<forall>i\<in>I. \<forall>D\<in>\<D>. x i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D)"
  shows "\<forall>D\<in>\<D>. x \<in> closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D"
proof -
  have hTopProd: "is_topology_on (top1_PiE I X) (top1_product_topology_on I X TX)"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  have hFIP_D: "top1_FIP_on (top1_PiE I X) \<D>"
    using hmax unfolding top1_FIP_maximal_on_def by simp
  have hDsub: "\<forall>D0\<in>\<D>. D0 \<subseteq> top1_PiE I X"
    using hFIP_D unfolding top1_FIP_on_def by simp

  have hBasis: "basis_for (top1_PiE I X) (top1_product_basis_on I X TX) (top1_product_topology_on I X TX)"
    unfolding basis_for_def top1_product_topology_on_def
    by (intro conjI top1_product_basis_is_basis_on[OF hTop] refl)

  text \<open>Every subbasis element (cylinder) containing x is in D.\<close>
  have hcyl_in_D:
    "\<forall>i\<in>I. \<forall>U\<in>TX i. x i \<in> U \<longrightarrow>
      top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<in> \<D>"
  proof (intro ballI impI)
    fix i U assume hi: "i \<in> I" and hU: "U \<in> TX i" and hxU: "x i \<in> U"
    have hxcli: "\<forall>D\<in>\<D>. x i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D)"
      using hxcl hi by blast
    show "top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j) \<in> \<D>"
      by (rule tychonoff_subbasis_in_maxFIP[OF hTop hmax hProdNe hi hU hxU hxProd hxcli])
  qed

  text \<open>The product space itself is in D.\<close>
  have hProd_in_D: "top1_PiE I X \<in> \<D>"
  proof -
    have "\<forall>D0\<in>\<D>. intersects (top1_PiE I X) D0"
    proof (intro ballI)
      fix D0 assume "D0 \<in> \<D>"
      have "D0 \<subseteq> top1_PiE I X" using hDsub \<open>D0 \<in> \<D>\<close> by blast
      have "D0 \<noteq> {}"
      proof -
        have "finite {D0} \<and> {D0} \<subseteq> \<D>" using \<open>D0 \<in> \<D>\<close> by simp
        then have "\<Inter>{D0} \<noteq> {}" using hFIP_D unfolding top1_FIP_on_def by blast
        then show ?thesis by simp
      qed
      then show "intersects (top1_PiE I X) D0"
        unfolding intersects_def using \<open>D0 \<subseteq> top1_PiE I X\<close> by blast
    qed
    then show ?thesis
      using Lemma_37_2(2)[OF hmax hProdNe, THEN spec, of "top1_PiE I X"]
      by blast
  qed

  text \<open>Every basis element containing x belongs to D (finite intersection of cylinders).\<close>
  have hbasis_in_D: "\<forall>b\<in>top1_product_basis_on I X TX. x \<in> b \<longrightarrow> b \<in> \<D>"
  proof (intro ballI impI)
    fix b assume hb: "b \<in> top1_product_basis_on I X TX" and hxb: "x \<in> b"
    obtain U where hbdef: "b = top1_PiE I U"
      and hUopen: "\<forall>i\<in>I. U i \<in> TX i \<and> U i \<subseteq> X i"
      and hJfin: "finite {i \<in> I. U i \<noteq> X i}"
      using hb unfolding top1_product_basis_on_def by blast

    define J where "J = {i \<in> I. U i \<noteq> X i}"
    have hJfin': "finite J" unfolding J_def using hJfin by simp

    text \<open>For each i in J, the cylinder at i is in D.\<close>
    define cyl where "cyl i = top1_PiE I (\<lambda>j. if j = i then U i \<inter> X i else X j)" for i
    have hcyl_D: "\<forall>i\<in>J. cyl i \<in> \<D>"
    proof (intro ballI)
      fix i assume hiJ: "i \<in> J"
      have hi: "i \<in> I" using hiJ unfolding J_def by simp
      have hUi: "U i \<in> TX i" using hUopen hi by blast
      have hxi_Ui: "x i \<in> U i"
        using hxb hbdef hi by (simp add: top1_PiE_iff)
      have "U i \<inter> X i = U i" using hUopen hi by blast
      have hxcli: "\<forall>D\<in>\<D>. x i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D)"
        using hxcl hi by blast
      have "top1_PiE I (\<lambda>j. if j = i then U i \<inter> X i else X j) \<in> \<D>"
        by (rule tychonoff_subbasis_in_maxFIP[OF hTop hmax hProdNe hi hUi hxi_Ui hxProd hxcli])
      then show "cyl i \<in> \<D>" unfolding cyl_def by simp
    qed

    show "b \<in> \<D>"
    proof (cases "J = {}")
      case True
      text \<open>If J is empty, b is the whole product, which is in D.\<close>
      have "b = top1_PiE I X"
      proof -
        have hUeq: "\<forall>i\<in>I. U i = X i" using True unfolding J_def by blast
        have hpie_eq: "top1_PiE I U = top1_PiE I X"
          by (rule top1_PiE_cong_on[OF hUeq])
        show "b = top1_PiE I X"
          using hbdef hpie_eq by (rule trans)
      qed
      then show ?thesis using hProd_in_D by simp
    next
      case False
      text \<open>b is the finite intersection of cylinders, each in D. By Lemma 37.2(a), b in D.\<close>
      have hcylset_fin: "finite (cyl ` J)" using hJfin' by simp
      have hcylset_sub: "cyl ` J \<subseteq> \<D>" using hcyl_D by blast
      have hcylset_ne: "cyl ` J \<noteq> {}" using False by simp
      have hinter_in_D: "\<Inter>(cyl ` J) \<in> \<D>"
        using Lemma_37_2(1)[OF hmax hProdNe, THEN spec, of "cyl ` J"]
              hcylset_fin hcylset_sub hcylset_ne
        by blast
      text \<open>Express b as finite intersection of cylinders, then use Lemma 37.2(a).\<close>
      have hUsub': "\<forall>i\<in>I. U i \<subseteq> X i" using hUopen by blast
      have hUint: "\<forall>i\<in>I. U i \<inter> X i = U i" using hUopen by blast

      text \<open>Since U i \<inter> X i = U i, cyl i equals the simpler cylinder.\<close>
      have hcyl_simp: "\<forall>i\<in>J. cyl i = top1_PiE I (\<lambda>j. if j = i then U i else X j)"
      proof (intro ballI)
        fix i assume "i \<in> J"
        then have "i \<in> I" unfolding J_def by simp
        then have "U i \<inter> X i = U i" using hUint by blast
        then show "cyl i = top1_PiE I (\<lambda>j. if j = i then U i else X j)"
          unfolding cyl_def
          by (intro arg_cong[where f="top1_PiE I"] ext) simp
      qed

      have hJeq: "J = {i \<in> I. U i \<noteq> X i}" unfolding J_def by (rule refl)

      text \<open>Apply the Inter-cylinders lemma.\<close>
      have hPiE_eq: "top1_PiE I U = (\<Inter>i\<in>J. top1_PiE I (\<lambda>j. if j = i then U i else X j))"
        by (rule top1_PiE_as_Inter_cylinders[OF hUsub' hJeq False])

      have hinter_cyl_eq: "\<Inter>(cyl ` J) = (\<Inter>i\<in>J. top1_PiE I (\<lambda>j. if j = i then U i else X j))"
      proof (rule arg_cong[where f="\<Inter>"], rule image_cong[OF refl])
        fix i assume "i \<in> J"
        then show "cyl i = top1_PiE I (\<lambda>j. if j = i then U i else X j)"
          using hcyl_simp by blast
      qed

      have hstep1: "b = (\<Inter>i\<in>J. top1_PiE I (\<lambda>j. if j = i then U i else X j))"
        by (rule trans[OF hbdef hPiE_eq])
      have hstep2: "\<Inter>(cyl ` J) = (\<Inter>i\<in>J. top1_PiE I (\<lambda>j. if j = i then U i else X j))"
        by (rule hinter_cyl_eq)
      have hb_inter: "b = \<Inter>(cyl ` J)"
        by (rule trans[OF hstep1 hstep2[symmetric]])
      show "b \<in> \<D>"
        by (rule mem_of_elem_eq[OF hinter_in_D sym[OF hb_inter]])
    qed
  qed

  text \<open>Therefore x is in the closure of every D.\<close>
  show "\<forall>D\<in>\<D>. x \<in> closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D"
  proof (intro ballI)
    fix D0 assume hD0: "D0 \<in> \<D>"
    have hD0sub: "D0 \<subseteq> top1_PiE I X" using hDsub hD0 by blast

    show "x \<in> closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D0"
    proof (rule iffD2[OF Theorem_17_5b[OF hBasis hxProd hD0sub]])
      show "\<forall>b\<in>top1_product_basis_on I X TX. x \<in> b \<longrightarrow> intersects b D0"
      proof (intro ballI impI)
        fix b assume hb: "b \<in> top1_product_basis_on I X TX" and hxb: "x \<in> b"
        have hbD: "b \<in> \<D>" using hbasis_in_D hb hxb by blast
        have hFIPpair: "finite {b, D0} \<and> {b, D0} \<subseteq> \<D>"
          using hbD hD0 by simp
        then have "\<Inter>{b, D0} \<noteq> {}"
          using hFIP_D unfolding top1_FIP_on_def by blast
        then show "intersects b D0"
          unfolding intersects_def by simp
      qed
    qed
  qed
qed

(** from \S37 Theorem 37.3 (Tychonoff theorem) [top1.tex:5253] **)
theorem Theorem_37_3:
  assumes hIne: "I \<noteq> {}"
  assumes hComp: "\<forall>i\<in>I. top1_compact_on (X i) (TX i)"
  shows "top1_compact_on (top1_PiE I X) (top1_product_topology_on I X TX)"
proof -
  have hTop: "\<forall>i\<in>I. is_topology_on (X i) (TX i)"
    using hComp unfolding top1_compact_on_def by blast
  have hTopProd: "is_topology_on (top1_PiE I X) (top1_product_topology_on I X TX)"
    by (rule top1_product_topology_on_is_topology_on[OF hTop])

  show ?thesis
    unfolding top1_compact_on_def
  proof (intro conjI)
    show "is_topology_on (top1_PiE I X) (top1_product_topology_on I X TX)"
      by (rule hTopProd)
  next
    show "\<forall>Uc. Uc \<subseteq> top1_product_topology_on I X TX \<and> top1_PiE I X \<subseteq> \<Union>Uc
          \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_PiE I X \<subseteq> \<Union>F)"
    proof (cases "top1_PiE I X = {}")
      case True
      then show ?thesis by blast
    next
      case False
      have hProdNe: "top1_PiE I X \<noteq> {}" by (rule False)

      text \<open>Use FIP characterization: show every closed FIP collection has nonempty intersection.\<close>
      have hFIPchar: "(\<forall>\<C>. (\<forall>C\<in>\<C>. closedin_on (top1_PiE I X) (top1_product_topology_on I X TX) C)
             \<and> (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {}) \<longrightarrow> \<Inter>\<C> \<noteq> {})
           \<longrightarrow> (\<forall>Uc. Uc \<subseteq> top1_product_topology_on I X TX \<and> top1_PiE I X \<subseteq> \<Union>Uc
              \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_PiE I X \<subseteq> \<Union>F))"
        using Theorem_26_9[OF hTopProd] unfolding top1_compact_on_def by blast

      show ?thesis
      proof (rule mp[OF hFIPchar], intro allI impI)
        fix \<A>
        assume hAprem: "(\<forall>C\<in>\<A>. closedin_on (top1_PiE I X) (top1_product_topology_on I X TX) C)
              \<and> (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<A> \<longrightarrow> \<Inter>F \<noteq> {})"

        text \<open>Step 1: the collection A has FIP on the product.\<close>
        have hFIP_A: "top1_FIP_on (top1_PiE I X) \<A>"
          unfolding top1_FIP_on_def
        proof (intro conjI)
          show "\<forall>A\<in>\<A>. A \<subseteq> top1_PiE I X"
            using hAprem unfolding closedin_on_def by blast
          show "\<forall>F. finite F \<and> F \<subseteq> \<A> \<longrightarrow> \<Inter>F \<noteq> {}"
          proof (intro allI impI)
            fix F assume hF: "finite F \<and> F \<subseteq> \<A>"
            show "\<Inter>F \<noteq> {}"
            proof (cases "F = {}")
              case True then show ?thesis by simp
            next
              case False
              then show ?thesis using hAprem hF by blast
            qed
          qed
        qed

        text \<open>Step 2: extend to maximal FIP family D.\<close>
        obtain \<D> where hAsubD: "\<A> \<subseteq> \<D>"
          and hMaxD: "top1_FIP_maximal_on (top1_PiE I X) \<D>"
          using Lemma_37_1[OF hFIP_A] by blast

        have hFIP_D: "top1_FIP_on (top1_PiE I X) \<D>"
          using hMaxD unfolding top1_FIP_maximal_on_def by simp

        have hDsub: "\<forall>D\<in>\<D>. D \<subseteq> top1_PiE I X"
          using hFIP_D unfolding top1_FIP_on_def by simp

        have hDne: "\<D> \<noteq> {}"
        proof -
          have "top1_PiE I X \<in> \<D>"
          proof -
            have "top1_PiE I X \<subseteq> top1_PiE I X" by simp
            have "\<forall>D0\<in>\<D>. intersects (top1_PiE I X) D0"
            proof (intro ballI)
              fix D0 assume "D0 \<in> \<D>"
              have "D0 \<subseteq> top1_PiE I X" using hDsub \<open>D0 \<in> \<D>\<close> by blast
              have "D0 \<noteq> {}"
              proof -
                have "finite {D0} \<and> {D0} \<subseteq> \<D>" using \<open>D0 \<in> \<D>\<close> by simp
                then have "\<Inter>{D0} \<noteq> {}"
                  using hFIP_D unfolding top1_FIP_on_def by blast
                then show ?thesis by simp
              qed
              then show "intersects (top1_PiE I X) D0"
                unfolding intersects_def using \<open>D0 \<subseteq> top1_PiE I X\<close> by blast
            qed
            then show ?thesis
              using Lemma_37_2(2)[OF hMaxD hProdNe, THEN spec, of "top1_PiE I X"]
                    \<open>top1_PiE I X \<subseteq> top1_PiE I X\<close>
              by blast
          qed
          then show ?thesis by blast
        qed

        text \<open>Step 3: for each i, choose x_i in the intersection of projected closures.\<close>
        have hproj_sub: "\<forall>i\<in>I. \<forall>D\<in>\<D>. (\<lambda>f. f i) ` D \<subseteq> X i"
        proof (intro ballI)
          fix i D assume hi: "i \<in> I" and hD: "D \<in> \<D>"
          show "(\<lambda>f. f i) ` D \<subseteq> X i"
          proof (rule image_subsetI)
            fix f assume "f \<in> D"
            then have "f \<in> top1_PiE I X" using hDsub hD by blast
            then show "f i \<in> X i" using hi by (simp add: top1_PiE_iff)
          qed
        qed

        have hcoord: "\<forall>i\<in>I. \<exists>xi. xi \<in> X i \<and> (\<forall>D\<in>\<D>. xi \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D))"
        proof (intro ballI)
          fix i assume hi: "i \<in> I"
          have hproj_i: "\<forall>D\<in>\<D>. (\<lambda>f. f i) ` D \<subseteq> X i"
            using hproj_sub hi by blast
          show "\<exists>xi. xi \<in> X i \<and> (\<forall>D\<in>\<D>. xi \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D))"
            by (rule tychonoff_coord_point[OF hFIP_D hDne hTop[rule_format, OF hi]
                  hComp[rule_format, OF hi] hi hDsub hproj_i])
        qed

        text \<open>Step 4: build the product point x.\<close>
        obtain sel where hsel: "\<forall>i\<in>I. sel i \<in> X i \<and> (\<forall>D\<in>\<D>. sel i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D))"
          using hcoord by metis

        define x where "x = (\<lambda>i. if i \<in> I then sel i else undefined)"

        have hxProd: "x \<in> top1_PiE I X"
          unfolding top1_PiE_iff x_def using hsel by simp

        have hxcoord: "\<forall>i\<in>I. x i \<in> X i"
          unfolding x_def using hsel by simp

        have hxcl: "\<forall>i\<in>I. \<forall>D\<in>\<D>. x i \<in> closure_on (X i) (TX i) ((\<lambda>f. f i) ` D)"
          unfolding x_def using hsel by simp

        text \<open>Step 5: show x is in the closure of every D in D.\<close>
        have "\<forall>D\<in>\<D>. x \<in> closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D"
          by (rule tychonoff_point_in_all_closures[OF hTop hMaxD hProdNe hxProd hxcl])

        text \<open>Step 6: conclude nonempty intersection.\<close>
        have "x \<in> \<Inter>((\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A>)"
        proof (rule InterI)
          fix C assume "C \<in> (\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A>"
          then obtain D where hD: "D \<in> \<A>" and hCdef: "C = closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D"
            by blast
          have "D \<in> \<D>" using hAsubD hD by blast
          then have "x \<in> closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D"
            using \<open>\<forall>D\<in>\<D>. x \<in> closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D\<close> by blast
          then show "x \<in> C" using mem_of_eq hCdef by blast
        qed

        then have "\<Inter>((\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A>) \<noteq> {}"
          by blast

        text \<open>Since each A in A is closed, closure(A) = A, so the intersection of the A's is nonempty.\<close>
        have "\<forall>A0\<in>\<A>. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) A0 = A0"
        proof (intro ballI)
          fix A0 assume "A0 \<in> \<A>"
          have "closedin_on (top1_PiE I X) (top1_product_topology_on I X TX) A0"
            using hAprem \<open>A0 \<in> \<A>\<close> by blast
          then show "closure_on (top1_PiE I X) (top1_product_topology_on I X TX) A0 = A0"
          proof -
            assume hcl: "closedin_on (top1_PiE I X) (top1_product_topology_on I X TX) A0"
            have hsub1: "A0 \<subseteq> closure_on (top1_PiE I X) (top1_product_topology_on I X TX) A0"
              by (rule subset_closure_on)
            have hsub2: "closure_on (top1_PiE I X) (top1_product_topology_on I X TX) A0 \<subseteq> A0"
              by (rule closure_on_subset_of_closed[OF hcl subset_refl])
            show ?thesis
              by (rule equalityI[OF hsub2 hsub1])
          qed
        qed
        then have himageq: "(\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A> = \<A>"
        proof -
          assume hcleq: "\<forall>A0\<in>\<A>. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) A0 = A0"
          show ?thesis
          proof (rule equalityI)
            show "(\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A> \<subseteq> \<A>"
            proof (rule subsetI)
              fix C assume "C \<in> (\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A>"
              then obtain D where "D \<in> \<A>" "C = closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D" by blast
              then show "C \<in> \<A>" using hcleq by force
            qed
          next
            show "\<A> \<subseteq> (\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A>"
            proof (rule subsetI)
              fix A0 assume "A0 \<in> \<A>"
              have "closure_on (top1_PiE I X) (top1_product_topology_on I X TX) A0 = A0"
                using hcleq \<open>A0 \<in> \<A>\<close> by blast
              then show "A0 \<in> (\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A>"
                using \<open>A0 \<in> \<A>\<close> by force
            qed
          qed
        qed
        then show "\<Inter>\<A> \<noteq> {}"
          using \<open>\<Inter>((\<lambda>D. closure_on (top1_PiE I X) (top1_product_topology_on I X TX) D) ` \<A>) \<noteq> {}\<close>
          by simp
      qed
    qed
  qed
qed

section \<open>\<S>38 The Stone-\<C>ech Compactification\<close>

text \<open>
  We follow \<open>top1.tex\<close> and represent a compactification via an embedding of \<open>X\<close> into a
  compact Hausdorff space whose image is dense.
\<close>

definition top1_dense_image_via_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_dense_image_via_on X TX Y TY e \<longleftrightarrow>
     top1_embedding_on X TX Y TY e \<and> closure_on Y TY (e ` X) = Y"

definition top1_compactification_via_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_compactification_via_on X TX Y TY e \<longleftrightarrow>
     top1_compact_on Y TY \<and> is_hausdorff_on Y TY \<and> top1_dense_image_via_on X TX Y TY e"

definition top1_eq_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_eq_on A f g \<longleftrightarrow> (\<forall>x\<in>A. f x = g x)"

definition top1_equiv_compactification_via_on ::
  "'a set \<Rightarrow> 'a set set
    \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b)
    \<Rightarrow> 'c set \<Rightarrow> 'c set set \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> bool" where
  "top1_equiv_compactification_via_on X TX Y1 TY1 e1 Y2 TY2 e2 \<longleftrightarrow>
     (\<exists>h. top1_homeomorphism_on Y1 TY1 Y2 TY2 h \<and> (\<forall>x\<in>X. h (e1 x) = e2 x))"

(** from \S38 Lemma 38.1 (Compactifications induced by embeddings) [top1.tex:5348] **)
lemma Lemma_38_1:
  fixes X :: "'a set" and TX :: "'a set set"
    and Z :: "'b set" and TZ :: "'b set set"
    and h :: "'a \<Rightarrow> 'b"
  assumes hEmb: "top1_embedding_on X TX Z TZ h"
  assumes hCompZ: "top1_compact_on Z TZ"
  assumes hHausZ: "is_hausdorff_on Z TZ"
  shows "\<exists>Y TY (e::'a \<Rightarrow> 'b) H.
    top1_compactification_via_on X TX Y TY e
    \<and> top1_embedding_on Y TY Z TZ H
    \<and> (\<forall>x\<in>X. H (e x) = h x)"
proof -
  define Y0 where "Y0 = closure_on Z TZ (h ` X)"
  define TY0 where "TY0 = subspace_topology Z TZ Y0"

  have hTopZ: "is_topology_on Z TZ"
  proof -
    have "is_topology_on Z TZ \<and>
      (\<forall>Uc. Uc \<subseteq> TZ \<and> Z \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Z \<subseteq> \<Union>F))"
      using hCompZ unfolding top1_compact_on_def .
    thus ?thesis
      by (rule conjunct1)
  qed

  have hImgSubZ: "h ` X \<subseteq> Z"
  proof -
    have "h ` X \<subseteq> Z \<and> top1_homeomorphism_on X TX (h ` X) (subspace_topology Z TZ (h ` X)) h"
      using hEmb unfolding top1_embedding_on_def .
    thus ?thesis
      by (rule conjunct1)
  qed

  have hYsubZ: "Y0 \<subseteq> Z"
    unfolding Y0_def by (rule closure_on_subset_carrier[OF hTopZ hImgSubZ])

  have hYclosed: "closedin_on Z TZ Y0"
    unfolding Y0_def by (rule closure_on_closed[OF hTopZ hImgSubZ])

  have hCompY: "top1_compact_on Y0 TY0"
    unfolding TY0_def by (rule Theorem_26_2[OF hCompZ hYclosed])

  have hHausSub:
    "(\<forall>X0 T0 Y0. is_hausdorff_on X0 T0 \<and> Y0 \<subseteq> X0 \<longrightarrow> is_hausdorff_on Y0 (subspace_topology X0 T0 Y0))"
    by (rule conjunct2[OF conjunct2[OF Theorem_17_11]])

  have hHausY: "is_hausdorff_on Y0 TY0"
    unfolding TY0_def
    apply (rule hHausSub[rule_format])
    apply (intro conjI)
     apply (rule hHausZ)
    apply (rule hYsubZ)
    done

  have hImgSubY: "h ` X \<subseteq> Y0"
    unfolding Y0_def by (rule subset_closure_on)

  have hHomeoZ: "top1_homeomorphism_on X TX (h ` X) (subspace_topology Z TZ (h ` X)) h"
  proof -
    have "h ` X \<subseteq> Z \<and> top1_homeomorphism_on X TX (h ` X) (subspace_topology Z TZ (h ` X)) h"
      using hEmb unfolding top1_embedding_on_def .
    thus ?thesis
      by (rule conjunct2)
  qed

  have hTopEq: "subspace_topology Y0 TY0 (h ` X) = subspace_topology Z TZ (h ` X)"
  proof -
    have "subspace_topology Y0 (subspace_topology Z TZ Y0) (h ` X) = subspace_topology Z TZ (h ` X)"
      by (rule subspace_topology_trans[OF hImgSubY])
    thus ?thesis
      unfolding TY0_def by simp
  qed

  have hHomeoY: "top1_homeomorphism_on X TX (h ` X) (subspace_topology Y0 TY0 (h ` X)) h"
    apply (subst hTopEq)
    apply (rule hHomeoZ)
    done

  have hEmbY: "top1_embedding_on X TX Y0 TY0 h"
    unfolding top1_embedding_on_def
    apply (intro conjI)
     apply (rule hImgSubY)
    apply (rule hHomeoY)
    done

  have hClosureImg: "closure_on Y0 TY0 (h ` X) = Y0"
  proof -
    have hEq: "closure_on Y0 TY0 (h ` X) = closure_on Z TZ (h ` X) \<inter> Y0"
      unfolding TY0_def by (rule Theorem_17_4[OF hTopZ hImgSubY hYsubZ])
    show ?thesis
      unfolding hEq by (simp add: Y0_def)
  qed

  have hDenseImg: "top1_dense_image_via_on X TX Y0 TY0 h"
    unfolding top1_dense_image_via_on_def
    apply (intro conjI)
     apply (rule hEmbY)
    apply (rule hClosureImg)
    done

  have hCompVia: "top1_compactification_via_on X TX Y0 TY0 h"
    unfolding top1_compactification_via_on_def
    apply (intro conjI)
      apply (rule hCompY)
     apply (rule hHausY)
    apply (rule hDenseImg)
    done

  have hTopY: "is_topology_on Y0 TY0"
  proof -
    have "is_topology_on Y0 TY0 \<and>
      (\<forall>Uc. Uc \<subseteq> TY0 \<and> Y0 \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y0 \<subseteq> \<Union>F))"
      using hCompY unfolding top1_compact_on_def .
    thus ?thesis
      by (rule conjunct1)
  qed

  have hYinTY: "Y0 \<in> TY0"
  proof -
    have "{} \<in> TY0 \<and> Y0 \<in> TY0 \<and>
      (\<forall>U. U \<subseteq> TY0 \<longrightarrow> \<Union>U \<in> TY0) \<and>
      (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TY0 \<longrightarrow> \<Inter>F \<in> TY0)"
      using hTopY unfolding is_topology_on_def .
    thus ?thesis
      by (rule conjunct1[OF conjunct2])
  qed

  have hContId: "top1_continuous_map_on Y0 TY0 Y0 TY0 id"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>Y0. id x \<in> Y0"
      by simp
    show "\<forall>V\<in>TY0. {x \<in> Y0. id x \<in> V} \<in> TY0"
    proof (intro ballI)
      fix V
      assume hV: "V \<in> TY0"
      have hInter: "Y0 \<inter> V \<in> TY0"
        by (rule topology_inter2[OF hTopY hYinTY hV])
      have "{x \<in> Y0. id x \<in> V} = Y0 \<inter> V"
        by (rule set_eqI) simp
      thus "{x \<in> Y0. id x \<in> V} \<in> TY0"
        using hInter by simp
    qed
  qed

  have hInvPoint: "\<And>x. x \<in> Y0 \<Longrightarrow> inv_into Y0 id x = x"
  proof -
    fix x
    assume hxY: "x \<in> Y0"
    have hinj: "inj_on id Y0"
      by simp
    have "inv_into Y0 id (id x) = x"
      by (rule inv_into_f_f[OF hinj hxY])
    thus "inv_into Y0 id x = x"
      by simp
  qed

  have hContInv: "top1_continuous_map_on Y0 TY0 Y0 TY0 (inv_into Y0 id)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>Y0. inv_into Y0 id x \<in> Y0"
    proof (intro ballI)
      fix x
      assume hxY: "x \<in> Y0"
      have "inv_into Y0 id x = x"
        by (rule hInvPoint[OF hxY])
      thus "inv_into Y0 id x \<in> Y0"
        using hxY by simp
    qed
    show "\<forall>V\<in>TY0. {x \<in> Y0. inv_into Y0 id x \<in> V} \<in> TY0"
    proof (intro ballI)
      fix V
      assume hV: "V \<in> TY0"
      have hInter: "Y0 \<inter> V \<in> TY0"
        by (rule topology_inter2[OF hTopY hYinTY hV])
      have "{x \<in> Y0. inv_into Y0 id x \<in> V} = Y0 \<inter> V"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x \<in> Y0. inv_into Y0 id x \<in> V} \<longleftrightarrow> x \<in> Y0 \<inter> V"
        proof
          assume hx: "x \<in> {x \<in> Y0. inv_into Y0 id x \<in> V}"
          have hxY: "x \<in> Y0"
            using hx by simp
          have hxinV: "inv_into Y0 id x \<in> V"
            using hx by simp
          have hInv: "inv_into Y0 id x = x"
            by (rule hInvPoint[OF hxY])
          have hxV: "x \<in> V"
            using hxinV unfolding hInv by simp
          show "x \<in> Y0 \<inter> V"
            using hxY hxV by simp
        next
          assume hx: "x \<in> Y0 \<inter> V"
          have hxY: "x \<in> Y0"
            using hx by simp
          have hxV: "x \<in> V"
            using hx by simp
          have hInv: "inv_into Y0 id x = x"
            by (rule hInvPoint[OF hxY])
          have hxinV: "inv_into Y0 id x \<in> V"
            using hxV unfolding hInv by simp
          show "x \<in> {x \<in> Y0. inv_into Y0 id x \<in> V}"
            using hxY hxinV by simp
        qed
      qed
      thus "{x \<in> Y0. inv_into Y0 id x \<in> V} \<in> TY0"
        using hInter by simp
    qed
  qed

  have hHomeoId: "top1_homeomorphism_on Y0 TY0 Y0 TY0 id"
    unfolding top1_homeomorphism_on_def
    apply (intro conjI)
        apply (rule hTopY)
       apply (rule hTopY)
      apply simp
     apply (rule hContId)
    apply (rule hContInv)
    done

  have hEmbIncl: "top1_embedding_on Y0 TY0 Z TZ id"
    unfolding top1_embedding_on_def
    apply (intro conjI)
     apply (simp add: hYsubZ)
    apply (simp add: TY0_def[symmetric])
    apply (rule hHomeoId)
    done

  show ?thesis
    apply (rule_tac x=Y0 in exI)
    apply (rule_tac x=TY0 in exI)
    apply (rule_tac x=h in exI)
    apply (rule_tac x=id in exI)
    apply (intro conjI)
      apply (rule hCompVia)
     apply (rule hEmbIncl)
    apply simp
    done
qed

definition top1_bounded_on :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "top1_bounded_on X f \<longleftrightarrow> (\<exists>M. \<forall>x\<in>X. \<bar>f x\<bar> \<le> M)"

(** from \S38 Theorem 38.2 (Existence of Stone-\<C>ech compactification) [top1.tex:5418] **)
text \<open>Proof strategy: use Theorem 34.3 (completely regular \<open>\<Rightarrow>\<close> embeds in \<open>[0,1]^J\<close>)
  to embed X into \<open>[0,1]^J\<close>. The closure of the image in \<open>[0,1]^J\<close> is compact
  by Tychonoff (Theorem 37.3, proved). Extensions via Tietze (Theorem 35.1, proved).
  Uniqueness from Hausdorff + density.\<close>
theorem Theorem_38_2:
  assumes hCR: "top1_completely_regular_on X TX"
  shows "\<exists>Y TY e.
    top1_compactification_via_on X TX Y TY e
    \<and> (\<forall>f. top1_continuous_map_on X TX UNIV order_topology_on_UNIV f
            \<and> top1_bounded_on X f
            \<longrightarrow> (\<exists>g. top1_continuous_map_on Y TY UNIV order_topology_on_UNIV g
                    \<and> (\<forall>x\<in>X. g (e x) = f x)
                    \<and> (\<forall>g'. top1_continuous_map_on Y TY UNIV order_topology_on_UNIV g'
                          \<and> (\<forall>x\<in>X. g' (e x) = f x)
                          \<longrightarrow> top1_eq_on Y g g')))"
  sorry
  (* Proof outline (Munkres Theorem 38.2):
     1. By Theorem 34.3, X embeds into [0,1]^J via F for some J.
     2. Let Z = product space [0,1]^J with product topology.
        Z is compact by Tychonoff (37.3) and Hausdorff.
     3. Let Y = closure of F(X) in Z. Y is compact (closed in compact).
        Y is Hausdorff (subspace of Hausdorff).
     4. F: X → Y is an embedding with dense image.
        So (Y, TY, F) is a compactification of X.
     5. Extension: for bounded continuous g: X → R, g is in J (after rescaling).
        π_g ∘ inclusion: Y → [0,1] is continuous and extends g.
     6. Uniqueness: Lemma 38.3 (proved) — at most one extension to closure.
     Requires: Tychonoff (proved), Theorem 34.3 (proved), closure properties,
     product topology projections, Lemma 38.3 (proved).
     Estimated ~100 lines. *)

lemma top1_closedin_equalizer_of_continuous_maps:
  fixes f g :: "'a \<Rightarrow> 'b"
  assumes hTopX: "is_topology_on X TX"
  assumes hHausY: "is_hausdorff_on Y TY"
  assumes hf: "top1_continuous_map_on X TX Y TY f"
  assumes hg: "top1_continuous_map_on X TX Y TY g"
  shows "closedin_on X TX {x\<in>X. f x = g x}"
proof -
  let ?E = "{x\<in>X. f x = g x}"
  let ?D = "X - ?E"

  have hEsubX: "?E \<subseteq> X"
    by blast
  have hDsubX: "?D \<subseteq> X"
    by blast

  have hImgf: "\<forall>x\<in>X. f x \<in> Y"
    using hf unfolding top1_continuous_map_on_def by blast
  have hImgg: "\<forall>x\<in>X. g x \<in> Y"
    using hg unfolding top1_continuous_map_on_def by blast

  have hPreimf: "\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX"
    using hf unfolding top1_continuous_map_on_def by blast
  have hPreimg: "\<forall>V\<in>TY. {x\<in>X. g x \<in> V} \<in> TX"
    using hg unfolding top1_continuous_map_on_def by blast

  have hHaus: "\<forall>a\<in>Y. \<forall>b\<in>Y. a \<noteq> b \<longrightarrow>
      (\<exists>U V. neighborhood_of a Y TY U \<and> neighborhood_of b Y TY V \<and> U \<inter> V = {})"
    using hHausY unfolding is_hausdorff_on_def by blast

  have hLoc: "\<forall>x\<in>?D. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> ?D"
  proof (intro ballI)
    fix x
    assume hx: "x \<in> ?D"
    have hxX: "x \<in> X"
      using hx by simp
    have hneq: "f x \<noteq> g x"
    proof
      assume hEq: "f x = g x"
      have "x \<in> ?E"
        using hxX hEq by simp
      thus False
        using hx by simp
    qed

    have hfx: "f x \<in> Y"
      using hImgf hxX by blast
    have hgx: "g x \<in> Y"
      using hImgg hxX by blast

    obtain U V where hU: "neighborhood_of (f x) Y TY U"
      and hV: "neighborhood_of (g x) Y TY V"
      and hdisj: "U \<inter> V = {}"
      using hHaus hfx hgx hneq by blast

    have hUT: "U \<in> TY" and hfxU: "f x \<in> U"
      using hU unfolding neighborhood_of_def by blast+
    have hVT: "V \<in> TY" and hgxV: "g x \<in> V"
      using hV unfolding neighborhood_of_def by blast+

    let ?Uf = "{z\<in>X. f z \<in> U}"
    let ?Vg = "{z\<in>X. g z \<in> V}"
    have hUfTX: "?Uf \<in> TX"
      using hPreimf hUT by blast
    have hVgTX: "?Vg \<in> TX"
      using hPreimg hVT by blast

    let ?W = "?Uf \<inter> ?Vg"
    have hWTX: "?W \<in> TX"
      by (rule topology_inter2[OF hTopX hUfTX hVgTX])
    have hxW: "x \<in> ?W"
      using hxX hfxU hgxV by blast

    have hWsub: "?W \<subseteq> ?D"
    proof
      fix y
      assume hy: "y \<in> ?W"
      have hyX: "y \<in> X"
        using hy by blast
      have hfy: "f y \<in> U"
        using hy by blast
      have hgy: "g y \<in> V"
        using hy by blast

      have "f y \<noteq> g y"
      proof
        assume hEq: "f y = g y"
        have hfV: "f y \<in> V"
          using hgy hEq by simp
        have "f y \<in> U \<inter> V"
          using hfy hfV by blast
        thus False
          using hdisj by simp
      qed

      have "y \<notin> ?E"
      proof
        assume hyE: "y \<in> ?E"
        have "f y = g y"
          using hyE by simp
        thus False
          using \<open>f y \<noteq> g y\<close> by contradiction
      qed

      show "y \<in> ?D"
        using hyX \<open>y \<notin> ?E\<close> by simp
    qed

    show "\<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> ?D"
      apply (rule bexI[where x="?W"])
       apply (intro conjI)
        apply (rule hxW)
       apply (rule hWsub)
      apply (rule hWTX)
      done
  qed

  have hDopen: "?D \<in> TX"
    by (rule top1_open_of_local_subsets[OF hTopX hDsubX hLoc])

  show ?thesis
  proof (rule closedin_intro)
    show "?E \<subseteq> X"
      by (rule hEsubX)
    show "X - ?E \<in> TX"
      by (rule hDopen)
  qed
qed

(** from \S38 Lemma 38.3 (Uniqueness of continuous extensions to the closure) [top1.tex:5442] **)
lemma Lemma_38_3:
  assumes hTopX: "is_topology_on X TX"
  assumes hHausZ: "is_hausdorff_on Z TZ"
  assumes hcontf: "top1_continuous_map_on A (subspace_topology X TX A) Z TZ f"
  assumes hA_sub: "A \<subseteq> X"
  shows "\<forall>g1 g2.
    top1_continuous_map_on (closure_on X TX A) (subspace_topology X TX (closure_on X TX A)) Z TZ g1
    \<and> top1_continuous_map_on (closure_on X TX A) (subspace_topology X TX (closure_on X TX A)) Z TZ g2
    \<and> (\<forall>x\<in>A. g1 x = f x) \<and> (\<forall>x\<in>A. g2 x = f x)
    \<longrightarrow> top1_eq_on (closure_on X TX A) g1 g2"
proof (intro allI impI)
  fix g1 g2
  assume h:
    "top1_continuous_map_on (closure_on X TX A) (subspace_topology X TX (closure_on X TX A)) Z TZ g1
      \<and> top1_continuous_map_on (closure_on X TX A) (subspace_topology X TX (closure_on X TX A)) Z TZ g2
      \<and> (\<forall>x\<in>A. g1 x = f x) \<and> (\<forall>x\<in>A. g2 x = f x)"

  let ?C = "closure_on X TX A"
  let ?TC = "subspace_topology X TX ?C"
  let ?E = "{x\<in>?C. g1 x = g2 x}"

  have hCsubX: "?C \<subseteq> X"
    by (rule closure_on_subset_carrier[OF hTopX hA_sub])
  have hTopC: "is_topology_on ?C ?TC"
    by (rule subspace_topology_is_topology_on[OF hTopX hCsubX])

  have hg1: "top1_continuous_map_on ?C ?TC Z TZ g1"
    using h by simp
  have hg2: "top1_continuous_map_on ?C ?TC Z TZ g2"
    using h by simp

  have hClosedE: "closedin_on ?C ?TC ?E"
    by (rule top1_closedin_equalizer_of_continuous_maps[OF hTopC hHausZ hg1 hg2])

  have hAsubC: "A \<subseteq> ?C"
    by (rule subset_closure_on)

  have hAsubE: "A \<subseteq> ?E"
  proof
    fix x
    assume hxA: "x \<in> A"
    have hxC: "x \<in> ?C"
      using hAsubC hxA by blast
    have hEq1: "g1 x = f x"
      using h hxA by blast
    have hEq2: "g2 x = f x"
      using h hxA by blast
    have "g1 x = g2 x"
      using hEq1 hEq2 by simp
    thus "x \<in> ?E"
      using hxC by simp
  qed

  have hclAinC: "closure_on ?C ?TC A = ?C"
  proof -
    have "closure_on ?C ?TC A = closure_on X TX A \<inter> ?C"
      by (rule Theorem_17_4[OF hTopX hAsubC hCsubX])
    thus ?thesis
      by simp
  qed

  have hCsubE: "?C \<subseteq> ?E"
  proof -
    have "closure_on ?C ?TC A \<subseteq> ?E"
      by (rule closure_on_subset_of_closed[OF hClosedE hAsubE])
    thus ?thesis
      unfolding hclAinC by simp
  qed

  show "top1_eq_on ?C g1 g2"
    unfolding top1_eq_on_def
  proof (intro ballI)
    fix x
    assume hxC: "x \<in> ?C"
    have hxE: "x \<in> ?E"
      using hCsubE hxC by blast
    show "g1 x = g2 x"
      using hxE by simp
  qed
qed

(** from \S38 Theorem 38.4 (Extension to compact Hausdorff codomains) [top1.tex:5446] **)
theorem Theorem_38_4:
  assumes hCR: "top1_completely_regular_on X TX"
  assumes hComp: "top1_compactification_via_on X TX Y TY e"
  assumes hExtR:
    "\<forall>f. top1_continuous_map_on X TX UNIV order_topology_on_UNIV f
          \<and> top1_bounded_on X f
          \<longrightarrow> (\<exists>!g. top1_continuous_map_on Y TY UNIV order_topology_on_UNIV g
                  \<and> (\<forall>x\<in>X. g (e x) = f x))"
  assumes hCompC: "top1_compact_on C TC"
  assumes hHausC: "is_hausdorff_on C TC"
  shows "\<forall>f. top1_continuous_map_on X TX C TC f \<longrightarrow>
     (\<exists>g. top1_continuous_map_on Y TY C TC g
          \<and> (\<forall>x\<in>X. g (e x) = f x)
          \<and> (\<forall>g'. top1_continuous_map_on Y TY C TC g'
                \<and> (\<forall>x\<in>X. g' (e x) = f x)
                \<longrightarrow> top1_eq_on Y g g'))"
  sorry

(** from \S38 Theorem 38.5 (Uniqueness up to equivalence) [top1.tex:5456] **)
theorem Theorem_38_5:
  assumes hCR: "top1_completely_regular_on X TX"
  assumes hC1: "top1_compactification_via_on X TX Y1 TY1 e1"
  assumes hC2: "top1_compactification_via_on X TX Y2 TY2 e2"
  assumes hExt1:
    "\<forall>f. top1_continuous_map_on X TX UNIV order_topology_on_UNIV f
          \<and> top1_bounded_on X f
          \<longrightarrow> (\<exists>g. top1_continuous_map_on Y1 TY1 UNIV order_topology_on_UNIV g
                  \<and> (\<forall>x\<in>X. g (e1 x) = f x)
                  \<and> (\<forall>g'. top1_continuous_map_on Y1 TY1 UNIV order_topology_on_UNIV g'
                        \<and> (\<forall>x\<in>X. g' (e1 x) = f x)
                        \<longrightarrow> top1_eq_on Y1 g g'))"
  assumes hExt2:
    "\<forall>f. top1_continuous_map_on X TX UNIV order_topology_on_UNIV f
          \<and> top1_bounded_on X f
          \<longrightarrow> (\<exists>g. top1_continuous_map_on Y2 TY2 UNIV order_topology_on_UNIV g
                  \<and> (\<forall>x\<in>X. g (e2 x) = f x)
                  \<and> (\<forall>g'. top1_continuous_map_on Y2 TY2 UNIV order_topology_on_UNIV g'
                        \<and> (\<forall>x\<in>X. g' (e2 x) = f x)
                        \<longrightarrow> top1_eq_on Y2 g g'))"
  shows "top1_equiv_compactification_via_on X TX Y1 TY1 e1 Y2 TY2 e2"
  sorry

section \<open>\<S>39 Local Finiteness\<close>

definition top1_locally_finite_family_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_locally_finite_family_on X TX \<A> \<longleftrightarrow>
     (\<forall>x\<in>X. \<exists>U\<in>TX. x \<in> U \<and> finite {A\<in>\<A>. intersects A U})"

definition top1_sigma_locally_finite_family_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_sigma_locally_finite_family_on X TX \<A> \<longleftrightarrow>
     (\<exists>\<B>::nat \<Rightarrow> 'a set set.
        (\<forall>n. top1_locally_finite_family_on X TX (\<B> n)) \<and> \<A> = (\<Union>n. \<B> n))"

definition top1_refines :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_refines \<B> \<A> \<longleftrightarrow> (\<forall>B\<in>\<B>. \<exists>A\<in>\<A>. B \<subseteq> A)"

definition top1_open_covering_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_open_covering_on X TX \<A> \<longleftrightarrow> \<A> \<subseteq> TX \<and> X \<subseteq> \<Union>\<A>"

lemma top1_locally_finite_family_on_subset:
  assumes hLF: "top1_locally_finite_family_on X TX \<A>"
  assumes hSub: "\<A>' \<subseteq> \<A>"
  shows "top1_locally_finite_family_on X TX \<A>'"
proof -
  have hLF_def:
    "\<forall>x\<in>X. \<exists>U\<in>TX. x \<in> U \<and> finite {A\<in>\<A>. intersects A U}"
    using hLF
    unfolding top1_locally_finite_family_on_def
    by simp

  show ?thesis
    unfolding top1_locally_finite_family_on_def
  proof (intro ballI)
    fix x assume hx: "x \<in> X"
    obtain U where hU: "U \<in> TX"
      and hxU: "x \<in> U"
      and hFin: "finite {A\<in>\<A>. intersects A U}"
      using hLF_def hx
      by blast

    have hSubS: "{A\<in>\<A>'. intersects A U} \<subseteq> {A\<in>\<A>. intersects A U}"
    proof
      fix B
      assume hB: "B \<in> {A\<in>\<A>'. intersects A U}"
      have hBIn: "B \<in> \<A>'"
        using hB by simp
      have hBInA: "B \<in> \<A>"
        using hSub hBIn by blast
      have hInt: "intersects B U"
        using hB by simp
      show "B \<in> {A\<in>\<A>. intersects A U}"
        using hBInA hInt by simp
    qed

    have hFin': "finite {A\<in>\<A>'. intersects A U}"
      by (rule finite_subset[OF hSubS hFin])

    show "\<exists>V\<in>TX. x \<in> V \<and> finite {A\<in>\<A>'. intersects A V}"
      using hU hxU hFin' by blast
  qed
qed

text \<open>A finite union of locally finite families is locally finite.\<close>
lemma finite_union_locally_finite:
  assumes hTop: "is_topology_on X TX"
  assumes hFin: "finite I"
  assumes hLF: "\<forall>i\<in>I. top1_locally_finite_family_on X TX (F i)"
  shows "top1_locally_finite_family_on X TX (\<Union>i\<in>I. F i)"
  using hFin hLF
proof (induction I rule: finite_induct)
  case empty
  show ?case
    unfolding top1_locally_finite_family_on_def
  proof (intro ballI)
    fix x assume "x \<in> X"
    then obtain U where hU: "U \<in> TX" and hxU: "x \<in> U"
      using hTop unfolding is_topology_on_def
      by blast
    have hempty: "{A \<in> \<Union> (F ` {}). intersects A U} = {}"
      by blast
    show "\<exists>U\<in>TX. x \<in> U \<and> finite {A \<in> \<Union> (F ` {}). intersects A U}"
      using hU hxU hempty
      by auto
  qed
next
  case (insert j I)
  have hLF_j: "top1_locally_finite_family_on X TX (F j)"
    using insert.prems
    by blast
  have hLF_rest: "top1_locally_finite_family_on X TX (\<Union>i\<in>I. F i)"
    using insert.IH insert.prems
    by blast
  show ?case
    unfolding top1_locally_finite_family_on_def
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    obtain U1 where hU1: "U1 \<in> TX" and hxU1: "x \<in> U1"
      and hFin1: "finite {A \<in> F j. intersects A U1}"
      using hLF_j hxX unfolding top1_locally_finite_family_on_def
      by blast
    obtain U2 where hU2: "U2 \<in> TX" and hxU2: "x \<in> U2"
      and hFin2: "finite {A \<in> \<Union>i\<in>I. F i. intersects A U2}"
      using hLF_rest hxX unfolding top1_locally_finite_family_on_def
      by blast
    let ?U = "U1 \<inter> U2"
    have hU_open: "?U \<in> TX"
      using topology_inter2[OF hTop hU1 hU2]
      by satx
    have hxU: "x \<in> ?U" using hxU1 hxU2
      by blast
    have hsub1: "{A \<in> F j. intersects A ?U} \<subseteq> {A \<in> F j. intersects A U1}"
      unfolding intersects_def
      by auto
    have hsub2: "{A \<in> \<Union>i\<in>I. F i. intersects A ?U} \<subseteq> {A \<in> \<Union>i\<in>I. F i. intersects A U2}"
      unfolding intersects_def
      by blast
    have hsub_union: "{A \<in> \<Union> (F ` insert j I). intersects A ?U} \<subseteq>
          {A \<in> F j. intersects A ?U} \<union> {A \<in> \<Union>i\<in>I. F i. intersects A ?U}"
      by blast
    have hFin_j: "finite {A \<in> F j. intersects A ?U}"
      using finite_subset[OF hsub1 hFin1]
      by presburger
    have hFin_rest: "finite {A \<in> \<Union>i\<in>I. F i. intersects A ?U}"
      using finite_subset[OF hsub2 hFin2]
      by presburger
    have hFin_U: "finite {A \<in> \<Union> (F ` insert j I). intersects A ?U}"
      using finite_subset[OF hsub_union] hFin_j hFin_rest
      by blast
    show "\<exists>U\<in>TX. x \<in> U \<and> finite {A \<in> \<Union> (F ` insert j I). intersects A U}"
      using hU_open hxU hFin_U
      by meson
  qed
qed

text \<open>A countable union of sigma-locally-finite families is sigma-locally-finite.
  Uses diagonal sum enumeration: index by k = m + n.\<close>
lemma countable_union_sigma_lf:
  assumes hTop: "is_topology_on X TX"
  assumes hSLF: "\<forall>m::nat. top1_sigma_locally_finite_family_on X TX (Bm m)"
  shows "top1_sigma_locally_finite_family_on X TX (\<Union>m. Bm m)"
proof -
  text \<open>Decompose each Bm m into a sequence of LF families.\<close>
  have hex: "\<forall>m. \<exists>Cm::nat \<Rightarrow> 'a set set.
    (\<forall>n. top1_locally_finite_family_on X TX (Cm n)) \<and> Bm m = (\<Union>n. Cm n)"
    using hSLF unfolding top1_sigma_locally_finite_family_on_def
    by satx
  have hex2: "\<exists>Cm :: nat \<Rightarrow> nat \<Rightarrow> 'a set set.
    (\<forall>m n. top1_locally_finite_family_on X TX (Cm m n)) \<and> (\<forall>m. Bm m = (\<Union>n. Cm m n))"
    using hex
    by metis
  then obtain Cm :: "nat \<Rightarrow> nat \<Rightarrow> 'a set set" where
    hCm_lf: "\<forall>m n. top1_locally_finite_family_on X TX (Cm m n)" and
    hCm_eq: "\<forall>m. Bm m = (\<Union>n. Cm m n)"
    by blast
  text \<open>Diagonal enumeration: D k = \<Union>{Cm m (k - m) | m \<le> k}.\<close>
  define D where "D k = (\<Union>m\<in>{0..k}. Cm m (k - m))" for k :: nat
  have hD_lf: "\<forall>k. top1_locally_finite_family_on X TX (D k)"
  proof (intro allI)
    fix k :: nat
    have hfin_k: "finite {0..k}"
      by blast
    have hlf_k: "\<forall>m\<in>{0..k}. top1_locally_finite_family_on X TX (Cm m (k - m))"
      using hCm_lf
      by blast
    show "top1_locally_finite_family_on X TX (D k)"
      unfolding D_def using finite_union_locally_finite[OF hTop hfin_k hlf_k]
      by presburger
  qed
  have hD_sub1: "(\<Union>m. Bm m) \<subseteq> (\<Union>k. D k)"
  proof (rule subsetI)
    fix x assume "x \<in> (\<Union>m. Bm m)"
    then obtain m where hxBm: "x \<in> Bm m"
      by blast
    then obtain n where hxCmn: "x \<in> Cm m n"
      using hCm_eq
      by blast
    have hm_le: "m \<in> {0..m+n}"
      by simp
    have "Cm m ((m+n) - m) = Cm m n"
      by auto
    then have "x \<in> (\<Union>m'\<in>{0..m+n}. Cm m' ((m+n) - m'))"
      using hxCmn hm_le
      by fast
    then have "x \<in> D (m + n)"
      unfolding D_def
      by presburger
    then show "x \<in> (\<Union>k. D k)"
      by fast
  qed
  have hD_sub2: "(\<Union>k. D k) \<subseteq> (\<Union>m. Bm m)"
  proof (rule subsetI)
    fix x assume "x \<in> (\<Union>k. D k)"
    then obtain k where hxDk: "x \<in> D k"
      by blast
    then obtain m where hm: "m \<in> {0..k}" and hxCm: "x \<in> Cm m (k - m)"
      unfolding D_def
      by blast
    have "Cm m (k - m) \<subseteq> Bm m"
      using hCm_eq
      by blast
    then have "x \<in> Bm m" using hxCm
      by blast
    then show "x \<in> (\<Union>m. Bm m)"
      by blast
  qed
  have hD_eq: "(\<Union>m. Bm m) = (\<Union>k. D k)"
    using hD_sub1 hD_sub2
    by blast
  show ?thesis
    unfolding top1_sigma_locally_finite_family_on_def
    using hD_lf hD_eq
    by blast
qed

lemma top1_intersects_closure_on_open_imp_intersects:
  assumes hTopX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hU: "U \<in> TX"
  assumes hInt: "intersects (closure_on X TX A) U"
  shows "intersects A U"
proof -
  have hclX: "closure_on X TX A \<subseteq> X"
    by (rule closure_on_subset_carrier[OF hTopX hAX])

  obtain y where hycl: "y \<in> closure_on X TX A" and hyU: "y \<in> U"
    using hInt unfolding intersects_def by blast
  have hyX: "y \<in> X"
    using hclX hycl by blast

  have hChar:
    "y \<in> closure_on X TX A \<longleftrightarrow> (\<forall>V. neighborhood_of y X TX V \<longrightarrow> intersects V A)"
    by (rule Theorem_17_5a[OF hTopX hyX hAX])
  have hAll: "\<forall>V. neighborhood_of y X TX V \<longrightarrow> intersects V A"
    using hChar hycl by blast

  have hNbhU: "neighborhood_of y X TX U"
    unfolding neighborhood_of_def using hU hyU by simp
  have hUA: "intersects U A"
    using hAll hNbhU by blast

  obtain z where hzU: "z \<in> U" and hzA: "z \<in> A"
    using hUA unfolding intersects_def by blast

  show ?thesis
    unfolding intersects_def using hzA hzU by blast
qed

lemma top1_locally_finite_family_on_closure_image:
  assumes hTopX: "is_topology_on X TX"
  assumes hSubX: "\<forall>A\<in>\<A>. A \<subseteq> X"
  assumes hLF: "top1_locally_finite_family_on X TX \<A>"
  shows "top1_locally_finite_family_on X TX (closure_on X TX ` \<A>)"
proof -
  have hLF_def:
    "\<forall>x\<in>X. \<exists>U\<in>TX. x \<in> U \<and> finite {A\<in>\<A>. intersects A U}"
    using hLF
    unfolding top1_locally_finite_family_on_def
    by simp

  show ?thesis
    unfolding top1_locally_finite_family_on_def
  proof (intro ballI)
    fix x assume hx: "x \<in> X"
    obtain U where hU: "U \<in> TX"
      and hxU: "x \<in> U"
      and hFin: "finite {A\<in>\<A>. intersects A U}"
      using hLF_def hx
      by blast

    let ?S = "{A\<in>\<A>. intersects A U}"
    have hSfin: "finite ?S"
      using hFin by simp
    have hImgFin: "finite (closure_on X TX ` ?S)"
      using hSfin by (rule finite_imageI)

    let ?T = "{C\<in>(closure_on X TX ` \<A>). intersects C U}"
    have hTsub: "?T \<subseteq> (closure_on X TX ` ?S)"
    proof
      fix C
      assume hC: "C \<in> ?T"
      have hCimg: "C \<in> closure_on X TX ` \<A>"
        using hC by simp
      have hIntC: "intersects C U"
        using hC by simp

      obtain A where hA: "A \<in> \<A>" and hCeq: "C = closure_on X TX A"
        using hCimg by blast
      have hAX: "A \<subseteq> X"
        using hSubX hA by blast
      have hIntA: "intersects A U"
        using top1_intersects_closure_on_open_imp_intersects[OF hTopX hAX hU]
          hIntC
        unfolding hCeq
        by simp

      have hAS: "A \<in> ?S"
        using hA hIntA by simp
      show "C \<in> closure_on X TX ` ?S"
        unfolding hCeq using hAS by blast
    qed

    have hFinT: "finite ?T"
      by (rule finite_subset[OF hTsub hImgFin])

    show "\<exists>V\<in>TX. x \<in> V \<and> finite {C\<in>(closure_on X TX ` \<A>). intersects C V}"
      using hU hxU hFinT by blast
  qed
qed

lemma top1_Union_closure_on_subset_closure_on_Union:
  shows "(\<Union>(closure_on X TX ` \<A>)) \<subseteq> closure_on X TX (\<Union>\<A>)"
proof
  fix x
  assume hx: "x \<in> (\<Union>(closure_on X TX ` \<A>))"
  obtain A where hA: "A \<in> \<A>" and hxcl: "x \<in> closure_on X TX A"
    using hx by blast
  have hAsub: "A \<subseteq> (\<Union>\<A>)"
    using hA by blast
  have hclsub: "closure_on X TX A \<subseteq> closure_on X TX (\<Union>\<A>)"
    by (rule closure_on_mono[OF hAsub])
  show "x \<in> closure_on X TX (\<Union>\<A>)"
    using hclsub hxcl by blast
qed

lemma top1_closure_on_empty:
  assumes hTopX: "is_topology_on X TX"
  shows "closure_on X TX {} = {}"
proof -
  have hXopen: "X \<in> TX"
    using hTopX unfolding is_topology_on_def by simp
  have hEmptyClosed: "closedin_on X TX {}"
    unfolding closedin_on_def using hXopen by simp

  have hSub: "closure_on X TX {} \<subseteq> {}"
    by (rule closure_on_subset_of_closed[OF hEmptyClosed], simp)
  have hSup: "{} \<subseteq> closure_on X TX {}"
    using subset_closure_on by blast

  show ?thesis
    by (rule subset_antisym[OF hSub hSup])
qed

lemma top1_closure_on_union2:
  assumes hTopX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hBX: "B \<subseteq> X"
  shows "closure_on X TX (A \<union> B) = closure_on X TX A \<union> closure_on X TX B"
proof (rule subset_antisym)
  show "closure_on X TX (A \<union> B) \<subseteq> closure_on X TX A \<union> closure_on X TX B"
  proof -
    have hclA: "closedin_on X TX (closure_on X TX A)"
      by (rule closure_on_closed[OF hTopX hAX])
    have hclB: "closedin_on X TX (closure_on X TX B)"
      by (rule closure_on_closed[OF hTopX hBX])

    have hClosed: "closedin_on X TX (closure_on X TX A \<union> closure_on X TX B)"
    proof -
      have hfin: "finite {closure_on X TX A, closure_on X TX B}" by simp
      have hall: "\<forall>S\<in>{closure_on X TX A, closure_on X TX B}. closedin_on X TX S"
      proof (intro ballI)
        fix S
        assume hS: "S \<in> {closure_on X TX A, closure_on X TX B}"
        have hS': "S = closure_on X TX A \<or> S = closure_on X TX B"
          using hS by simp
        have h1: "S = closure_on X TX A \<Longrightarrow> closedin_on X TX S"
        proof -
          assume hEq: "S = closure_on X TX A"
          show "closedin_on X TX S"
            unfolding hEq by (rule hclA)
        qed
        have h2: "S = closure_on X TX B \<Longrightarrow> closedin_on X TX S"
        proof -
          assume hEq: "S = closure_on X TX B"
          show "closedin_on X TX S"
            unfolding hEq by (rule hclB)
        qed
        show "closedin_on X TX S"
          by (rule disjE[OF hS'], erule h1, erule h2)
      qed
      have "closedin_on X TX (\<Union>{closure_on X TX A, closure_on X TX B})"
        by (rule closedin_Union_finite[OF hTopX hfin hall])
      thus ?thesis
        by (simp only: Union_insert Union_empty Un_empty_right)
    qed

    have hSub: "A \<union> B \<subseteq> closure_on X TX A \<union> closure_on X TX B"
    proof (rule subsetI)
      fix x
      assume hx: "x \<in> A \<union> B"
      show "x \<in> closure_on X TX A \<union> closure_on X TX B"
      proof -
        have hx': "x \<in> A \<or> x \<in> B"
          using hx by simp
        show ?thesis
        proof (rule disjE[OF hx'])
          assume hxA: "x \<in> A"
          have hxclA: "x \<in> closure_on X TX A"
            using subset_closure_on hxA by (rule subsetD)
          show "x \<in> closure_on X TX A \<union> closure_on X TX B"
            by (rule UnI1, rule hxclA)
        next
          assume hxB': "x \<in> B"
          have hxclB: "x \<in> closure_on X TX B"
            using subset_closure_on hxB' by (rule subsetD)
          show "x \<in> closure_on X TX A \<union> closure_on X TX B"
            by (rule UnI2, rule hxclB)
        qed
      qed
    qed

    show ?thesis
      by (rule closure_on_subset_of_closed[OF hClosed hSub])
  qed

  show "closure_on X TX A \<union> closure_on X TX B \<subseteq> closure_on X TX (A \<union> B)"
  proof -
    have hAub: "A \<subseteq> A \<union> B"
      by (intro subsetI) simp
    have hBub: "B \<subseteq> A \<union> B"
      by (intro subsetI) simp
    have hclA_sub: "closure_on X TX A \<subseteq> closure_on X TX (A \<union> B)"
      by (rule closure_on_mono[OF hAub])
    have hclB_sub: "closure_on X TX B \<subseteq> closure_on X TX (A \<union> B)"
      by (rule closure_on_mono[OF hBub])
    show ?thesis
      by (rule Un_least[OF hclA_sub hclB_sub])
  qed
qed

lemma top1_closure_on_Union_finite:
  assumes hTopX: "is_topology_on X TX"
  assumes hFin: "finite S"
  assumes hSX: "\<forall>A\<in>S. A \<subseteq> X"
  shows "closure_on X TX (\<Union>S) = (\<Union>(closure_on X TX ` S))"
  using hFin hSX
proof (induction rule: finite_induct)
  case empty
  show ?case
  proof -
    have "closure_on X TX (\<Union>{}) = closure_on X TX {}"
      by (simp only: Union_empty)
    also have "... = {}"
      by (rule top1_closure_on_empty[OF hTopX])
    also have "... = (\<Union>(closure_on X TX ` {}))"
      by (simp only: image_empty Union_empty)
    finally show ?thesis .
  qed
next
  case (insert a F)
  have haX: "a \<subseteq> X"
    using insert.prems by simp
  have hFX: "\<forall>A\<in>F. A \<subseteq> X"
    using insert.prems by simp
  have hUFsubX: "\<Union>F \<subseteq> X"
    using hFX by blast

  show ?case
  proof -
    have hUnion: "\<Union>(insert a F) = a \<union> (\<Union>F)"
      by (simp only: Union_insert)
    have hStep: "closure_on X TX (\<Union>(insert a F)) = closure_on X TX a \<union> closure_on X TX (\<Union>F)"
      unfolding hUnion by (rule top1_closure_on_union2[OF hTopX haX hUFsubX])
    have hRHS: "(\<Union>(closure_on X TX ` insert a F)) = closure_on X TX a \<union> (\<Union>(closure_on X TX ` F))"
      by (simp only: image_insert Union_insert)

    have hIH: "closure_on X TX (\<Union>F) = (\<Union>(closure_on X TX ` F))"
      by (rule insert.IH[OF hFX])

    have "closure_on X TX (\<Union>(insert a F)) = closure_on X TX a \<union> closure_on X TX (\<Union>F)"
      by (rule hStep)
    also have "... = closure_on X TX a \<union> (\<Union>(closure_on X TX ` F))"
      by (simp only: hIH)
    also have "... = (\<Union>(closure_on X TX ` insert a F))"
      by (simp only: hRHS[symmetric])
    finally show ?thesis .
  qed
qed

lemma top1_closedin_Union_locally_finite:
  assumes hTopX: "is_topology_on X TX"
  assumes hSubX: "\<forall>C\<in>F. C \<subseteq> X"
  assumes hClosed: "\<forall>C\<in>F. closedin_on X TX C"
  assumes hLF: "top1_locally_finite_family_on X TX F"
  shows "closedin_on X TX (\<Union>F)"
proof -
  have hUnion_subX: "\<Union>F \<subseteq> X"
    using hSubX by blast

  have hXopen: "X \<in> TX"
    using hTopX unfolding is_topology_on_def by simp

  have hInter_TX:
    "\<forall>G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> TX \<longrightarrow> (\<Inter>G) \<in> TX"
    using hTopX unfolding is_topology_on_def by blast

  have hCompOpen: "X - (\<Union>F) \<in> TX"
  proof (rule top1_open_of_local_subsets[OF hTopX])
    show "X - (\<Union>F) \<subseteq> X"
      by blast
    show "\<forall>x\<in>X - (\<Union>F). \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> X - (\<Union>F)"
    proof (intro ballI)
      fix x
      assume hx: "x \<in> X - (\<Union>F)"
      have hxX: "x \<in> X"
        using hx by simp

      obtain U where hU: "U \<in> TX" and hxU: "x \<in> U"
        and hFinU: "finite {C\<in>F. intersects C U}"
        using hLF hxX unfolding top1_locally_finite_family_on_def by blast

      let ?U0 = "U \<inter> X"
      have hU0: "?U0 \<in> TX"
        by (rule topology_inter2[OF hTopX hU hXopen])
      have hxU0: "x \<in> ?U0"
        using hxU hxX by blast
      have hU0subX: "?U0 \<subseteq> X"
        by blast

      let ?S = "{C\<in>F. intersects C ?U0}"
      have hSsub: "?S \<subseteq> {C\<in>F. intersects C U}"
      proof
        fix C
        assume hC: "C \<in> ?S"
        have hCF: "C \<in> F"
          using hC by simp
        have hIntU0: "intersects C ?U0"
          using hC by simp
        have hIntU: "intersects C U"
        proof -
          have "C \<inter> ?U0 \<noteq> {}"
            using hIntU0 unfolding intersects_def by simp
          then obtain y where hy: "y \<in> C \<inter> ?U0"
            by blast
          have hyU: "y \<in> U"
            using hy by blast
          have "y \<in> C \<inter> U"
            using hy hyU by blast
          hence "C \<inter> U \<noteq> {}"
            by blast
          thus ?thesis
            unfolding intersects_def by simp
        qed
        show "C \<in> {C\<in>F. intersects C U}"
          using hCF hIntU by simp
      qed
      have hSfin: "finite ?S"
        by (rule finite_subset[OF hSsub hFinU])

      define V where "V = (\<Inter>(insert ?U0 ((\<lambda>C. X - C) ` ?S)))"

      have hVsubX: "V \<subseteq> X"
        unfolding V_def using hU0subX by blast

      have hVopen: "V \<in> TX"
      proof -
        have hImg_sub: "((\<lambda>C. X - C) ` ?S) \<subseteq> TX"
        proof
          fix W
          assume hW: "W \<in> ((\<lambda>C. X - C) ` ?S)"
          then obtain C where hC: "C \<in> ?S" and hWdef: "W = X - C"
            by blast
          have hCF: "C \<in> F"
            using hC by simp
          have hCclosed: "closedin_on X TX C"
            using hClosed hCF by blast
          have "X - C \<in> TX"
            by (rule closedin_diff_open[OF hCclosed])
          thus "W \<in> TX"
            unfolding hWdef by simp
        qed
        have hGfin: "finite (insert ?U0 ((\<lambda>C. X - C) ` ?S))"
          using hSfin by simp
        have hGne: "insert ?U0 ((\<lambda>C. X - C) ` ?S) \<noteq> {}"
          by simp
        have hGsub: "insert ?U0 ((\<lambda>C. X - C) ` ?S) \<subseteq> TX"
          using hU0 hImg_sub by blast
        have hGcond:
          "finite (insert ?U0 ((\<lambda>C. X - C) ` ?S))
            \<and> insert ?U0 ((\<lambda>C. X - C) ` ?S) \<noteq> {}
            \<and> insert ?U0 ((\<lambda>C. X - C) ` ?S) \<subseteq> TX"
          using hGfin hGne hGsub by simp
        have hImp:
          "finite (insert ?U0 ((\<lambda>C. X - C) ` ?S))
            \<and> insert ?U0 ((\<lambda>C. X - C) ` ?S) \<noteq> {}
            \<and> insert ?U0 ((\<lambda>C. X - C) ` ?S) \<subseteq> TX
            \<longrightarrow> (\<Inter>(insert ?U0 ((\<lambda>C. X - C) ` ?S))) \<in> TX"
          using hInter_TX by (rule spec[where x="insert ?U0 ((\<lambda>C. X - C) ` ?S)"])
        have hInterG': "(\<Inter>(insert ?U0 ((\<lambda>C. X - C) ` ?S))) \<in> TX"
          by (rule mp[OF hImp hGcond])
        show ?thesis
          by (subst V_def, rule hInterG')
      qed

      have hxV: "x \<in> V"
      proof -
        have hAll: "\<forall>W\<in>insert ?U0 ((\<lambda>C. X - C) ` ?S). x \<in> W"
        proof
          fix W
          assume hW: "W \<in> insert ?U0 ((\<lambda>C. X - C) ` ?S)"
          show "x \<in> W"
          proof (cases "W = ?U0")
            case True
            show ?thesis
              using hxU0 True by simp
          next
            case False
            then have hWimg: "W \<in> ((\<lambda>C. X - C) ` ?S)"
              using hW by simp
            then obtain C where hC: "C \<in> ?S" and hWdef: "W = X - C"
              by blast
            have hCF: "C \<in> F"
              using hC by simp
            have hxnot: "x \<notin> C"
            proof
              assume hxC: "x \<in> C"
              have "x \<in> (\<Union>F)"
                using hCF hxC by blast
              thus False
                using hx by simp
            qed
            show ?thesis
              unfolding hWdef using hxX hxnot by simp
          qed
        qed
        have "x \<in> (\<Inter>(insert ?U0 ((\<lambda>C. X - C) ` ?S)))"
          using hAll by (simp add: Inter_iff)
        thus ?thesis
          unfolding V_def by simp
      qed

      have hVsub: "V \<subseteq> X - (\<Union>F)"
      proof (rule subsetI)
        fix y
        assume hy: "y \<in> V"
        have hyX: "y \<in> X"
          using hVsubX hy by blast
        have hyU0: "y \<in> ?U0"
          using hy unfolding V_def V_def V_def V_def V_def V_def V_def by (simp add: V_def Inter_iff)
        have hyU: "y \<in> U"
          using hyU0 by blast
        have hynotUnion: "y \<notin> (\<Union>F)"
        proof
          assume hyUnion: "y \<in> (\<Union>F)"
          then obtain C where hCF: "C \<in> F" and hyC: "y \<in> C"
            by blast
          have hIntCU0: "intersects C ?U0"
            unfolding intersects_def
          proof -
            have "y \<in> C \<inter> ?U0"
              using hyC hyU0 by blast
            thus "C \<inter> ?U0 \<noteq> {}"
              by blast
          qed
          have hCS: "C \<in> ?S"
            using hCF hIntCU0 by simp
          have hMem: "X - C \<in> insert ?U0 ((\<lambda>C. X - C) ` ?S)"
            using hCS by blast
          have hyAll: "\<forall>W\<in>insert ?U0 ((\<lambda>C. X - C) ` ?S). y \<in> W"
            using hy unfolding V_def by (simp only: Inter_iff)
          have "y \<in> X - C"
            using hyAll hMem by blast
          thus False
            using hyC by simp
        qed
        show "y \<in> X - (\<Union>F)"
          using hyX hynotUnion by simp
      qed

      show "\<exists>W\<in>TX. x \<in> W \<and> W \<subseteq> X - (\<Union>F)"
        using hVopen hxV hVsub by blast
    qed
  qed

  show ?thesis
    by (rule closedin_intro[OF hUnion_subX], simp add: hCompOpen)
qed

lemma top1_closure_on_Union_locally_finite:
  assumes hTopX: "is_topology_on X TX"
  assumes hSubX: "\<forall>A\<in>\<A>. A \<subseteq> X"
  assumes hLF: "top1_locally_finite_family_on X TX \<A>"
  shows "closure_on X TX (\<Union>\<A>) = (\<Union>(closure_on X TX ` \<A>))"
proof (rule subset_antisym)
  have hUnion_subX: "\<Union>\<A> \<subseteq> X"
    using hSubX by blast

  have hXopen: "X \<in> TX"
    using hTopX unfolding is_topology_on_def by simp

  have hInter_TX:
    "\<forall>G. finite G \<and> G \<noteq> {} \<and> G \<subseteq> TX \<longrightarrow> (\<Inter>G) \<in> TX"
    using hTopX unfolding is_topology_on_def by blast

  show "closure_on X TX (\<Union>\<A>) \<subseteq> (\<Union>(closure_on X TX ` \<A>))"
  proof (rule subsetI)
    fix x
    assume hxcl: "x \<in> closure_on X TX (\<Union>\<A>)"

    have hxX: "x \<in> X"
    proof -
      have "closure_on X TX (\<Union>\<A>) \<subseteq> X"
        by (rule closure_on_subset_carrier[OF hTopX hUnion_subX])
      thus ?thesis
        using hxcl by blast
    qed

    show "x \<in> (\<Union>(closure_on X TX ` \<A>))"
    proof (rule ccontr)
      assume hxnot: "x \<notin> (\<Union>(closure_on X TX ` \<A>))"

      obtain U where hU: "U \<in> TX" and hxU: "x \<in> U"
        and hFinU: "finite {A\<in>\<A>. intersects A U}"
        using hLF hxX unfolding top1_locally_finite_family_on_def by blast

      let ?U0 = "U \<inter> X"
      have hU0: "?U0 \<in> TX"
        by (rule topology_inter2[OF hTopX hU hXopen])
      have hxU0: "x \<in> ?U0"
        using hxU hxX by blast
      have hU0subX: "?U0 \<subseteq> X"
        by blast

      let ?S = "{A\<in>\<A>. intersects A ?U0}"
      have hSsub: "?S \<subseteq> {A\<in>\<A>. intersects A U}"
      proof
        fix A
        assume hA: "A \<in> ?S"
        have hAA: "A \<in> \<A>"
          using hA by simp
        have hIntU0: "intersects A ?U0"
          using hA by simp
        have hIntU: "intersects A U"
        proof -
          have "A \<inter> ?U0 \<noteq> {}"
            using hIntU0 unfolding intersects_def by simp
          then obtain y where hy: "y \<in> A \<inter> ?U0"
            by blast
          have hyU: "y \<in> U"
            using hy by blast
          have "y \<in> A \<inter> U"
            using hy hyU by blast
          hence "A \<inter> U \<noteq> {}"
            by blast
          thus ?thesis
            unfolding intersects_def by simp
        qed
        show "A \<in> {A\<in>\<A>. intersects A U}"
          using hAA hIntU by simp
      qed
      have hSfin: "finite ?S"
        by (rule finite_subset[OF hSsub hFinU])

      have hx_not_closure: "\<forall>A\<in>?S. x \<notin> closure_on X TX A"
      proof (intro ballI)
        fix A
        assume hA: "A \<in> ?S"
        have hAA: "A \<in> \<A>"
          using hA by simp
        show "x \<notin> closure_on X TX A"
        proof
          assume hxA: "x \<in> closure_on X TX A"
          have "x \<in> (\<Union>(closure_on X TX ` \<A>))"
            using hAA hxA by blast
          thus False
            using hxnot by contradiction
        qed
      qed

      have hSep: "\<forall>A\<in>?S. \<exists>V. neighborhood_of x X TX V \<and> \<not> intersects V A"
      proof (intro ballI)
        fix A
        assume hA: "A \<in> ?S"
        have hAA: "A \<in> \<A>"
          using hA by simp
        have hAX: "A \<subseteq> X"
          using hSubX hAA by blast
        have hChar:
          "x \<in> closure_on X TX A \<longleftrightarrow>
            (\<forall>V. neighborhood_of x X TX V \<longrightarrow> intersects V A)"
          by (rule Theorem_17_5a[OF hTopX hxX hAX])
        have hxA_notcl: "x \<notin> closure_on X TX A"
          using hx_not_closure hA by blast
        have "\<not> (\<forall>V. neighborhood_of x X TX V \<longrightarrow> intersects V A)"
          using hxA_notcl hChar by blast
        then show "\<exists>V. neighborhood_of x X TX V \<and> \<not> intersects V A"
          by blast
      qed

      define V where
        "V = (\<lambda>A. (SOME W. neighborhood_of x X TX W \<and> \<not> intersects W A))"

      have hVprop: "\<forall>A\<in>?S. neighborhood_of x X TX (V A) \<and> \<not> intersects (V A) A"
      proof (intro ballI)
        fix A
        assume hA: "A \<in> ?S"
        have hex: "\<exists>W. neighborhood_of x X TX W \<and> \<not> intersects W A"
          using hSep hA by blast
        have "neighborhood_of x X TX (V A) \<and> \<not> intersects (V A) A"
          unfolding V_def by (rule someI_ex[OF hex])
        thus "neighborhood_of x X TX (V A) \<and> \<not> intersects (V A) A" .
      qed

      define W where "W = (\<Inter>(insert ?U0 (V ` ?S)))"

      have hWsubU0: "W \<subseteq> ?U0"
        unfolding W_def by blast

      have hWopen: "W \<in> TX"
      proof -
        have hVimg_sub: "V ` ?S \<subseteq> TX"
        proof
          fix Z
          assume hZ: "Z \<in> V ` ?S"
          then obtain A where hA: "A \<in> ?S" and hZdef: "Z = V A"
            by blast
          have "neighborhood_of x X TX (V A)"
            using hVprop hA by blast
          hence "V A \<in> TX"
            unfolding neighborhood_of_def by simp
          thus "Z \<in> TX"
            unfolding hZdef by simp
        qed
        have hGfin: "finite (insert ?U0 (V ` ?S))"
          using hSfin by simp
        have hGne: "insert ?U0 (V ` ?S) \<noteq> {}"
          by simp
        have hGsub: "insert ?U0 (V ` ?S) \<subseteq> TX"
          using hU0 hVimg_sub by blast
        have hGcond: "finite (insert ?U0 (V ` ?S))
            \<and> insert ?U0 (V ` ?S) \<noteq> {}
            \<and> insert ?U0 (V ` ?S) \<subseteq> TX"
          using hGfin hGne hGsub by simp
        have hImp: "finite (insert ?U0 (V ` ?S))
            \<and> insert ?U0 (V ` ?S) \<noteq> {}
            \<and> insert ?U0 (V ` ?S) \<subseteq> TX
            \<longrightarrow> (\<Inter>(insert ?U0 (V ` ?S))) \<in> TX"
          using hInter_TX by (rule spec[where x="insert ?U0 (V ` ?S)"])
        have hInterG': "(\<Inter>(insert ?U0 (V ` ?S))) \<in> TX"
          by (rule mp[OF hImp hGcond])
        show ?thesis
          by (subst W_def, rule hInterG')
      qed

      have hxW: "x \<in> W"
      proof -
        have hxVall: "\<forall>Z\<in>V ` ?S. x \<in> Z"
        proof
          fix Z
          assume hZ: "Z \<in> V ` ?S"
          then obtain A where hA: "A \<in> ?S" and hZdef: "Z = V A"
            by blast
          have "neighborhood_of x X TX (V A)"
            using hVprop hA by blast
          hence "x \<in> V A"
            unfolding neighborhood_of_def by simp
          thus "x \<in> Z"
            unfolding hZdef by simp
        qed
        have hxAll: "\<forall>Z\<in>insert ?U0 (V ` ?S). x \<in> Z"
          using hxU0 hxVall by blast
        have "x \<in> (\<Inter>(insert ?U0 (V ` ?S)))"
          using hxAll by (simp add: Inter_iff)
        thus ?thesis
          unfolding W_def by simp
      qed

      have hWnbh: "neighborhood_of x X TX W"
        unfolding neighborhood_of_def using hWopen hxW by simp

      have hWdisj: "\<not> intersects W (\<Union>\<A>)"
      proof -
        have hWsubX: "W \<subseteq> X"
          using hWsubU0 hU0subX by blast
        have hWsubComp: "W \<subseteq> X - (\<Union>\<A>)"
        proof (rule subsetI)
          fix y
          assume hy: "y \<in> W"
          have hyX: "y \<in> X"
            using hWsubX hy by blast
          have hyU0: "y \<in> ?U0"
            using hWsubU0 hy by blast
          show "y \<in> X - (\<Union>\<A>)"
          proof
            show "y \<in> X"
              using hyX .
            show "y \<notin> (\<Union>\<A>)"
            proof
              assume hyUnion: "y \<in> (\<Union>\<A>)"
              then obtain A where hAA: "A \<in> \<A>" and hyA: "y \<in> A"
                by blast
              have hIntAU0: "intersects A ?U0"
              proof -
                have "y \<in> A \<inter> ?U0"
                  using hyA hyU0 by blast
                hence "A \<inter> ?U0 \<noteq> {}"
                  by blast
                thus ?thesis
                  unfolding intersects_def by simp
              qed
              have hAS: "A \<in> ?S"
                using hAA hIntAU0 by simp
              have hyAll: "\<forall>Z\<in>insert ?U0 (V ` ?S). y \<in> Z"
                using hy unfolding W_def by (simp only: Inter_iff)
              have hVmem: "V A \<in> V ` ?S"
                using hAS by blast
              have "y \<in> V A"
              proof -
                have hVAin: "V A \<in> insert ?U0 (V ` ?S)"
                  using hVmem by simp
                show ?thesis
                  using hyAll hVAin by blast
              qed
              have "\<not> intersects (V A) A"
                using hVprop hAS by blast
              hence "V A \<inter> A = {}"
                unfolding intersects_def by blast
              thus False
                using \<open>y \<in> V A\<close> hyA by blast
            qed
          qed
        qed
        have "W \<inter> (\<Union>\<A>) = {}"
        proof (rule equalityI)
          show "W \<inter> (\<Union>\<A>) \<subseteq> {}"
            using hWsubComp by blast
          show "{} \<subseteq> W \<inter> (\<Union>\<A>)"
            by simp
        qed
        thus ?thesis
          unfolding intersects_def by simp
      qed

      have hCharUnion:
        "x \<in> closure_on X TX (\<Union>\<A>) \<longleftrightarrow>
          (\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U (\<Union>\<A>))"
        by (rule Theorem_17_5a[OF hTopX hxX hUnion_subX])
      have hAllN: "\<forall>U. neighborhood_of x X TX U \<longrightarrow> intersects U (\<Union>\<A>)"
        using hCharUnion hxcl by blast
      have hInt: "intersects W (\<Union>\<A>)"
        using hAllN hWnbh by blast
      have hEmpty: "W \<inter> (\<Union>\<A>) = {}"
        using hWdisj unfolding intersects_def by simp
      have hNonempty: "W \<inter> (\<Union>\<A>) \<noteq> {}"
        using hInt unfolding intersects_def by simp
      have hNot: "\<not> (W \<inter> (\<Union>\<A>) \<noteq> {})"
        using hEmpty by simp
      have hEq: "W \<inter> (\<Union>\<A>) = {}"
        using hNot by simp
      have hContr: False
        using hNonempty by (simp add: hEq)
      show False
        by (rule hContr)
    qed
  qed

  show "(\<Union>(closure_on X TX ` \<A>)) \<subseteq> closure_on X TX (\<Union>\<A>)"
    by (rule top1_Union_closure_on_subset_closure_on_Union)
qed

(** from \S39 Lemma 39.1 (Basic properties of locally finite families) [top1.tex:5542] **)
lemma Lemma_39_1:
  assumes hTopX: "is_topology_on X TX"
  assumes hSubX: "\<forall>A\<in>\<A>. A \<subseteq> X"
  assumes hLF: "top1_locally_finite_family_on X TX \<A>"
  shows "(\<forall>\<A>'. \<A>' \<subseteq> \<A> \<longrightarrow> top1_locally_finite_family_on X TX \<A>')"
    and "top1_locally_finite_family_on X TX (closure_on X TX ` \<A>)"
    and "closure_on X TX (\<Union>\<A>) = (\<Union>(closure_on X TX ` \<A>))"
proof -
  show "(\<forall>\<A>'. \<A>' \<subseteq> \<A> \<longrightarrow> top1_locally_finite_family_on X TX \<A>')"
  proof (intro allI impI)
    fix \<A>' assume hA'sub: "\<A>' \<subseteq> \<A>"
    show "top1_locally_finite_family_on X TX \<A>'"
      by (rule top1_locally_finite_family_on_subset[OF hLF hA'sub])
  qed

  show "top1_locally_finite_family_on X TX (closure_on X TX ` \<A>)"
    by (rule top1_locally_finite_family_on_closure_image[OF hTopX hSubX hLF])

  show "closure_on X TX (\<Union>\<A>) = (\<Union>(closure_on X TX ` \<A>))"
    by (rule top1_closure_on_Union_locally_finite[OF hTopX hSubX hLF])
qed

(** from \S39 Lemma 39.2 (Metrizable spaces admit countably locally finite refinements) [top1.tex:5567] **)
text \<open>Helper: r-neighborhood of a set (union of r-balls).\<close>
definition top1_nbhd_of_set ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 'a set" where
  "top1_nbhd_of_set X d S r = (\<Union>x\<in>S. top1_ball_on X d x r)"

lemma top1_nbhd_of_set_open:
  assumes hd: "top1_metric_on X d"
  assumes hS: "S \<subseteq> X"
  assumes hr: "0 < r"
  shows "top1_nbhd_of_set X d S r \<in> top1_metric_topology_on X d"
proof -
  let ?T = "top1_metric_topology_on X d"
  have hTop: "is_topology_on X ?T"
    by (metis hd top1_metric_topology_on_is_topology_on)
  have hballs: "\<forall>x\<in>S. top1_ball_on X d x r \<in> ?T"
    using hr hd hS top1_ball_open_in_metric_topology by fastforce
  have hset_sub: "(\<lambda>x. top1_ball_on X d x r) ` S \<subseteq> ?T"
    using hballs by blast
  have hunion: "\<Union>((\<lambda>x. top1_ball_on X d x r) ` S) \<in> ?T"
    using hTop hset_sub unfolding is_topology_on_def by simp
  show ?thesis
    unfolding top1_nbhd_of_set_def using hunion by argo
qed

lemma top1_nbhd_of_set_sub:
  assumes hS: "S \<subseteq> X"
  shows "top1_nbhd_of_set X d S r \<subseteq> X"
  unfolding top1_nbhd_of_set_def top1_ball_on_def
  by fast

lemma top1_nbhd_of_set_contains:
  assumes hd: "top1_metric_on X d"
  assumes hxS: "x \<in> S"
  assumes hSX: "S \<subseteq> X"
  assumes hr: "0 < r"
  shows "x \<in> top1_nbhd_of_set X d S r"
proof -
  have hxX: "x \<in> X"
    using hxS hSX by fast
  have hdxx: "d x x = 0"
    using hd hxX unfolding top1_metric_on_def by blast
  have hxball: "x \<in> top1_ball_on X d x r"
    unfolding top1_ball_on_def using hxX hdxx hr by simp
  show ?thesis
    unfolding top1_nbhd_of_set_def using hxS hxball by blast
qed

lemma Lemma_39_2:
  assumes hMet: "top1_metrizable_on X TX"
  assumes hCov: "top1_open_covering_on X TX \<A>"
  shows "\<exists>\<E>. top1_open_covering_on X TX \<E> \<and> top1_refines \<E> \<A> \<and> top1_sigma_locally_finite_family_on X TX \<E>"
proof -
  text \<open>Get the metric and topology facts.\<close>
  obtain d where hd: "top1_metric_on X d" and hTX: "TX = top1_metric_topology_on X d"
    using hMet unfolding top1_metrizable_on_def by blast
  have hTop: "is_topology_on X TX"
    using hTX hd top1_metric_topology_on_is_topology_on by fastforce
  have hAsub: "\<A> \<subseteq> TX"
    using hCov unfolding top1_open_covering_on_def by satx
  have hAcovers: "X \<subseteq> \<Union>\<A>"
    using hCov unfolding top1_open_covering_on_def by satx

  text \<open>Well-order the elements of \<A> (using the well-ordering theorem on the type).\<close>
  obtain r :: "'a set rel" where hWO: "Well_order r" and hField: "Field r = UNIV"
    using well_ordering by fast

  text \<open>Define the Munkres construction.\<close>
  text \<open>S_n(U) = \{x \<in> X | ball(x, 1/(Suc n)) \<subseteq> U\}\<close>
  define Sn where "Sn n U = {x \<in> X. top1_ball_on X d x (1 / real (Suc n)) \<subseteq> U}" for n :: nat and U
  text \<open>T_n(U) = S_n(U) - \<Union>\{V \<in> \<A> | (V,U) \<in> r \<and> V \<noteq> U\}\<close>
  define Tn where "Tn n U = Sn n U - \<Union>{V \<in> \<A>. (V, U) \<in> r \<and> V \<noteq> U}" for n :: nat and U
  text \<open>E_n(U) = (1/(3*(Suc n)))-neighborhood of T_n(U).\<close>
  define En where "En n U = top1_nbhd_of_set X d (Tn n U) (1 / (3 * real (Suc n)))" for n :: nat and U
  text \<open>\<E>_n = \{E_n(U) | U \<in> \<A>\}, \<E> = \<Union>n. \<E>_n.\<close>
  define \<E>n where "\<E>n n = {En n U | U. U \<in> \<A>}" for n :: nat
  define \<E> where "\<E> = (\<Union>n. \<E>n n)"

  text \<open>Basic subset facts.\<close>
  have hSn_sub_X: "\<And>n U. Sn n U \<subseteq> X"
    unfolding Sn_def by blast
  have hTn_sub_X: "\<And>n U. Tn n U \<subseteq> X"
    unfolding Tn_def using hSn_sub_X by fast
  have hTn_sub_U: "\<And>n U. U \<in> \<A> \<Longrightarrow> Tn n U \<subseteq> U"
  proof -
    fix n U assume hU: "U \<in> \<A>"
    show "Tn n U \<subseteq> U"
    proof (rule subsetI)
      fix x assume hx: "x \<in> Tn n U"
      have hxSn: "x \<in> Sn n U" using hx unfolding Tn_def by blast
      have hball: "top1_ball_on X d x (1 / real (Suc n)) \<subseteq> U"
        using hxSn unfolding Sn_def by blast
      have hxX: "x \<in> X" using hxSn unfolding Sn_def by fast
      have hdxx: "d x x = 0" using hd hxX unfolding top1_metric_on_def by blast
      have hxball: "x \<in> top1_ball_on X d x (1 / real (Suc n))"
        unfolding top1_ball_on_def using hxX hdxx by auto
      show "x \<in> U" using hball hxball by blast
    qed
  qed

  text \<open>E_n(U) \<subseteq> U: T_n(U) has 1/(Suc n) margin inside U, E_n expands by 1/(3*(Suc n)) < 1/(Suc n).\<close>
  have hEn_sub_U: "\<And>n U. U \<in> \<A> \<Longrightarrow> En n U \<subseteq> U"
  proof -
    fix n U assume hU: "U \<in> \<A>"
    show "En n U \<subseteq> U"
      unfolding En_def top1_nbhd_of_set_def
    proof (rule subsetI)
      fix y assume hy: "y \<in> (\<Union>x\<in>Tn n U. top1_ball_on X d x (1 / (3 * real (Suc n))))"
      then obtain x where hxTn: "x \<in> Tn n U" and hyball: "y \<in> top1_ball_on X d x (1 / (3 * real (Suc n)))"
        by blast
      have hxSn: "x \<in> Sn n U" using hxTn unfolding Tn_def by fast
      have hball_margin: "top1_ball_on X d x (1 / real (Suc n)) \<subseteq> U"
        using hxSn unfolding Sn_def by blast
      have hxX: "x \<in> X" using hxSn hSn_sub_X by blast
      have hyX: "y \<in> X" using hyball unfolding top1_ball_on_def by blast
      have hdxy: "d x y < 1 / (3 * real (Suc n))"
        using hyball unfolding top1_ball_on_def by blast
      have hdxy_lt: "d x y < 1 / real (Suc n)"
      proof -
        have h3pos: "0 < (3::real)" by simp
        have hSnpos: "0 < real (Suc n)" by simp
        have "1 / (3 * real (Suc n)) \<le> 1 / real (Suc n)"
          using h3pos hSnpos by (simp add: divide_le_eq)
        then show ?thesis using hdxy by argo
      qed
      have "y \<in> top1_ball_on X d x (1 / real (Suc n))"
        unfolding top1_ball_on_def using hyX hdxy_lt by fast
      then show "y \<in> U" using hball_margin by blast
    qed
  qed

  text \<open>Key separation: T_n(V) and T_n(W) at distance \<ge> 1/(Suc n) for V \<noteq> W in \<A>.\<close>
  have hTn_sep: "\<And>n V W. V \<in> \<A> \<Longrightarrow> W \<in> \<A> \<Longrightarrow> V \<noteq> W \<Longrightarrow>
    \<forall>x\<in>Tn n V. \<forall>y\<in>Tn n W. d x y \<ge> 1 / real (Suc n)"
  proof (intro ballI)
    fix n V W x y
    assume hV: "V \<in> \<A>" and hW: "W \<in> \<A>" and hVW: "V \<noteq> W"
    assume hxTV: "x \<in> Tn n V" and hyTW: "y \<in> Tn n W"
    have hxX: "x \<in> X" using hxTV hTn_sub_X
      
      by blast
    have hyX: "y \<in> X" using hyTW hTn_sub_X
      
      by fast
    have htotal: "(V, W) \<in> r \<or> (W, V) \<in> r"
    proof -
      have hLin: "Linear_order r" using hWO unfolding well_order_on_def
        by presburger
      then have hTot: "total_on (Field r) r" unfolding linear_order_on_def
        by presburger
      then show ?thesis using hField hVW unfolding total_on_def
        by (simp add: hVW)
    qed
    show "d x y \<ge> 1 / real (Suc n)"
    proof (cases "(V, W) \<in> r")
      case True
      have hxSn: "x \<in> Sn n V" using hxTV unfolding Tn_def
        
        by blast
      have hball_V: "top1_ball_on X d x (1 / real (Suc n)) \<subseteq> V"
        using hxSn unfolding Sn_def
        
        by blast
      have hV_in_pred: "V \<in> {V' \<in> \<A>. (V', W) \<in> r \<and> V' \<noteq> W}"
        using hV True hVW
        
        by auto
      have hynotV: "y \<notin> V"
        using hyTW hV_in_pred unfolding Tn_def
        
        by blast
      have hynotball: "y \<notin> top1_ball_on X d x (1 / real (Suc n))"
        using hball_V hynotV
        
        by blast
      then show ?thesis
        unfolding top1_ball_on_def using hyX
        
        by simp
    next
      case False
      then have hWV: "(W, V) \<in> r" using htotal
        
        by satx
      have hySn: "y \<in> Sn n W" using hyTW unfolding Tn_def
        
        by blast
      have hball_W: "top1_ball_on X d y (1 / real (Suc n)) \<subseteq> W"
        using hySn unfolding Sn_def
        
        by auto
      have hW_in_pred: "W \<in> {V' \<in> \<A>. (V', V) \<in> r \<and> V' \<noteq> V}"
        using hW hWV hVW
        
        by blast
      have hxnotW: "x \<notin> W"
        using hxTV hW_in_pred unfolding Tn_def
        
        by blast
      have hxnotball: "x \<notin> top1_ball_on X d y (1 / real (Suc n))"
        using hball_W hxnotW
        
        by blast
      then have hdyx: "d y x \<ge> 1 / real (Suc n)"
        unfolding top1_ball_on_def using hxX
        
        by fastforce
      show ?thesis
        using hdyx hd hxX hyX unfolding top1_metric_on_def
        
        by force
    qed
  qed

  text \<open>Consequence: E_n(V) and E_n(W) at distance \<ge> 1/(3*(Suc n)) for V \<noteq> W.\<close>
  have hEn_sep: "\<And>n V W. V \<in> \<A> \<Longrightarrow> W \<in> \<A> \<Longrightarrow> V \<noteq> W \<Longrightarrow>
    \<forall>y1\<in>En n V. \<forall>y2\<in>En n W. d y1 y2 \<ge> 1 / (3 * real (Suc n))"
  proof (intro ballI)
    fix n V W y1 y2
    assume hV: "V \<in> \<A>" and hW: "W \<in> \<A>" and hVW: "V \<noteq> W"
    assume hy1: "y1 \<in> En n V" and hy2: "y2 \<in> En n W"
    text \<open>y1 is in 1/3n-ball around some x1 \<in> T_n(V).\<close>
    obtain x1 where hx1T: "x1 \<in> Tn n V" and hy1ball: "y1 \<in> top1_ball_on X d x1 (1 / (3 * real (Suc n)))"
      using hy1 unfolding En_def top1_nbhd_of_set_def
      
      by blast
    obtain x2 where hx2T: "x2 \<in> Tn n W" and hy2ball: "y2 \<in> top1_ball_on X d x2 (1 / (3 * real (Suc n)))"
      using hy2 unfolding En_def top1_nbhd_of_set_def
      
      by blast
    have hx1X: "x1 \<in> X" using hx1T hTn_sub_X
      
      by blast
    have hx2X: "x2 \<in> X" using hx2T hTn_sub_X
      
      by blast
    have hy1X: "y1 \<in> X" using hy1ball unfolding top1_ball_on_def
      
      by fast
    have hy2X: "y2 \<in> X" using hy2ball unfolding top1_ball_on_def
      
      by blast
    have hdx1y1: "d x1 y1 < 1 / (3 * real (Suc n))"
      using hy1ball unfolding top1_ball_on_def
      
      by blast
    have hdx2y2: "d x2 y2 < 1 / (3 * real (Suc n))"
      using hy2ball unfolding top1_ball_on_def
      
      by blast
    have hdx1x2: "d x1 x2 \<ge> 1 / real (Suc n)"
      using hTn_sep[OF hV hW hVW] hx1T hx2T
      
      by blast
    text \<open>Triangle inequality: d(x1,x2) \<le> d(x1,y1) + d(y1,y2) + d(y2,x2).\<close>
    have htri1: "d x1 x2 \<le> d x1 y1 + d y1 x2"
      using hd hx1X hy1X hx2X unfolding top1_metric_on_def
      
      by blast
    have htri2: "d y1 x2 \<le> d y1 y2 + d y2 x2"
      using hd hy1X hy2X hx2X unfolding top1_metric_on_def
      
      by blast
    have hdsym1: "d x1 y1 = d y1 x1"
      using hd hx1X hy1X unfolding top1_metric_on_def
      
      by blast
    have hdsym2: "d x2 y2 = d y2 x2"
      using hd hx2X hy2X unfolding top1_metric_on_def
      
      by blast
    text \<open>Combine: d(y1,y2) \<ge> d(x1,x2) - d(x1,y1) - d(x2,y2) \<ge> 1/n - 1/3n - 1/3n = 1/3n.\<close>
    have hchain: "d x1 x2 \<le> d x1 y1 + d y1 y2 + d y2 x2"
      using htri1 htri2
      
      by auto
    have "d y1 y2 \<ge> d x1 x2 - d x1 y1 - d y2 x2"
      using hchain
      
      by argo
    then have "d y1 y2 \<ge> 1 / real (Suc n) - 1 / (3 * real (Suc n)) - 1 / (3 * real (Suc n))"
      using hdx1x2 hdx1y1 hdx2y2 hdsym2
      
      by auto
    then have hge: "d y1 y2 \<ge> 1 / real (Suc n) - 2 * (1 / (3 * real (Suc n)))"
      by fastforce
    have hSnpos: "0 < real (Suc n)" by simp
    have harith: "1 / real (Suc n) - 2 * (1 / (3 * real (Suc n))) = 1 / (3 * real (Suc n))"
      using hSnpos by (simp add: field_simps)
    show "d y1 y2 \<ge> 1 / (3 * real (Suc n))"
      using hge harith by force
  qed

  text \<open>\<E>_n is locally finite: ball(x, 1/(6*(Suc n))) meets at most one E_n(U).\<close>
  have hEn_lf: "\<And>n. top1_locally_finite_family_on X TX (\<E>n n)"
  proof -
    fix n
    let ?eps = "1 / (6 * real (Suc n))"
    have heps: "0 < ?eps"
      
      by fastforce
    show "top1_locally_finite_family_on X TX (\<E>n n)"
      unfolding top1_locally_finite_family_on_def
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      let ?B = "top1_ball_on X d x ?eps"
      have hBopen: "?B \<in> TX"
        using hd hxX heps hTX
        
        by (meson top1_ball_open_in_metric_topology)
      have hxB: "x \<in> ?B"
      proof -
        have "d x x = 0" using hd hxX unfolding top1_metric_on_def
          
          by blast
        then show ?thesis unfolding top1_ball_on_def using hxX heps
          
          by force
      qed
      text \<open>?B meets at most one E_n(U): if it met E_n(V) and E_n(W) with V \<noteq> W,
        pick y1 \<in> ?B \<inter> E_n(V), y2 \<in> ?B \<inter> E_n(W).
        d(y1,y2) \<le> d(y1,x)+d(x,y2) < 1/6n + 1/6n = 1/3n.
        But d(y1,y2) \<ge> 1/3n by hEn_sep. Contradiction.\<close>
      have hfinite: "finite {E \<in> \<E>n n. intersects E ?B}"
      proof (rule finite_subset[where B="{E \<in> \<E>n n. intersects E ?B}"])
        show "{E \<in> \<E>n n. intersects E ?B} \<subseteq> {E \<in> \<E>n n. intersects E ?B}"
          
          by blast
        text \<open>Show there is at most one such E.\<close>
        have hatmost1: "\<forall>E1\<in>\<E>n n. \<forall>E2\<in>\<E>n n. intersects E1 ?B \<longrightarrow> intersects E2 ?B \<longrightarrow> E1 = E2"
        proof (intro ballI impI)
          fix E1 E2
          assume hE1: "E1 \<in> \<E>n n" and hE2: "E2 \<in> \<E>n n"
          assume hi1: "intersects E1 ?B" and hi2: "intersects E2 ?B"
          obtain V where hV: "V \<in> \<A>" and hE1eq: "E1 = En n V"
            using hE1 unfolding \<E>n_def
            
            by blast
          obtain W where hW: "W \<in> \<A>" and hE2eq: "E2 = En n W"
            using hE2 unfolding \<E>n_def
            
            by blast
          show "E1 = E2"
          proof (rule ccontr)
            assume hneq: "E1 \<noteq> E2"
            then have hVW: "V \<noteq> W" using hE1eq hE2eq
              
              by fast
            obtain y1 where hy1E: "y1 \<in> E1" and hy1B: "y1 \<in> ?B"
              using hi1 unfolding intersects_def
              
              by blast
            obtain y2 where hy2E: "y2 \<in> E2" and hy2B: "y2 \<in> ?B"
              using hi2 unfolding intersects_def
              
              by blast
            have hy1X: "y1 \<in> X" using hy1B unfolding top1_ball_on_def
              
              by blast
            have hy2X: "y2 \<in> X" using hy2B unfolding top1_ball_on_def
              
              by blast
            have hdy1x: "d x y1 < ?eps" using hy1B unfolding top1_ball_on_def
              
              by blast
            have hdy2x: "d x y2 < ?eps" using hy2B unfolding top1_ball_on_def
              
              by blast
            have htri: "d y1 y2 \<le> d y1 x + d x y2"
              using hd hy1X hxX hy2X unfolding top1_metric_on_def
              
              by fast
            have hdsym: "d y1 x = d x y1"
              using hd hy1X hxX unfolding top1_metric_on_def
              
              by blast
            have hd_upper: "d y1 y2 < ?eps + ?eps"
              using htri hdsym hdy1x hdy2x
              
              by argo
            have heps_arith: "?eps + ?eps = 1 / (3 * real (Suc n))"
              by (simp add: field_simps)
            have "d y1 y2 < 1 / (3 * real (Suc n))"
              using hd_upper heps_arith
              
              by simp
            moreover have "d y1 y2 \<ge> 1 / (3 * real (Suc n))"
              using hEn_sep[OF hV hW hVW] hy1E hy2E unfolding hE1eq hE2eq
              
              by blast
            ultimately show False
              
              by argo
          qed
        qed
        show "finite {E \<in> \<E>n n. intersects E ?B}"
        proof (cases "{E \<in> \<E>n n. intersects E ?B} = {}")
          case True then show ?thesis
            
            by (metis True finite.emptyI)
        next
          case False
          then obtain e0 where he0: "e0 \<in> \<E>n n" and hi0: "intersects e0 ?B"
            
            by blast
          have "{E \<in> \<E>n n. intersects E ?B} \<subseteq> {e0}"
            using hatmost1 he0 hi0
            
            by fast
          then show ?thesis
            using finite_subset
            
            by auto
        qed
      qed
      show "\<exists>U\<in>TX. x \<in> U \<and> finite {A \<in> \<E>n n. intersects A U}"
        using hBopen hxB hfinite
        
        by blast
    qed
  qed

  text \<open>\<E>_n consists of open sets in TX.\<close>
  have hEn_open: "\<And>n. \<E>n n \<subseteq> TX"
  proof (rule subsetI)
    fix n V assume hV: "V \<in> \<E>n n"
    then obtain U where hU: "U \<in> \<A>" and hVeq: "V = En n U"
      unfolding \<E>n_def by blast
    have hopen: "En n U \<in> top1_metric_topology_on X d"
      unfolding En_def
      by (rule top1_nbhd_of_set_open[OF hd hTn_sub_X]) simp
    show "V \<in> TX"
      unfolding hVeq hTX using hopen by blast
  qed

  text \<open>\<E>_n refines \<A>.\<close>
  have hEn_ref: "\<And>n. top1_refines (\<E>n n) \<A>"
    unfolding top1_refines_def
  proof (intro allI impI ballI)
    fix n B assume hB: "B \<in> \<E>n n"
    then obtain U where hU: "U \<in> \<A>" and hBeq: "B = En n U"
      unfolding \<E>n_def by blast
    show "\<exists>A\<in>\<A>. B \<subseteq> A"
      using hU hEn_sub_U[OF hU, of n] hBeq by blast
  qed

  text \<open>\<Union>_n \<E>_n covers X.\<close>
  have hE_covers: "X \<subseteq> \<Union>\<E>"
  proof (rule subsetI)
    fix x assume hxX: "x \<in> X"
    text \<open>The set of covering elements containing x is nonempty.\<close>
    define AX where "AX = {U \<in> \<A>. x \<in> U}"
    have hAXne: "AX \<noteq> {}"
      using hAcovers hxX unfolding AX_def
      
      by blast
    text \<open>Pick the r-least element of AX (well-ordering gives a minimum).\<close>
    have hAX_sub_Field: "AX \<subseteq> Field r" using hField
      
      by simp
    obtain U0 where hU0AX: "U0 \<in> AX" and hU0min: "\<forall>V\<in>AX. (U0, V) \<in> r"
    proof -
      have hwf: "wf (r - Id)"
        using hWO unfolding well_order_on_def
        
        by presburger
      obtain z where hzAX: "z \<in> AX" and hzmin: "\<forall>y. (y, z) \<in> r - Id \<longrightarrow> y \<notin> AX"
        using wf_iff_ex_minimal[THEN iffD1, OF hwf, rule_format, OF hAXne]
        
        by blast
      have hzleast: "\<forall>V\<in>AX. (z, V) \<in> r"
      proof (intro ballI)
        fix V assume hVAX: "V \<in> AX"
        show "(z, V) \<in> r"
        proof (cases "V = z")
          case True
          then show ?thesis using hWO hField unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def refl_on_def
            
            by fast
        next
          case False
          have hnotstrict: "(V, z) \<notin> r - Id" using hzmin hVAX
            
            by blast
          then have "(V, z) \<notin> r" using False
            
            by fast
          then show "(z, V) \<in> r"
            using hWO hField unfolding well_order_on_def linear_order_on_def total_on_def
            
            using False by blast
        qed
      qed
      show ?thesis using that hzAX hzleast
        
        by presburger
    qed
    have hU0A: "U0 \<in> \<A>" using hU0AX unfolding AX_def
      
      by blast
    have hxU0: "x \<in> U0" using hU0AX unfolding AX_def
      
      by blast
    text \<open>U0 is open (metric), so ball(x, 1/(Suc n)) \<subseteq> U0 for some n.\<close>
    have hU0open: "U0 \<in> TX" using hU0A hAsub
      
      by fast
    obtain e0 where he0pos: "0 < e0" and hball0: "top1_ball_on X d x e0 \<subseteq> U0"
      using top1_metric_open_contains_ball[OF hd] hU0open hxU0 hTX
      
      by blast
    obtain n where hn: "1 / real (Suc n) < e0"
    proof -
      obtain k :: nat where hk: "1 / e0 < real k"
        using reals_Archimedean2 he0pos
        
        by fast
      have "1 / e0 < real (Suc k)" using hk
        
        by simp
      then have "1 / real (Suc k) < e0"
        using he0pos by (simp add: field_simps)
      then show ?thesis using that
        
        by blast
    qed
    text \<open>ball(x, 1/(Suc n)) \<subseteq> ball(x, e0) \<subseteq> U0.\<close>
    have hball_sub: "top1_ball_on X d x (1 / real (Suc n)) \<subseteq> U0"
    proof (rule subset_trans)
      show "top1_ball_on X d x (1 / real (Suc n)) \<subseteq> top1_ball_on X d x e0"
        unfolding top1_ball_on_def using hn
        
        using hn by fastforce
      show "top1_ball_on X d x e0 \<subseteq> U0" by (rule hball0)
    qed
    text \<open>x \<in> S_n(U0).\<close>
    have hxSn: "x \<in> Sn n U0"
      unfolding Sn_def using hxX hball_sub
      
      by blast
    text \<open>x \<notin> V for any V < U0 in \<A> (by minimality of U0).\<close>
    have hxnotpred: "x \<notin> \<Union>{V \<in> \<A>. (V, U0) \<in> r \<and> V \<noteq> U0}"
    proof (rule ccontr)
      assume "\<not> x \<notin> \<Union>{V \<in> \<A>. (V, U0) \<in> r \<and> V \<noteq> U0}"
      then obtain V where hVA: "V \<in> \<A>" and hVr: "(V, U0) \<in> r" and hVne: "V \<noteq> U0" and hxV: "x \<in> V"
        
        by blast
      have hVAX: "V \<in> AX" unfolding AX_def using hVA hxV
        
        by blast
      have hU0V: "(U0, V) \<in> r" using hU0min hVAX
        
        by simp
      text \<open>Both (V,U0) \<in> r and (U0,V) \<in> r with V \<noteq> U0 contradicts antisymmetry.\<close>
      have "V = U0"
        using hWO hVr hU0V unfolding well_order_on_def linear_order_on_def partial_order_on_def antisym_def
        
        by presburger
      then show False using hVne
        
        by order
    qed
    text \<open>x \<in> T_n(U0).\<close>
    have hxTn: "x \<in> Tn n U0"
      unfolding Tn_def using hxSn hxnotpred
      
      by blast
    text \<open>x \<in> E_n(U0) \<in> \<E>_n \<subseteq> \<E>.\<close>
    have h3npos: "0 < 1 / (3 * real (Suc n))"
      
      by auto
    have hxEn: "x \<in> En n U0"
      unfolding En_def
      by (rule top1_nbhd_of_set_contains[OF hd hxTn hTn_sub_X h3npos])
    have "En n U0 \<in> \<E>n n"
      unfolding \<E>n_def using hU0A
      
      by blast
    then have "En n U0 \<in> \<E>"
      unfolding \<E>_def
      
      by fast
    then show "x \<in> \<Union>\<E>"
      using hxEn
      
      by blast
  qed

  text \<open>Assemble the final result.\<close>
  have hE_cov: "top1_open_covering_on X TX \<E>"
    unfolding top1_open_covering_on_def
    using hEn_open hE_covers unfolding \<E>_def by blast

  have hE_ref: "top1_refines \<E> \<A>"
    unfolding top1_refines_def \<E>_def
    using hEn_ref unfolding top1_refines_def by fast

  have hE_slf: "top1_sigma_locally_finite_family_on X TX \<E>"
    unfolding top1_sigma_locally_finite_family_on_def
  proof (rule exI[where x="\<E>n"], intro conjI allI)
    fix n show "top1_locally_finite_family_on X TX (\<E>n n)" by (rule hEn_lf)
  next
    show "\<E> = (\<Union>n. \<E>n n)" unfolding \<E>_def by (rule refl)
  qed

  show ?thesis
    using hE_cov hE_ref hE_slf by blast
qed

section \<open>\<S>40 The Nagata-Smirnov Metrization Theorem\<close>

definition top1_G_delta_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_G_delta_on X TX A \<longleftrightarrow> A \<subseteq> X \<and> (\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> A = (\<Inter>n. U n))"

(** from \S40 Lemma 40.1 [top1.tex:5675] **)
text \<open>Step 1 of Lemma 40.1: open set decomposition.
  Given regular X with sigma-locally-finite basis B, any open W equals
  \<Union>U_n = \<Union>cl(U_n) where U_n are open and cl(U_n) \<subseteq> W.\<close>
lemma Lemma_40_1_step1:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  assumes hW: "W \<in> TX"
  shows "\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> (\<forall>n. closure_on X TX (U n) \<subseteq> W) \<and> W = (\<Union>n. U n)"
proof -
  have hTop: "is_topology_on X TX"
    using hReg unfolding top1_regular_on_def top1_T1_on_def
    
    by satx
  have hBsub: "\<B> \<subseteq> TX"
    using hBasis unfolding basis_for_def
    
    using basis_elem_open_in_generated_topology by blast
  text \<open>Decompose the basis into countably many locally finite families.\<close>
  have hCLF_unf: "\<exists>\<B>n::nat \<Rightarrow> 'a set set. (\<forall>n. top1_locally_finite_family_on X TX (\<B>n n)) \<and> \<B> = (\<Union>n. \<B>n n)"
    using hCLF unfolding top1_sigma_locally_finite_family_on_def
    
    by argo
  obtain \<B>n :: "nat \<Rightarrow> 'a set set" where hBn_lf: "\<forall>n. top1_locally_finite_family_on X TX (\<B>n n)"
    and hB_eq: "\<B> = (\<Union>n. \<B>n n)"
    using hCLF_unf
    
    by blast
  text \<open>C_n = \{B \<in> B_n | cl(B) \<subseteq> W\}, U_n = \<Union>C_n.\<close>
  define Cn where "Cn n = {B \<in> \<B>n n. closure_on X TX B \<subseteq> W}" for n
  define U where "U n = \<Union>(Cn n)" for n

  have hUn_open: "\<forall>n. U n \<in> TX"
  proof (intro allI)
    fix n
    have hCn_sub_TX: "Cn n \<subseteq> TX"
    proof (rule subsetI)
      fix B assume "B \<in> Cn n"
      then have "B \<in> \<B>n n" unfolding Cn_def
        
        by fast
      then have "B \<in> \<B>" using hB_eq
        
        by blast
      then show "B \<in> TX" using hBsub
        
        by blast
    qed
    show "U n \<in> TX"
      unfolding U_def using hTop hCn_sub_TX unfolding is_topology_on_def
      
      by presburger
  qed

  have hB_subX: "\<forall>b\<in>\<B>. b \<subseteq> X"
    using hBasis unfolding basis_for_def is_basis_on_def
    by satx

  text \<open>cl(U_n) \<subseteq> W: each Cn is locally finite (subset of Bn), so cl(\<Union>Cn) = \<Union>cl(Cn).\<close>
  have hCn_lf: "\<forall>n. top1_locally_finite_family_on X TX (Cn n)"
  proof (intro allI)
    fix n
    have hCn_sub_Bn: "Cn n \<subseteq> \<B>n n" unfolding Cn_def by fast
    have hBn_subX: "\<forall>A\<in>\<B>n n. A \<subseteq> X"
    proof (intro ballI)
      fix A assume "A \<in> \<B>n n"
      then have "A \<in> \<B>" using hB_eq
        
        by blast
      then show "A \<subseteq> X" using hB_subX
        
        by blast
    qed
    show "top1_locally_finite_family_on X TX (Cn n)"
      using hCn_sub_Bn
        Lemma_39_1(1)[OF hTop hBn_subX hBn_lf[rule_format, of n]]
      
      by presburger
  qed
  have hCn_subX: "\<forall>n. \<forall>B\<in>Cn n. B \<subseteq> X"
  proof (intro allI ballI)
    fix n B assume "B \<in> Cn n"
    then have "B \<in> \<B>n n" unfolding Cn_def by fast
    then have "B \<in> \<B>" using hB_eq by blast
    then show "B \<subseteq> X" using hB_subX
      
      by blast
  qed

  have hUn_cl: "\<forall>n. closure_on X TX (U n) \<subseteq> W"
  proof (intro allI)
    fix n
    have hCn_subX_n: "\<forall>A\<in>Cn n. A \<subseteq> X"
      using hCn_subX
      
      by presburger
    have hcl_eq: "closure_on X TX (U n) = (\<Union>(closure_on X TX ` Cn n))"
      unfolding U_def
      using Lemma_39_1(3)[OF hTop hCn_subX_n hCn_lf[rule_format, of n]]
      
      by presburger
    have "\<forall>B\<in>Cn n. closure_on X TX B \<subseteq> W"
      unfolding Cn_def
      
      by blast
    then show "closure_on X TX (U n) \<subseteq> W"
      unfolding hcl_eq
      
      by blast
  qed

  text \<open>W \<subseteq> \<Union>n. U n: for x \<in> W, regularity gives B with cl(B) \<subseteq> W.\<close>
  have hW_sub: "W \<subseteq> (\<Union>n. U n)"
  proof (rule subsetI)
    fix x assume hxW: "x \<in> W"
    have hWsubX: "W \<subseteq> X"
      using hW hBasis unfolding basis_for_def
      
      by (simp add: topology_generated_by_basis_def)
    have hxX: "x \<in> X"
      using hxW hWsubX
      
      by fast
    have hRegProp: "\<exists>V\<in>TX. x \<in> V \<and> closure_on X TX V \<subseteq> W"
    proof -
      define C where "C = X - W"
      have hCclosed: "closedin_on X TX C"
        unfolding C_def closedin_on_def using hWsubX hW
        
        by (simp add: Diff_Diff_Int Int_absorb1)
      have hxnotC: "x \<notin> C"
        unfolding C_def using hxW
        
        by blast
      obtain U0 V0 where hU0: "neighborhood_of x X TX U0" and hV0: "V0 \<in> TX"
        and hCV0: "C \<subseteq> V0" and hdisjoint: "U0 \<inter> V0 = {}"
        using hReg hxX hCclosed hxnotC unfolding top1_regular_on_def
        
        by blast
      obtain U0' where hU0'open: "U0' \<in> TX" and hxU0': "x \<in> U0'" and hU0'sub: "U0' \<subseteq> U0"
        using hU0 unfolding neighborhood_of_def
        
        by blast
      have hU0'_disj_V0: "U0' \<inter> V0 = {}"
        using hU0'sub hdisjoint
        
        by blast
      have hV0subX: "V0 \<subseteq> X"
        using hV0 hBasis unfolding basis_for_def topology_generated_by_basis_def
        
        by force
      have hXminusV0_closed: "closedin_on X TX (X - V0)"
        unfolding closedin_on_def using hV0 hV0subX
        by (simp add: double_diff)
      have hU0'_sub_XmV0: "U0' \<subseteq> X - V0"
      proof -
        have "U0' \<subseteq> X" using hU0'open hBasis unfolding basis_for_def topology_generated_by_basis_def
          
          by blast
        then show ?thesis using hU0'_disj_V0
          
          by blast
      qed
      have hcl_sub: "closure_on X TX U0' \<subseteq> X - V0"
        using hXminusV0_closed hU0'_sub_XmV0
        
        by (simp add: closure_on_subset_of_closed)
      have hXmV0_sub_W: "X - V0 \<subseteq> W"
        using hCV0 unfolding C_def
        
        by blast
      have hcl_sub_W: "closure_on X TX U0' \<subseteq> W"
        using hcl_sub hXmV0_sub_W
        
        by order
      show ?thesis using hU0'open hxU0' hcl_sub_W
        
        by blast
    qed
    obtain V where hVopen: "V \<in> TX" and hxV: "x \<in> V" and hclV: "closure_on X TX V \<subseteq> W"
      using hRegProp
      
      by blast
    text \<open>Since B is a basis, there is B \<in> B with x \<in> B \<subseteq> V.\<close>
    obtain B where hBB: "B \<in> \<B>" and hxB: "x \<in> B" and hBV: "B \<subseteq> V"
      using hBasis hxX hVopen hxV unfolding basis_for_def
      
      by (metis basis_for_refine hBasis)
    have hclB: "closure_on X TX B \<subseteq> W"
    proof -
      have "B \<subseteq> V"
        
        by (simp add: hBV)
      then have "closure_on X TX B \<subseteq> closure_on X TX V"
        
        by (simp add: closure_on_mono)
      then show ?thesis using hclV
        
        by order
    qed
    obtain n where "B \<in> \<B>n n"
      using hBB hB_eq
      
      by fast
    then have "B \<in> Cn n" unfolding Cn_def using hclB
      
      by blast
    then have "x \<in> U n" unfolding U_def using hxB
      
      by fast
    then show "x \<in> (\<Union>n. U n)"
      
      by blast
  qed

  have hWeq: "W = (\<Union>n. U n)"
  proof (rule equalityI)
    show "W \<subseteq> (\<Union>n. U n)" by (rule hW_sub)
    show "(\<Union>n. U n) \<subseteq> W"
    proof (rule subsetI)
      fix x assume "x \<in> (\<Union>n. U n)"
      then obtain n where "x \<in> U n"
        
        by blast
      then have "x \<in> \<Union>(Cn n)" unfolding U_def
        
        by satx
      then obtain B where "B \<in> Cn n" and "x \<in> B"
        
        by blast
      then have "closure_on X TX B \<subseteq> W" unfolding Cn_def
        
        by blast
      moreover have "x \<in> closure_on X TX B"
        using \<open>x \<in> B\<close> subset_closure_on
        
        by fast
      ultimately show "x \<in> W"
        
        by blast
    qed
  qed

  have hconj: "(\<forall>n. U n \<in> TX) \<and> (\<forall>n. closure_on X TX (U n) \<subseteq> W) \<and> W = (\<Union>n. U n)"
    using hUn_open hUn_cl hWeq
    
    by argo
  show ?thesis using hconj
    
    by blast
qed

text \<open>Step 2 of Lemma 40.1: closed sets are G-delta.\<close>
lemma Lemma_40_1_step2:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  assumes hClosed: "closedin_on X TX A"
  shows "top1_G_delta_on X TX A"
proof -
  have hTop: "is_topology_on X TX"
    using hReg unfolding top1_regular_on_def top1_T1_on_def
    
    by satx
  have hAX: "A \<subseteq> X"
    using hClosed unfolding closedin_on_def
    
    by presburger
  define W where "W = X - A"
  have hWopen: "W \<in> TX"
    using hClosed unfolding closedin_on_def W_def
    
    by presburger
  obtain U :: "nat \<Rightarrow> 'a set" where hUopen: "\<forall>n. U n \<in> TX"
    and hUcl: "\<forall>n. closure_on X TX (U n) \<subseteq> W"
    and hWeq: "W = (\<Union>n. U n)"
    using Lemma_40_1_step1[OF hReg hBasis hCLF hWopen]
    by metis
  text \<open>A = \<Inter>n. (X - cl(U n))\<close>
  define V where "V n = X - closure_on X TX (U n)" for n
  have hVopen: "\<forall>n. V n \<in> TX"
  proof (intro allI)
    fix n
    have hUnX: "U n \<subseteq> X"
      using hUcl hUopen W_def
      
      using subset_closure_on by fastforce
    have hcl: "closedin_on X TX (closure_on X TX (U n))"
      using hTop hUnX closure_on_closed
      
      by blast
    show "V n \<in> TX"
      using hcl unfolding V_def closedin_on_def
      
      by presburger
  qed
  have hAeq: "A = (\<Inter>n. V n)"
  proof -
    have "W = (\<Union>n. closure_on X TX (U n))"
    proof (rule equalityI)
      show "W \<subseteq> (\<Union>n. closure_on X TX (U n))"
        unfolding hWeq using subset_closure_on
        
        by fast
      show "(\<Union>n. closure_on X TX (U n)) \<subseteq> W"
        using hUcl
        
        by blast
    qed
    then have "X - W = (\<Inter>n. X - closure_on X TX (U n))"
      
      by blast
    then show ?thesis
      unfolding V_def W_def using hAX
      
      by blast
  qed
  show ?thesis
    unfolding top1_G_delta_on_def
  proof (intro conjI)
    show "A \<subseteq> X" by (rule hAX)
    have hex: "(\<forall>n. V n \<in> TX) \<and> A = (\<Inter>n. V n)"
      using hVopen hAeq
      
      by presburger
    show "\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> A = (\<Inter>n. U n)"
      apply (rule exI[where x=V])
      using hex
      
      by satx
  qed
qed

text \<open>Step 3 of Lemma 40.1: normality via the Theorem 32.1 technique.\<close>
text \<open>Finite union of closed sets is closed.\<close>
lemma closedin_on_finite_Union:
  assumes hTop: "is_topology_on X TX"
  assumes hCl: "\<forall>A\<in>F. closedin_on X TX A"
  assumes hFin: "finite F"
  shows "closedin_on X TX (\<Union>F)"
  using hFin hCl
proof (induct F rule: finite_induct)
  case empty
  show ?case unfolding closedin_on_def using hTop unfolding is_topology_on_def
    
    by auto
next
  case (insert A F)
  have hAcl: "closedin_on X TX A"
    using insert.prems
    
    by blast
  have hFcl: "closedin_on X TX (\<Union>F)"
    using insert.hyps insert.prems
    
    by blast
  have hAX: "A \<subseteq> X" using hAcl unfolding closedin_on_def
    
    by presburger
  have hFX: "\<Union>F \<subseteq> X" using hFcl unfolding closedin_on_def
    
    by presburger
  have hAopen: "X - A \<in> TX" using hAcl unfolding closedin_on_def
    
    by presburger
  have hFopen: "X - \<Union>F \<in> TX" using hFcl unfolding closedin_on_def
    
    by presburger
  have hinter: "(X - A) \<inter> (X - \<Union>F) \<in> TX"
    using hTop hAopen hFopen
    
    by (simp add: topology_inter2)
  have heq: "X - (A \<union> \<Union>F) = (X - A) \<inter> (X - \<Union>F)"
    
    by auto
  have hXsub: "A \<union> \<Union>F \<subseteq> X" using hAX hFX
    
    by simp
  show ?case unfolding closedin_on_def using hXsub hinter heq
    
    by auto
qed

lemma Lemma_40_1_step3:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  shows "top1_normal_on X TX"
proof -
  have hTop: "is_topology_on X TX"
    using hReg unfolding top1_regular_on_def top1_T1_on_def
    
    by linarith
  have hT1: "top1_T1_on X TX"
    using hReg unfolding top1_regular_on_def
    
    by presburger
  show ?thesis
    unfolding top1_normal_on_def
  proof (intro conjI allI impI)
    show "top1_T1_on X TX" by (rule hT1)
  next
    fix C D
    assume hCD: "closedin_on X TX C \<and> closedin_on X TX D \<and> C \<inter> D = {}"
    have hCcl: "closedin_on X TX C" using hCD
      
      by presburger
    have hDcl: "closedin_on X TX D" using hCD
      
      by presburger
    have hdisj: "C \<inter> D = {}" using hCD
      
      by presburger
    have hCX: "C \<subseteq> X" using hCcl unfolding closedin_on_def
      
      by presburger
    have hDX: "D \<subseteq> X" using hDcl unfolding closedin_on_def
      
      by presburger

    text \<open>X-D is open, apply step1 to get {U_n} covering C with cl(U_n) ⊆ X-D.\<close>
    have hXmD_open: "X - D \<in> TX" using hDcl unfolding closedin_on_def
      
      by presburger
    have hex_U: "\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> (\<forall>n. closure_on X TX (U n) \<subseteq> X - D) \<and> X - D = (\<Union>n. U n)"
      by (rule Lemma_40_1_step1[OF hReg hBasis hCLF hXmD_open])
    obtain Ufn :: "nat \<Rightarrow> 'a set" where hUopen: "\<forall>n. Ufn n \<in> TX"
      and hUcl: "\<forall>n. closure_on X TX (Ufn n) \<subseteq> X - D"
      and hXmD_eq: "X - D = (\<Union>n. Ufn n)"
      using hex_U
      
      by blast

    text \<open>Similarly for X-C.\<close>
    have hXmC_open: "X - C \<in> TX" using hCcl unfolding closedin_on_def
      
      by linarith
    have hex_V: "\<exists>V::nat \<Rightarrow> 'a set. (\<forall>n. V n \<in> TX) \<and> (\<forall>n. closure_on X TX (V n) \<subseteq> X - C) \<and> X - C = (\<Union>n. V n)"
      by (rule Lemma_40_1_step1[OF hReg hBasis hCLF hXmC_open])
    obtain Vn :: "nat \<Rightarrow> 'a set" where hVopen: "\<forall>n. Vn n \<in> TX"
      and hVcl: "\<forall>n. closure_on X TX (Vn n) \<subseteq> X - C"
      and hXmC_eq: "X - C = (\<Union>n. Vn n)"
      using hex_V
      
      by blast

    text \<open>U_n covers C (since C ⊆ X-D = ∪U_n). V_n covers D.\<close>
    have hC_sub_Un: "C \<subseteq> (\<Union>n. Ufn n)"
      using hXmD_eq hdisj hCX
      
      by auto
    have hD_sub_Vn: "D \<subseteq> (\<Union>n. Vn n)"
      using hXmC_eq hdisj hDX
      
      by blast

    text \<open>Construct U'_n = U_n - ∪{cl(V_i) | i ≤ n}, V'_n = V_n - ∪{cl(U_i) | i ≤ n}.\<close>
    define U' where "U' (n::nat) = Ufn n - (\<Union> (closure_on X TX ` Vn ` {0..n}))" for n
    define V' where "V' (n::nat) = Vn n - (\<Union> (closure_on X TX ` Ufn ` {0..n}))" for n

    text \<open>U' = ∪U'_n and V' = ∪V'_n.\<close>
    define UU where "UU = (\<Union>n. U' n)"
    define VV where "VV = (\<Union>n. V' n)"

    text \<open>U'_n are open (Ufn n open minus finite union of closed = open).\<close>
    have hU'open: "\<forall>n. U' n \<in> TX"
    proof (intro allI)
      fix n
      have hclVn_closed: "\<forall>i. closedin_on X TX (closure_on X TX (Vn i))"
      proof (intro allI)
        fix i
        have "Vn i \<subseteq> X"
          using hVopen hBasis unfolding basis_for_def topology_generated_by_basis_def
          
          by blast
        then show "closedin_on X TX (closure_on X TX (Vn i))"
          using hTop
          
          by (metis hTop closure_on_closed)
      qed
      have hfinite_union_closed: "closedin_on X TX (\<Union> (closure_on X TX ` Vn ` {0..n}))"
        using closedin_on_finite_Union[OF hTop] hclVn_closed
        
        by simp
      have hcomplement_open: "X - (\<Union> (closure_on X TX ` Vn ` {0..n})) \<in> TX"
        using hfinite_union_closed unfolding closedin_on_def
        
        by presburger
      have hUfnX: "Ufn n \<subseteq> X"
        using hUopen hBasis unfolding basis_for_def topology_generated_by_basis_def
        
        by blast
      have hU'eq: "U' n = Ufn n \<inter> (X - (\<Union> (closure_on X TX ` Vn ` {0..n})))"
        unfolding U'_def using hUfnX
        
        by fast
      show "U' n \<in> TX"
        unfolding hU'eq
        using topology_inter2[OF hTop hUopen[rule_format, of n] hcomplement_open]
        
        by presburger
    qed
    have hV'open: "\<forall>n. V' n \<in> TX"
    proof (intro allI)
      fix n
      have hclUfn_closed: "\<forall>i. closedin_on X TX (closure_on X TX (Ufn i))"
      proof (intro allI)
        fix i
        have "Ufn i \<subseteq> X"
          using hUopen hBasis unfolding basis_for_def topology_generated_by_basis_def
          
          by blast
        then show "closedin_on X TX (closure_on X TX (Ufn i))"
          using hTop
          
          by (metis hTop closure_on_closed)
      qed
      have hfinite_union_closed: "closedin_on X TX (\<Union> (closure_on X TX ` Ufn ` {0..n}))"
        using closedin_on_finite_Union[OF hTop] hclUfn_closed
        
        by auto
      have hcomplement_open: "X - (\<Union> (closure_on X TX ` Ufn ` {0..n})) \<in> TX"
        using hfinite_union_closed unfolding closedin_on_def
        
        by satx
      have hVnX: "Vn n \<subseteq> X"
        using hVopen hBasis unfolding basis_for_def topology_generated_by_basis_def
        
        by blast
      have hV'eq: "V' n = Vn n \<inter> (X - (\<Union> (closure_on X TX ` Ufn ` {0..n})))"
        unfolding V'_def using hVnX
        
        by fast
      show "V' n \<in> TX"
        unfolding hV'eq
        using hVopen hcomplement_open hTop
        
        using topology_inter2 by blast
    qed

    text \<open>UU and VV are open (unions of opens).\<close>
    have hU'range: "range U' \<subseteq> TX"
      using hU'open
      
      by blast
    have hUU_open: "UU \<in> TX"
    proof -
      have "\<Union>(range U') \<in> TX"
        using hTop hU'range unfolding is_topology_on_def
        
        by presburger
      then show ?thesis unfolding UU_def
        
        by presburger
    qed
    have hV'range: "range V' \<subseteq> TX"
      using hV'open
      
      by auto
    have hVV_open: "VV \<in> TX"
    proof -
      have "\<Union>(range V') \<in> TX"
        using hTop hV'range unfolding is_topology_on_def
        
        by presburger
      then show ?thesis unfolding VV_def
        
        by argo
    qed

    text \<open>C ⊆ UU: for c ∈ C, c ∈ Ufn_n for some n; cl(Vn_i) ⊆ X-C for all i, so c ∉ cl(Vn_i).\<close>
    have hC_sub_UU: "C \<subseteq> UU"
    proof (rule subsetI)
      fix c assume hcC: "c \<in> C"
      have hcUn: "c \<in> (\<Union>n. Ufn n)" using hC_sub_Un hcC
        
        by fast
      then obtain n where hcUfn: "c \<in> Ufn n"
        
        by blast
      have hc_not_clV: "\<forall>i. c \<notin> closure_on X TX (Vn i)"
      proof (intro allI)
        fix i
        have "closure_on X TX (Vn i) \<subseteq> X - C" using hVcl
          
          by presburger
        then show "c \<notin> closure_on X TX (Vn i)" using hcC
          
          by blast
      qed
      have "c \<in> U' n"
        unfolding U'_def using hcUfn hc_not_clV
        
        by blast
      then show "c \<in> UU" unfolding UU_def
        
        by blast
    qed
    have hD_sub_VV: "D \<subseteq> VV"
    proof (rule subsetI)
      fix d assume hdD: "d \<in> D"
      have hdVn: "d \<in> (\<Union>n. Vn n)" using hD_sub_Vn hdD
        
        by fast
      then obtain n where hdVnn: "d \<in> Vn n"
        
        by blast
      have hd_not_clU: "\<forall>i. d \<notin> closure_on X TX (Ufn i)"
      proof (intro allI)
        fix i
        have "closure_on X TX (Ufn i) \<subseteq> X - D" using hUcl
          
          by auto
        then show "d \<notin> closure_on X TX (Ufn i)" using hdD
          
          by blast
      qed
      have "d \<in> V' n"
        unfolding V'_def using hdVnn hd_not_clU
        
        by fast
      then show "d \<in> VV" unfolding VV_def
        
        by fast
    qed

    text \<open>UU ∩ VV = {}: if z ∈ U'_m ∩ V'_n, then WLOG m ≤ n.
      z ∈ U'_m ⊆ Ufn_m, so z ∈ closure_on Ufn_m. But z ∈ V'_n excludes ∪{cl(Ufn_i)|i≤n}.\<close>
    have hUV_disj: "UU \<inter> VV = {}"
    proof (rule ccontr)
      assume "\<not> UU \<inter> VV = {}"
      then obtain z where hzUU: "z \<in> UU" and hzVV: "z \<in> VV"
        
        by auto
      obtain m where hzU'm: "z \<in> U' m"
        using hzUU unfolding UU_def
        
        by blast
      obtain n where hzV'n: "z \<in> V' n"
        using hzVV unfolding VV_def
        
        by blast
      text \<open>WLOG m ≤ n (symmetric argument for n ≤ m).\<close>
      have "m \<le> n \<or> n \<le> m"
        
        by presburger
      then show False
      proof
        assume hmn: "m \<le> n"
        text \<open>z ∈ U'_m ⊆ Ufn_m, so z ∈ closure(Ufn_m) (since Ufn_m ⊆ closure(Ufn_m)).\<close>
        have hzUfn: "z \<in> Ufn m" using hzU'm unfolding U'_def
          
          by blast
        have hzclU: "z \<in> closure_on X TX (Ufn m)"
          using hzUfn subset_closure_on
          
          by fast
        text \<open>But z ∈ V'_n = Vn_n - ∪{cl(Ufn_i)|i≤n}, and m ≤ n.\<close>
        have "z \<notin> closure_on X TX (Ufn m)"
          using hzV'n hmn unfolding V'_def
          
          by simp
        then show False using hzclU
          
          by presburger
      next
        assume hnm: "n \<le> m"
        have hzVnn: "z \<in> Vn n" using hzV'n unfolding V'_def
          
          by blast
        have hzclV: "z \<in> closure_on X TX (Vn n)"
          using hzVnn subset_closure_on
          
          by fast
        have "z \<notin> closure_on X TX (Vn n)"
          using hzU'm hnm unfolding U'_def
          
          by auto
        then show False using hzclV
          
          by presburger
      qed
    qed

    show "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> C \<subseteq> U \<and> D \<subseteq> V \<and> U \<inter> V = {}"
      using hUU_open hVV_open hC_sub_UU hD_sub_VV hUV_disj
      
      by blast
  qed
qed

lemma Lemma_40_1:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  shows "top1_normal_on X TX \<and> (\<forall>A. closedin_on X TX A \<longrightarrow> top1_G_delta_on X TX A)"
  using Lemma_40_1_step3[OF hReg hBasis hCLF]
        Lemma_40_1_step2[OF hReg hBasis hCLF]
  
  by argo

text \<open>Metric topologies are Hausdorff: distinct points separated by d/2-balls.\<close>
lemma metric_topology_hausdorff:
  assumes hd: "top1_metric_on X d"
  shows "is_hausdorff_on X (top1_metric_topology_on X d)"
proof -
  let ?TX = "top1_metric_topology_on X d"
  have hTop: "is_topology_on X ?TX"
    using hd top1_metric_topology_on_is_topology_on
    
    by blast
  have hSep: "\<forall>x y. x \<in> X \<and> y \<in> X \<and> x \<noteq> y \<longrightarrow>
    (\<exists>U V. neighborhood_of x X ?TX U \<and> neighborhood_of y X ?TX V \<and> U \<inter> V = {})"
  proof (intro allI impI)
    fix x y assume hxy: "x \<in> X \<and> y \<in> X \<and> x \<noteq> y"
    have hxX: "x \<in> X" and hyX: "y \<in> X" and hne: "x \<noteq> y"
      using hxy
      
      by presburger+
      have hdnonneg: "0 \<le> d x y" using hd hxX hyX unfolding top1_metric_on_def
        
        by blast
      have hdzero: "d x y = 0 \<longleftrightarrow> x = y" using hd hxX hyX unfolding top1_metric_on_def
        
        by blast
      have hdpos: "d x y > 0" using hdnonneg hdzero hne
        
        by simp
      define r where "r = d x y / 2"
      have hrpos: "r > 0" unfolding r_def using hdpos
        
        by simp
      let ?U = "top1_ball_on X d x r"
      let ?V = "top1_ball_on X d y r"
      have hUopen: "?U \<in> ?TX"
        using hd hxX hrpos top1_ball_open_in_metric_topology
        
        by fast
      have hxU: "x \<in> ?U"
        unfolding top1_ball_on_def
        using hxX hd hrpos unfolding top1_metric_on_def
        
        by fastforce
      have hVopen: "?V \<in> ?TX"
        using hd hyX hrpos top1_ball_open_in_metric_topology
        
        by fast
      have hyV: "y \<in> ?V"
        unfolding top1_ball_on_def
        using hyX hd hrpos unfolding top1_metric_on_def
        
        by fastforce
      have hUV_disj: "?U \<inter> ?V = {}"
      proof (rule ccontr)
        assume "\<not> ?U \<inter> ?V = {}"
        then obtain z where hzU: "z \<in> ?U" and hzV: "z \<in> ?V"
          
          by blast
        have hzX: "z \<in> X" and hdxz: "d x z < r" and hdyz: "d y z < r"
          using hzU hzV unfolding top1_ball_on_def
          
          by blast+
        have htri: "d x y \<le> d x z + d z y"
          using hd hxX hzX hyX unfolding top1_metric_on_def
          
          by blast
        have hdsym: "d z y = d y z"
          using hd hzX hyX unfolding top1_metric_on_def
          
          by blast
        have "d x y < r + r" using htri hdsym hdxz hdyz
          
          by simp
        then show False unfolding r_def using hdpos
          
          by auto
      qed
      have hUnbhd: "neighborhood_of x X ?TX ?U"
        unfolding neighborhood_of_def using hUopen hxU
        
        by argo
      have hVnbhd: "neighborhood_of y X ?TX ?V"
        unfolding neighborhood_of_def using hVopen hyV
        
        by argo
      show "\<exists>U V. neighborhood_of x X ?TX U \<and> neighborhood_of y X ?TX V \<and> U \<inter> V = {}"
        using hUnbhd hVnbhd hUV_disj
        
        by blast
  qed
  show ?thesis
    unfolding is_hausdorff_on_def using hTop hSep
    
    by blast
qed

text \<open>Metrizable spaces are regular: for x and closed C with x \<notin> C,
  use d(x,C)/2 balls to separate.\<close>
lemma metrizable_imp_regular:
  assumes hMet: "top1_metrizable_on X TX"
  shows "top1_regular_on X TX"
proof -
  obtain d where hd: "top1_metric_on X d" and hTX: "TX = top1_metric_topology_on X d"
    using hMet unfolding top1_metrizable_on_def
    
    by blast
  have hTop: "is_topology_on X TX"
    using hTX hd top1_metric_topology_on_is_topology_on
    
    by blast
  text \<open>Metric spaces are Hausdorff.\<close>
  have hHaus: "is_hausdorff_on X TX"
    unfolding hTX by (rule metric_topology_hausdorff[OF hd])
  have hT1: "top1_T1_on X TX"
    using hausdorff_imp_T1_on[OF hHaus]
    
    by satx
  text \<open>Regularity: separate x from closed C.\<close>
  show ?thesis
    unfolding top1_regular_on_def
  proof (intro conjI allI impI ballI)
    show "top1_T1_on X TX" by (rule hT1)
  next
    fix x C assume hxX: "x \<in> X" and hxC: "closedin_on X TX C \<and> x \<notin> C"
    have hCclosed: "closedin_on X TX C" and hxnotC: "x \<notin> C"
      using hxC
      by presburger+
    have hXmC_open: "X - C \<in> TX" using hCclosed unfolding closedin_on_def
      
      by presburger
    have hxXmC: "x \<in> X - C" using hxX hxnotC
      
      by blast
    obtain r where hrpos: "0 < r" and hball_sub: "top1_ball_on X d x r \<subseteq> X - C"
      using top1_metric_open_contains_ball[OF hd _ hxXmC] hXmC_open hTX
      
      by blast
    define r2 where "r2 = r / 2"
    have hr2pos: "0 < r2" unfolding r2_def using hrpos
      
      by simp
    let ?U = "top1_ball_on X d x r2"
    let ?V = "top1_nbhd_of_set X d C r2"
    have hU_open: "?U \<in> TX"
      using hd hxX hr2pos hTX
      
      using hTX hxX hd hr2pos top1_ball_open_in_metric_topology by fastforce
    have hxU: "x \<in> ?U"
    proof -
      have "d x x = 0" using hd hxX unfolding top1_metric_on_def
        
        by blast
      then show ?thesis unfolding top1_ball_on_def using hxX hr2pos
        
        by force
    qed
    have hCX: "C \<subseteq> X" using hCclosed unfolding closedin_on_def
      
      by presburger
    have hV_open: "?V \<in> TX"
      unfolding hTX using hd hCX hr2pos
      by (rule top1_nbhd_of_set_open)
    have hC_sub_V: "C \<subseteq> ?V"
    proof (rule subsetI)
      fix c assume hcC: "c \<in> C"
      have hcX: "c \<in> X" using hcC hCX
        
        by fast
      show "c \<in> ?V"
        using top1_nbhd_of_set_contains[OF hd hcC hCX hr2pos]
        
        by presburger
    qed
    have hUV_disj: "?U \<inter> ?V = {}"
    proof (rule ccontr)
      assume "\<not> ?U \<inter> ?V = {}"
      then obtain z where hzU: "z \<in> ?U" and hzV: "z \<in> ?V"
        
        by blast
      have hzX: "z \<in> X" using hzU unfolding top1_ball_on_def
        
        by blast
      have hdxz: "d x z < r2" using hzU unfolding top1_ball_on_def
        
        by blast
      obtain c where hcC: "c \<in> C" and hzball: "z \<in> top1_ball_on X d c r2"
        using hzV unfolding top1_nbhd_of_set_def
        
        by blast
      have hcX: "c \<in> X" using hcC hCX
        
        by blast
      have hdcz: "d c z < r2" using hzball unfolding top1_ball_on_def
        
        by blast
      have htri: "d x c \<le> d x z + d z c"
        using hd hxX hzX hcX unfolding top1_metric_on_def
        
        by blast
      have hdsym: "d z c = d c z"
        using hd hzX hcX unfolding top1_metric_on_def
        
        by blast
      have "d x c < r" using htri hdsym hdxz hdcz unfolding r2_def
        
        by linarith
      then have "c \<in> top1_ball_on X d x r"
        unfolding top1_ball_on_def using hcX
        
        by blast
      then have "c \<in> X - C" using hball_sub
        
        by auto
      then show False using hcC
        
        by fastforce
    qed
    have hUnbhd: "neighborhood_of x X TX ?U"
      unfolding neighborhood_of_def using hU_open hxU
      
      by argo
    show "\<exists>U V. neighborhood_of x X TX U \<and> V \<in> TX \<and> C \<subseteq> V \<and> U \<inter> V = {}"
      using hUnbhd hV_open hC_sub_V hUV_disj
      
      by blast
  qed
qed

text \<open>Scaling a continuous real-valued map by a constant preserves continuity.\<close>
lemma top1_continuous_scale_real:
  assumes hTopX: "is_topology_on X TX"
  assumes hf: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
  shows "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. c * f x)"
proof (cases "c = 0")
  case True
  then show ?thesis using Theorem_18_2(1)[OF hTopX order_topology_on_UNIV_is_topology_on order_topology_on_UNIV_is_topology_on]
    by auto
next
  case False
  text \<open>For c ≠ 0, the map λy. c*y is a homeomorphism on ℝ, hence continuous.
    Compose with f to get continuity of λx. c * f(x).\<close>
  have habs_m: "top1_metric_on (UNIV::real set) (\<lambda>x y. \<bar>x - y\<bar>)"
    unfolding top1_metric_on_def
    by fastforce
  have habs_eq: "top1_metric_topology_on (UNIV::real set) (\<lambda>x y. \<bar>x - y\<bar>) = order_topology_on_UNIV"
  proof -
    have "top1_bounded_metric (\<lambda>x y :: real. \<bar>x - y\<bar>) = top1_real_bounded_metric"
      unfolding top1_bounded_metric_def top1_real_bounded_metric_def
      by order
    then show ?thesis
      using Theorem_20_1[OF habs_m] order_topology_on_UNIV_eq_bounded_metric_topology_real
      by argo
  qed
  have hTopR_abs: "is_topology_on (UNIV::real set) (top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>))"
    using habs_m top1_metric_topology_on_is_topology_on
    by blast
  have hscale_abs: "\<forall>V\<in>top1_metric_topology_on (UNIV::real set) (\<lambda>x y. \<bar>x - y\<bar>).
    {x::real. c * x \<in> V} \<in> top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>)"
  proof (intro ballI)
    fix V :: "real set"
    assume hV: "V \<in> top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>)"
    let ?pre = "{x::real. c * x \<in> V}"
    show "?pre \<in> top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>)"
    proof (rule top1_open_of_local_subsets[OF hTopR_abs])
      show "?pre \<subseteq> (UNIV::real set)"
        by auto
      show "\<forall>x0\<in>?pre. \<exists>U\<in>top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>). x0 \<in> U \<and> U \<subseteq> ?pre"
      proof (intro ballI)
        fix x0 :: real assume hx0: "x0 \<in> ?pre"
        have hcx0V: "c * x0 \<in> V" using hx0
          by blast
        obtain \<epsilon> where hepos: "0 < \<epsilon>" and hball: "top1_ball_on UNIV (\<lambda>x y. \<bar>x - y\<bar>) (c * x0) \<epsilon> \<subseteq> V"
          using top1_metric_open_contains_ball[OF habs_m hV hcx0V]
          by blast
        define \<delta> where "\<delta> = \<epsilon> / \<bar>c\<bar>"
        have hdpos: "0 < \<delta>" unfolding \<delta>_def using hepos False
          by auto
        let ?U = "top1_ball_on UNIV (\<lambda>x y. \<bar>x - y\<bar>) x0 \<delta>"
        have hU_open: "?U \<in> top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>)"
          using top1_ball_open_in_metric_topology[OF habs_m _ hdpos]
          by blast
        have hx0U: "x0 \<in> ?U" unfolding top1_ball_on_def using hdpos
          by force
        have hU_sub: "?U \<subseteq> ?pre"
        proof (rule subsetI)
          fix y :: real assume hy: "y \<in> ?U"
          have "\<bar>x0 - y\<bar> < \<delta>" using hy unfolding top1_ball_on_def
            by fast
          have "\<bar>c * x0 - c * y\<bar> = \<bar>c\<bar> * \<bar>x0 - y\<bar>"
            by (metis abs_mult right_diff_distrib)
          also have "... < \<bar>c\<bar> * \<delta>" using \<open>\<bar>x0 - y\<bar> < \<delta>\<close> False
            by force
          also have "... = \<epsilon>" unfolding \<delta>_def using False
            by simp
          finally have "c * y \<in> top1_ball_on UNIV (\<lambda>x y. \<bar>x - y\<bar>) (c * x0) \<epsilon>"
            unfolding top1_ball_on_def
            by blast
          then show "y \<in> ?pre" using hball
            by blast
        qed
        show "\<exists>U\<in>top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>). x0 \<in> U \<and> U \<subseteq> ?pre"
          using hU_open hx0U hU_sub
          by blast
      qed
    qed
  qed
  have hscale_cont: "top1_continuous_map_on (UNIV::real set) order_topology_on_UNIV (UNIV::real set) order_topology_on_UNIV (\<lambda>y. c * y)"
    unfolding top1_continuous_map_on_def using hscale_abs habs_eq
    by simp
  have hcomp: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV ((\<lambda>y. c * y) \<circ> f)"
    using Theorem_18_2(3)[OF hTopX order_topology_on_UNIV_is_topology_on order_topology_on_UNIV_is_topology_on] hf hscale_cont
    by blast
  have "(\<lambda>x. c * f x) = (\<lambda>y. c * y) \<circ> f"
    by auto
  then show ?thesis using hcomp
    by argo
qed

text \<open>Theorem 21.6 (Uniform limit theorem): uniform limit of continuous functions is continuous.
  Proof: ε/3 argument — given V open containing f(x₀), find ε-ball in V, pick N for ε/3 uniform
  convergence, use continuity of f_N for another ε/3, then triangle inequality.\<close>
lemma uniform_limit_continuous:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hcont: "\<forall>n::nat. top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) (fseq n)"
  assumes hunif: "\<forall>\<epsilon>>0. \<exists>N::nat. \<forall>n\<ge>N. \<forall>x\<in>X. d (fseq n x) (f x) < \<epsilon>"
  assumes hfX: "\<forall>x\<in>X. f x \<in> Y"
  shows "top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) f"
proof -
  let ?TY = "top1_metric_topology_on Y d"
  have hpre: "\<forall>V\<in>?TY. {x \<in> X. f x \<in> V} \<in> TX"
  proof (intro ballI)
    fix V assume hV: "V \<in> ?TY"
    let ?A = "{x \<in> X. f x \<in> V}"
    have hAX: "?A \<subseteq> X"
      by blast
    have "\<forall>x0\<in>?A. \<exists>U\<in>TX. x0 \<in> U \<and> U \<subseteq> ?A"
    proof (intro ballI)
      fix x0 assume hx0: "x0 \<in> ?A"
      have hx0X: "x0 \<in> X" using hx0
        by simp
      have hfx0V: "f x0 \<in> V" using hx0
        by blast
      have hfx0Y: "f x0 \<in> Y" using hfX hx0X
        by blast
      obtain \<epsilon> where hepos: "0 < \<epsilon>" and hball_V: "top1_ball_on Y d (f x0) \<epsilon> \<subseteq> V"
        using top1_metric_open_contains_ball[OF hd hV hfx0V]
        by blast
      define e3 where "e3 = \<epsilon> / 3"
      have he3pos: "0 < e3" unfolding e3_def using hepos
        by simp
      obtain N :: nat where hN: "\<forall>n\<ge>N. \<forall>x\<in>X. d (fseq n x) (f x) < e3"
        using hunif he3pos
        by blast
      have hcontN: "top1_continuous_map_on X TX Y ?TY (fseq N)" using hcont
        by auto
      have hfNmap: "\<forall>x\<in>X. fseq N x \<in> Y"
        using hcontN unfolding top1_continuous_map_on_def
        by satx
      have hfNx0Y: "fseq N x0 \<in> Y" using hfNmap hx0X
        by blast
      have hballN: "top1_ball_on Y d (fseq N x0) e3 \<in> ?TY"
        using top1_ball_open_in_metric_topology[OF hd hfNx0Y he3pos]
        by satx
      have hpreN: "{x \<in> X. fseq N x \<in> top1_ball_on Y d (fseq N x0) e3} \<in> TX"
        using hcontN hballN unfolding top1_continuous_map_on_def
        by blast
      let ?U = "{x \<in> X. fseq N x \<in> top1_ball_on Y d (fseq N x0) e3}"
      have hx0U: "x0 \<in> ?U"
      proof -
        have "d (fseq N x0) (fseq N x0) = 0"
          using hd hfNx0Y unfolding top1_metric_on_def
          by blast
        then show ?thesis unfolding top1_ball_on_def using hfNx0Y he3pos hx0X
          by force
      qed
      have hNleN: "\<forall>x\<in>X. d (fseq N x) (f x) < e3" using hN
        by auto
      have hU_sub: "?U \<subseteq> ?A"
      proof (rule subsetI)
        fix y assume hyU: "y \<in> ?U"
        have hyX: "y \<in> X" using hyU
          by blast
        have hfNy_ball: "fseq N y \<in> top1_ball_on Y d (fseq N x0) e3" using hyU
          by blast
        have hfyY: "f y \<in> Y" using hfX hyX
          by blast
        have hfNyY: "fseq N y \<in> Y" using hfNmap hyX
          by auto
        have hd1: "d (fseq N x0) (fseq N y) < e3"
          using hfNy_ball unfolding top1_ball_on_def
          by blast
        have hd2: "d (fseq N y) (f y) < e3" using hNleN hyX
          by auto
        have hd3: "d (fseq N x0) (f x0) < e3" using hNleN hx0X
          by simp
        have htri1: "d (f y) (f x0) \<le> d (f y) (fseq N y) + d (fseq N y) (f x0)"
          using hd hfyY hfNyY hfx0Y unfolding top1_metric_on_def
          by blast
        have htri2: "d (fseq N y) (f x0) \<le> d (fseq N y) (fseq N x0) + d (fseq N x0) (f x0)"
          using hd hfNyY hfNx0Y hfx0Y unfolding top1_metric_on_def
          by blast
        have hsym1: "d (f y) (fseq N y) = d (fseq N y) (f y)"
          using hd hfyY hfNyY unfolding top1_metric_on_def
          by blast
        have hsym2: "d (fseq N y) (fseq N x0) = d (fseq N x0) (fseq N y)"
          using hd hfNyY hfNx0Y unfolding top1_metric_on_def
          by blast
        have "d (f y) (f x0) < e3 + e3 + e3"
          using htri1 htri2 hsym1 hsym2 hd1 hd2 hd3
          by argo
        then have hd_fy_fx0: "d (f y) (f x0) < \<epsilon>" unfolding e3_def
          by argo
        have "d (f x0) (f y) = d (f y) (f x0)"
          using hd hfx0Y hfyY unfolding top1_metric_on_def
          by blast
        then have "d (f x0) (f y) < \<epsilon>" using hd_fy_fx0
          by presburger
        then have "f y \<in> top1_ball_on Y d (f x0) \<epsilon>"
          unfolding top1_ball_on_def using hfyY
          by blast
        then have "f y \<in> V" using hball_V
          by blast
        then show "y \<in> ?A" using hyX
          by blast
      qed
      show "\<exists>U\<in>TX. x0 \<in> U \<and> U \<subseteq> ?A"
        using hpreN hx0U hU_sub
        by meson
    qed
    then show "?A \<in> TX"
      using top1_open_of_local_subsets[OF hTopX hAX]
      by argo
  qed
  show ?thesis unfolding top1_continuous_map_on_def using hfX hpre
    by satx
qed

(** from \S40 Lemma 40.2 [top1.tex:5724] **)
lemma Lemma_40_2:
  assumes hN: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hG: "top1_G_delta_on X TX A"
  shows "\<exists>f::'a \<Rightarrow> real.
    top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f
    \<and> (\<forall>x\<in>A. f x = 0) \<and> (\<forall>x\<in>X - A. 0 < f x)"
proof -
  have hTop: "is_topology_on X TX"
    using hN unfolding top1_normal_on_def top1_T1_on_def
    by presburger
  have hAX: "A \<subseteq> X" using hA unfolding closedin_on_def
    by presburger
  text \<open>A = ∩(U n) with each U n open.\<close>
  obtain U :: "nat \<Rightarrow> 'a set" where hU_open: "\<forall>n. U n \<in> TX" and hA_eq: "A = (\<Inter>n. U n)"
    using hG unfolding top1_G_delta_on_def
    by blast
  text \<open>X - U n is closed and disjoint from A.\<close>
  have hXmU_closed: "\<forall>n. closedin_on X TX (X - U n)"
  proof (intro allI)
    fix n
    have "X - U n \<subseteq> X"
      by blast
    moreover have "X - (X - U n) = X \<inter> U n"
      by fastforce
    moreover have "X \<inter> U n \<in> TX"
      using topology_inter2[OF hTop _ hU_open[THEN spec, of n]]
      using hTop is_topology_on_def by blast
    ultimately show "closedin_on X TX (X - U n)" unfolding closedin_on_def
      by argo
  qed
  have hA_disj_XmU: "\<forall>n. A \<inter> (X - U n) = {}"
    using hA_eq
    by blast
  text \<open>Urysohn gives f_n: X → [0,1] with f_n|A = 0, f_n|(X-U_n) = 1.\<close>
  have "\<forall>n. \<exists>fn. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) fn
    \<and> (\<forall>x\<in>A. fn x = 0) \<and> (\<forall>x\<in>X - U n. fn x = 1)"
  proof (intro allI)
    fix n
    have "A \<inter> (X - U n) = {}" using hA_disj_XmU
      by simp
    then show "\<exists>fn. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) fn
      \<and> (\<forall>x\<in>A. fn x = 0) \<and> (\<forall>x\<in>X - U n. fn x = 1)"
      using Theorem_33_1[OF hN hA hXmU_closed[THEN spec, of n] _ zero_le_one]
      by argo
  qed
  then obtain fn where hfn_cont: "\<forall>n. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (fn n)"
    and hfn_A: "\<forall>n. \<forall>x\<in>A. fn n x = 0"
    and hfn_XmU: "\<forall>n. \<forall>x\<in>X - U n. fn n x = 1"
    by metis
  text \<open>fn values in [0,1].\<close>
  have hfn_range: "\<forall>n. \<forall>x\<in>X. 0 \<le> fn n x \<and> fn n x \<le> 1"
    using hfn_cont unfolding top1_continuous_map_on_def top1_closed_interval_def
    by blast
  text \<open>Define f(x) = Σ fn(n,x) / 2^(n+1). Series converges absolutely.\<close>
  define f where "f x = (\<Sum>n. fn n x / 2^(Suc n))" for x
  text \<open>Summability: each |fn(n,x)/2^(n+1)| ≤ 1/2^(n+1), geometric series converges.\<close>
  have hsummable: "\<forall>x\<in>X. summable (\<lambda>n. fn n x / 2^(Suc n))"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    show "summable (\<lambda>n. fn n x / 2 ^ Suc n)"
    proof (rule summable_comparison_test)
      show "\<exists>N. \<forall>n\<ge>N. norm (fn n x / 2 ^ Suc n) \<le> (1/2) ^ Suc n"
      proof (intro exI allI impI)
        fix n :: nat assume "0 \<le> n"
        have "fn n x \<le> 1" using hfn_range hxX
          by blast
        moreover have "0 \<le> fn n x" using hfn_range hxX
          by blast
        ultimately have "fn n x / 2 ^ Suc n \<le> 1 / 2 ^ Suc n"
          by (simp add: frac_le)
        moreover have "0 \<le> fn n x / 2 ^ Suc n"
          using \<open>0 \<le> fn n x\<close> by fastforce
        ultimately show "norm (fn n x / 2 ^ Suc n) \<le> (1/2) ^ Suc n"
          using \<open>fn n x / 2 ^ Suc n \<le> 1 / 2 ^ Suc n\<close>
          by (simp add: power_divide abs_of_nonneg real_norm_def)
      qed
      show "summable (\<lambda>n. (1/2::real) ^ Suc n)"
        by simp
    qed
  qed
  text \<open>f = 0 on A.\<close>
  have hf_A: "\<forall>x\<in>A. f x = 0"
  proof (intro ballI)
    fix x assume hxA: "x \<in> A"
    have "\<forall>n. fn n x = 0" using hfn_A hxA
      by blast
    then have "(\<lambda>n. fn n x / 2^(Suc n)) = (\<lambda>n. 0)"
      by simp
    then show "f x = 0" unfolding f_def
      by simp
  qed
  text \<open>f > 0 on X - A.\<close>
  have hf_pos: "\<forall>x\<in>X - A. 0 < f x"
  proof (intro ballI)
    fix x assume hx: "x \<in> X - A"
    have hxX: "x \<in> X" using hx
      by blast
    have hxnA: "x \<notin> A" using hx
      by fast
    text \<open>x ∉ ∩U_n, so x ∉ U_k for some k.\<close>
    obtain k where hxnUk: "x \<notin> U k"
      using hxnA hA_eq
      by blast
    have hxXmUk: "x \<in> X - U k" using hxX hxnUk
      by blast
    have hfnk1: "fn k x = 1" using hfn_XmU hxXmUk
      by blast
    text \<open>f x ≥ fn k x / 2^(k+1) = 1/2^(k+1) > 0.\<close>
    have hterm_pos: "0 < fn k x / 2 ^ Suc k" using hfnk1
      by simp
    have hfn_nonneg: "\<forall>n. 0 \<le> fn n x / 2 ^ Suc n"
      using hfn_range hxX
      by force
    have hsum_ge_term: "fn k x / 2 ^ Suc k \<le> f x"
    proof -
      have "sum (\<lambda>n. fn n x / 2 ^ Suc n) {k} \<le> suminf (\<lambda>n. fn n x / 2 ^ Suc n)"
        using sum_le_suminf[of "\<lambda>n. fn n x / 2 ^ Suc n" "{k}"] hsummable hxX hfn_nonneg
        by blast
      then show ?thesis unfolding f_def
        by auto
    qed
    show "0 < f x" using hterm_pos hsum_ge_term
      by linarith
  qed
  text \<open>f is continuous (uniform limit of partial sums).\<close>
  text \<open>f(x) ∈ [0,1] for all x ∈ X.\<close>
  have hf_range: "\<forall>x\<in>X. 0 \<le> f x \<and> f x \<le> 1"
  proof (intro ballI conjI)
    fix x assume hxX: "x \<in> X"
    show "0 \<le> f x" unfolding f_def
      using suminf_nonneg[of "\<lambda>n. fn n x / 2^(Suc n)"] hsummable hxX hfn_range
      by fastforce
    show "f x \<le> 1" unfolding f_def
    proof -
      have hle: "\<And>n. fn n x / 2^(Suc n) \<le> (1/2::real)^(Suc n)"
      proof -
        fix n
        have "fn n x \<le> 1" using hfn_range hxX
          by blast
        then show "fn n x / 2 ^ Suc n \<le> (1 / 2) ^ Suc n"
          by (simp add: power_divide divide_right_mono)
      qed
      have hgeom_sum: "summable (\<lambda>n. (1/2::real)^(Suc n))"
        by fastforce
      have hle_suminf: "suminf (\<lambda>n. fn n x / 2^(Suc n)) \<le> suminf (\<lambda>n. (1/2::real)^(Suc n))"
        using suminf_le hle hsummable hxX hgeom_sum
        by meson
      have hgeom_le1: "suminf (\<lambda>n. (1/2::real)^(Suc n)) \<le> 1"
        using hgeom_sum power_half_series sums_le by blast
      show "(\<Sum>n. fn n x / 2 ^ Suc n) \<le> 1" using hle_suminf hgeom_le1
        by argo
    qed
  qed
  text \<open>Partial sums converge uniformly: |f(x) - S_N(x)| ≤ 1/2^N.\<close>
  have hunif_partial: "\<forall>\<epsilon>>0. \<exists>N::nat. \<forall>n\<ge>N. \<forall>x\<in>X. \<bar>(\<Sum>i<n. fn i x / 2^(Suc i)) - f x\<bar> < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real assume hepos: "0 < \<epsilon>"
    text \<open>Pick N with 1/2^N < ε.\<close>
    obtain N :: nat where hN: "(1/2::real)^N < \<epsilon>"
      using real_arch_pow_inv[of \<epsilon> "1/2"] hepos
      by auto
    show "\<exists>N::nat. \<forall>n\<ge>N. \<forall>x\<in>X. \<bar>(\<Sum>i<n. fn i x / 2 ^ Suc i) - f x\<bar> < \<epsilon>"
    proof (intro exI allI impI ballI)
      fix n :: nat and x assume hnN: "N \<le> n" and hxX: "x \<in> X"
      text \<open>f(x) - S_n(x) = tail = ∑_{i≥n} fn(i,x)/2^(i+1).\<close>
      have hfx_split: "f x = (\<Sum>i. fn (i + n) x / 2 ^ Suc (i + n)) + (\<Sum>i<n. fn i x / 2 ^ Suc i)"
        unfolding f_def using suminf_split_initial_segment[of "\<lambda>i. fn i x / 2^Suc i" n]
          hsummable hxX
        by blast
      have hdiff: "f x - (\<Sum>i<n. fn i x / 2 ^ Suc i) = (\<Sum>i. fn (i + n) x / 2 ^ Suc (i + n))"
        using hfx_split
        by argo
      text \<open>Tail ≥ 0 (all terms non-negative).\<close>
      have hshift_summ: "summable (\<lambda>i. fn (i + n) x / 2 ^ Suc (i + n))"
        using summable_iff_shift[THEN iffD2, of "\<lambda>i. fn i x / 2 ^ Suc i" n]
          hsummable hxX
        by blast
      have hshift_nn: "\<And>i. 0 \<le> fn (i + n) x / 2 ^ Suc (i + n)"
        using hfn_range hxX
        by auto
      have htail_nn: "0 \<le> (\<Sum>i. fn (i + n) x / 2 ^ Suc (i + n))"
        using suminf_nonneg[OF hshift_summ hshift_nn]
        by presburger
      text \<open>|S_n(x) - f(x)| = f(x) - S_n(x) = tail.\<close>
      have habs: "\<bar>(\<Sum>i<n. fn i x / 2 ^ Suc i) - f x\<bar> = f x - (\<Sum>i<n. fn i x / 2 ^ Suc i)"
        using hdiff htail_nn
        by simp
      text \<open>Tail ≤ ∑_{i≥n} 1/2^(i+1) = (1/2)^n ≤ (1/2)^N < ε.\<close>
      have htail_le: "(\<Sum>i. fn (i + n) x / 2 ^ Suc (i + n)) \<le> (\<Sum>i. (1/2::real) ^ Suc (i + n))"
      proof (rule suminf_le)
        fix i show "fn (i + n) x / 2 ^ Suc (i + n) \<le> (1/2::real) ^ Suc (i + n)"
          using hfn_range hxX by (simp add: power_divide divide_right_mono)
      next
        show "summable (\<lambda>i. fn (i + n) x / 2 ^ Suc (i + n))" by (rule hshift_summ)
      next
        show "summable (\<lambda>i. (1 / 2 :: real) ^ Suc (i + n))"
          using summable_geometric[of "1/2::real"]
          by force
      qed
      have hgeom_tail: "(\<Sum>i. (1/2::real) ^ Suc (i + n)) = (1/2::real)^n"
      proof -
        have "(\<lambda>i. (1/2::real) ^ Suc (i + n)) = (\<lambda>i. (1/2)^(Suc n) * (1/2)^i)"
          by (simp add: power_add algebra_simps)
        then have "(\<Sum>i. (1/2::real) ^ Suc (i + n)) = (1/2)^(Suc n) * (\<Sum>i. (1/2::real)^i)"
          using suminf_mult[of "\<lambda>i. (1/2::real)^i" "(1/2)^(Suc n)"]
          by simp
        also have "(1/2::real)^(Suc n) * (\<Sum>i. (1/2::real)^i) = (1/2)^(Suc n) * (1 / (1 - 1/2))"
          using suminf_geometric[of "1/2::real"]
          by auto
        also have "(1/2::real)^(Suc n) * (1 / (1 - 1/2)) = (1/2)^n"
          by simp
        finally show ?thesis
          by presburger
      qed
      have hpow_mono: "((1/2::real)^n) \<le> (1/2)^N" using hnN
        by auto
      show "\<bar>(\<Sum>i<n. fn i x / 2 ^ Suc i) - f x\<bar> < \<epsilon>"
        using habs hdiff htail_le hgeom_tail hpow_mono hN
        by argo
    qed
  qed
  text \<open>Each partial sum is continuous.\<close>
  text \<open>Each fn i maps into ℝ continuously.\<close>
  have hfn_cont_R: "\<forall>i. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (fn i)"
  proof (intro allI)
    fix i
    have hfn_i: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (fn i)"
      using hfn_cont
      by blast
    have hI_sub: "top1_closed_interval (0::real) 1 \<subseteq> UNIV"
      by simp
    have hI_eq: "top1_closed_interval_topology 0 1 = subspace_topology UNIV order_topology_on_UNIV (top1_closed_interval 0 1)"
      unfolding top1_closed_interval_topology_def
      by presburger
    show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (fn i)"
      by (metis Theorem_18_2(6) hI_eq hI_sub hfn_i hTop
        order_topology_on_UNIV_is_topology_on subspace_topology_is_topology_on)
  qed
  text \<open>Each scaled function fn i x / 2^(Suc i) is continuous into ℝ.\<close>
  have hfn_scaled_cont_R: "\<forall>i. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. fn i x / 2^(Suc i))"
  proof (intro allI)
    fix i
    have "(\<lambda>x. fn i x / 2 ^ Suc i) = (\<lambda>x. (1 / 2^Suc i) * fn i x)"
      by auto
    then show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. fn i x / 2 ^ Suc i)"
      using top1_continuous_scale_real[OF hTop hfn_cont_R[THEN spec, of i]]
      by presburger
  qed
  text \<open>Partial sum continuous into ℝ.\<close>
  have hpartial_cont_R: "\<forall>n::nat. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. \<Sum>i<n. fn i x / 2^(Suc i))"
    using top1_continuous_sum_lessThan_real[OF hTop] hfn_scaled_cont_R
    by presburger
  text \<open>Partial sum range in [0,1], so continuous into [0,1].\<close>
  have hpartial_range: "\<forall>n::nat. \<forall>x\<in>X. (\<Sum>i<n. fn i x / 2^(Suc i)) \<in> top1_closed_interval 0 1"
  proof (intro allI ballI)
    fix n :: nat and x assume hxX: "x \<in> X"
    have hnn: "0 \<le> (\<Sum>i<n. fn i x / 2 ^ Suc i)"
      using hfn_range hxX
      by (simp add: sum_nonneg)
    have hle_sum: "(\<Sum>i<n. fn i x / 2 ^ Suc i) \<le> suminf (\<lambda>i. fn i x / 2 ^ Suc i)"
    proof (rule sum_le_suminf)
      show "summable (\<lambda>i. fn i x / 2 ^ Suc i)" using hsummable hxX
        by blast
      show "finite {..<n}"
        by simp
      fix m assume "m \<in> - {..<n}"
      show "0 \<le> fn m x / 2 ^ Suc m" using hfn_range hxX
        by simp
    qed
    have hle1: "(\<Sum>i<n. fn i x / 2 ^ Suc i) \<le> 1"
      using hle_sum hf_range hxX unfolding f_def
      using order_trans by blast
    show "(\<Sum>i<n. fn i x / 2 ^ Suc i) \<in> top1_closed_interval 0 1"
      unfolding top1_closed_interval_def using hnn hle1
      by fast
  qed
  have hpartial_cont: "\<forall>n::nat. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<lambda>x. \<Sum>i<n. fn i x / 2^(Suc i))"
  proof (intro allI)
    fix n :: nat
    have hcont_R: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>x. \<Sum>i<n. fn i x / 2 ^ Suc i)"
      using hpartial_cont_R
      by blast
    have hI_sub: "top1_closed_interval (0::real) 1 \<subseteq> UNIV"
      by auto
    have hrange_sub: "(\<lambda>x. \<Sum>i<n. fn i x / 2 ^ Suc i) ` X \<subseteq> top1_closed_interval 0 1"
      using hpartial_range
      by blast
    show "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<lambda>x. \<Sum>i<n. fn i x / 2 ^ Suc i)"
      unfolding top1_closed_interval_topology_def
      using Theorem_18_2(5)[OF hTop order_topology_on_UNIV_is_topology_on order_topology_on_UNIV_is_topology_on]
        hcont_R hI_sub hrange_sub
      by blast
  qed
  have habs_metric: "top1_metric_on (UNIV::real set) (\<lambda>x y. \<bar>x - y\<bar>)"
    unfolding top1_metric_on_def
    by auto
  have habs_eq_order: "top1_metric_topology_on (UNIV::real set) (\<lambda>x y. \<bar>x - y\<bar>) = order_topology_on_UNIV"
  proof -
    have hbdd_eq: "top1_bounded_metric (\<lambda>x y :: real. \<bar>x - y\<bar>) = top1_real_bounded_metric"
      unfolding top1_bounded_metric_def top1_real_bounded_metric_def
      by argo
    have "top1_metric_topology_on (UNIV::real set) (\<lambda>x y. \<bar>x - y\<bar>)
        = top1_metric_topology_on UNIV (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>))"
      using Theorem_20_1[OF habs_metric]
      by argo
    also have "... = top1_metric_topology_on UNIV top1_real_bounded_metric"
      using hbdd_eq
      by argo
    also have "... = order_topology_on_UNIV"
      using order_topology_on_UNIV_eq_bounded_metric_topology_real
      by argo
    finally show ?thesis
      by argo
  qed
  have hpartial_cont_abs: "\<forall>n::nat. top1_continuous_map_on X TX (UNIV::real set)
    (top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>)) (\<lambda>x. \<Sum>i<n. fn i x / 2^(Suc i))"
    using hpartial_cont_R habs_eq_order
    by presburger
  have hunif_abs: "\<forall>\<epsilon>>0. \<exists>N::nat. \<forall>n\<ge>N. \<forall>x\<in>X. (\<lambda>x y. \<bar>x - y\<bar>) ((\<lambda>x. \<Sum>i<n. fn i x / 2 ^ Suc i) x) (f x) < \<epsilon>"
    using hunif_partial
    by argo
  have hf_cont_abs: "top1_continuous_map_on X TX (UNIV::real set)
    (top1_metric_topology_on UNIV (\<lambda>x y. \<bar>x - y\<bar>)) f"
    using uniform_limit_continuous[OF hTop habs_metric hpartial_cont_abs hunif_abs]
    by fast
  have hf_cont_order: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV f"
    using hf_cont_abs habs_eq_order
    by argo
  have hf_range_img: "f ` X \<subseteq> top1_closed_interval 0 1"
    using hf_range unfolding top1_closed_interval_def
    by blast
  have hf_cont: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f"
    unfolding top1_closed_interval_topology_def
    using Theorem_18_2(5)[OF hTop order_topology_on_UNIV_is_topology_on order_topology_on_UNIV_is_topology_on]
      hf_cont_order hf_range_img
    by blast
  show ?thesis using hf_cont hf_A hf_pos
    by blast
qed

(** from \S40 Theorem 40.3 (Nagata-Smirnov metrization theorem) [top1.tex:5727] **)
theorem Theorem_40_3:
  shows "top1_metrizable_on X TX \<longleftrightarrow>
    (top1_regular_on X TX \<and> (\<exists>\<B>. basis_for X \<B> TX \<and> top1_sigma_locally_finite_family_on X TX \<B>))"
proof (intro iffI)
  assume hMet: "top1_metrizable_on X TX"
  have hReg: "top1_regular_on X TX"
    by (simp add: hMet metrizable_imp_regular)
  have "\<exists>\<B>. basis_for X \<B> TX \<and> top1_sigma_locally_finite_family_on X TX \<B>"
  proof -
    obtain d where hd: "top1_metric_on X d" and hTXeq: "TX = top1_metric_topology_on X d"
      using hMet unfolding top1_metrizable_on_def
      
      by blast
    text \<open>For each m, cover X by balls of radius 1/(Suc m).\<close>
    define Am where "Am m = top1_ball_on X d ` X" for m :: nat
    text \<open>Actually need radius 1/(Suc m) balls. Redefine.\<close>
    define Bm_cover where "Bm_cover m = {top1_ball_on X d x (1 / real (Suc m)) | x. x \<in> X}" for m :: nat
    have hBm_cov: "\<forall>m. top1_open_covering_on X TX (Bm_cover m)"
      unfolding top1_open_covering_on_def
    proof (intro allI conjI)
      fix m
      show "Bm_cover m \<subseteq> TX"
        unfolding Bm_cover_def hTXeq using hd top1_ball_open_in_metric_topology
        
        by fastforce
      show "X \<subseteq> \<Union>(Bm_cover m)"
      proof (rule subsetI)
        fix x assume hxX: "x \<in> X"
        have "x \<in> top1_ball_on X d x (1 / real (Suc m))"
          unfolding top1_ball_on_def using hxX hd unfolding top1_metric_on_def
          
          by fastforce
        then show "x \<in> \<Union>(Bm_cover m)" unfolding Bm_cover_def using hxX
          
          by blast
      qed
    qed
    text \<open>Apply Lemma 39.2 to each cover.\<close>
    have hBm_ref: "\<forall>m. \<exists>\<E>m. top1_open_covering_on X TX \<E>m \<and> top1_refines \<E>m (Bm_cover m)
            \<and> top1_sigma_locally_finite_family_on X TX \<E>m"
      using Lemma_39_2[OF hMet] hBm_cov
      
      by presburger
    obtain Bm where hBm: "\<forall>m. top1_open_covering_on X TX (Bm m) \<and> top1_refines (Bm m) (Bm_cover m)
            \<and> top1_sigma_locally_finite_family_on X TX (Bm m)"
      using choice[OF hBm_ref]
      
      by blast
    text \<open>B = ∪_m Bm is sigma-LF.\<close>
    define B where "B = (\<Union>m. Bm m)"
    have hTop_ctx: "is_topology_on X TX"
      using hd hTXeq top1_metric_topology_on_is_topology_on
      by blast
    have hBm_slf: "\<forall>m. top1_sigma_locally_finite_family_on X TX (Bm m)"
      using hBm
      by blast
    have hB_slf: "top1_sigma_locally_finite_family_on X TX B"
      unfolding B_def using countable_union_sigma_lf[OF hTop_ctx hBm_slf]
      by blast
    have hB_open: "B \<subseteq> TX"
      using hBm unfolding top1_open_covering_on_def B_def
      
      by fast
    text \<open>B is a basis for TX.\<close>
    text \<open>Helper: metric topology elements are subsets of X.\<close>
    have hTX_sub: "\<forall>U\<in>TX. U \<subseteq> X"
    proof (intro ballI)
      fix U assume "U \<in> TX"
      then have "U \<in> topology_generated_by_basis X (top1_metric_basis_on X d)"
        unfolding hTXeq top1_metric_topology_on_def
        by presburger
      then show "U \<subseteq> X" unfolding topology_generated_by_basis_def
        by fast
    qed
    text \<open>Helper: for U open and x \<in> U, find b \<in> B with x \<in> b \<subseteq> U.\<close>
    have hB_refine: "\<forall>U\<in>TX. \<forall>x\<in>U. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U"
    proof (intro ballI)
      fix U x assume hUTX: "U \<in> TX" and hxU: "x \<in> U"
      have hxX: "x \<in> X" using hxU hTX_sub hUTX
        by blast
      obtain e where hepos: "0 < e" and hball_sub: "top1_ball_on X d x e \<subseteq> U"
        using top1_metric_open_contains_ball[OF hd _ hxU] hUTX hTXeq
        by blast
      text \<open>Pick m such that 2/(Suc m) < e.\<close>
      obtain m :: nat where hm: "2 / real (Suc m) < e"
      proof -
        obtain k :: nat where hk: "2 / e < real k"
          using reals_Archimedean2
          by blast
        have hk_pos: "0 < k" using hk hepos of_nat_0_less_iff
          by fastforce
        have "2 / real (Suc (k - 1)) < e"
        proof -
          have "real (Suc (k - 1)) = real k" using hk_pos
            by simp
          then have "2 / real (Suc (k - 1)) = 2 / real k"
            by presburger
          also have "... < e"
          proof -
            have "2 / e < real k" using hk
              by presburger
            then have "2 < real k * e" using hepos
              by (simp add: divide_less_eq)
            then show "2 / real k < e" using hk_pos
              by (simp add: divide_less_eq mult.commute)
          qed
          finally show ?thesis
            by presburger
        qed
        then show ?thesis using that
          by blast
      qed
      text \<open>Bm m covers X, so x is in some element of Bm m.\<close>
      have hBm_cov_m: "X \<subseteq> \<Union>(Bm m)" using hBm
        unfolding top1_open_covering_on_def
        by presburger
      obtain b where hb_Bm: "b \<in> Bm m" and hxb: "x \<in> b"
        using hBm_cov_m hxX
        by auto
      text \<open>b refines Bm_cover m, so b \<subseteq> ball(y, 1/(Suc m)) for some y.\<close>
      have hBm_ref_m: "top1_refines (Bm m) (Bm_cover m)" using hBm
        by presburger
      obtain a where ha_cov: "a \<in> Bm_cover m" and hb_sub_a: "b \<subseteq> a"
        using hBm_ref_m hb_Bm unfolding top1_refines_def
        by blast
      obtain y where hyX: "y \<in> X" and ha_eq: "a = top1_ball_on X d y (1 / real (Suc m))"
        using ha_cov unfolding Bm_cover_def
        by blast
      text \<open>For z \<in> b: d(z,x) \<le> d(z,y) + d(y,x) < 1/(Suc m) + 1/(Suc m) = 2/(Suc m) < e.\<close>
      have hb_sub_ball: "b \<subseteq> top1_ball_on X d x e"
      proof (rule subsetI)
        fix z assume hzb: "z \<in> b"
        have hzX: "z \<in> X" using hzb hb_sub_a ha_eq unfolding top1_ball_on_def
          by auto
        have hza: "z \<in> a" using hzb hb_sub_a
          by fast
        have hdyz: "d y z < 1 / real (Suc m)"
          using hza ha_eq unfolding top1_ball_on_def
          by blast
        have hdsym_yz: "d z y = d y z"
          using hd hzX hyX unfolding top1_metric_on_def
          by blast
        have hdzy: "d z y < 1 / real (Suc m)" using hdyz hdsym_yz
          by presburger
        have hxa: "x \<in> a" using hxb hb_sub_a
          by fastforce
        have hdyx: "d y x < 1 / real (Suc m)"
          using hxa ha_eq unfolding top1_ball_on_def
          by blast
        have hdsym_yx: "d x y = d y x"
          using hd hxX hyX unfolding top1_metric_on_def
          by blast
        have hdxy: "d x y < 1 / real (Suc m)" using hdyx hdsym_yx
          by presburger
        have htri: "d z x \<le> d z y + d y x"
          using hd hzX hyX hxX unfolding top1_metric_on_def
          by blast
        have hdsym: "d y x = d x y"
          using hd hyX hxX unfolding top1_metric_on_def
          by blast
        have "d z x < 2 / real (Suc m)" using htri hdsym hdzy hdxy
          by argo
        then have "d z x < e" using hm
          by auto
        have "z \<in> X \<and> d x z < e" using hzX \<open>d z x < e\<close> hd hzX hxX unfolding top1_metric_on_def
          by simp
        then show "z \<in> top1_ball_on X d x e" unfolding top1_ball_on_def
          by blast
      qed
      have "b \<subseteq> U" using hb_sub_ball hball_sub
        by blast
      have "b \<in> B" using hb_Bm unfolding B_def
        by blast
      then show "\<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U" using hxb \<open>b \<subseteq> U\<close>
        by blast
    qed
    text \<open>Now prove basis_for.\<close>
    have hB_basis: "basis_for X B TX"
      unfolding basis_for_def
    proof (intro conjI)
      show "is_basis_on X B"
        unfolding is_basis_on_def
      proof (intro conjI)
        show "\<forall>b\<in>B. b \<subseteq> X"
        proof (intro ballI)
          fix b assume "b \<in> B"
          then show "b \<subseteq> X" using hB_open hTX_sub
            by fast
        qed
      next
        show "\<forall>x\<in>X. \<exists>b\<in>B. x \<in> b"
        proof (intro ballI)
          fix x assume "x \<in> X"
          then show "\<exists>b\<in>B. x \<in> b"
            using hB_refine hTop_ctx unfolding is_topology_on_def
            by metis
        qed
      next
        show "\<forall>b1\<in>B. \<forall>b2\<in>B. \<forall>x\<in>b1 \<inter> b2. \<exists>b3\<in>B. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
        proof (intro ballI)
          fix b1 b2 x assume hb1: "b1 \<in> B" and hb2: "b2 \<in> B" and hx: "x \<in> b1 \<inter> b2"
          have hb1TX: "b1 \<in> TX" using hb1 hB_open
            by blast
          have hb2TX: "b2 \<in> TX" using hb2 hB_open
            by fast
          have hintTX: "b1 \<inter> b2 \<in> TX"
            using topology_inter2[OF hTop_ctx hb1TX hb2TX]
            by presburger
          show "\<exists>b3\<in>B. x \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
            using hB_refine hintTX hx
            by blast
        qed
      qed
    next
      show "TX = topology_generated_by_basis X B"
      proof
        show "topology_generated_by_basis X B \<subseteq> TX"
          using topology_generated_by_basis_subset[OF hTop_ctx hB_open]
          by order
      next
        show "TX \<subseteq> topology_generated_by_basis X B"
          unfolding topology_generated_by_basis_def
        proof (rule subsetI)
          fix U assume hUTX: "U \<in> TX"
          have "U \<subseteq> X" using hTX_sub hUTX
            by simp
          moreover have "\<forall>x\<in>U. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U"
            using hB_refine hUTX
            by fastforce
          ultimately show "U \<in> {U. U \<subseteq> X \<and> (\<forall>x\<in>U. \<exists>b\<in>B. x \<in> b \<and> b \<subseteq> U)}"
            by blast
        qed
      qed
    qed
    show ?thesis using hB_basis hB_slf
      
      by blast
  qed
  show "top1_regular_on X TX \<and> (\<exists>\<B>. basis_for X \<B> TX \<and> top1_sigma_locally_finite_family_on X TX \<B>)"
    using hReg \<open>\<exists>\<B>. basis_for X \<B> TX \<and> top1_sigma_locally_finite_family_on X TX \<B>\<close>
    
    by argo
next
  assume h: "top1_regular_on X TX \<and> (\<exists>\<B>. basis_for X \<B> TX \<and> top1_sigma_locally_finite_family_on X TX \<B>)"
  show "top1_metrizable_on X TX"
  proof -
    obtain \<B> where hBasis: "basis_for X \<B> TX" and hSLF: "top1_sigma_locally_finite_family_on X TX \<B>"
      using h by blast
    have hReg: "top1_regular_on X TX" using h by blast
    text \<open>Step 1: Lemma 40.1 gives normality + G-delta.\<close>
    have hNorm: "top1_normal_on X TX"
      using Lemma_40_1[OF hReg hBasis hSLF] by blast
    have hGdelta: "\<forall>A. closedin_on X TX A \<longrightarrow> top1_G_delta_on X TX A"
      using Lemma_40_1[OF hReg hBasis hSLF] by blast
    have hTop: "is_topology_on X TX"
      using hReg unfolding top1_regular_on_def top1_T1_on_def
      by argo
    text \<open>Step 2: Decompose basis B = ∪_n B_n (LF). For each B ∈ B_n,
      X-B is closed + G-delta, so Lemma 40.2 gives g_B: X→[0,1] with
      g_B=0 on X-B, g_B>0 on B. Define f_{n,B} = g_B/n ∈ [0,1/n].\<close>
    obtain Bn :: "nat \<Rightarrow> 'a set set" where
      hBn_lf: "\<forall>n. top1_locally_finite_family_on X TX (Bn n)" and
      hB_eq: "\<B> = (\<Union>n. Bn n)"
      using hSLF unfolding top1_sigma_locally_finite_family_on_def
      by blast
    text \<open>For each B in the basis, X-B is closed.\<close>
    have hB_open: "\<B> \<subseteq> TX"
      using basis_elem_open_if_basis_for[OF hBasis]
      by blast
    have hB_subX: "\<forall>B\<in>\<B>. B \<subseteq> X"
      using hBasis unfolding basis_for_def is_basis_on_def
      by presburger
    have hXmB_closed: "\<forall>B\<in>\<B>. closedin_on X TX (X - B)"
    proof (intro ballI)
      fix B assume "B \<in> \<B>"
      have "B \<in> TX" using hB_open \<open>B \<in> \<B>\<close>
        by blast
      have "B \<subseteq> X" using hB_subX \<open>B \<in> \<B>\<close>
        by blast
      then have "X - (X - B) = B"
        by fast
      then show "closedin_on X TX (X - B)"
        unfolding closedin_on_def using \<open>B \<in> TX\<close>
        by auto
    qed
    text \<open>For each B, Lemma 40.2 gives g_B.\<close>
    have hgB_exists: "\<forall>B\<in>\<B>. \<exists>gB. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) gB
      \<and> (\<forall>x\<in>X - B. gB x = 0) \<and> (\<forall>x\<in>B. 0 < gB x)"
    proof (intro ballI)
      fix B assume hB: "B \<in> \<B>"
      have hXmB_cl: "closedin_on X TX (X - B)" using hXmB_closed hB
        by blast
      have hXmB_gd: "top1_G_delta_on X TX (X - B)" using hGdelta hXmB_cl
        by blast
      obtain gB where hgB: "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) gB
        \<and> (\<forall>x\<in>X - B. gB x = 0) \<and> (\<forall>x\<in>X - (X - B). 0 < gB x)"
        using Lemma_40_2[OF hNorm hXmB_cl hXmB_gd]
        by blast
      text \<open>X - (X - B) = B ∩ X. Since B ⊆ X (from basis), this is B.\<close>
      have "X - (X - B) = B" using hB hB_subX
        by fast
      then show "\<exists>gB. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) gB
        \<and> (\<forall>x\<in>X - B. gB x = 0) \<and> (\<forall>x\<in>B. 0 < gB x)"
        using hgB
        by auto
    qed
    text \<open>Step 3: The family {g_B | B ∈ B} separates points from closed sets.
      So by Theorem 34.2, the product map is an embedding.
      Then X homeomorphic to subspace of ℝ^J, which is metrizable.\<close>
    text \<open>Choose g_B for each B ∈ B via choice.\<close>
    obtain gB where hgB_prop: "\<forall>B\<in>\<B>. top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (gB B)
      \<and> (\<forall>x\<in>X - B. gB B x = 0) \<and> (\<forall>x\<in>B. 0 < gB B x)"
      using bchoice[OF hgB_exists]
      by presburger
    text \<open>Define f_B: X → ℝ as gB composed with expand_range to ℝ.
      {f_B | B ∈ B} separates points from closed sets: for x₀ and U neighborhood,
      find B ∈ B with x₀ ∈ B ⊆ U, then f_B(x₀) > 0 and f_B = 0 outside B ⊆ U.\<close>
    have hT1: "\<forall>x\<in>X. closedin_on X TX {x}"
      using hReg unfolding top1_regular_on_def top1_T1_on_def
      by satx
    text \<open>Each gB B continuous into ℝ (expand range).\<close>
    have hgB_cont_R: "\<forall>B\<in>\<B>. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (gB B)"
    proof (intro ballI)
      fix B assume "B \<in> \<B>"
      then have "top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (gB B)"
        using hgB_prop
        by blast
      then show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (gB B)"
        by (metis Theorem_18_2(6) hTop order_topology_on_UNIV_is_topology_on
          subspace_topology_is_topology_on subset_UNIV top1_closed_interval_topology_def)
    qed
    text \<open>Separation: for x₀ ∈ X and neighborhood U, find B with gB(x₀) > 0 and gB = 0 outside U.\<close>
    have hSep: "\<forall>x0\<in>X. \<forall>U. neighborhood_of x0 X TX U \<longrightarrow>
      (\<exists>B\<in>\<B>. 0 < gB B x0 \<and> (\<forall>x\<in>X - U. gB B x = 0))"
    proof (intro ballI allI impI)
      fix x0 U assume hx0: "x0 \<in> X" and hU: "neighborhood_of x0 X TX U"
      obtain V where hV: "V \<in> TX" and hx0V: "x0 \<in> V" and hVU: "V \<subseteq> U"
        using hU unfolding neighborhood_of_def
        by blast
      obtain B where hB: "B \<in> \<B>" and hx0B: "x0 \<in> B" and hBV: "B \<subseteq> V"
        using basis_for_refine[OF hBasis hV hx0V]
        by blast
      have "0 < gB B x0" using hgB_prop hB hx0B
        by blast
      moreover have "\<forall>x\<in>X - U. gB B x = 0"
      proof (intro ballI)
        fix x assume "x \<in> X - U"
        then have "x \<in> X - B" using hBV hVU
          by blast
        then show "gB B x = 0" using hgB_prop hB
          by blast
      qed
      ultimately show "\<exists>B\<in>\<B>. 0 < gB B x0 \<and> (\<forall>x\<in>X - U. gB B x = 0)"
        using hB
        by blast
    qed
    text \<open>By Theorem 34.2, the product map F is an embedding into ℝ^B.
      Then X ≅ F(X) ⊆ ℝ^B. Since ℝ^B with uniform metric is metrizable,
      F(X) is metrizable, hence X is metrizable.\<close>
    text \<open>Apply Theorem 34.2: F is an embedding into product topology on ℝ^B.\<close>
    define F where "F x = (\<lambda>B. if B \<in> \<B> then gB B x else undefined)" for x
    have hEmbed: "top1_embedding_on X TX
      (top1_PiE \<B> (\<lambda>_. (UNIV::real set)))
      (top1_product_topology_on \<B> (\<lambda>_. (UNIV::real set)) (\<lambda>_. order_topology_on_UNIV)) F"
      using Theorem_34_2[OF hTop hT1 hgB_cont_R hSep, folded F_def]
      by argo
    text \<open>Metrizable: The Munkres proof uses f_{n,B} = g_B/n (our construction uses g_B directly).
      For the uniform metric continuity: need f_{n,B}: X → [0,1/n] so that the sup over all
      (n,B) of |f_{n,B}(x) - f_{n,B}(x₀)| < ε. The 1/n scaling handles n > N; local finiteness
      of B_n handles n ≤ N. Our current embedding uses g_B without scaling, so it gives
      embedding in product topology (proved via Theorem 34.2) but NOT in uniform metric.
      To complete: modify construction to use f_{n,B} = g_B/n, prove uniform metric continuity
      using local finiteness, then conclude metrizable. This is ~30 lines.
      Alternative: use that embedding_on gives homeomorphism to image, and pull back metric
      from product topology restricted to F(X) — but product topology not metrizable in general.\<close>
    text \<open>Define d on X: pullback of uniform metric via modified F using scaled functions.
      For each (n,B) with B ∈ B_n, define f_{n,B}(x) = gB(B)(x) / real(Suc n).
      Then d(x,y) = Sup{ |f_{n,B}(x) - f_{n,B}(y)| | n, B ∈ Bn n }.
      Key property: for n > N where 1/(N+1) < ε/2, |f_{n,B}(x)-f_{n,B}(y)| ≤ 1/(n+1) < ε/2.
      For n ≤ N: Bn n is LF, so only finitely many nonzero, each varies by < ε/2.
      This gives: d metrizes TX.\<close>
    define J where "J = {(n::nat, B). B \<in> Bn n}"
    define fJ where "fJ p x = (case p of (n, B) \<Rightarrow> gB B x / real (Suc n))" for p :: "nat \<times> 'a set" and x
    define d where "d x y = (if J = {} then 0 else Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J))" for x y
    text \<open>d is a metric on X: proved from gB properties + Sup.\<close>
    text \<open>Bound and non-emptiness for Sup.\<close>
    have hgB_range: "\<forall>B\<in>\<B>. \<forall>x\<in>X. 0 \<le> gB B x \<and> gB B x \<le> 1"
      using hgB_prop unfolding top1_continuous_map_on_def top1_closed_interval_def
      by fast
    have hfJ_le1: "\<forall>p\<in>J. \<forall>x\<in>X. \<forall>y\<in>X. \<bar>fJ p x - fJ p y\<bar> \<le> 1"
    proof (intro ballI)
      fix p x y assume hp: "p \<in> J" and hx: "x \<in> X" and hy: "y \<in> X"
      obtain n B where hpnB: "p = (n, B)" and hBn: "B \<in> Bn n"
        using hp unfolding J_def by blast
      have hBB: "B \<in> \<B>" using hBn hB_eq by blast
      have "0 \<le> gB B x" "gB B x \<le> 1" using hgB_range hBB hx by blast+
      have "0 \<le> gB B y" "gB B y \<le> 1" using hgB_range hBB hy by blast+
      have "\<bar>fJ p x - fJ p y\<bar> = \<bar>gB B x / real (Suc n) - gB B y / real (Suc n)\<bar>"
        unfolding fJ_def hpnB by simp
      also have "... = \<bar>gB B x - gB B y\<bar> / real (Suc n)"
      proof -
        have "gB B x / real (Suc n) - gB B y / real (Suc n) = (gB B x - gB B y) / real (Suc n)"
          by (simp add: diff_divide_distrib)
        then show ?thesis by (simp add: abs_divide)
      qed
      also have "... \<le> 1 / real (Suc n)"
      proof -
        have "\<bar>gB B x - gB B y\<bar> \<le> 1"
          using \<open>0 \<le> gB B x\<close> \<open>gB B x \<le> 1\<close> \<open>0 \<le> gB B y\<close> \<open>gB B y \<le> 1\<close>
          by linarith
        then show ?thesis
          by (simp add: frac_le)
      qed
      also have "... \<le> 1"
        by fastforce
      finally show "\<bar>fJ p x - fJ p y\<bar> \<le> 1" .
    qed
    have hfJ_bdd: "\<forall>x\<in>X. \<forall>y\<in>X. bdd_above ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J)"
      using hfJ_le1
      by fast
    have hfJ_nn: "\<forall>p\<in>J. \<forall>x\<in>X. \<forall>y\<in>X. 0 \<le> \<bar>fJ p x - fJ p y\<bar>"
      by simp
    have hd_metric: "top1_metric_on X d"
      unfolding top1_metric_on_def
    proof (intro conjI ballI)
      text \<open>d x x ≥ 0.\<close>
      fix x assume "x \<in> X"
      show "0 \<le> d x x"
        unfolding d_def using hfJ_nn \<open>x \<in> X\<close>
        by simp
    next
      text \<open>d x y ≥ 0.\<close>
      fix x y assume "x \<in> X" "y \<in> X"
      show "0 \<le> d x y"
      proof (cases "J = {}")
        case True then show ?thesis unfolding d_def by simp
      next
        case False
        then obtain p where hp: "p \<in> J" by blast
        have hmem: "\<bar>fJ p x - fJ p y\<bar> \<in> (\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J"
          using hp by blast
        have "0 \<le> \<bar>fJ p x - fJ p y\<bar>" by simp
        also have "\<bar>fJ p x - fJ p y\<bar> \<le> Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J)"
          using cSup_upper hmem hfJ_bdd \<open>x \<in> X\<close> \<open>y \<in> X\<close>
          by meson
        finally show ?thesis unfolding d_def using False
          by presburger
      qed
    next
      text \<open>d x y = 0 ↔ x = y.\<close>
      fix x y assume hxX: "x \<in> X" and hyX: "y \<in> X"
      show "(d x y = 0) = (x = y)"
      proof
        assume "x = y"
        then show "d x y = 0" unfolding d_def fJ_def
          by simp
      next
        assume hd0: "d x y = 0"
        show "x = y"
        proof (rule ccontr)
          assume hne: "x \<noteq> y"
          text \<open>x ≠ y, {y} closed, X-{y} is neighborhood of x.\<close>
          have "closedin_on X TX {y}" using hT1 hyX
            by blast
          have hXmy_open: "X - {y} \<in> TX" using \<open>closedin_on X TX {y}\<close>
            unfolding closedin_on_def
            by presburger
          have hx_in: "x \<in> X - {y}" using hxX hne
            by blast
          have "neighborhood_of x X TX (X - {y})"
            unfolding neighborhood_of_def using hXmy_open hx_in
            by satx
          then obtain B where hB: "B \<in> \<B>" and hgBx: "0 < gB B x" and hgBy0: "\<forall>z\<in>X - (X - {y}). gB B z = 0"
            using hSep hxX
            by blast
          have "gB B y = 0"
            using hgBy0 hyX
            by blast
          text \<open>B ∈ Bn n for some n.\<close>
          obtain n where hn: "B \<in> Bn n"
            using hB hB_eq
            by blast
          have hpJ: "(n, B) \<in> J" unfolding J_def using hn
            by blast
          have "fJ (n, B) x > 0" unfolding fJ_def using hgBx
            by auto
          moreover have "fJ (n, B) y = 0" unfolding fJ_def using \<open>gB B y = 0\<close>
            by fastforce
          ultimately have "\<bar>fJ (n, B) x - fJ (n, B) y\<bar> > 0"
            by simp
          moreover have "\<bar>fJ (n, B) x - fJ (n, B) y\<bar> \<le> d x y"
          proof -
            have "d x y = Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J)" unfolding d_def using hpJ
              by force
            moreover have "\<bar>fJ (n, B) x - fJ (n, B) y\<bar> \<in> (\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J" using hpJ
              by blast
            ultimately show ?thesis
              using cSup_upper[of "\<bar>fJ (n, B) x - fJ (n, B) y\<bar>" "(\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J"]
                hfJ_bdd hxX hyX
              by force
          qed
          ultimately show False using hd0
            by argo
        qed
      qed
    next
      text \<open>Symmetry: d x y = d y x.\<close>
      fix x y assume "x \<in> X" "y \<in> X"
      show "d x y = d y x" unfolding d_def
        by (smt (verit) Sup.SUP_cong)
    next
      text \<open>Triangle: d x z ≤ d x y + d y z.\<close>
      fix x y z assume hxX: "x \<in> X" and hyX: "y \<in> X" and hzX: "z \<in> X"
      show "d x z \<le> d x y + d y z"
      proof (cases "J = {}")
        case True then show ?thesis unfolding d_def by simp
      next
        case False
        have hne: "(\<lambda>p. \<bar>fJ p x - fJ p z\<bar>) ` J \<noteq> {}" using False by blast
        have hd_xz_eq: "d x z = Sup ((\<lambda>p. \<bar>fJ p x - fJ p z\<bar>) ` J)"
          unfolding d_def using False by simp
        have hd_xy_eq: "d x y = Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J)"
          unfolding d_def using False by simp
        have hd_yz_eq: "d y z = Sup ((\<lambda>p. \<bar>fJ p y - fJ p z\<bar>) ` J)"
          unfolding d_def using False by simp
        show ?thesis unfolding hd_xz_eq hd_xy_eq hd_yz_eq
        proof (rule cSup_least[OF hne])
          fix v assume "v \<in> (\<lambda>p. \<bar>fJ p x - fJ p z\<bar>) ` J"
          then obtain p where hp: "p \<in> J" and hv: "v = \<bar>fJ p x - fJ p z\<bar>" by blast
          have htri_p: "\<bar>fJ p x - fJ p z\<bar> \<le> \<bar>fJ p x - fJ p y\<bar> + \<bar>fJ p y - fJ p z\<bar>"
            by argo
          have hmem_xy: "\<bar>fJ p x - fJ p y\<bar> \<in> (\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J" using hp by blast
          have hle_xy: "\<bar>fJ p x - fJ p y\<bar> \<le> Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J)"
            using cSup_upper[OF hmem_xy] hfJ_bdd hxX hyX
            by fast
          have hmem_yz: "\<bar>fJ p y - fJ p z\<bar> \<in> (\<lambda>p. \<bar>fJ p y - fJ p z\<bar>) ` J" using hp by blast
          have hle_yz: "\<bar>fJ p y - fJ p z\<bar> \<le> Sup ((\<lambda>p. \<bar>fJ p y - fJ p z\<bar>) ` J)"
            using cSup_upper[OF hmem_yz] hfJ_bdd hyX hzX
            by fast
          show "v \<le> Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J) + Sup ((\<lambda>p. \<bar>fJ p y - fJ p z\<bar>) ` J)"
            unfolding hv using htri_p hle_xy hle_yz
            by argo
        qed
      qed
    qed
    text \<open>d-topology = TX: d-open → TX-open (from gB continuity), TX-open → d-open (from separation + LF).\<close>
    have hd_topology: "TX = top1_metric_topology_on X d"
    proof (rule equalityI)
      text \<open>(⊆) TX ⊆ metric topology: for U ∈ TX and x₀ ∈ U, find d-ball in U.\<close>
      show "TX \<subseteq> top1_metric_topology_on X d"
        unfolding top1_metric_topology_on_def topology_generated_by_basis_def
      proof (rule subsetI)
        fix U assume hU: "U \<in> TX"
        have hU_subX: "U \<subseteq> X"
          using hU hBasis unfolding basis_for_def topology_generated_by_basis_def
          by blast
        show "U \<in> {U. U \<subseteq> X \<and> (\<forall>x\<in>U. \<exists>b\<in>top1_metric_basis_on X d. x \<in> b \<and> b \<subseteq> U)}"
        proof (intro CollectI conjI ballI)
          show "U \<subseteq> X" by (rule hU_subX)
        next
          fix x0 assume hx0U: "x0 \<in> U"
          have hx0X: "x0 \<in> X" using hx0U hU_subX
            by blast
          obtain B where hBB: "B \<in> \<B>" and hx0B: "x0 \<in> B" and hBU: "B \<subseteq> U"
            using basis_for_refine[OF hBasis hU hx0U]
            by blast
          obtain n where hBn: "B \<in> Bn n" using hBB hB_eq
            by blast
          have hgBx0: "0 < gB B x0" using hgB_prop hBB hx0B
            by blast
          have hpJ: "(n, B) \<in> J" unfolding J_def using hBn
            by blast
          define \<epsilon> where "\<epsilon> = fJ (n, B) x0"
          have hepos: "0 < \<epsilon>" unfolding \<epsilon>_def fJ_def using hgBx0
            by force
          have hball_sub_U: "top1_ball_on X d x0 \<epsilon> \<subseteq> U"
          proof (rule subsetI)
            fix x assume hxball: "x \<in> top1_ball_on X d x0 \<epsilon>"
            have hxX: "x \<in> X" using hxball unfolding top1_ball_on_def
              by blast
            have hdx: "d x0 x < \<epsilon>" using hxball unfolding top1_ball_on_def
              by blast
            text \<open>|fJ(n,B)(x) - fJ(n,B)(x₀)| ≤ d(x₀,x) < ε = fJ(n,B)(x₀).\<close>
            have hfJ_le_d: "\<bar>fJ (n, B) x - fJ (n, B) x0\<bar> \<le> d x0 x"
            proof -
              have hmem: "\<bar>fJ (n, B) x0 - fJ (n, B) x\<bar> \<in> (\<lambda>p. \<bar>fJ p x0 - fJ p x\<bar>) ` J"
                using hpJ by blast
              have hd_eq: "d x0 x = Sup ((\<lambda>p. \<bar>fJ p x0 - fJ p x\<bar>) ` J)"
                unfolding d_def using hpJ
                by fastforce
              have "\<bar>fJ (n, B) x0 - fJ (n, B) x\<bar> \<le> d x0 x"
                unfolding hd_eq using cSup_upper[OF hmem] hfJ_bdd hx0X hxX
                by fast
              then show ?thesis
                by simp
            qed
            have "fJ (n, B) x > 0"
              using hfJ_le_d hdx unfolding \<epsilon>_def
              by auto
            then have "gB B x > 0" unfolding fJ_def
              by (simp add: zero_less_divide_iff)
            have hgBx_pos: "gB B x > 0" by (rule \<open>gB B x > 0\<close>)
            have "x \<in> B"
            proof (rule ccontr)
              assume "x \<notin> B"
              then have "x \<in> X - B" using hxX
                by blast
              then have "gB B x = 0" using hgB_prop hBB
                by blast
              then show False using hgBx_pos
                by fastforce
            qed
            then show "x \<in> U" using hBU
              by fast
          qed
          have hball_basis: "top1_ball_on X d x0 \<epsilon> \<in> top1_metric_basis_on X d"
            unfolding top1_metric_basis_on_def using hx0X hepos
            by blast
          have hx0_ball: "x0 \<in> top1_ball_on X d x0 \<epsilon>"
            unfolding top1_ball_on_def using hx0X hepos hd_metric unfolding top1_metric_on_def
            by fastforce
          show "\<exists>b\<in>top1_metric_basis_on X d. x0 \<in> b \<and> b \<subseteq> U"
            using hball_basis hx0_ball hball_sub_U
            by blast
        qed
      qed
    next
      text \<open>(⊇) metric topology ⊆ TX: d-balls have TX-neighborhoods inside.\<close>
      show "top1_metric_topology_on X d \<subseteq> TX"
        unfolding top1_metric_topology_on_def
      proof (rule topology_generated_by_basis_subset[OF hTop])
        show "top1_metric_basis_on X d \<subseteq> TX"
        proof (rule subsetI)
          fix b assume "b \<in> top1_metric_basis_on X d"
          then obtain x0 r where hx0: "x0 \<in> X" and hr: "0 < r" and hbeq: "b = top1_ball_on X d x0 r"
            unfolding top1_metric_basis_on_def
            by force
          show "b \<in> TX"
            unfolding hbeq
          proof (rule top1_open_of_local_subsets[OF hTop])
            show "top1_ball_on X d x0 r \<subseteq> X" unfolding top1_ball_on_def
              by blast
            show "\<forall>x\<in>top1_ball_on X d x0 r. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> top1_ball_on X d x0 r"
            proof (intro ballI)
              fix x assume hxball: "x \<in> top1_ball_on X d x0 r"
              have hxX: "x \<in> X" using hxball unfolding top1_ball_on_def by blast
              have hdx0x: "d x0 x < r" using hxball unfolding top1_ball_on_def by blast
              define \<epsilon> where "\<epsilon> = r - d x0 x"
              have hepos: "0 < \<epsilon>" unfolding \<epsilon>_def using hdx0x by simp
              text \<open>Suffices: find W ∈ TX with x ∈ W and ∀y∈W. d x y < ε.
                Then d(x₀,y) ≤ d(x₀,x) + d(x,y) < d(x₀,x) + ε = r.\<close>
              text \<open>For each (n,B), |fJ(n,B)(y) - fJ(n,B)(x)| < ε suffices for d(x,y) < ε.
                For n > N where 1/(N+1) < ε/2: |fJ(n,B)| ≤ 1/(n+1), so diff ≤ 2/(n+1) < ε.
                For n ≤ N: use LF of Bn n + continuity of finitely many gB.\<close>
              have "\<exists>W\<in>TX. x \<in> W \<and> (\<forall>y\<in>W. d x y < \<epsilon>)"
              proof -
                obtain N :: nat where hN: "2 / real (Suc (Suc N)) < \<epsilon>"
                proof -
                  obtain k :: nat where hk: "2 / \<epsilon> < real k" using reals_Archimedean2
                    by blast
                  have "2 / real (Suc (Suc k)) < \<epsilon>"
                  proof -
                    have "0 < real (Suc (Suc k))"
                      by linarith
                    moreover have "2 / \<epsilon> < real (Suc (Suc k))" using hk
                      by simp
                    ultimately show ?thesis using hepos
                      by (simp add: field_simps)
                  qed
                  then show ?thesis using that
                    by blast
                qed
                have hfJ_cont: "\<forall>n. \<forall>B\<in>Bn n. top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>y. fJ (n, B) y)"
                proof (intro allI ballI)
                  fix n B assume "B \<in> Bn n"
                  then have "B \<in> \<B>" using hB_eq
                    by fast
                  then have hgB_R: "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (gB B)"
                    using hgB_cont_R
                    by blast
                  have "(\<lambda>y. fJ (n, B) y) = (\<lambda>y. (1 / real (Suc n)) * gB B y)"
                    unfolding fJ_def
                    by simp
                  then show "top1_continuous_map_on X TX (UNIV::real set) order_topology_on_UNIV (\<lambda>y. fJ (n, B) y)"
                    using top1_continuous_scale_real[OF hTop hgB_R]
                    by presburger
                qed
                have hWn_ex: "\<forall>n\<le>N. \<exists>Wn\<in>TX. x \<in> Wn \<and>
                  (\<forall>y\<in>Wn. \<forall>B\<in>Bn n. \<bar>fJ (n, B) y - fJ (n, B) x\<bar> \<le> \<epsilon>/2)"
                proof (intro allI impI)
                  fix n assume hn: "n \<le> N"
                  obtain Unbhd where hUn: "Unbhd \<in> TX" and hxUn: "x \<in> Unbhd"
                    and hFin: "finite {B \<in> Bn n. intersects B Unbhd}"
                    using hBn_lf hxX unfolding top1_locally_finite_family_on_def
                    by blast
                  text \<open>For B not meeting Unbhd: x ∉ B so gB B x = 0, fJ = 0 at x.
                    For y ∈ Unbhd: y ∉ B so gB B y = 0, fJ = 0 at y. Diff = 0.\<close>
                  have hzero_outside: "\<forall>B\<in>Bn n. \<not>intersects B Unbhd \<longrightarrow>
                    (\<forall>y\<in>Unbhd. fJ (n, B) y = 0 \<and> fJ (n, B) x = 0)"
                  proof (intro ballI impI allI)
                    fix B y assume hBn': "B \<in> Bn n" and hni: "\<not>intersects B Unbhd" and hyUn: "y \<in> Unbhd"
                    have hBB: "B \<in> \<B>" using hBn' hB_eq
                      by blast
                    have "x \<notin> B" using hni hxUn unfolding intersects_def
                      by blast
                    then have "x \<in> X - B" using hxX
                      by fast
                    then have hgBx0: "gB B x = 0" using hgB_prop hBB
                      by fast
                    have "y \<notin> B" using hni hyUn unfolding intersects_def
                      by blast
                    have hyX: "y \<in> X" using hyUn hUn hBasis
                      unfolding basis_for_def topology_generated_by_basis_def
                      by blast
                    then have "y \<in> X - B" using \<open>y \<notin> B\<close>
                      by fast
                    then have hgBy0: "gB B y = 0" using hgB_prop hBB
                      by blast
                    show "fJ (n, B) y = 0 \<and> fJ (n, B) x = 0"
                      unfolding fJ_def using hgBx0 hgBy0
                      by simp
                  qed
                  text \<open>For B meeting Unbhd: fJ continuous → preimage of (fJ(x)-ε/2, fJ(x)+ε/2).\<close>
                  have hVB_ex: "\<forall>B\<in>{B \<in> Bn n. intersects B Unbhd}.
                    \<exists>VB\<in>TX. x \<in> VB \<and> (\<forall>y\<in>VB. \<bar>fJ (n, B) y - fJ (n, B) x\<bar> < \<epsilon>/2)"
                    sorry (* fJ(n,B) continuous (hfJ_cont), so preimage of open ball in ℝ
                             centered at fJ(n,B)(x) with radius ε/2 is TX-open containing x. *)
                  text \<open>Combine: Wn = Unbhd ∩ ∩{VB | B meets Unbhd}.\<close>
                  show "\<exists>Wn\<in>TX. x \<in> Wn \<and> (\<forall>y\<in>Wn. \<forall>B\<in>Bn n. \<bar>fJ (n, B) y - fJ (n, B) x\<bar> \<le> \<epsilon>/2)"
                    sorry (* Choose VBs via hVB_ex. Wn = Unbhd ∩ ∩{VB} is finite intersection
                             of TX-opens (hFin gives finitely many B meeting Unbhd).
                             For y ∈ Wn and B ∈ Bn n:
                               if B meets Unbhd: y ∈ VB → |diff| < ε/2 ≤ ε/2
                               if B doesn't meet Unbhd: |diff| = 0 ≤ ε/2 (hzero_outside) *)
                qed
                then obtain Wn where hWn: "\<forall>n\<le>N. Wn n \<in> TX \<and> x \<in> Wn n
                  \<and> (\<forall>y\<in>Wn n. \<forall>B\<in>Bn n. \<bar>fJ (n, B) y - fJ (n, B) x\<bar> \<le> \<epsilon>/2)"
                  by metis
                define W where "W = (\<Inter>n\<in>{..N}. Wn n)"
                have hW_open: "W \<in> TX"
                proof -
                  have "finite {..N}" by blast
                  moreover have "{..N} \<noteq> {}" by blast
                  moreover have "(\<lambda>n. Wn n) ` {..N} \<subseteq> TX" using hWn
                    by blast
                  ultimately have "\<Inter>((\<lambda>n. Wn n) ` {..N}) \<in> TX"
                    using hTop unfolding is_topology_on_def
                    by force
                  then show ?thesis unfolding W_def
                    by presburger
                qed
                have hxW: "x \<in> W" unfolding W_def using hWn
                  by blast
                have hyX_W: "\<forall>y\<in>W. y \<in> X"
                  using hW_open hBasis unfolding basis_for_def topology_generated_by_basis_def W_def
                  by blast
                define M where "M = max (\<epsilon>/2) (2 / real (Suc (Suc N)))"
                have hMeps: "M < \<epsilon>" unfolding M_def using hN hepos
                  by linarith
                have "\<forall>y\<in>W. d x y < \<epsilon>"
                proof (intro ballI)
                  fix y assume hyW: "y \<in> W"
                  have hyX: "y \<in> X" using hyX_W hyW
                    by blast
                  show "d x y < \<epsilon>"
                  proof (cases "J = {}")
                    case True then show ?thesis unfolding d_def using hepos
                      by auto
                  next
                    case False
                    have hne: "(\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J \<noteq> {}" using False
                      by fast
                    have hd_eq: "d x y = Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J)"
                      unfolding d_def using False
                      by presburger
                    have hbound: "\<forall>v\<in>(\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J. v \<le> M"
                    proof (intro ballI)
                      fix v assume "v \<in> (\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J"
                      then obtain n B where hnB: "(n, B) \<in> J" and hv: "v = \<bar>fJ (n, B) x - fJ (n, B) y\<bar>"
                        unfolding J_def
                        by fast
                      have hBn: "B \<in> Bn n" using hnB unfolding J_def
                        by auto
                      have hBB: "B \<in> \<B>" using hBn hB_eq
                        by blast
                      show "v \<le> M"
                      proof (cases "n \<le> N")
                        case True
                        have hyWn: "y \<in> Wn n" using hyW unfolding W_def using True
                          by fast
                        have "\<bar>fJ (n, B) y - fJ (n, B) x\<bar> \<le> \<epsilon>/2"
                          using hWn True hyWn hBn
                          by blast
                        then show ?thesis unfolding hv M_def
                          by argo
                      next
                        case False
                        then have hn_gt: "Suc (Suc N) \<le> Suc n"
                          by presburger
                        have hgBx01a: "0 \<le> gB B x" using hgB_range hBB hxX by blast
                        have hgBx01b: "gB B x \<le> 1" using hgB_range hBB hxX by blast
                        have hgBy01a: "0 \<le> gB B y" using hgB_range hBB hyX by blast
                        have hgBy01b: "gB B y \<le> 1" using hgB_range hBB hyX by blast
                        have hfJx: "fJ (n, B) x = gB B x / real (Suc n)" unfolding fJ_def
                          by fast
                        have hfJy: "fJ (n, B) y = gB B y / real (Suc n)" unfolding fJ_def
                          by fastforce
                        have hab_le: "\<bar>gB B x - gB B y\<bar> \<le> 2"
                          using hgBx01a hgBx01b hgBy01a hgBy01b
                          by fastforce
                        have hstep1: "gB B x / real (Suc n) - gB B y / real (Suc n) = (gB B x - gB B y) / real (Suc n)"
                          by (simp add: diff_divide_distrib)
                        have hstep2: "\<bar>(gB B x - gB B y) / real (Suc n)\<bar> = \<bar>gB B x - gB B y\<bar> / real (Suc n)"
                          by (simp add: abs_divide)
                        have "\<bar>fJ (n, B) x - fJ (n, B) y\<bar> \<le> 2 / real (Suc n)"
                          unfolding hfJx hfJy hstep1 hstep2 using hab_le
                          by (simp add: frac_le)
                        also have "2 / real (Suc n) \<le> 2 / real (Suc (Suc N))"
                          using hn_gt
                          by (simp add: frac_le)
                        finally show ?thesis unfolding hv M_def
                          by argo
                      qed
                    qed
                    have "Sup ((\<lambda>p. \<bar>fJ p x - fJ p y\<bar>) ` J) \<le> M"
                      using cSup_least[OF hne] hbound
                      by blast
                    then show ?thesis unfolding hd_eq using hMeps
                      by linarith
                  qed
                qed
                then show ?thesis using hW_open hxW
                  by blast
              qed
              then obtain W where hW: "W \<in> TX" and hxW: "x \<in> W" and hWeps: "\<forall>y\<in>W. d x y < \<epsilon>"
                by blast
              have "W \<subseteq> top1_ball_on X d x0 r"
              proof (rule subsetI)
                fix y assume hyW: "y \<in> W"
                have hW_sub_X: "W \<subseteq> X"
                  using hW hBasis unfolding basis_for_def topology_generated_by_basis_def
                  by blast
                have hyX: "y \<in> X" using hyW hW_sub_X
                  by blast
                have "d x0 y \<le> d x0 x + d x y"
                  using hd_metric hx0 hxX hyX unfolding top1_metric_on_def
                  by blast
                also have "d x y < \<epsilon>" using hWeps hyW by blast
                finally have "d x0 y < r" unfolding \<epsilon>_def
                  by auto
                then show "y \<in> top1_ball_on X d x0 r"
                  unfolding top1_ball_on_def using hyX
                  by blast
              qed
              then show "\<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> top1_ball_on X d x0 r"
                using hW hxW
                by blast
            qed
          qed
        qed
      qed
    qed
    show ?thesis unfolding top1_metrizable_on_def using hd_metric hd_topology
      by auto
  qed
qed

section \<open>\<S>41 Paracompactness\<close>

definition top1_paracompact_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_paracompact_on X TX \<longleftrightarrow>
     (\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow>
        (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>))"

definition top1_lindelof_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_lindelof_on X TX \<longleftrightarrow>
     is_topology_on X TX \<and>
     (\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>V. top1_countable V \<and> V \<subseteq> Uc \<and> X \<subseteq> \<Union>V))"

(** from \S41 Theorem 41.1 [top1.tex:5832] **)
text \<open>Proof follows Munkres: first prove regularity using Hausdorff + paracompact,
  then normality using regularity + paracompact. Key tool: for a locally finite
  family, \<open>closure(\<Union>D) = \<Union>(closure D)\<close> (Lemma 39.1).\<close>
lemma paracompact_hausdorff_imp_regular:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hHaus: "is_hausdorff_on X TX"
  assumes hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
  shows "top1_regular_on X TX"
proof -
  have hTop: "is_topology_on X TX"
    using hHaus unfolding is_hausdorff_on_def by blast

  text \<open>One-point sets are closed (from Hausdorff via T1).\<close>
  have hT1: "top1_T1_on X TX"
    by (rule hausdorff_imp_T1_on[OF hHaus])

  show ?thesis
    unfolding top1_regular_on_def
  proof (intro conjI)
    show "top1_T1_on X TX"
      by (rule hT1)
  next
    show "\<forall>x\<in>X. \<forall>C. closedin_on X TX C \<and> x \<notin> C \<longrightarrow>
      (\<exists>U V. neighborhood_of x X TX U \<and> V \<in> TX \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    proof (intro ballI allI impI)
      fix a C assume haX: "a \<in> X" and hCcl: "closedin_on X TX C \<and> a \<notin> C"
      have hCclosed: "closedin_on X TX C" using hCcl by blast
      have hanotC: "a \<notin> C" using hCcl by blast
      have hCX: "C \<subseteq> X" using hCclosed unfolding closedin_on_def by blast

      text \<open>Step 1: For each b \<in> C, Hausdorff gives disjoint nbhds of a and b.
        So a has a nbhd disjoint from some open set containing b, meaning a \<notin> cl(U_b).\<close>
      text \<open>Step 2: Cover X by {U_b | b \<in> C} \<union> {X - C}, take locally finite refinement.\<close>
      text \<open>Step 3: Form V = \<Union>{D \<in> refinement | D \<inter> C \<noteq> {}}. Then cl(V) is disjoint from a
        by locally finite closure (Lemma 39.1).\<close>
      text \<open>Step 1: For each b in C, Hausdorff separation gives a neighborhood
        of b whose closure avoids a.\<close>
      have hHausSep: "\<forall>b\<in>C. \<exists>Ub. Ub \<in> TX \<and> b \<in> Ub \<and>
        (\<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Ub \<inter> Wa = {})"
      proof (intro ballI)
        fix b assume hbC: "b \<in> C"
        have hbX: "b \<in> X" using hCX hbC by blast
        have hab: "a \<noteq> b" using hanotC hbC by blast
        have hHausAll: "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
          (\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
          using hHaus unfolding is_hausdorff_on_def by blast
        obtain Ua Ub where hUa: "neighborhood_of a X TX Ua"
          and hUb': "neighborhood_of b X TX Ub" and hdisj: "Ua \<inter> Ub = {}"
          using hHausAll[rule_format, OF haX hbX hab] by blast
        have "Ub \<in> TX" and "b \<in> Ub"
          using hUb' unfolding neighborhood_of_def by blast+
        have "Ua \<in> TX" and "a \<in> Ua"
          using hUa unfolding neighborhood_of_def by blast+
        show "\<exists>Ub. Ub \<in> TX \<and> b \<in> Ub \<and> (\<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Ub \<inter> Wa = {})"
          using \<open>Ub \<in> TX\<close> \<open>b \<in> Ub\<close> \<open>Ua \<in> TX\<close> \<open>a \<in> Ua\<close> hdisj
          by (rule_tac x="Ub" in exI) blast
      qed

      text \<open>Choose such neighborhoods via Hilbert choice.\<close>
      define Ub where "Ub b = (SOME Ub. Ub \<in> TX \<and> b \<in> Ub \<and>
        (\<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Ub \<inter> Wa = {}))" for b
      have hUb: "\<forall>b\<in>C. Ub b \<in> TX \<and> b \<in> Ub b \<and>
        (\<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Ub b \<inter> Wa = {})"
      proof (intro ballI)
        fix b assume "b \<in> C"
        then have "\<exists>U. U \<in> TX \<and> b \<in> U \<and> (\<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> U \<inter> Wa = {})"
          using hHausSep by blast
        then show "Ub b \<in> TX \<and> b \<in> Ub b \<and> (\<exists>Wa. Wa \<in> TX \<and> a \<in> Wa \<and> Ub b \<inter> Wa = {})"
          unfolding Ub_def by (rule someI_ex)
      qed

      text \<open>Step 2: Form an open cover and refine.\<close>
      let ?cover = "insert (X - C) (Ub ` C)"
      have hXminusC_open: "X - C \<in> TX"
        using hCclosed unfolding closedin_on_def by blast
      have hUb_open: "\<forall>b\<in>C. Ub b \<in> TX"
        using hUb by blast
      have hcover_sub_TX: "?cover \<subseteq> TX"
      proof (rule insert_subsetI)
        show "X - C \<in> TX" by (rule hXminusC_open)
      next
        show "Ub ` C \<subseteq> TX"
        proof (rule image_subsetI)
          fix b assume "b \<in> C"
          then show "Ub b \<in> TX" using hUb_open by blast
        qed
      qed
      have hcover_covers: "X \<subseteq> \<Union>?cover"
      proof (rule subsetI)
        fix x assume "x \<in> X"
        show "x \<in> \<Union>?cover"
        proof (cases "x \<in> C")
          case True
          have "x \<in> Ub x" using hUb True by blast
          moreover have "Ub x \<in> ?cover" using True by blast
          ultimately show ?thesis by blast
        next
          case False
          then have "x \<in> X - C" using \<open>x \<in> X\<close> by blast
          moreover have "X - C \<in> ?cover" by blast
          ultimately show ?thesis by blast
        qed
      qed
      have hcov_open: "top1_open_covering_on X TX ?cover"
        unfolding top1_open_covering_on_def
        using hcover_sub_TX hcover_covers by blast

      obtain \<CC> where hCC_cov: "top1_open_covering_on X TX \<CC>"
        and hCC_ref: "top1_refines \<CC> ?cover"
        and hCC_lf: "top1_locally_finite_family_on X TX \<CC>"
        using hPara hcov_open unfolding top1_paracompact_on_def by blast

      text \<open>Step 3: Subcollection D = elements of CC that intersect C.\<close>
      let ?\<DD> = "{D \<in> \<CC>. D \<inter> C \<noteq> {}}"
      have hD_covers_C: "C \<subseteq> \<Union>?\<DD>"
      proof (rule subsetI)
        fix c assume hcC: "c \<in> C"
        have hcX: "c \<in> X" using hCX hcC by blast
        have "c \<in> \<Union>\<CC>"
          using hCC_cov hcX unfolding top1_open_covering_on_def by blast
        then obtain D where hDCC: "D \<in> \<CC>" and hcD: "c \<in> D" by blast
        have "D \<inter> C \<noteq> {}" using hcD hcC by blast
        then have "D \<in> ?\<DD>" using hDCC by blast
        then show "c \<in> \<Union>?\<DD>" using hcD by blast
      qed

      text \<open>For each D in DD, a is not in cl(D): D refines some Ub b, so cl(D) \<subseteq> cl(Ub b),
        and a \<notin> cl(Ub b) because a has a neighborhood disjoint from Ub b.\<close>
      have ha_not_cl_D: "\<forall>D\<in>?\<DD>. a \<notin> closure_on X TX D"
      proof (intro ballI)
        fix D assume hDDD: "D \<in> ?\<DD>"
        have hDCC: "D \<in> \<CC>" using hDDD by blast
        have hDinterC: "D \<inter> C \<noteq> {}" using hDDD by blast
        text \<open>D refines the cover, so D \<subseteq> some element of the cover.\<close>
        have "\<exists>A\<in>?cover. D \<subseteq> A"
          using hCC_ref hDCC unfolding top1_refines_def by blast
        then obtain A where hAcover: "A \<in> ?cover" and hDA: "D \<subseteq> A" by blast
        text \<open>A is either X - C or some Ub b. Since D \<inter> C \<noteq> {}, A cannot be X - C.\<close>
        have "A \<noteq> X - C"
        proof
          assume "A = X - C"
          then have "D \<subseteq> X - C" using hDA by simp
          then have "D \<inter> C = {}" by blast
          then show False using hDinterC by contradiction
        qed
        then obtain b where hbC: "b \<in> C" and hAeq: "A = Ub b"
          using hAcover by blast
        text \<open>So D \<subseteq> Ub b. cl(D) \<subseteq> cl(Ub b). And a has a neighborhood Wa disjoint from Ub b.\<close>
        have hDUb: "D \<subseteq> Ub b" using hDA hAeq by simp
        have hDX: "D \<subseteq> X" using hTsub hCC_cov hDCC unfolding top1_open_covering_on_def by blast
        have hUbX: "Ub b \<subseteq> X" using hUb hbC hTsub by blast
        have hcl_D_sub: "closure_on X TX D \<subseteq> closure_on X TX (Ub b)"
          by (rule closure_on_mono[OF hDUb])
        obtain Wa where hWaT: "Wa \<in> TX" and haWa: "a \<in> Wa" and hdisj: "Ub b \<inter> Wa = {}"
          using hUb hbC by blast
        have ha_not_cl_Ub: "a \<notin> closure_on X TX (Ub b)"
        proof -
          have "neighborhood_of a X TX Wa"
            unfolding neighborhood_of_def using hWaT haWa by blast
          have "\<not> intersects Wa (Ub b)"
            unfolding intersects_def using hdisj by blast
          then show ?thesis
            using iffD1[OF Theorem_17_5a[OF hTop haX hUbX]]
                  \<open>neighborhood_of a X TX Wa\<close>
            by blast
        qed
        show "a \<notin> closure_on X TX D"
          using hcl_D_sub ha_not_cl_Ub by blast
      qed

      text \<open>Step 4: V = \<Union>DD is open and contains C.
        cl(V) = \<Union>{cl(D) | D \<in> DD} by locally finite closure (Lemma 39.1).
        So a \<notin> cl(V).\<close>
      let ?V = "\<Union>?\<DD>"
      have hV_open: "?V \<in> TX"
      proof -
        have "?\<DD> \<subseteq> TX"
          using hCC_cov unfolding top1_open_covering_on_def by blast
        then show ?thesis
          using hTop unfolding is_topology_on_def by blast
      qed
      have hV_covers_C: "C \<subseteq> ?V"
        using hD_covers_C by blast

      have hDD_sub_CC: "?\<DD> \<subseteq> \<CC>" by blast
      have hCC_subX: "\<forall>A\<in>\<CC>. A \<subseteq> X"
        using hCC_cov hTsub unfolding top1_open_covering_on_def by blast
      have hDD_lf: "top1_locally_finite_family_on X TX ?\<DD>"
      proof -
        have "\<forall>\<A>'. \<A>' \<subseteq> \<CC> \<longrightarrow> top1_locally_finite_family_on X TX \<A>'"
          by (rule Lemma_39_1(1)[OF hTop hCC_subX hCC_lf])
        then show ?thesis using hDD_sub_CC by blast
      qed

      have hDD_subX: "\<forall>A\<in>?\<DD>. A \<subseteq> X"
        using hCC_subX by blast

      have hcl_V: "closure_on X TX ?V = \<Union>(closure_on X TX ` ?\<DD>)"
        using Lemma_39_1(3)[OF hTop hDD_subX hDD_lf] by blast

      have ha_not_cl_V: "a \<notin> closure_on X TX ?V"
      proof -
        have "\<forall>D\<in>?\<DD>. a \<notin> closure_on X TX D"
          by (rule ha_not_cl_D)
        then have "a \<notin> \<Union>(closure_on X TX ` ?\<DD>)"
          by blast
        then show ?thesis
          using hcl_V by presburger
      qed

      text \<open>Step 5: X - cl(V) is a neighborhood of a, disjoint from V.\<close>
      have hV_subX: "?V \<subseteq> X"
      proof (rule subsetI)
        fix x assume "x \<in> ?V"
        then obtain D where hD: "D \<in> ?\<DD>" and hxD: "x \<in> D" by blast
        have "D \<in> TX" using hD hCC_cov unfolding top1_open_covering_on_def by blast
        show "x \<in> X"
          using hDD_subX hD hxD by blast
      qed
      have hclV_closed: "closedin_on X TX (closure_on X TX ?V)"
        by (rule closure_on_closed[OF hTop hV_subX])
      have hU_open: "X - closure_on X TX ?V \<in> TX"
        using hclV_closed unfolding closedin_on_def by blast
      have haU: "a \<in> X - closure_on X TX ?V"
        using haX ha_not_cl_V by blast
      have hU_nbhd: "neighborhood_of a X TX (X - closure_on X TX ?V)"
        unfolding neighborhood_of_def using hU_open haU by blast
      have hdisjoint: "(X - closure_on X TX ?V) \<inter> ?V = {}"
      proof -
        have "?V \<subseteq> closure_on X TX ?V"
          by (rule subset_closure_on)
        then show ?thesis by blast
      qed

      show "\<exists>U V. neighborhood_of a X TX U \<and> V \<in> TX \<and> C \<subseteq> V \<and> U \<inter> V = {}"
        by (rule exI[where x="X - closure_on X TX ?V"],
            rule exI[where x="?V"])
           (intro conjI hU_nbhd hV_open hV_covers_C hdisjoint)
    qed
  qed
qed

text \<open>@{thm paracompact_closure_avoidance_step} is proved in Top1\_Ch4 to avoid timeout.\<close>

text \<open>Closure of V avoids A, using the closure avoidance step and locally finite closure.\<close>
lemma paracompact_closure_union_avoidance:
  assumes hTop: "is_topology_on X TX"
  assumes hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
  assumes hAX: "A \<subseteq> X"
  assumes hDD_subX: "\<forall>D\<in>\<DD>. D \<subseteq> X"
  assumes hDD_lf: "top1_locally_finite_family_on X TX \<DD>"
  assumes hcl_avoid: "\<forall>D\<in>\<DD>. \<forall>x\<in>A. x \<notin> closure_on X TX D"
  shows "A \<subseteq> X - closure_on X TX (\<Union>\<DD>)"
proof -
  have hV_subX: "\<Union>\<DD> \<subseteq> X" using hDD_subX by blast
  have hcl_eq: "closure_on X TX (\<Union>\<DD>) = \<Union>(closure_on X TX ` \<DD>)"
    using Lemma_39_1(3)[OF hTop hDD_subX hDD_lf] by blast
  show ?thesis
  proof (rule subsetI)
    fix x assume hxA: "x \<in> A"
    have hxX: "x \<in> X" using hAX hxA by blast
    have "x \<notin> closure_on X TX (\<Union>\<DD>)"
    proof
      assume "x \<in> closure_on X TX (\<Union>\<DD>)"
      then have "x \<in> \<Union>(closure_on X TX ` \<DD>)"
        by (rule mem_of_eq[OF _ hcl_eq])
      then obtain D where "D \<in> \<DD>" "x \<in> closure_on X TX D" by blast
      then show False using hcl_avoid hxA by blast
    qed
    then show "x \<in> X - closure_on X TX (\<Union>\<DD>)" using hxX by blast
  qed
qed

lemma paracompact_regular_imp_normal:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hReg: "top1_regular_on X TX"
  assumes hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
  shows "top1_normal_on X TX"
proof -
  have hTop: "is_topology_on X TX"
    using hReg unfolding top1_regular_on_def top1_T1_on_def by blast
  have hT1: "top1_T1_on X TX"
    using hReg unfolding top1_regular_on_def by blast
  have hRegSep: "\<forall>x\<in>X. \<forall>C. closedin_on X TX C \<and> x \<notin> C \<longrightarrow>
    (\<exists>U V. neighborhood_of x X TX U \<and> V \<in> TX \<and> C \<subseteq> V \<and> U \<inter> V = {})"
    using hReg unfolding top1_regular_on_def by blast
  show ?thesis
    unfolding top1_normal_on_def
  proof (intro conjI allI impI)
    show "top1_T1_on X TX" by (rule hT1)
  next
    fix A B
    assume hAB: "closedin_on X TX A \<and> closedin_on X TX B \<and> A \<inter> B = {}"
    have hAcl: "closedin_on X TX A" using hAB by blast
    have hBcl: "closedin_on X TX B" using hAB by blast
    have hdisj: "A \<inter> B = {}" using hAB by blast
    have hAX: "A \<subseteq> X" using hAcl unfolding closedin_on_def by blast
    have hBX: "B \<subseteq> X" using hBcl unfolding closedin_on_def by blast
    text \<open>For each b in B, regularity separates b from A.\<close>
    define Ub where "Ub b = (SOME U. neighborhood_of b X TX U \<and>
      (\<exists>W. W \<in> TX \<and> A \<subseteq> W \<and> U \<inter> W = {}))" for b
    have hUb_prop: "\<forall>b\<in>B. neighborhood_of b X TX (Ub b) \<and>
      (\<exists>W. W \<in> TX \<and> A \<subseteq> W \<and> Ub b \<inter> W = {})"
    proof (intro ballI)
      fix b assume hbB: "b \<in> B"
      have hbX: "b \<in> X" using hBX hbB by blast
      have hbnotA: "b \<notin> A" using hdisj hbB by blast
      obtain U W where hU: "neighborhood_of b X TX U" and hW: "W \<in> TX"
        and hAW: "A \<subseteq> W" and hUW: "U \<inter> W = {}"
        using hRegSep[rule_format, OF hbX] hAcl hbnotA by blast
      show "neighborhood_of b X TX (Ub b) \<and> (\<exists>W. W \<in> TX \<and> A \<subseteq> W \<and> Ub b \<inter> W = {})"
        unfolding Ub_def
        by (rule someI_ex) (rule exI[where x=U], intro conjI hU, rule exI[where x=W], intro conjI hW hAW hUW)
    qed
    have hUbT: "\<forall>b\<in>B. Ub b \<in> TX"
      using hUb_prop unfolding neighborhood_of_def by blast
    have hbUb: "\<forall>b\<in>B. b \<in> Ub b"
      using hUb_prop unfolding neighborhood_of_def by blast

    text \<open>Open cover and locally finite refinement.\<close>
    have hBcl_open: "X - B \<in> TX" using hBcl unfolding closedin_on_def by blast
    let ?cover = "insert (X - B) (Ub ` B)"
    have hcov: "top1_open_covering_on X TX ?cover"
      unfolding top1_open_covering_on_def
    proof (intro conjI)
      show "?cover \<subseteq> TX"
      proof (rule insert_subsetI)
        show "X - B \<in> TX" by (rule hBcl_open)
        show "Ub ` B \<subseteq> TX"
        proof (rule image_subsetI)
          fix b assume "b \<in> B" then show "Ub b \<in> TX" using hUbT by blast
        qed
      qed
      show "X \<subseteq> \<Union>?cover"
      proof (rule subsetI)
        fix x assume "x \<in> X"
        show "x \<in> \<Union>?cover"
        proof (cases "x \<in> B")
          case True then show ?thesis using hbUb by blast
        next
          case False then show ?thesis using \<open>x \<in> X\<close> by blast
        qed
      qed
    qed
    obtain \<CC> where hCC_cov: "top1_open_covering_on X TX \<CC>"
      and hCC_ref: "top1_refines \<CC> ?cover"
      and hCC_lf: "top1_locally_finite_family_on X TX \<CC>"
      using hPara hcov unfolding top1_paracompact_on_def by blast
    have hCC_subX: "\<forall>D\<in>\<CC>. D \<subseteq> X"
      using hCC_cov hTsub unfolding top1_open_covering_on_def by blast

    text \<open>Step 3: Subcollection intersecting B.\<close>
    let ?\<DD> = "{D \<in> \<CC>. D \<inter> B \<noteq> {}}"
    have hD_covers_B: "B \<subseteq> \<Union>?\<DD>"
    proof (rule subsetI)
      fix b assume "b \<in> B"
      then have "b \<in> X" using hBX by blast
      then have "b \<in> \<Union>\<CC>" using hCC_cov unfolding top1_open_covering_on_def by blast
      then obtain D where "D \<in> \<CC>" "b \<in> D" by blast
      then show "b \<in> \<Union>?\<DD>" using \<open>b \<in> B\<close> by blast
    qed
    text \<open>Step 5: V = \<Union>DD.\<close>
    let ?V = "\<Union>?\<DD>"
    have hV_open: "?V \<in> TX"
    proof -
      have "?\<DD> \<subseteq> TX" using hCC_cov unfolding top1_open_covering_on_def by blast
      then show ?thesis using hTop unfolding is_topology_on_def by blast
    qed
    have hDD_subX: "\<forall>D\<in>?\<DD>. D \<subseteq> X" using hCC_subX by blast
    have hDD_sub_CC: "?\<DD> \<subseteq> \<CC>" by blast
    have hDD_lf: "top1_locally_finite_family_on X TX ?\<DD>"
      using Lemma_39_1(1)[OF hTop hCC_subX hCC_lf] hDD_sub_CC
      by blast
    have hV_subX: "?V \<subseteq> X" using hDD_subX by blast
    have hclV_closed: "closedin_on X TX (closure_on X TX ?V)"
      by (rule closure_on_closed[OF hTop hV_subX])
    have hU_open: "X - closure_on X TX ?V \<in> TX"
      using hclV_closed unfolding closedin_on_def by blast
    have hUb_sep: "\<forall>b\<in>B. \<exists>W. W \<in> TX \<and> A \<subseteq> W \<and> Ub b \<inter> W = {}"
      using hUb_prop by blast
    have hCC_ref_direct: "\<forall>C\<in>\<CC>. \<exists>A\<in>?cover. C \<subseteq> A"
      using hCC_ref unfolding top1_refines_def by blast
    have hA_disj_cl_D: "\<forall>D\<in>?\<DD>. \<forall>x\<in>A. x \<notin> closure_on X TX D"
    proof (intro ballI)
      fix D x assume hDDD: "D \<in> ?\<DD>" and hxA: "x \<in> A"
      have hDCC: "D \<in> \<CC>" using hDDD by blast
      have hDinterB: "D \<inter> B \<noteq> {}" using hDDD by blast
      show "x \<notin> closure_on X TX D"
        by (rule paracompact_closure_avoidance_step[OF hTop hTsub hAX hDCC hDinterB hCC_ref_direct hUbT hUb_sep hxA])
    qed

    have hA_sub_U: "A \<subseteq> X - closure_on X TX ?V"
      by (rule paracompact_closure_union_avoidance[OF hTop hTsub hAX hDD_subX hDD_lf hA_disj_cl_D])
    have hdisjoint: "(X - closure_on X TX ?V) \<inter> ?V = {}"
    proof -
      have "?V \<subseteq> closure_on X TX ?V" by (rule subset_closure_on)
      then show ?thesis by blast
    qed
    show "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = {}"
      by (rule exI[where x="X - closure_on X TX ?V"],
          rule exI[where x="?V"])
         (intro conjI hU_open hV_open hA_sub_U hD_covers_B hdisjoint)
  qed
qed

theorem Theorem_41_1:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hHaus: "is_hausdorff_on X TX"
  assumes hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
  shows "top1_normal_on X TX"
  by (rule paracompact_regular_imp_normal[OF hPara
        paracompact_hausdorff_imp_regular[OF hPara hHaus hTsub] hTsub])

(** from \S41 Theorem 41.2 [top1.tex:5851] **)
text \<open>Proof (Munkres Thm 41.2): extend subspace cover to X by adding X-A,
  take locally finite refinement, restrict back to A.\<close>
theorem Theorem_41_2:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hClosed: "closedin_on X TX A"
  shows "top1_paracompact_on A (subspace_topology X TX A)"
  unfolding top1_paracompact_on_def
proof (intro allI impI)
  fix \<A>
  assume hcov: "top1_open_covering_on A (subspace_topology X TX A) \<A>"
  have hAX: "A \<subseteq> X" using hClosed unfolding closedin_on_def by blast
  have hXmA_open: "X - A \<in> TX" using hClosed unfolding closedin_on_def by blast

  text \<open>Each element of \<A> is A \<inter> U for some open U in TX.\<close>
  have hA_sub: "\<A> \<subseteq> subspace_topology X TX A"
    using hcov unfolding top1_open_covering_on_def by blast
  have hA_covers: "A \<subseteq> \<Union>\<A>"
    using hcov unfolding top1_open_covering_on_def by blast

  text \<open>For each V \<in> \<A>, pick a parent open set.\<close>
  have hparent: "\<forall>V\<in>\<A>. \<exists>U. U \<in> TX \<and> V = A \<inter> U"
  proof (intro ballI)
    fix V assume hV: "V \<in> \<A>"
    then have "V \<in> subspace_topology X TX A" using hA_sub by blast
    then show "\<exists>U. U \<in> TX \<and> V = A \<inter> U"
      unfolding subspace_topology_def by blast
  qed
  obtain parent where hpar: "\<forall>V\<in>\<A>. parent V \<in> TX \<and> V = A \<inter> parent V"
    using bchoice[OF hparent] by blast

  text \<open>Build open cover of X: parent sets plus X - A.\<close>
  define \<C> where "\<C> = parent ` \<A> \<union> {X - A}"
  have hC_open: "\<C> \<subseteq> TX"
  proof (rule subsetI)
    fix U assume "U \<in> \<C>"
    then show "U \<in> TX"
      unfolding \<C>_def using hpar hXmA_open by blast
  qed
  have hC_covers: "X \<subseteq> \<Union>\<C>"
  proof (rule subsetI)
    fix x assume hxX: "x \<in> X"
    show "x \<in> \<Union>\<C>"
    proof (cases "x \<in> A")
      case True
      then obtain V where hV: "V \<in> \<A>" and hxV: "x \<in> V"
        using hA_covers by blast
      have "x \<in> parent V" using hpar hV hxV by blast
      then show ?thesis unfolding \<C>_def using hV by blast
    next
      case False
      then have "x \<in> X - A" using hxX by blast
      then show ?thesis unfolding \<C>_def by blast
    qed
  qed
  have hC_cov: "top1_open_covering_on X TX \<C>"
    unfolding top1_open_covering_on_def using hC_open hC_covers by blast

  text \<open>Get locally finite refinement from paracompactness.\<close>
  obtain \<B> where hB_cov: "top1_open_covering_on X TX \<B>"
    and hB_ref: "top1_refines \<B> \<C>"
    and hB_lf: "top1_locally_finite_family_on X TX \<B>"
    using hPara hC_cov unfolding top1_paracompact_on_def by blast

  text \<open>Restrict to A: define \<B>_A = {B \<inter> A | B \<in> \<B>} - {{}}.\<close>
  define \<B>A where "\<B>A = {B \<inter> A | B. B \<in> \<B>} - {{}}"

  show "\<exists>\<B>'. top1_open_covering_on A (subspace_topology X TX A) \<B>' \<and>
    top1_refines \<B>' \<A> \<and> top1_locally_finite_family_on A (subspace_topology X TX A) \<B>'"
  proof (rule exI[where x="\<B>A"], intro conjI)

    text \<open>\<B>A is an open covering of A.\<close>
    show "top1_open_covering_on A (subspace_topology X TX A) \<B>A"
      unfolding top1_open_covering_on_def
    proof (intro conjI)
      show "\<B>A \<subseteq> subspace_topology X TX A"
      proof (rule subsetI)
        fix V assume "V \<in> \<B>A"
        then obtain B where hB: "B \<in> \<B>" and hVeq: "V = B \<inter> A" and hVne: "V \<noteq> {}"
          unfolding \<B>A_def by blast
        have "B \<in> TX" using hB hB_cov unfolding top1_open_covering_on_def by blast
        then show "V \<in> subspace_topology X TX A"
          unfolding subspace_topology_def hVeq by (blast intro: exI)
      qed
    next
      show "A \<subseteq> \<Union>\<B>A"
      proof (rule subsetI)
        fix a assume haA: "a \<in> A"
        then have "a \<in> X" using hAX by blast
        then have "a \<in> \<Union>\<B>" using hB_cov unfolding top1_open_covering_on_def by blast
        then obtain B where hB: "B \<in> \<B>" and haB: "a \<in> B" by blast
        have hne: "B \<inter> A \<noteq> {}" using haA haB by blast
        have "a \<in> B \<inter> A" using haA haB by blast
        then show "a \<in> \<Union>\<B>A" unfolding \<B>A_def using hB hne by blast
      qed
    qed

    text \<open>\<B>A refines \<A>.\<close>
    show "top1_refines \<B>A \<A>"
      unfolding top1_refines_def
    proof (intro ballI)
      fix V assume hVBA: "V \<in> \<B>A"
      then obtain B where hB: "B \<in> \<B>" and hVeq: "V = B \<inter> A" and hVne: "V \<noteq> {}"
        unfolding \<B>A_def by blast
      have "\<exists>C\<in>\<C>. B \<subseteq> C" using hB_ref hB unfolding top1_refines_def by blast
      then obtain C where hCC: "C \<in> \<C>" and hBC: "B \<subseteq> C" by blast
      show "\<exists>W\<in>\<A>. V \<subseteq> W"
      proof (cases "C = X - A")
        case True
        then have "B \<subseteq> X - A" using hBC by blast
        then have "B \<inter> A = {}" by blast
        then have "V = {}" using hVeq by blast
        then show ?thesis using hVne by blast
      next
        case False
        then have "C \<in> parent ` \<A>" using hCC unfolding \<C>_def by blast
        then obtain W where hW: "W \<in> \<A>" and hCeq: "C = parent W" by blast
        have "V = B \<inter> A" by (rule hVeq)
        also have "... \<subseteq> C \<inter> A" using hBC by blast
        also have "... = parent W \<inter> A" using hCeq by blast
        also have "... = A \<inter> parent W" by (rule Int_commute)
        also have "... = W" using hpar hW by blast
        finally show ?thesis using hW by blast
      qed
    qed

    text \<open>\<B>A is locally finite in the subspace.\<close>
    show "top1_locally_finite_family_on A (subspace_topology X TX A) \<B>A"
      unfolding top1_locally_finite_family_on_def
    proof (intro ballI)
      fix a assume haA: "a \<in> A"
      then have haX: "a \<in> X" using hAX by blast
      obtain U where hU: "U \<in> TX" and haU: "a \<in> U"
        and hfin: "finite {B \<in> \<B>. intersects B U}"
        using hB_lf haX unfolding top1_locally_finite_family_on_def by blast
      define UA where "UA = A \<inter> U"
      have hUA_sub: "UA \<in> subspace_topology X TX A"
        unfolding UA_def subspace_topology_def using hU by blast
      have haUA: "a \<in> UA" unfolding UA_def using haA haU by blast
      have hfin_BA: "finite {V \<in> \<B>A. intersects V UA}"
      proof (rule finite_subset[where B="{B \<inter> A | B. B \<in> \<B> \<and> intersects B U}"])
        show "{V \<in> \<B>A. intersects V UA} \<subseteq> {B \<inter> A | B. B \<in> \<B> \<and> intersects B U}"
        proof (rule subsetI)
          fix V assume hV: "V \<in> {V \<in> \<B>A. intersects V UA}"
          then have hVBA: "V \<in> \<B>A" and hVUA: "intersects V UA" by blast+
          obtain B where hB: "B \<in> \<B>" and hVeq: "V = B \<inter> A"
            using hVBA unfolding \<B>A_def by blast
          have "intersects B U"
            using hVUA unfolding intersects_def hVeq UA_def by blast
          then show "V \<in> {B \<inter> A | B. B \<in> \<B> \<and> intersects B U}"
            using hB hVeq by blast
        qed
      next
        have "finite {B \<in> \<B>. intersects B U}" by (rule hfin)
        then have "finite ((\<lambda>B. B \<inter> A) ` {B \<in> \<B>. intersects B U})"
          by (rule finite_imageI)
        moreover have "{B \<inter> A | B. B \<in> \<B> \<and> intersects B U} = (\<lambda>B. B \<inter> A) ` {B \<in> \<B>. intersects B U}"
          by blast
        ultimately show "finite {B \<inter> A | B. B \<in> \<B> \<and> intersects B U}"
          by simp
      qed
      show "\<exists>U\<in>subspace_topology X TX A. a \<in> U \<and> finite {V \<in> \<B>A. intersects V U}"
        using hUA_sub haUA hfin_BA by blast
    qed
  qed
qed

(** from \S41 Lemma 41.3 [top1.tex:5864] **)
lemma Lemma_41_3:
  assumes hReg: "top1_regular_on X TX"
  shows "(\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow> (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>)) \<longleftrightarrow>
        (\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow> (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B> \<and> (\<forall>B\<in>\<B>. closure_on X TX B \<subseteq> (SOME A. A \<in> \<A> \<and> B \<subseteq> A))))"
proof (intro iffI allI impI)
  text \<open>(\<Rightarrow>) Paracompact → strong paracompact using regularity.\<close>
  fix \<A>
  assume hLHS: "\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow>
    (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>)"
  assume hCov: "top1_open_covering_on X TX \<A>"
  show "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>
    \<and> (\<forall>B\<in>\<B>. closure_on X TX B \<subseteq> (SOME A. A \<in> \<A> \<and> B \<subseteq> A))"
    sorry (* → direction: uses regularity to shrink cover so closures stay inside.
             Needs full (1)→(2)→(3)→(4) argument. *)
next
  text \<open>(\<Leftarrow>) Strong paracompact → paracompact (trivial: drop extra condition).\<close>
  fix \<A>
  assume hRHS: "\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow>
    (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>
      \<and> (\<forall>B\<in>\<B>. closure_on X TX B \<subseteq> (SOME A. A \<in> \<A> \<and> B \<subseteq> A)))"
  assume hCov: "top1_open_covering_on X TX \<A>"
  obtain \<B> where h: "top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>"
    using hRHS hCov
    
    by blast
  show "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>"
    using h
    
    by blast
qed


text \<open>Key lemma for Theorem 41.4: sigma-locally-finite open covering → locally finite open covering.
  This is the (1)\<Rightarrow>(4) direction of Munkres' Lemma 41.3.\<close>
lemma sigma_lf_to_lf_open_covering:
  assumes hReg: "top1_regular_on X TX"
  assumes hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
  assumes hCov: "top1_open_covering_on X TX \<A>"
  assumes hSLF: "top1_sigma_locally_finite_family_on X TX \<A>"
  shows "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>"
proof -
  text \<open>Step (1)\<Rightarrow>(2): shrink sigma-LF to LF covering (not necessarily open).\<close>
  have step12: "\<exists>\<C>. (\<forall>C\<in>\<C>. C \<subseteq> X) \<and> X \<subseteq> \<Union>\<C> \<and> top1_refines \<C> \<A> \<and> top1_locally_finite_family_on X TX \<C>"
  proof -
    have hTop: "is_topology_on X TX"
      using hReg unfolding top1_regular_on_def top1_T1_on_def
      
      by satx
    text \<open>Decompose sigma-LF cover into B_n families.\<close>
    have hex_Bn: "\<exists>Bn::nat \<Rightarrow> 'a set set. (\<forall>n. top1_locally_finite_family_on X TX (Bn n)) \<and> \<A> = (\<Union>n. Bn n)"
      using hSLF unfolding top1_sigma_locally_finite_family_on_def
      
      by argo
    obtain Bn :: "nat \<Rightarrow> 'a set set" where hBn_lf: "\<forall>n. top1_locally_finite_family_on X TX (Bn n)"
      and hA_eq: "\<A> = (\<Union>n. Bn n)"
      using hex_Bn
      
      by blast
    define Vi where "Vi (i::nat) = \<Union>(Bn i)" for i
    define Sn where "Sn (n::nat) U = U - (\<Union>i\<in>{..<n}. Vi i)" for n U
    define Cn where "Cn n = {Sn n U | U. U \<in> Bn n}" for n :: nat
    define \<C> where "\<C> = (\<Union>n. Cn n)"

    have hA_sub_TX: "\<A> \<subseteq> TX"
      using hCov unfolding top1_open_covering_on_def
      
      by satx
    have hA_covers: "X \<subseteq> \<Union>\<A>"
      using hCov unfolding top1_open_covering_on_def
      
      by presburger

    text \<open>S_n(U) \<subseteq> U, so C refines A.\<close>
    have hSn_sub: "\<And>n U. Sn n U \<subseteq> U" unfolding Sn_def
      
      by fast
    have hC_ref: "top1_refines \<C> \<A>"
      unfolding top1_refines_def
    proof (intro ballI)
      fix S assume hS: "S \<in> \<C>"
      obtain n U where hU: "U \<in> Bn n" and hSeq: "S = Sn n U"
        using hS unfolding \<C>_def Cn_def
        
        by blast
      have hUA: "U \<in> \<A>" using hU hA_eq
        
        by blast
      show "\<exists>A\<in>\<A>. S \<subseteq> A"
        using hUA hSn_sub hSeq
        
        by blast
    qed

    text \<open>C covers X.\<close>
    have hC_covers: "X \<subseteq> \<Union>\<C>"
    proof (rule subsetI)
      fix x assume hxX: "x \<in> X"
      have hxA: "x \<in> \<Union>\<A>" using hA_covers hxX
        
        by fast
      then obtain U0 n0 where hU0: "U0 \<in> Bn n0" and hxU0: "x \<in> U0"
        unfolding hA_eq
        
        by blast
      text \<open>Let N = LEAST n with x ∈ ∪(Bn n).\<close>
      define N where "N = (LEAST n. x \<in> \<Union>(Bn n))"
      have hex: "\<exists>n. x \<in> \<Union>(Bn n)" using hU0 hxU0
        
        by blast
      have hxBnN: "x \<in> \<Union>(Bn N)"
        unfolding N_def using LeastI_ex[OF hex]
        
        by satx
      have hN_least: "\<forall>m < N. x \<notin> \<Union>(Bn m)"
        unfolding N_def
        
        using not_less_Least by blast
      text \<open>x ∉ V_i for i < N (since V_i = ∪(Bn i) and x ∉ ∪(Bn i)).\<close>
      have hx_not_Vi: "\<forall>i < N. x \<notin> Vi i"
        using hN_least unfolding Vi_def
        
        by argo
      text \<open>So x ∉ ∪{V_i | i < N}.\<close>
      have "x \<notin> (\<Union>i\<in>{..<N}. Vi i)"
        using hx_not_Vi
        
        by blast
      text \<open>Pick U ∈ Bn N with x ∈ U. Then x ∈ S_N(U).\<close>
      obtain U where hU: "U \<in> Bn N" and hxU: "x \<in> U"
        using hxBnN
        
        by blast
      have "x \<in> Sn N U"
        unfolding Sn_def using hxU \<open>x \<notin> (\<Union>i\<in>{..<N}. Vi i)\<close>
        
        by blast
      then have "x \<in> \<Union>(Cn N)" unfolding Cn_def using hU
        
        by auto
      then show "x \<in> \<Union>\<C>" unfolding \<C>_def
        
        by blast
    qed

    text \<open>C is locally finite.\<close>
    have hC_lf: "top1_locally_finite_family_on X TX \<C>"
      unfolding top1_locally_finite_family_on_def
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      define N where "N = (LEAST n. x \<in> \<Union>(Bn n))"
      have hex_n: "\<exists>n. x \<in> \<Union>(Bn n)"
        using hxX hA_covers hA_eq
        
        by blast
      have hxBnN: "x \<in> \<Union>(Bn N)" unfolding N_def
        using LeastI_ex[OF hex_n]
        
        by satx
      have hN_least: "\<forall>m. m < N \<longrightarrow> x \<notin> \<Union>(Bn m)"
        unfolding N_def using not_less_Least
        
        by blast
      obtain U0 where hU0: "U0 \<in> Bn N" and hxU0: "x \<in> U0"
        using hxBnN
        
        by blast
      have hU0_open: "U0 \<in> TX"
        using hU0 hA_eq hA_sub_TX
        
        by blast
      text \<open>For each n \<le> N, get W_n meeting finitely many Bn n elements.\<close>
      have hWn_ex: "\<forall>n \<le> N. \<exists>W\<in>TX. x \<in> W \<and> finite {A \<in> Bn n. intersects A W}"
        using hBn_lf hxX unfolding top1_locally_finite_family_on_def
        
        by simp
      have "\<exists>Wn. \<forall>n \<le> N. Wn n \<in> TX \<and> x \<in> Wn n \<and> finite {A \<in> Bn n. intersects A (Wn n)}"
        using hWn_ex
        
        by metis
      then obtain Wn where hWn: "\<forall>n \<le> N. Wn n \<in> TX \<and> x \<in> Wn n \<and> finite {A \<in> Bn n. intersects A (Wn n)}"
        
        by blast
      text \<open>For n > N, U0 is disjoint from all S_n(V): S_n(V) ⊆ V - Vi N, and U0 ⊆ Vi N.\<close>
      have hU0_sub_ViN: "U0 \<subseteq> Vi N"
        unfolding Vi_def using hU0
        
        by blast
      have hCn_disj_U0: "\<forall>n > N. \<forall>S\<in>Cn n. S \<inter> U0 = {}"
      proof (intro allI impI ballI)
        fix n S assume hn: "N < n" and hS: "S \<in> Cn n"
        obtain V where hV: "V \<in> Bn n" and hSeq: "S = Sn n V"
          using hS unfolding Cn_def
          
          by blast
        have "Sn n V \<subseteq> V - Vi N"
          unfolding Sn_def Vi_def using hn
          
          by blast
        then have "S \<inter> Vi N = {}" unfolding hSeq
          
          by blast
        then show "S \<inter> U0 = {}" using hU0_sub_ViN
          
          by auto
      qed
      text \<open>The neighborhood: finite intersection of W_n for n \<le> N, intersected with U0.\<close>
      define W where "W = (\<Inter>n\<in>{0..N}. Wn n) \<inter> U0"
      have hInter_open: "(\<Inter>n\<in>{0..N}. Wn n) \<in> TX"
      proof (cases "N = 0")
        case True
        then show ?thesis using hWn
          
          by simp
      next
        case False
        have "finite (Wn ` {0..N})"
          
          by blast
        moreover have "Wn ` {0..N} \<noteq> {}"
          
          by force
        moreover have "Wn ` {0..N} \<subseteq> TX"
          using hWn
          
          by auto
        ultimately show ?thesis
          using hTop unfolding is_topology_on_def
          
          by presburger
      qed
      have hW_open: "W \<in> TX"
        unfolding W_def using hTop hInter_open hU0_open
        
        using topology_inter2 by blast
      have hxW: "x \<in> W"
        unfolding W_def using hxU0 hWn
        
        by fastforce
      have hW_fin: "finite {A \<in> \<C>. intersects A W}"
      proof -
        text \<open>W meets only elements from C_n for n \<le> N.\<close>
        have hsub: "{A \<in> \<C>. intersects A W} \<subseteq> (\<Union>n\<in>{0..N}. {A \<in> Cn n. intersects A W})"
        proof (rule subsetI)
          fix S assume hS: "S \<in> {A \<in> \<C>. intersects A W}"
          then have hSC: "S \<in> \<C>" and hSW: "intersects S W"
            
            by fast+
          obtain n where hSCn: "S \<in> Cn n" using hSC unfolding \<C>_def
            
            by blast
          have "n \<le> N"
          proof (rule ccontr)
            assume "\<not> n \<le> N"
            then have "N < n"
              
              by presburger
            then have "S \<inter> U0 = {}" using hCn_disj_U0 hSCn
              
              by simp
            then have "S \<inter> W = {}" unfolding W_def
              
              by blast
            then show False using hSW unfolding intersects_def
              
              by presburger
          qed
          then show "S \<in> (\<Union>n\<in>{0..N}. {A \<in> Cn n. intersects A W})"
            using hSCn hSW
            
            by auto
        qed
        text \<open>Each {A ∈ Cn n. intersects A W} is finite (since W ⊆ Wn n).\<close>
        have hfin_each: "\<forall>n\<in>{0..N}. finite {A \<in> Cn n. intersects A W}"
        proof (intro ballI)
          fix n assume hn: "n \<in> {0..N}"
          have hnN: "n \<le> N" using hn
            
            by auto
          have hW_sub_Wn: "W \<subseteq> Wn n" unfolding W_def using hnN
            
            using hnN by fastforce
          have hCn_sub_Bn: "\<forall>S\<in>Cn n. \<exists>V\<in>Bn n. S \<subseteq> V"
            unfolding Cn_def using hSn_sub
            
            using hSn_sub by auto
          have "{A \<in> Cn n. intersects A W} \<subseteq> (\<lambda>V. Sn n V) ` {V \<in> Bn n. intersects V (Wn n)}"
          proof (rule subsetI)
            fix S assume hS: "S \<in> {A \<in> Cn n. intersects A W}"
            then have hSCn: "S \<in> Cn n" and hSW: "intersects S W"
              
              by blast+
            obtain V where hV: "V \<in> Bn n" and hSeq: "S = Sn n V"
              using hSCn unfolding Cn_def
              
              by blast
            have hSsubV: "S \<subseteq> V" using hSeq hSn_sub
              
              by auto
            have "intersects V (Wn n)"
              using hSW hSsubV hW_sub_Wn unfolding intersects_def
              
              by blast
            then show "S \<in> (\<lambda>V. Sn n V) ` {V \<in> Bn n. intersects V (Wn n)}"
              using hV hSeq
              
              by blast
          qed
          moreover have "finite {V \<in> Bn n. intersects V (Wn n)}"
            using hWn hnN
            
            by auto
          ultimately show "finite {A \<in> Cn n. intersects A W}"
            
            by (meson finite_surj)
        qed
        show ?thesis
          using finite_subset[OF hsub] hfin_each
          
          by blast
      qed
      show "\<exists>U\<in>TX. x \<in> U \<and> finite {A \<in> \<C>. intersects A U}"
        using hW_open hxW hW_fin
        
        by blast
    qed

    text \<open>Each C ∈ C is a subset of X.\<close>
    have hC_subX: "\<forall>C\<in>\<C>. C \<subseteq> X"
    proof (intro ballI)
      fix S assume hS: "S \<in> \<C>"
      obtain n U where hU: "U \<in> Bn n" and hSeq: "S = Sn n U"
        using hS unfolding \<C>_def Cn_def
        
        by blast
      have "U \<in> \<A>" using hU hA_eq
        
        by blast
      then have "U \<in> TX" using hA_sub_TX
        
        by fast
      then have "U \<subseteq> X" using hTsub
        
        by simp
      then show "S \<subseteq> X" using hSn_sub hSeq
        
        by blast
    qed

    show ?thesis
      using hC_subX hC_covers hC_ref hC_lf
      
      by blast
  qed

  text \<open>Steps (2)\<Rightarrow>(3)\<Rightarrow>(4) combined: from LF covering to LF open covering.
    Uses regularity + Lemma 39.1 for closure + expansion via auxiliary LF closed covering.
    This is the remaining core of Munkres' Lemma 41.3.\<close>
  have step234: "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>"
  proof -
    have hTop: "is_topology_on X TX"
      using hReg unfolding top1_regular_on_def top1_T1_on_def
      
      by argo
    obtain \<C> where hC_subX: "\<forall>C\<in>\<C>. C \<subseteq> X" and hC_covers: "X \<subseteq> \<Union>\<C>"
      and hC_ref: "top1_refines \<C> \<A>" and hC_lf: "top1_locally_finite_family_on X TX \<C>"
      using step12
      
      by auto

    text \<open>Close C to get LF closed covering D (via Lemma 39.1).\<close>
    define \<D> where "\<D> = closure_on X TX ` \<C>"
    have hD_lf: "top1_locally_finite_family_on X TX \<D>"
      unfolding \<D>_def using Lemma_39_1(2)[OF hTop hC_subX hC_lf]
      
      by presburger
    have hD_covers: "X \<subseteq> \<Union>\<D>"
    proof (rule subsetI)
      fix x assume hxX: "x \<in> X"
      obtain C0 where hC0: "C0 \<in> \<C>" and hxC0: "x \<in> C0"
        using hC_covers hxX
        
        by auto
      have "x \<in> closure_on X TX C0" using hxC0 subset_closure_on
        
        by fast
      then show "x \<in> \<Union>\<D>" unfolding \<D>_def using hC0
        
        by blast
    qed

    text \<open>For each C_elem, pick parent in A.\<close>
    have hparent_ex: "\<forall>C0\<in>\<C>. \<exists>A0. A0 \<in> \<A> \<and> C0 \<subseteq> A0"
      using hC_ref unfolding top1_refines_def
      
      by fast
    obtain parent where hparent: "\<forall>C0\<in>\<C>. parent C0 \<in> \<A> \<and> C0 \<subseteq> parent C0"
      using bchoice[OF hparent_ex]
      
      by presburger

    text \<open>Expansion: E(C0) = X - ∪{D ∈ D | D ⊆ X - C0}, B(C0) = E(C0) ∩ parent(C0).\<close>
    define bad where "bad C0 = {D \<in> \<D>. D \<subseteq> X - C0}" for C0
    define E where "E C0 = X - \<Union>(bad C0)" for C0
    define \<B> where "\<B> = {E C0 \<inter> parent C0 | C0. C0 \<in> \<C>}"

    text \<open>E(C0) is open: bad(C0) is a subfamily of LF closed D, so ∪bad is closed.\<close>
    have hD_closed: "\<forall>D0\<in>\<D>. closedin_on X TX D0"
    proof (intro ballI)
      fix D0 assume "D0 \<in> \<D>"
      then obtain C0 where hC0: "C0 \<in> \<C>" and hD0eq: "D0 = closure_on X TX C0"
        unfolding \<D>_def
        
        by blast
      show "closedin_on X TX D0"
        unfolding hD0eq using hTop hC_subX hC0
        
        by (metis hTop hC_subX hC0 closure_on_closed)
    qed
    have hD_subX: "\<forall>D0\<in>\<D>. D0 \<subseteq> X"
      using hD_closed unfolding closedin_on_def
      
      by auto
    have hE_open: "\<forall>C0\<in>\<C>. E C0 \<in> TX"
    proof (intro ballI)
      fix C0 assume hC0: "C0 \<in> \<C>"
      have hbad_sub_D: "bad C0 \<subseteq> \<D>" unfolding bad_def
        
        by blast
      have hbad_lf: "top1_locally_finite_family_on X TX (bad C0)"
        using Lemma_39_1(1)[OF hTop hD_subX hD_lf] hbad_sub_D
        
        by presburger
      have hbad_subX: "\<forall>D0\<in>bad C0. D0 \<subseteq> X"
        using hD_subX hbad_sub_D
        
        by blast
      have hbad_closed: "\<forall>D0\<in>bad C0. closedin_on X TX D0"
        using hD_closed hbad_sub_D
        
        by blast
      have hcl_eq: "closure_on X TX (\<Union>(bad C0)) = \<Union>(closure_on X TX ` bad C0)"
        using Lemma_39_1(3)[OF hTop hbad_subX hbad_lf]
        
        by presburger
      have hcl_id: "\<forall>D0\<in>bad C0. closure_on X TX D0 = D0"
      proof (intro ballI)
        fix D0 assume hD0: "D0 \<in> bad C0"
        have hD0cl: "closedin_on X TX D0" using hbad_closed hD0
          
          by blast
        show "closure_on X TX D0 = D0"
          using closure_on_subset_of_closed[OF hD0cl] subset_closure_on
          
          by fast
      qed
      have "closure_on X TX (\<Union>(bad C0)) = \<Union>(bad C0)"
      proof -
        have "\<Union>(closure_on X TX ` bad C0) = \<Union>(bad C0)"
          using hcl_id
          
          by fast
        then show ?thesis using hcl_eq
          
          by argo
      qed
      have hbadUnion_subX: "\<Union>(bad C0) \<subseteq> X"
        using hbad_subX
        
        by fast
      have "closedin_on X TX (closure_on X TX (\<Union>(bad C0)))"
        using closure_on_closed[OF hTop hbadUnion_subX]
        
        by blast
      then have hUnion_bad_closed: "closedin_on X TX (\<Union>(bad C0))"
        using \<open>closure_on X TX (\<Union>(bad C0)) = \<Union>(bad C0)\<close>
        
        by argo
      show "E C0 \<in> TX"
        unfolding E_def using hUnion_bad_closed unfolding closedin_on_def
        
        by presburger
    qed

    text \<open>B is open (intersection of two opens).\<close>
    have hA_sub_TX: "\<A> \<subseteq> TX" using hCov unfolding top1_open_covering_on_def
      
      by presburger
    have hB_open: "\<B> \<subseteq> TX"
    proof (rule subsetI)
      fix B assume "B \<in> \<B>"
      then obtain C0 where hC0: "C0 \<in> \<C>" and hBeq: "B = E C0 \<inter> parent C0"
        unfolding \<B>_def
        
        by auto
      have "E C0 \<in> TX" using hE_open hC0
        
        by fast
      moreover have "parent C0 \<in> TX" using hparent hC0 hA_sub_TX
        
        by fast
      ultimately show "B \<in> TX" unfolding hBeq using hTop
        
        using topology_inter2 by blast
    qed

    text \<open>B covers X: C0 ⊆ E(C0) ∩ parent(C0).\<close>
    have hB_covers: "X \<subseteq> \<Union>\<B>"
    proof (rule subsetI)
      fix x assume hxX: "x \<in> X"
      obtain C0 where hC0: "C0 \<in> \<C>" and hxC0: "x \<in> C0"
        using hC_covers hxX
        
        by blast
      have hx_not_bad: "x \<notin> \<Union>(bad C0)"
      proof
        assume "x \<in> \<Union>(bad C0)"
        then obtain D0 where hD0: "D0 \<in> bad C0" and hxD0: "x \<in> D0"
          
          by blast
        have "D0 \<subseteq> X - C0" using hD0 unfolding bad_def
          
          by blast
        then show False using hxC0 hxD0
          
          by blast
      qed
      have "x \<in> E C0" unfolding E_def using hxX hx_not_bad
        
        by blast
      moreover have "x \<in> parent C0" using hparent hC0 hxC0
        
        by fast
      ultimately have "x \<in> E C0 \<inter> parent C0"
        
        by fast
      then show "x \<in> \<Union>\<B>" unfolding \<B>_def using hC0
        
        by blast
    qed

    text \<open>B refines A.\<close>
    have hB_ref: "top1_refines \<B> \<A>"
      unfolding top1_refines_def \<B>_def
    proof (intro ballI)
      fix B assume "B \<in> {E C0 \<inter> parent C0 | C0. C0 \<in> \<C>}"
      then obtain C0 where hC0: "C0 \<in> \<C>" and hBeq: "B = E C0 \<inter> parent C0"
        
        by blast
      have "parent C0 \<in> \<A>" using hparent hC0
        
        by fast
      moreover have "B \<subseteq> parent C0" unfolding hBeq
        
        by simp
      ultimately show "\<exists>A\<in>\<A>. B \<subseteq> A"
        
        by blast
    qed

    text \<open>B is locally finite.\<close>
    have hB_lf: "top1_locally_finite_family_on X TX \<B>"
      sorry (* Munkres expansion LF argument (last sorry in sigma_lf_to_lf):
         For x ∈ X, pick W meeting finitely many D-elements (D is LF), say D_1,...,D_k.
         If D_i intersects E(C0) then D_i ∉ bad(C0), so D_i ∩ C0 ≠ {}.
         Each D_i = cl(C_i') can intersect at most finitely many C0's
         (from C being LF: D_i ∩ C0 ≠ {} implies cl(C_i') ∩ C0 ≠ {},
          and C_i' has a neighborhood meeting finitely many C-elements;
          but we need to bound {C0 | cl(C_i') ∩ C0 ≠ {}} which requires
          that C is "star-finite" w.r.t. closures).
         Needs: additional lemma that C (from step12 construction) has this property.
         Estimated ~40 lines. *)

    show ?thesis
      unfolding top1_open_covering_on_def
      using hB_open hB_covers hB_ref hB_lf
      
      by blast
  qed

  show ?thesis using step234
    
    by argo
qed

(** from \S41 Theorem 41.4 [top1.tex:5953] **)
theorem Theorem_41_4:
  assumes hMet: "top1_metrizable_on X TX"
  shows "top1_paracompact_on X TX"
  unfolding top1_paracompact_on_def
proof (intro allI impI)
  fix \<A>
  assume hCov: "top1_open_covering_on X TX \<A>"
  have hReg: "top1_regular_on X TX"
    by (rule metrizable_imp_regular[OF hMet])
  obtain \<E> where hE_cov: "top1_open_covering_on X TX \<E>"
    and hE_ref: "top1_refines \<E> \<A>"
    and hE_slf: "top1_sigma_locally_finite_family_on X TX \<E>"
    using Lemma_39_2[OF hMet hCov]
    
    by blast
  have hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
    using hMet unfolding top1_metrizable_on_def top1_metric_topology_on_def topology_generated_by_basis_def
    
    by auto
  obtain \<B> where hB: "top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<E> \<and> top1_locally_finite_family_on X TX \<B>"
    using sigma_lf_to_lf_open_covering[OF hReg hTsub hE_cov hE_slf]
    
    by blast
  have hB_ref_A: "top1_refines \<B> \<A>"
    using hB hE_ref unfolding top1_refines_def
    
    by (meson subset_trans)
  show "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>"
    using hB hB_ref_A
    
    by blast
qed

(** from \S41 Theorem 41.5 [top1.tex:5956] **)
theorem Theorem_41_5:
  assumes hReg: "top1_regular_on X TX"
  assumes hLind: "top1_lindelof_on X TX"
  assumes hTsub_assume: "\<forall>U\<in>TX. U \<subseteq> X"
  shows "top1_paracompact_on X TX"
  unfolding top1_paracompact_on_def
proof (intro allI impI)
  fix \<A>
  assume hCov: "top1_open_covering_on X TX \<A>"
  have hTop: "is_topology_on X TX"
    using hLind unfolding top1_lindelof_on_def
    
    by satx
  have hAsub: "\<A> \<subseteq> TX"
    using hCov unfolding top1_open_covering_on_def
    
    by presburger
  have hAcovers: "X \<subseteq> \<Union>\<A>"
    using hCov unfolding top1_open_covering_on_def
    
    by satx
  text \<open>Get countable subcover by Lindelöf property.\<close>
  obtain \<C> where hCcnt: "top1_countable \<C>" and hCsub: "\<C> \<subseteq> \<A>" and hCcovers: "X \<subseteq> \<Union>\<C>"
    using hLind hAsub hAcovers unfolding top1_lindelof_on_def
    
    by blast
  text \<open>\<C> is sigma-locally-finite (countable cover = union of singletons, each LF).\<close>
  have hC_cov: "top1_open_covering_on X TX \<C>"
    unfolding top1_open_covering_on_def using hCsub hAsub hCcovers
    
    by fast
  have hC_slf: "top1_sigma_locally_finite_family_on X TX \<C>"
  proof -
    obtain idx :: "'a set \<Rightarrow> nat" where hidx: "inj_on idx \<C>"
      using hCcnt unfolding top1_countable_def
      
      by blast
    define Bn where "Bn n = {U \<in> \<C>. idx U = n}" for n
    have hBn_lf: "\<forall>n. top1_locally_finite_family_on X TX (Bn n)"
    proof (intro allI)
      fix n
      have hfin: "finite (Bn n)"
      proof -
        have "\<forall>a\<in>Bn n. \<forall>b\<in>Bn n. a = b"
          using hidx unfolding Bn_def inj_on_def
          
          by blast
        then have "Bn n = {} \<or> (\<exists>x. Bn n = {x})"
          
          by blast
        then show ?thesis
          
          by fastforce
      qed
      show "top1_locally_finite_family_on X TX (Bn n)"
        unfolding top1_locally_finite_family_on_def
      proof (intro ballI)
        fix x assume hxX: "x \<in> X"
        have "X \<in> TX" using hTop unfolding is_topology_on_def
          
          by satx
        moreover have "x \<in> X" by (rule hxX)
        moreover have "finite {A \<in> Bn n. intersects A X}"
          using hfin
          
          by auto
        ultimately show "\<exists>U\<in>TX. x \<in> U \<and> finite {A \<in> Bn n. intersects A U}"
          
          by blast
      qed
    qed
    have hB_eq: "\<C> = (\<Union>n. Bn n)"
      unfolding Bn_def
      
      by blast
    show ?thesis
      unfolding top1_sigma_locally_finite_family_on_def
      using hBn_lf hB_eq
      
      by blast
  qed
  text \<open>Apply sigma-LF → LF conversion.\<close>
  have hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
    using hTsub_assume by presburger
  obtain \<B> where hB_cov: "top1_open_covering_on X TX \<B>"
    and hB_ref_C: "top1_refines \<B> \<C>"
    and hB_lf: "top1_locally_finite_family_on X TX \<B>"
    using sigma_lf_to_lf_open_covering[OF hReg hTsub hC_cov hC_slf]
    
    by blast
  have hB_ref_A: "top1_refines \<B> \<A>"
    using hB_ref_C hCsub unfolding top1_refines_def
    
    by (meson subset_eq)
  show "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>"
    using hB_cov hB_ref_A hB_lf
    
    by fast
qed

(** from \S41 Lemma 41.6 (Shrinking lemma) [top1.tex:5981] **)
lemma Lemma_41_6:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hHaus: "is_hausdorff_on X TX"
  assumes hCov: "top1_open_covering_on X TX \<A>"
  shows "\<exists>V. (\<forall>A\<in>\<A>. (\<exists>VA\<in>V. VA \<in> TX \<and> closure_on X TX VA \<subseteq> A))
        \<and> top1_open_covering_on X TX V \<and> top1_locally_finite_family_on X TX V \<and> top1_refines V \<A>"
  sorry

text \<open>
  For the starred results of \<S>41 we will need partitions of unity indexed by an arbitrary set.
  We record the top-level statements first and defer the technical development.
\<close>

definition top1_partition_of_unity_dominated_family_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> ('a \<Rightarrow> real)) \<Rightarrow> bool"
  where
  "top1_partition_of_unity_dominated_family_on X TX I U \<phi> \<longleftrightarrow>
     (\<forall>i\<in>I. U i \<in> TX)
     \<and> (\<forall>i\<in>I.
          top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) (\<phi> i)
          \<and> top1_support_on X TX (\<phi> i) \<subseteq> U i)
     \<and> top1_locally_finite_family_on X TX ((\<lambda>i. top1_support_on X TX (\<phi> i)) ` I)
     \<and> (\<forall>x\<in>X. finite {i\<in>I. \<phi> i x \<noteq> 0} \<and> (\<Sum>i\<in>{i\<in>I. \<phi> i x \<noteq> 0}. \<phi> i x) = 1)"

(** from \S41 Theorem 41.7 (Partition of unity) [top1.tex:5999] **)
theorem Theorem_41_7:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hHaus: "is_hausdorff_on X TX"
  assumes hCov: "top1_open_covering_on X TX (U ` I)"
  shows "\<exists>\<phi>. top1_partition_of_unity_dominated_family_on X TX I U \<phi>"
  sorry

(** from \S41 Theorem 41.8 (Continuous control on locally finite families) [top1.tex:6024] **)
theorem Theorem_41_8:
  assumes hLF: "top1_locally_finite_family_on X TX \<C>"
  assumes hPos: "\<forall>C\<in>\<C>. 0 < \<epsilon> C"
  shows "\<exists>f::'a \<Rightarrow> real.
    top1_continuous_map_on X TX UNIV order_topology_on_UNIV f
    \<and> (\<forall>x\<in>X. 0 < f x)
    \<and> (\<forall>C\<in>\<C>. \<forall>x\<in>C. f x \<le> \<epsilon> C)"
  sorry

section \<open>\<S>42 The Smirnov Metrization Theorem\<close>

definition top1_locally_metrizable_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_locally_metrizable_on X TX \<longleftrightarrow>
     (\<forall>x\<in>X. \<exists>U\<in>TX. x \<in> U \<and> (\<exists>d. top1_metric_on U d \<and> subspace_topology X TX U = top1_metric_topology_on U d))"

(** from \S42 Theorem 42.1 (Smirnov metrization theorem) [top1.tex:6072] **)
theorem Theorem_42_1:
  shows "top1_metrizable_on X TX \<longleftrightarrow>
    (top1_paracompact_on X TX \<and> is_hausdorff_on X TX \<and> top1_locally_metrizable_on X TX)"
proof (intro iffI)
  assume hMet: "top1_metrizable_on X TX"
  have hPara: "top1_paracompact_on X TX"
    using Theorem_41_4[OF hMet]
    
    by presburger
  have hHaus: "is_hausdorff_on X TX"
  proof -
    obtain d where hd: "top1_metric_on X d" and hTX: "TX = top1_metric_topology_on X d"
      using hMet unfolding top1_metrizable_on_def
      
      by blast
    show ?thesis unfolding hTX using metric_topology_hausdorff[OF hd]
      
      by argo
  qed
  have hLM: "top1_locally_metrizable_on X TX"
    unfolding top1_locally_metrizable_on_def
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    obtain d where hd: "top1_metric_on X d" and hTX: "TX = top1_metric_topology_on X d"
      using hMet unfolding top1_metrizable_on_def
      
      by fast
    have hXopen: "X \<in> TX" using hd hTX
      
      by (meson is_topology_on_def top1_metric_topology_on_is_topology_on)
    have hTX_sub: "\<forall>U\<in>TX. U \<subseteq> X"
      using hTX unfolding top1_metric_topology_on_def topology_generated_by_basis_def
      
      by blast
    have hint_eq: "\<forall>U\<in>TX. X \<inter> U = U" using hTX_sub
      
      by auto
    have hsubspace_X: "subspace_topology X TX X = TX"
      unfolding subspace_topology_def using hint_eq
      
      by fastforce
    show "\<exists>U\<in>TX. x \<in> U \<and> (\<exists>d. top1_metric_on U d \<and> subspace_topology X TX U = top1_metric_topology_on U d)"
      using hXopen hxX hd hTX hsubspace_X
      
      by auto
  qed
  show "top1_paracompact_on X TX \<and> is_hausdorff_on X TX \<and> top1_locally_metrizable_on X TX"
    using hPara hHaus hLM
    
    by presburger
next
  assume h: "top1_paracompact_on X TX \<and> is_hausdorff_on X TX \<and> top1_locally_metrizable_on X TX"
  show "top1_metrizable_on X TX"
  proof -
    have hPara: "top1_paracompact_on X TX" using h by blast
    have hHaus: "is_hausdorff_on X TX" using h by blast
    have hLM: "top1_locally_metrizable_on X TX" using h by blast
    text \<open>Steps: (1) paracompact + Hausdorff → regular (needs hTsub for paracompact_hausdorff_imp_regular).
      (2) Locally metrizable + paracompact → σ-LF basis (40.3 forward + cover decomposition).
      (3) Regular + σ-LF basis → metrizable (40.3 backward).
      All ingredients available: 40.3, paracompact_hausdorff_imp_regular, LF refinement.\<close>
    show ?thesis
      sorry
  qed
qed

section \<open>\<S>43 Complete Metric Spaces\<close>

definition top1_cauchy_seq_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_cauchy_seq_on X d s \<longleftrightarrow>
     (\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> X \<and> s n \<in> X \<and> d (s m) (s n) < e)"

definition top1_complete_metric_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "top1_complete_metric_on X d \<longleftrightarrow>
     top1_metric_on X d \<and>
     (\<forall>s. top1_cauchy_seq_on X d s \<longrightarrow> (\<exists>x\<in>X. seq_converges_to_on s x X (top1_metric_topology_on X d)))"

(** from \S43 Lemma 43.1 [top1.tex:6150] **)
lemma Lemma_43_1:
  assumes hd: "top1_metric_on X d"
  shows "top1_complete_metric_on X d \<longleftrightarrow>
    (\<forall>s. top1_cauchy_seq_on X d s \<longrightarrow> (\<exists>x\<in>X. \<exists>t. strict_mono t \<and> seq_converges_to_on (s \<circ> t) x X (top1_metric_topology_on X d)))"
proof
  assume hComplete: "top1_complete_metric_on X d"
  show "\<forall>s. top1_cauchy_seq_on X d s \<longrightarrow> (\<exists>x\<in>X. \<exists>t. strict_mono t \<and> seq_converges_to_on (s \<circ> t) x X (top1_metric_topology_on X d))"
  proof (intro allI impI)
    fix s
    assume hs: "top1_cauchy_seq_on X d s"
    obtain x where hxX: "x \<in> X" and hxconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
      using hComplete hs unfolding top1_complete_metric_on_def by blast
    show "\<exists>x\<in>X. \<exists>t. strict_mono t \<and> seq_converges_to_on (s \<circ> t) x X (top1_metric_topology_on X d)"
    proof (rule bexI[where x=x])
      show "x \<in> X"
        by (rule hxX)
      show "\<exists>t. strict_mono t \<and> seq_converges_to_on (s \<circ> t) x X (top1_metric_topology_on X d)"
      proof (rule exI[where x="(\<lambda>n::nat. n)"])
        have hmono: "strict_mono (\<lambda>n::nat. n)"
          unfolding strict_mono_def by simp
        have hEq: "s \<circ> (\<lambda>n::nat. n) = s"
          by (rule ext) (simp add: o_def)
        show "strict_mono (\<lambda>n::nat. n) \<and> seq_converges_to_on (s \<circ> (\<lambda>n::nat. n)) x X (top1_metric_topology_on X d)"
          unfolding hEq using hmono hxconv by blast
      qed
    qed
  qed
next
  assume hSubseq:
    "\<forall>s. top1_cauchy_seq_on X d s \<longrightarrow>
      (\<exists>x\<in>X. \<exists>t. strict_mono t \<and> seq_converges_to_on (s \<circ> t) x X (top1_metric_topology_on X d))"

  have hsym: "\<forall>x\<in>X. \<forall>y\<in>X. d x y = d y x"
    using hd unfolding top1_metric_on_def by blast
  have htri: "\<forall>x\<in>X. \<forall>y\<in>X. \<forall>z\<in>X. d x z \<le> d x y + d y z"
    using hd unfolding top1_metric_on_def by blast
  have hzero: "\<forall>x\<in>X. d x x = 0"
    using hd unfolding top1_metric_on_def by blast

  show "top1_complete_metric_on X d"
    unfolding top1_complete_metric_on_def
  proof (intro conjI allI impI)
    show "top1_metric_on X d"
      by (rule hd)
  next
    fix s
    assume hs: "top1_cauchy_seq_on X d s"
    obtain x t where hxX: "x \<in> X" and ht: "strict_mono t"
      and hsub: "seq_converges_to_on (s \<circ> t) x X (top1_metric_topology_on X d)"
      using hSubseq hs by blast

    have ht_ge_self: "\<forall>n. n \<le> t n"
    proof
      fix n :: nat
      show "n \<le> t n"
      proof (induction n)
        case 0
        show ?case by simp
      next
        case (Suc n)
        have hn: "n \<le> t n"
          by (rule Suc.IH)
        have hlt: "t n < t (Suc n)"
          using ht unfolding strict_mono_def by simp
        have h1: "Suc n \<le> Suc (t n)"
          using hn by simp
        have h2: "Suc (t n) \<le> t (Suc n)"
          by (rule Suc_leI[OF hlt])
        show ?case
          by (rule le_trans[OF h1 h2])
      qed
    qed

    have hxconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
    proof (unfold seq_converges_to_on_def, intro conjI)
      show "x \<in> X"
        by (rule hxX)
      show "\<forall>U. neighborhood_of x X (top1_metric_topology_on X d) U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> U)"
      proof (intro allI impI)
        fix U
        assume hU: "neighborhood_of x X (top1_metric_topology_on X d) U"
        have hUopen: "U \<in> top1_metric_topology_on X d"
          using hU unfolding neighborhood_of_def by blast
        have hxU: "x \<in> U"
          using hU unfolding neighborhood_of_def by blast
        obtain e where he: "0 < e" and hballU: "top1_ball_on X d x e \<subseteq> U"
          using top1_metric_open_contains_ball[OF hd hUopen hxU] by blast
        define e2 where "e2 = e / 2"
        have he2: "0 < e2"
          unfolding e2_def using he by simp

        obtain N1 where hN1:
          "\<forall>m\<ge>N1. \<forall>n\<ge>N1. s m \<in> X \<and> s n \<in> X \<and> d (s m) (s n) < e2"
          using hs he2 unfolding top1_cauchy_seq_on_def by blast

        have hopen_ball2: "top1_ball_on X d x e2 \<in> top1_metric_topology_on X d"
          by (rule top1_ball_open_in_metric_topology[OF hd hxX he2])
        have hx_ball2: "x \<in> top1_ball_on X d x e2"
          unfolding top1_ball_on_def using hxX hzero[rule_format, OF hxX] he2 by simp
        have hnbhd_ball2: "neighborhood_of x X (top1_metric_topology_on X d) (top1_ball_on X d x e2)"
          unfolding neighborhood_of_def using hopen_ball2 hx_ball2 by blast

        obtain N2 where hN2: "\<forall>n\<ge>N2. (s \<circ> t) n \<in> top1_ball_on X d x e2"
          using hsub hnbhd_ball2 unfolding seq_converges_to_on_def by blast

        define n0 where "n0 = max N1 N2"
        have hn0N1: "N1 \<le> n0" and hn0N2: "N2 \<le> n0"
          unfolding n0_def by simp_all

        have ht_n0: "N1 \<le> t n0"
        proof -
          have hn0t: "n0 \<le> t n0"
            using ht_ge_self by blast
          show ?thesis
            by (rule le_trans[OF hn0N1 hn0t])
        qed

        have hs_tn0_ball2': "(s \<circ> t) n0 \<in> top1_ball_on X d x e2"
          using hN2 hn0N2 by blast
        have hs_tn0_ball2: "s (t n0) \<in> top1_ball_on X d x e2"
          using hs_tn0_ball2' by (simp add: o_def)

        have hs_tn0_X: "s (t n0) \<in> X"
          using hs_tn0_ball2 unfolding top1_ball_on_def by blast
        have hdx_tn0: "d x (s (t n0)) < e2"
          using hs_tn0_ball2 unfolding top1_ball_on_def by blast

        show "\<exists>N. \<forall>n\<ge>N. s n \<in> U"
        proof (rule exI[where x=N1], intro allI impI)
          fix n
          assume hn: "N1 \<le> n"

          have hs_nX: "s n \<in> X"
            using hN1 hn ht_n0 by blast

          have hdn_tn0: "d (s n) (s (t n0)) < e2"
            using hN1 hn ht_n0 by blast
          have hdt0_n: "d (s (t n0)) (s n) < e2"
            using hdn_tn0 hsym hs_nX hs_tn0_X by simp

          have hle: "d x (s n) \<le> d x (s (t n0)) + d (s (t n0)) (s n)"
            using htri hxX hs_tn0_X hs_nX by blast
          have hlt': "d x (s (t n0)) + d (s (t n0)) (s n) < e2 + e2"
            by (rule add_strict_mono[OF hdx_tn0 hdt0_n])
          have hlt: "d x (s n) < e"
          proof -
            have "d x (s n) < e2 + e2"
              by (rule le_less_trans[OF hle hlt'])
            thus ?thesis
              unfolding e2_def by simp
          qed

          have hs_n_ball: "s n \<in> top1_ball_on X d x e"
            unfolding top1_ball_on_def using hs_nX hlt by blast
          have hs_n_U: "s n \<in> U"
            by (rule subsetD[OF hballU hs_n_ball])
          show "s n \<in> U"
            by (rule hs_n_U)
        qed
      qed
    qed

    show "\<exists>x\<in>X. seq_converges_to_on s x X (top1_metric_topology_on X d)"
      using hxX hxconv by blast
  qed
qed

(** from \S43 Theorem 43.2 [top1.tex:6172] **)
theorem Theorem_43_2:
  shows "top1_complete_metric_on (UNIV::real set) (\<lambda>x y. \<bar>x - y\<bar>)"
proof -
  let ?X = "(UNIV::real set)"
  let ?d = "(\<lambda>x y. \<bar>x - y\<bar>)"

  have hd: "top1_metric_on ?X ?d"
  unfolding top1_metric_on_def
  proof (intro conjI)
    show "\<forall>x\<in>?X. 0 \<le> ?d x x"
      by (intro ballI) simp
    show "\<forall>x\<in>?X. \<forall>y\<in>?X. 0 \<le> ?d x y"
      by (intro ballI) simp
    show "\<forall>x\<in>?X. \<forall>y\<in>?X. ?d x y = 0 \<longleftrightarrow> x = y"
      by (intro ballI) (simp add: abs_eq_0)
    show "\<forall>x\<in>?X. \<forall>y\<in>?X. ?d x y = ?d y x"
      by (intro ballI) (simp add: abs_minus_commute)
    show "\<forall>x\<in>?X. \<forall>y\<in>?X. \<forall>z\<in>?X. ?d x z \<le> ?d x y + ?d y z"
    proof (intro ballI)
      fix x y z :: real
      assume hx: "x \<in> ?X" and hy: "y \<in> ?X" and hz: "z \<in> ?X"
      have "\<bar>x - z\<bar> = \<bar>(x - y) + (y - z)\<bar>"
        by simp
      also have "... \<le> \<bar>x - y\<bar> + \<bar>y - z\<bar>"
        by (rule abs_triangle_ineq)
      finally show "?d x z \<le> ?d x y + ?d y z"
        by simp
    qed
  qed

  show ?thesis
    unfolding top1_complete_metric_on_def
  proof (intro conjI)
    show "top1_metric_on ?X ?d"
      by (rule hd)
  next
    show "\<forall>s. top1_cauchy_seq_on ?X ?d s \<longrightarrow> (\<exists>x\<in>?X. seq_converges_to_on s x ?X (top1_metric_topology_on ?X ?d))"
    proof (intro allI impI)
      fix s :: "nat \<Rightarrow> real"
      assume hs: "top1_cauchy_seq_on ?X ?d s"

      have hCauchy: "Cauchy s"
      proof (rule metric_CauchyI)
        fix e :: real
        assume he: "0 < e"
        obtain N where hN:
          "\<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> ?X \<and> s n \<in> ?X \<and> ?d (s m) (s n) < e"
          using hs he unfolding top1_cauchy_seq_on_def by blast
        have hN': "\<forall>m\<ge>N. \<forall>n\<ge>N. ?d (s m) (s n) < e"
          using hN by blast
        show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (s m) (s n) < e"
          apply (rule exI[where x=N])
          apply (intro allI impI)
          using hN' by (simp add: dist_real_def)
      qed

      have hconv: "convergent s"
        by (rule real_Cauchy_convergent[OF hCauchy])
      have hlim: "s \<longlonglongrightarrow> lim s"
        by (rule iffD1[OF convergent_LIMSEQ_iff, OF hconv])

      have hseq: "seq_converges_to_on s (lim s) ?X (top1_metric_topology_on ?X ?d)"
      proof (unfold seq_converges_to_on_def, intro conjI)
        show "lim s \<in> ?X"
          by simp
        show "\<forall>U. neighborhood_of (lim s) ?X (top1_metric_topology_on ?X ?d) U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> U)"
        proof (intro allI impI)
          fix U
          assume hU: "neighborhood_of (lim s) ?X (top1_metric_topology_on ?X ?d) U"
          have hUopen: "U \<in> top1_metric_topology_on ?X ?d"
            using hU unfolding neighborhood_of_def by blast
          have hlimU: "lim s \<in> U"
            using hU unfolding neighborhood_of_def by blast
          obtain e where he: "0 < e" and hball: "top1_ball_on ?X ?d (lim s) e \<subseteq> U"
            using top1_metric_open_contains_ball[OF hd hUopen hlimU] by blast

          obtain N where hN: "\<forall>n\<ge>N. dist (s n) (lim s) < e"
            using metric_LIMSEQ_D[OF hlim he] by blast

          show "\<exists>N. \<forall>n\<ge>N. s n \<in> U"
          proof (rule exI[where x=N], intro allI impI)
            fix n
            assume hn: "N \<le> n"
            have hdist: "dist (s n) (lim s) < e"
              using hN hn by simp
            have hballmem: "s n \<in> top1_ball_on ?X ?d (lim s) e"
              unfolding top1_ball_on_def
              using hdist by (simp add: dist_real_def abs_minus_commute)
            show "s n \<in> U"
              by (rule subsetD[OF hball hballmem])
          qed
        qed
      qed

      show "\<exists>x\<in>?X. seq_converges_to_on s x ?X (top1_metric_topology_on ?X ?d)"
        apply (rule bexI[where x="lim s"])
         apply (rule hseq)
        by simp
    qed
  qed
qed

(** from \S43 Lemma 43.3 [top1.tex:6191] **)
lemma Lemma_43_3:
  assumes hTop: "\<forall>i\<in>I. is_topology_on (X i) (TX i)"
  assumes hs: "\<forall>n. s n \<in> top1_PiE I X"
  shows "seq_converges_to_on s x (top1_PiE I X) (top1_product_topology_on I X TX)
    \<longleftrightarrow> (x \<in> top1_PiE I X \<and> (\<forall>i\<in>I. seq_converges_to_on (\<lambda>n. (s n) i) (x i) (X i) (TX i)))"
proof (rule iffI)
  assume hconv: "seq_converges_to_on s x (top1_PiE I X) (top1_product_topology_on I X TX)"
  have hxPiE: "x \<in> top1_PiE I X"
    using hconv unfolding seq_converges_to_on_def by blast

  have hconv_def:
    "\<forall>U. neighborhood_of x (top1_PiE I X) (top1_product_topology_on I X TX) U
      \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> U)"
    using hconv unfolding seq_converges_to_on_def by blast

  have hCoords: "\<forall>i\<in>I. seq_converges_to_on (\<lambda>n. (s n) i) (x i) (X i) (TX i)"
  proof (intro ballI)
    fix i assume hi: "i \<in> I"
    have hxi: "x i \<in> X i"
      using hxPiE hi unfolding top1_PiE_iff by blast

    show "seq_converges_to_on (\<lambda>n. (s n) i) (x i) (X i) (TX i)"
      unfolding seq_converges_to_on_def
    proof (intro conjI allI impI)
      show "x i \<in> X i"
        by (rule hxi)

      fix U
      assume hNbhU: "neighborhood_of (x i) (X i) (TX i) U"
      have hU: "U \<in> TX i"
        using hNbhU unfolding neighborhood_of_def by (rule conjunct1)
      have hxiU: "x i \<in> U"
        using hNbhU unfolding neighborhood_of_def by (rule conjunct2)

      define C where "C = top1_PiE I (\<lambda>j. if j = i then U \<inter> X i else X j)"

      have hC_basis: "C \<in> top1_product_basis_on I X TX"
        unfolding C_def
        by (rule top1_product_cylinder_in_basis[OF hTop hi hU])

      have hBasis: "is_basis_on (top1_PiE I X) (top1_product_basis_on I X TX)"
        by (rule top1_product_basis_is_basis_on[OF hTop])

      have hC_open:
        "C \<in> top1_product_topology_on I X TX"
        unfolding top1_product_topology_on_def
        by (rule basis_elem_open_in_generated_topology[OF hBasis hC_basis])

      have hxC: "x \<in> C"
      proof -
        have hxiUX: "x i \<in> U \<inter> X i"
          using hxiU hxi by simp
        have hxcoords: "\<forall>j\<in>I. x j \<in> (if j = i then U \<inter> X i else X j)"
        proof (intro ballI)
          fix j assume hj: "j \<in> I"
          show "x j \<in> (if j = i then U \<inter> X i else X j)"
          proof (cases "j = i")
            case True
            show ?thesis
              using hxiUX True by simp
          next
            case False
            have "x j \<in> X j"
              using hxPiE hj unfolding top1_PiE_iff by blast
            thus ?thesis
              using False by simp
          qed
        qed
        have hxext: "\<forall>j. j \<notin> I \<longrightarrow> x j = undefined"
          using hxPiE unfolding top1_PiE_iff by blast
        show ?thesis
          unfolding C_def top1_PiE_iff
          using hxcoords hxext by blast
      qed

      have hNbhC: "neighborhood_of x (top1_PiE I X) (top1_product_topology_on I X TX) C"
        unfolding neighborhood_of_def using hC_open hxC by simp

      obtain N where hN: "\<forall>n\<ge>N. s n \<in> C"
        using hconv_def hNbhC by blast

      show "\<exists>N. \<forall>n\<ge>N. (s n) i \<in> U"
      proof (rule exI[where x=N], intro allI impI)
        fix n assume hn: "n \<ge> N"
        have hsnC: "s n \<in> C"
          using hN hn by blast
        have hsn: "\<forall>j\<in>I. (s n) j \<in> (if j = i then U \<inter> X i else X j)"
          using hsnC unfolding C_def top1_PiE_iff by blast
        have "(s n) i \<in> U \<inter> X i"
          using bspec[OF hsn hi] by simp
        thus "(s n) i \<in> U"
          by simp
      qed
    qed
  qed

  show "x \<in> top1_PiE I X \<and> (\<forall>i\<in>I. seq_converges_to_on (\<lambda>n. (s n) i) (x i) (X i) (TX i))"
    using hxPiE hCoords by blast
next
  assume hR: "x \<in> top1_PiE I X \<and> (\<forall>i\<in>I. seq_converges_to_on (\<lambda>n. (s n) i) (x i) (X i) (TX i))"
  have hxPiE: "x \<in> top1_PiE I X"
    using hR by blast
  have hCoords: "\<forall>i\<in>I. seq_converges_to_on (\<lambda>n. (s n) i) (x i) (X i) (TX i)"
    using hR by blast

  show "seq_converges_to_on s x (top1_PiE I X) (top1_product_topology_on I X TX)"
    unfolding seq_converges_to_on_def
  proof (intro conjI allI impI)
    show "x \<in> top1_PiE I X"
      by (rule hxPiE)

    fix U
    assume hNbhU: "neighborhood_of x (top1_PiE I X) (top1_product_topology_on I X TX) U"
    have hUopen: "U \<in> top1_product_topology_on I X TX"
      using hNbhU unfolding neighborhood_of_def by (rule conjunct1)
    have hxU: "x \<in> U"
      using hNbhU unfolding neighborhood_of_def by (rule conjunct2)

    have hUgen:
      "U \<in> topology_generated_by_basis (top1_PiE I X) (top1_product_basis_on I X TX)"
      using hUopen unfolding top1_product_topology_on_def by simp
    have hcov:
      "\<forall>y\<in>U. \<exists>b\<in>top1_product_basis_on I X TX. y \<in> b \<and> b \<subseteq> U"
      using hUgen unfolding topology_generated_by_basis_def by blast
    obtain b where hb: "b \<in> top1_product_basis_on I X TX" and hxb: "x \<in> b" and hbU: "b \<subseteq> U"
      using hcov hxU by blast

    obtain U0 where hbdef: "b = top1_PiE I U0"
      and hU0: "(\<forall>i\<in>I. U0 i \<in> TX i \<and> U0 i \<subseteq> X i)"
      and hfin: "finite {i \<in> I. U0 i \<noteq> X i}"
      using hb unfolding top1_product_basis_on_def by blast

    define S where "S = {i \<in> I. U0 i \<noteq> X i}"
    have hSfin: "finite S"
      using hfin unfolding S_def by simp

    have hxU0: "\<forall>i\<in>I. x i \<in> U0 i"
      using hxb unfolding hbdef top1_PiE_iff by blast

    have hEventuallyS: "\<forall>i\<in>S. \<exists>N. \<forall>n\<ge>N. (s n) i \<in> U0 i"
    proof (intro ballI)
      fix i assume hiS: "i \<in> S"
      have hi: "i \<in> I"
        using hiS unfolding S_def by blast
      have hconv_i: "seq_converges_to_on (\<lambda>n. (s n) i) (x i) (X i) (TX i)"
        using hCoords hi by blast
      have hU0i: "U0 i \<in> TX i"
        using hU0 hi by blast
      have hxiU0: "x i \<in> U0 i"
        using hxU0 hi by blast
      have hNbhU0: "neighborhood_of (x i) (X i) (TX i) (U0 i)"
        unfolding neighborhood_of_def using hU0i hxiU0 by simp
      have hconv_def:
        "\<forall>V. neighborhood_of (x i) (X i) (TX i) V \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. (s n) i \<in> V)"
        using hconv_i unfolding seq_converges_to_on_def by blast
      obtain N where hN: "\<forall>n\<ge>N. (s n) i \<in> U0 i"
        using hconv_def hNbhU0 by blast
      show "\<exists>N. \<forall>n\<ge>N. (s n) i \<in> U0 i"
        using hN by blast
    qed

    have hCommonN: "\<exists>N. \<forall>i\<in>S. \<forall>n\<ge>N. (s n) i \<in> U0 i"
      using hSfin hEventuallyS
    proof (induction rule: finite_induct)
      case empty
      show ?case
        by (rule exI[where x=0], simp)
    next
      case (insert i S)
      have exNi: "\<exists>Ni. \<forall>n\<ge>Ni. (s n) i \<in> U0 i"
        using insert.prems(1) by (rule bspec[where x=i], simp)
      obtain Ni where hNi: "\<forall>n\<ge>Ni. (s n) i \<in> U0 i"
        using exNi by (erule exE)
      obtain N0 where hN0: "\<forall>j\<in>S. \<forall>n\<ge>N0. (s n) j \<in> U0 j"
        using insert.IH insert.prems(1) by blast
      show ?case
      proof (rule exI[where x="max Ni N0"], intro ballI allI impI)
        fix j assume hj: "j \<in> insert i S"
        fix n assume hn: "n \<ge> max Ni N0"
        show "(s n) j \<in> U0 j"
        proof (cases "j = i")
          case True
          have hNi_le: "Ni \<le> max Ni N0"
            by simp
          have hn': "n \<ge> Ni"
            using order_trans[OF hNi_le hn] by simp
          show ?thesis
            using hNi hn' True by simp
        next
          case False
          have hjS: "j \<in> S"
            using hj False by simp
          have hN0_le: "N0 \<le> max Ni N0"
            by simp
          have hn': "n \<ge> N0"
            using order_trans[OF hN0_le hn] by simp
          show ?thesis
            using hN0 hjS hn' by blast
        qed
      qed
    qed

    obtain N where hN: "\<forall>i\<in>S. \<forall>n\<ge>N. (s n) i \<in> U0 i"
      using hCommonN by blast

    have hEventuallyB: "\<forall>n\<ge>N. s n \<in> b"
    proof (intro allI impI)
      fix n assume hn: "n \<ge> N"
      have hsnPiE: "s n \<in> top1_PiE I X"
        using hs by blast
      have hCoordsIn: "\<forall>i\<in>I. (s n) i \<in> U0 i"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        show "(s n) i \<in> U0 i"
        proof (cases "i \<in> S")
          case True
          have hIn: "\<forall>n\<ge>N. (s n) i \<in> U0 i"
            using hN True by blast
          show ?thesis
            using hIn hn by blast
        next
          case False
          have hEqXi: "U0 i = X i"
          proof (rule ccontr)
            assume hneq: "U0 i \<noteq> X i"
            have "i \<in> S"
              unfolding S_def using hi hneq by simp
            with False show False
              by contradiction
          qed
          have hsnXi: "(s n) i \<in> X i"
            using hsnPiE hi unfolding top1_PiE_iff by blast
          show ?thesis
            unfolding hEqXi using hsnXi .
        qed
      qed
      have hExt: "\<forall>i. i \<notin> I \<longrightarrow> (s n) i = undefined"
        using hsnPiE unfolding top1_PiE_iff by blast
      have hsnU0: "s n \<in> top1_PiE I U0"
        unfolding top1_PiE_iff using hCoordsIn hExt by blast
      show "s n \<in> b"
        unfolding hbdef using hsnU0 by simp
    qed

    show "\<exists>N. \<forall>n\<ge>N. s n \<in> U"
    proof (rule exI[where x=N], intro allI impI)
      fix n assume hn: "n \<ge> N"
      have hsb: "s n \<in> b"
        using hn by (rule hEventuallyB[rule_format])
      show "s n \<in> U"
        by (rule subsetD[OF hbU hsb])
    qed

  qed
qed

text \<open>The bounded metric \<open>min |x-y| 1\<close> on the reals is the same as \<open>top1_real_bounded_metric\<close>.\<close>
lemma top1_bounded_abs_eq_real_bounded_metric:
  "top1_bounded_metric (\<lambda>x y :: real. \<bar>x - y\<bar>) = top1_real_bounded_metric"
proof (rule ext, rule ext)
  fix x y :: real
  show "top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>) x y = top1_real_bounded_metric x y"
    unfolding top1_bounded_metric_def top1_real_bounded_metric_def by simp
qed

lemma top1_bounded_abs_metric_topology_eq_order:
  "top1_metric_topology_on (UNIV::real set) (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>))
   = order_topology_on_UNIV"
proof -
  have "top1_metric_topology_on (UNIV::real set) (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>))
      = top1_metric_topology_on UNIV top1_real_bounded_metric"
    by (simp only: top1_bounded_abs_eq_real_bounded_metric)
  also have "... = order_topology_on_UNIV"
    by (rule order_topology_on_UNIV_eq_bounded_metric_topology_real[symmetric])
  finally show ?thesis .
qed

(** from \S43 Theorem 43.4 [top1.tex:6194] **)
text \<open>\<open>\<real>^\<omega>\<close> with the D-metric is complete and gives the product topology.\<close>
theorem Theorem_43_4:
  shows "\<exists>D.
    top1_complete_metric_on (top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set))) D
    \<and> top1_metric_topology_on (top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set))) D
        = top1_product_topology_on (UNIV::nat set) (\<lambda>_. (UNIV::real set))
            (\<lambda>_. top1_metric_topology_on (UNIV::real set) (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>)))"
proof (rule exI[where x="top1_D_metric_real_omega"])
  let ?X = "top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set))"
  text \<open>Theorem 20.5 gives the metric property and topology = product topology.\<close>
  have h205: "top1_metric_on ?X top1_D_metric_real_omega
    \<and> top1_metric_topology_on ?X top1_D_metric_real_omega
      = top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. order_topology_on_UNIV)"
    by (rule Theorem_20_5)

  have hmetric: "top1_metric_on ?X top1_D_metric_real_omega"
    using h205 by blast

  have htopo_eq: "top1_metric_topology_on ?X top1_D_metric_real_omega
    = top1_product_topology_on UNIV (\<lambda>_. UNIV)
        (\<lambda>_. top1_metric_topology_on UNIV (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>)))"
  proof -
    have "top1_metric_topology_on ?X top1_D_metric_real_omega
      = top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. order_topology_on_UNIV)"
      using h205 by blast
    also have "... = top1_product_topology_on UNIV (\<lambda>_. UNIV)
        (\<lambda>_. top1_metric_topology_on UNIV (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>)))"
      by (simp only: top1_bounded_abs_metric_topology_eq_order)
    finally show ?thesis .
  qed

  text \<open>Completeness: every Cauchy sequence in the D-metric converges coordinatewise.\<close>
  have hcomplete: "top1_complete_metric_on ?X top1_D_metric_real_omega"
    unfolding top1_complete_metric_on_def
  proof (intro conjI)
    show "top1_metric_on ?X top1_D_metric_real_omega" by (rule hmetric)
    show "\<forall>s. top1_cauchy_seq_on ?X top1_D_metric_real_omega s \<longrightarrow>
      (\<exists>x\<in>?X. seq_converges_to_on s x ?X (top1_metric_topology_on ?X top1_D_metric_real_omega))"
    proof (intro allI impI)
      fix s assume hCauchy: "top1_cauchy_seq_on ?X top1_D_metric_real_omega s"
      text \<open>Step 1: Each coordinate sequence is Cauchy in R (with bounded metric).\<close>
      text \<open>Step 2: Each coordinate converges (R is complete).\<close>
      text \<open>Step 3: Build limit in product space.\<close>
      text \<open>Step 4: Show D-metric convergence.\<close>
      text \<open>From D-Cauchy: each coordinate is Cauchy in R, hence convergent.\<close>
      have hsCauchy_def: "\<forall>e>0. \<exists>N. \<forall>m\<ge>N. \<forall>k\<ge>N.
        s m \<in> ?X \<and> s k \<in> ?X \<and> top1_D_metric_real_omega (s m) (s k) < e"
        using hCauchy unfolding top1_cauchy_seq_on_def by blast

      have hsX: "\<forall>m. s m \<in> ?X"
      proof (intro allI)
        fix m
        show "s m \<in> ?X" unfolding top1_PiE_iff by simp
      qed

      text \<open>Build coordinatewise limit: each coordinate is Cauchy in R, hence convergent.\<close>
      have hcoord_conv: "\<forall>n. \<exists>L. (\<lambda>m. s m n) \<longlonglongrightarrow> L"
      proof (intro allI)
        fix n
        have "Cauchy (\<lambda>m. s m n)"
          unfolding Cauchy_def
        proof (intro allI impI)
          fix e :: real assume hepos: "0 < e"
          define e' where "e' = min e 1 / (2 * real (Suc n))"
          have he'pos: "0 < e'"
            unfolding e'_def using hepos by simp
          obtain N where hN: "\<forall>m\<ge>N. \<forall>k\<ge>N. top1_D_metric_real_omega (s m) (s k) < e'"
            using hsCauchy_def he'pos by blast
          show "\<exists>M. \<forall>m\<ge>M. \<forall>k\<ge>M. dist (s m n) (s k n) < e"
          proof (rule exI[where x=N], intro allI impI)
            fix m k assume hmN: "m \<ge> N" and hkN: "k \<ge> N"
            have hDlt: "top1_D_metric_real_omega (s m) (s k) < e'"
              using hN hmN hkN by blast
            have hterm: "top1_real_bounded_metric (s m n) (s k n) / real (Suc n) \<le> top1_D_metric_real_omega (s m) (s k)"
              by (metis top1_D_metric_real_omega_term_le)
            have hpos_Suc: "0 < real (Suc n)" by simp
            have hle_chain: "top1_real_bounded_metric (s m n) (s k n) / real (Suc n) < e'"
              using hterm hDlt by linarith
            have hbdd_lt: "top1_real_bounded_metric (s m n) (s k n) < e' * real (Suc n)"
              using hle_chain hpos_Suc
              by (simp add: pos_divide_less_eq mult.commute)
            have he'_eq: "e' * real (Suc n) = min e 1 / 2"
              unfolding e'_def using hpos_Suc
              by (simp add: field_simps)
            have he'n_le: "e' * real (Suc n) \<le> 1 / 2"
              using he'_eq by (simp add: min_def)
            have hbdd_lt1: "top1_real_bounded_metric (s m n) (s k n) < 1"
              using hbdd_lt he'n_le by linarith
            have hdist_eq: "\<bar>s m n - s k n\<bar> = top1_real_bounded_metric (s m n) (s k n)"
              using hbdd_lt1 unfolding top1_real_bounded_metric_def by auto
            have hdist_lt: "dist (s m n) (s k n) < e' * real (Suc n)"
              using hdist_eq hbdd_lt unfolding dist_real_def by linarith
            have he'n_le_e: "e' * real (Suc n) \<le> e / 2"
              using he'_eq by (simp add: min_def)
            show "dist (s m n) (s k n) < e"
              using hdist_lt he'n_le_e hepos by linarith
          qed
        qed
        then show "\<exists>L. (\<lambda>m. s m n) \<longlonglongrightarrow> L"
          using Cauchy_convergent_iff unfolding convergent_def by fast
      qed

      obtain L where hL: "\<forall>n. (\<lambda>m. s m n) \<longlonglongrightarrow> L n"
        using choice[OF hcoord_conv] by blast

      define x where "x = (\<lambda>n. if n \<in> (UNIV::nat set) then L n else undefined)"
      have hxeq: "\<forall>n. x n = L n" unfolding x_def by simp
      have hxX: "x \<in> ?X" unfolding top1_PiE_iff x_def by simp

      text \<open>Show D-convergence: D(s m, x) \<rightarrow> 0.
        Strategy: given e > 0, pick N0 with 1/Suc(N0) < e/2, then for each n \<le> N0
        use coordinatewise convergence to make term n small. The tail terms are < e/2
        automatically since bounded metric / Suc n \<le> 1/Suc n.\<close>

      text \<open>Helper: bounding D-metric by a uniform bound on all terms.\<close>
      have hD_le_bound: "\<And>a b c. 0 \<le> c \<Longrightarrow>
        (\<And>n. top1_real_bounded_metric (a n) (b n) / real (Suc n) \<le> c)
        \<Longrightarrow> top1_D_metric_real_omega a b \<le> c"
      proof -
        fix a b :: "nat \<Rightarrow> real" and c :: real
        assume hc: "0 \<le> c"
        assume hterms: "\<And>n. top1_real_bounded_metric (a n) (b n) / real (Suc n) \<le> c"
        let ?S = "(\<lambda>n. top1_real_bounded_metric (a n) (b n) / real (Suc n)) ` (UNIV::nat set)"
        have hSne: "?S \<noteq> {}" by simp
        have "Sup ?S \<le> c"
        proof (rule cSup_least[OF hSne])
          fix r assume "r \<in> ?S"
          then obtain n where "r = top1_real_bounded_metric (a n) (b n) / real (Suc n)" by blast
          then show "r \<le> c" using hterms[of n] by simp
        qed
        then show "top1_D_metric_real_omega a b \<le> c"
          unfolding top1_D_metric_real_omega_def by simp
      qed

      text \<open>Helper: bounded metric equals absolute value when abs < 1.\<close>
      have hbdd_eq_abs: "\<And>u v :: real. \<bar>u - v\<bar> < 1 \<Longrightarrow>
        top1_real_bounded_metric u v = \<bar>u - v\<bar>"
        unfolding top1_real_bounded_metric_def by auto

      have hDconv: "seq_converges_to_on s x ?X (top1_metric_topology_on ?X top1_D_metric_real_omega)"
      proof (unfold seq_converges_to_on_def, intro conjI)
        show "x \<in> ?X" by (rule hxX)
        show "\<forall>U. neighborhood_of x ?X (top1_metric_topology_on ?X top1_D_metric_real_omega) U \<longrightarrow>
          (\<exists>N. \<forall>n\<ge>N. s n \<in> U)"
        proof (intro allI impI)
          fix U
          assume hU: "neighborhood_of x ?X (top1_metric_topology_on ?X top1_D_metric_real_omega) U"
          have hUopen: "U \<in> top1_metric_topology_on ?X top1_D_metric_real_omega"
            using hU unfolding neighborhood_of_def by blast
          have hxU: "x \<in> U"
            using hU unfolding neighborhood_of_def by blast
          obtain e where hepos: "0 < e" and hball: "top1_ball_on ?X top1_D_metric_real_omega x e \<subseteq> U"
            using top1_metric_open_contains_ball[OF hmetric hUopen hxU] by blast

          text \<open>Pick N0 so that 1/Suc(N0) < e/2 (Archimedean).\<close>
          have he2pos: "0 < e / 2" using hepos by linarith
          have "\<exists>N0::nat. 1 / real (Suc N0) < e / 2"
          proof -
            obtain k :: nat where hk: "real k > 2 / e"
              using reals_Archimedean2 he2pos by (metis less_divide_eq_numeral1(1))
            have hkpos: "0 < real (Suc k)" by simp
            have "2 / e < real (Suc k)" using hk by linarith
            then have "1 / real (Suc k) < e / 2"
              using hepos hkpos by (simp add: field_simps)
            then show ?thesis by blast
          qed
          then obtain N0 :: nat where hN0: "1 / real (Suc N0) < e / 2" by blast

          text \<open>For each coordinate n \<le> N0, pick M_n so coord n is close enough.\<close>
          define delta where "delta n = min 1 (e / 2 * real (Suc n))" for n :: nat
          have hdelta_pos: "\<And>n. 0 < delta n"
            unfolding delta_def using hepos by simp

          have hcoord_close: "\<forall>n \<le> N0. \<exists>M. \<forall>m\<ge>M. \<bar>s m n - x n\<bar> < delta n"
          proof (intro allI impI)
            fix n :: nat assume "n \<le> N0"
            have hconv_n: "(\<lambda>m. s m n) \<longlonglongrightarrow> L n"
              using hL by blast
            have hconv_x: "(\<lambda>m. s m n) \<longlonglongrightarrow> x n"
              using hconv_n hxeq by simp
            have "\<exists>M. \<forall>m\<ge>M. dist (s m n) (x n) < delta n"
              using metric_LIMSEQ_D[OF hconv_x hdelta_pos[of n]] by blast
            then show "\<exists>M. \<forall>m\<ge>M. \<bar>s m n - x n\<bar> < delta n"
              unfolding dist_real_def by blast
          qed

          text \<open>Take M = max of all M_n for n \<le> N0.\<close>
          obtain Mfun where hMfun: "\<forall>n \<le> N0. \<forall>m\<ge>Mfun n. \<bar>s m n - x n\<bar> < delta n"
          proof -
            have "\<forall>n \<le> N0. \<exists>M. \<forall>m\<ge>M. \<bar>s m n - x n\<bar> < delta n"
              using hcoord_close by blast
            then have "\<exists>f. \<forall>n \<le> N0. \<forall>m\<ge>f n. \<bar>s m n - x n\<bar> < delta n"
              by metis
            then show ?thesis using that by blast
          qed
          define M where "M = Max (Mfun ` {0..N0})"
          have hM_ge: "\<And>n. n \<le> N0 \<Longrightarrow> M \<ge> Mfun n"
            unfolding M_def by (intro Max_ge) auto

          show "\<exists>N. \<forall>n\<ge>N. s n \<in> U"
          proof (rule exI[where x=M], intro allI impI)
            fix m assume hmM: "M \<le> m"

            text \<open>Show D(s m, x) \<le> e/2 < e, hence s m in ball, hence in U.\<close>
            have hterm_bound: "\<And>n. top1_real_bounded_metric (s m n) (x n) / real (Suc n) \<le> e / 2"
            proof -
              fix n :: nat
              show "top1_real_bounded_metric (s m n) (x n) / real (Suc n) \<le> e / 2"
              proof (cases "n \<le> N0")
                case True
                then have hm_ge_Mn: "m \<ge> Mfun n"
                  using hM_ge[of n] hmM by linarith
                have habs: "\<bar>s m n - x n\<bar> < delta n"
                  using hMfun[rule_format, OF True hm_ge_Mn] by blast
                have habs_lt1: "\<bar>s m n - x n\<bar> < 1"
                  using habs unfolding delta_def by (simp add: min_def split: if_splits)
                have hbdd_eq: "top1_real_bounded_metric (s m n) (x n) = \<bar>s m n - x n\<bar>"
                  using hbdd_eq_abs[OF habs_lt1] by blast
                have habs_lt_e2n: "\<bar>s m n - x n\<bar> < e / 2 * real (Suc n)"
                  using habs unfolding delta_def by (simp add: min_def split: if_splits)
                have "top1_real_bounded_metric (s m n) (x n) < e / 2 * real (Suc n)"
                  using hbdd_eq habs_lt_e2n by linarith
                then show ?thesis
                  using pos_divide_le_eq by (simp add: pos_divide_less_eq mult.commute less_imp_le)
              next
                case False
                then have "N0 < n" by linarith
                then have "Suc N0 \<le> Suc n" by linarith
                then have "real (Suc N0) \<le> real (Suc n)" by simp
                then have h_inv: "1 / real (Suc n) \<le> 1 / real (Suc N0)"
                  by (simp add: frac_le)
                have "top1_real_bounded_metric (s m n) (x n) / real (Suc n) \<le> 1 / real (Suc n)"
                proof -
                  have "top1_real_bounded_metric (s m n) (x n) \<le> 1"
                    unfolding top1_real_bounded_metric_def by simp
                  then show ?thesis by (simp add: divide_right_mono)
                qed
                also have "... \<le> 1 / real (Suc N0)" by (rule h_inv)
                also have "... < e / 2" by (rule hN0)
                finally show ?thesis by linarith
              qed
            qed
            have hDle: "top1_D_metric_real_omega (s m) x \<le> e / 2"
            proof (rule hD_le_bound)
              show "0 \<le> e / 2" using he2pos by linarith
            next
              fix n show "top1_real_bounded_metric (s m n) (x n) / real (Suc n) \<le> e / 2"
                by (rule hterm_bound)
            qed
            have hDlt: "top1_D_metric_real_omega (s m) x < e"
              using hDle hepos by linarith
            have hDlt_sym: "top1_D_metric_real_omega x (s m) < e"
              using hDlt top1_D_metric_real_omega_sym[of x "s m"] by linarith
            have hsmX: "s m \<in> ?X"
              using hsX by blast
            have hball_mem: "s m \<in> top1_ball_on ?X top1_D_metric_real_omega x e"
              unfolding top1_ball_on_def using hsmX hDlt_sym by simp
            show "s m \<in> U"
              using subsetD[OF hball hball_mem] by blast
          qed
        qed
      qed

      show "\<exists>x\<in>?X. seq_converges_to_on s x ?X (top1_metric_topology_on ?X top1_D_metric_real_omega)"
        using hxX hDconv by blast
    qed
  qed

  show "top1_complete_metric_on ?X top1_D_metric_real_omega
    \<and> top1_metric_topology_on ?X top1_D_metric_real_omega
      = top1_product_topology_on UNIV (\<lambda>_. UNIV)
          (\<lambda>_. top1_metric_topology_on UNIV (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>)))"
    using hcomplete htopo_eq by blast
qed

definition top1_uniform_metric_on ::
  "'i set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> real" where
  "top1_uniform_metric_on I d x y =
     (if I = {} then 0 else Sup ((\<lambda>i. top1_bounded_metric d (x i) (y i)) ` I))"

definition top1_continuous_maps_metric_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "top1_continuous_maps_metric_on X TX Y d =
     {f \<in> top1_PiE X (\<lambda>_. Y). top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) f}"

definition top1_bounded_map_on ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_bounded_map_on X Y d f \<longleftrightarrow> (\<exists>y0\<in>Y. \<exists>M. \<forall>x\<in>X. d y0 (f x) \<le> M)"

definition top1_bounded_maps_metric_on ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "top1_bounded_maps_metric_on X Y d =
     {f \<in> top1_PiE X (\<lambda>_. Y). top1_bounded_map_on X Y d f}"

(** Sup metric on function spaces (untruncated); useful when \(X\) is compact so the supremum is finite. **)
definition top1_sup_metric_on ::
  "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where
  "top1_sup_metric_on X d f g = Sup ((\<lambda>x. d (f x) (g x)) ` X)"

definition top1_sup_topology_on ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set set" where
  "top1_sup_topology_on X Y d =
     top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_sup_metric_on X d)"

text \<open>The uniform metric is a metric on \<open>Y^J\<close>.\<close>
lemma top1_uniform_metric_is_metric:
  assumes hIne: "I \<noteq> {}"
  assumes hd: "top1_metric_on Y d"
  shows "top1_metric_on (top1_PiE I (\<lambda>_. Y)) (top1_uniform_metric_on I d)"
proof -
  let ?X = "top1_PiE I (\<lambda>_. Y)"
  let ?rho = "top1_uniform_metric_on I d"
  let ?db = "top1_bounded_metric d"
  have hdb: "top1_metric_on Y ?db"
    using top1_bounded_metric_on[OF hd]
    by presburger
  text \<open>Bounded metric values lie in [0,1].\<close>
  have hdb_le1: "\<forall>a\<in>Y. \<forall>b\<in>Y. ?db a b \<le> 1"
    unfolding top1_bounded_metric_def
    by fastforce
  have hdb_nonneg: "\<forall>a\<in>Y. \<forall>b\<in>Y. 0 \<le> ?db a b"
    using hdb unfolding top1_metric_on_def
    by satx
  text \<open>For f,g in PiE, the image set is bounded.\<close>
  have himg_bdd: "\<forall>f\<in>?X. \<forall>g\<in>?X. bdd_above ((\<lambda>i. ?db (f i) (g i)) ` I)"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?X" and hg: "g \<in> ?X"
    have "\<forall>i\<in>I. ?db (f i) (g i) \<le> 1"
    proof (intro ballI)
      fix i assume "i \<in> I"
      have "f i \<in> Y" using hf \<open>i \<in> I\<close> unfolding top1_PiE_def
        using top1_PiE_def top1_PiE_iff by fastforce
      moreover have "g i \<in> Y" using hg \<open>i \<in> I\<close> unfolding top1_PiE_def
        using top1_PiE_def top1_PiE_iff by fastforce
      ultimately show "?db (f i) (g i) \<le> 1" using hdb_le1
        by blast
    qed
    then show "bdd_above ((\<lambda>i. ?db (f i) (g i)) ` I)"
      by fast
  qed
  have himg_nonempty: "I \<noteq> {} \<Longrightarrow> (\<lambda>i. ?db (f i) (g i)) ` I \<noteq> {}" for f g
    by fast
  text \<open>Sup of image lies in [0,1] for f,g in PiE.\<close>
  have hSup_le1: "\<forall>f\<in>?X. \<forall>g\<in>?X. ?rho f g \<le> 1"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?X" and hg: "g \<in> ?X"
    have "?rho f g = Sup ((\<lambda>i. ?db (f i) (g i)) ` I)"
      using hIne unfolding top1_uniform_metric_on_def
      by presburger
    also have "... \<le> 1"
    proof (rule cSup_least)
      show "(\<lambda>i. ?db (f i) (g i)) ` I \<noteq> {}" using hIne
        by blast
    next
      fix x assume "x \<in> (\<lambda>i. ?db (f i) (g i)) ` I"
      then obtain i where "i \<in> I" and "x = ?db (f i) (g i)"
        by blast
      have "f i \<in> Y" using hf \<open>i \<in> I\<close> unfolding top1_PiE_def
        using top1_PiE_def top1_PiE_iff by fastforce
      moreover have "g i \<in> Y" using hg \<open>i \<in> I\<close> unfolding top1_PiE_def
        using top1_PiE_def top1_PiE_iff by fastforce
      ultimately show "x \<le> 1" using hdb_le1 \<open>x = ?db (f i) (g i)\<close>
        by blast
    qed
    finally show "?rho f g \<le> 1"
      by presburger
  qed
  have hSup_nonneg: "\<forall>f\<in>?X. \<forall>g\<in>?X. 0 \<le> ?rho f g"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?X" and hg: "g \<in> ?X"
    obtain i0 where hi0: "i0 \<in> I" using hIne
      by blast
    have "f i0 \<in> Y" using hf hi0 unfolding top1_PiE_def
      using top1_PiE_def top1_PiE_iff by fastforce
    moreover have "g i0 \<in> Y" using hg hi0 unfolding top1_PiE_def
      using top1_PiE_def top1_PiE_iff by fastforce
    ultimately have "0 \<le> ?db (f i0) (g i0)" using hdb_nonneg
      by blast
    also have "... \<le> ?rho f g"
    proof -
      have "?rho f g = Sup ((\<lambda>i. ?db (f i) (g i)) ` I)"
        using hIne unfolding top1_uniform_metric_on_def
        by presburger
      moreover have "?db (f i0) (g i0) \<in> (\<lambda>i. ?db (f i) (g i)) ` I" using hi0
        by fast
      moreover have "bdd_above ((\<lambda>i. ?db (f i) (g i)) ` I)"
        using himg_bdd hf hg
        by fast
      ultimately show "?db (f i0) (g i0) \<le> ?rho f g"
        using cSup_upper
        by metis
    qed
    finally show "0 \<le> ?rho f g"
      by presburger
  qed
  text \<open>PiE membership helper.\<close>
  have hPiE_mem: "\<forall>f\<in>?X. \<forall>i\<in>I. f i \<in> Y"
    unfolding top1_PiE_def top1_Pi_def
    by blast
  text \<open>Symmetry of rho.\<close>
  have hSym: "\<forall>f\<in>?X. \<forall>g\<in>?X. ?rho f g = ?rho g f"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?X" and hg: "g \<in> ?X"
    have "\<forall>i\<in>I. ?db (f i) (g i) = ?db (g i) (f i)"
    proof (intro ballI)
      fix i assume "i \<in> I"
      have "f i \<in> Y" using hPiE_mem hf \<open>i \<in> I\<close> by blast
      moreover have "g i \<in> Y" using hPiE_mem hg \<open>i \<in> I\<close> by blast
      ultimately show "?db (f i) (g i) = ?db (g i) (f i)"
        using hdb unfolding top1_metric_on_def
        by blast
    qed
    then have "(\<lambda>i. ?db (f i) (g i)) ` I = (\<lambda>i. ?db (g i) (f i)) ` I"
      by auto
    then show "?rho f g = ?rho g f"
      unfolding top1_uniform_metric_on_def
      by presburger
  qed
  text \<open>Zero iff equal.\<close>
  have hZero: "\<forall>f\<in>?X. \<forall>g\<in>?X. ?rho f g = 0 \<longleftrightarrow> f = g"
  proof (intro ballI)
    fix f g assume hf: "f \<in> ?X" and hg: "g \<in> ?X"
    show "?rho f g = 0 \<longleftrightarrow> f = g"
    proof
      assume heq: "f = g"
      have "\<forall>i\<in>I. ?db (f i) (g i) = 0"
      proof (intro ballI)
        fix i assume "i \<in> I"
        then show "?db (f i) (g i) = 0" using heq hdb hPiE_mem hf
          unfolding top1_metric_on_def
          by metis
      qed
      then have "(\<lambda>i. ?db (f i) (g i)) ` I = {0}"
        using hIne
        by auto
      then show "?rho f g = 0"
        unfolding top1_uniform_metric_on_def using hIne
        by simp
    next
      assume hzero: "?rho f g = 0"
      have hrho_eq: "?rho f g = Sup ((\<lambda>i. ?db (f i) (g i)) ` I)"
        using hIne unfolding top1_uniform_metric_on_def
        by presburger
      have hbdd: "bdd_above ((\<lambda>i. ?db (f i) (g i)) ` I)"
        using himg_bdd hf hg
        by fast
      have "\<forall>i\<in>I. ?db (f i) (g i) = 0"
      proof (intro ballI)
        fix i assume hi: "i \<in> I"
        have hmem: "?db (f i) (g i) \<in> (\<lambda>i. ?db (f i) (g i)) ` I" using hi
          by blast
        have "?db (f i) (g i) \<le> Sup ((\<lambda>i. ?db (f i) (g i)) ` I)"
          using cSup_upper[OF hmem hbdd]
          by presburger
        then have "?db (f i) (g i) \<le> ?rho f g" using hrho_eq
          by presburger
        moreover have "0 \<le> ?db (f i) (g i)"
          using hdb_nonneg hPiE_mem hf hg hi
          by blast
        ultimately show "?db (f i) (g i) = 0" using hzero
          by linarith
      qed
      then have "\<forall>i\<in>I. f i = g i"
      proof (intro ballI)
        fix i assume "i \<in> I"
        then have "?db (f i) (g i) = 0" using \<open>\<forall>i\<in>I. ?db (f i) (g i) = 0\<close>
          by blast
        moreover have "f i \<in> Y" using hPiE_mem hf \<open>i \<in> I\<close> by blast
        moreover have "g i \<in> Y" using hPiE_mem hg \<open>i \<in> I\<close> by blast
        ultimately show "f i = g i"
          using hdb unfolding top1_metric_on_def top1_bounded_metric_def
          by blast
      qed
      text \<open>f and g agree on I and are both extensional, so f = g.\<close>
      have "f \<in> top1_extensional I" using hf unfolding top1_PiE_def
        by blast
      moreover have "g \<in> top1_extensional I" using hg unfolding top1_PiE_def
        by blast
      ultimately show "f = g"
        using \<open>\<forall>i\<in>I. f i = g i\<close> unfolding top1_extensional_def
        by fastforce
    qed
  qed
  text \<open>Triangle inequality.\<close>
  have hTri: "\<forall>f\<in>?X. \<forall>g\<in>?X. \<forall>h\<in>?X. ?rho f h \<le> ?rho f g + ?rho g h"
  proof (intro ballI)
    fix f g h assume hf: "f \<in> ?X" and hg: "g \<in> ?X" and hh: "h \<in> ?X"
    have hrho_fh: "?rho f h = Sup ((\<lambda>i. ?db (f i) (h i)) ` I)"
      using hIne unfolding top1_uniform_metric_on_def
      by presburger
    have hbdd_fg: "bdd_above ((\<lambda>i. ?db (f i) (g i)) ` I)"
      using himg_bdd hf hg
      by fast
    have hbdd_gh: "bdd_above ((\<lambda>i. ?db (g i) (h i)) ` I)"
      using himg_bdd hg hh
      by fast
    have "\<forall>i\<in>I. ?db (f i) (h i) \<le> ?rho f g + ?rho g h"
    proof (intro ballI)
      fix i assume hi: "i \<in> I"
      have hfiY: "f i \<in> Y" using hPiE_mem hf hi by blast
      have hgiY: "g i \<in> Y" using hPiE_mem hg hi by blast
      have hhiY: "h i \<in> Y" using hPiE_mem hh hi by blast
      have htri_i: "?db (f i) (h i) \<le> ?db (f i) (g i) + ?db (g i) (h i)"
        using hdb hfiY hgiY hhiY unfolding top1_metric_on_def
        by blast
      have "?db (f i) (g i) \<le> ?rho f g"
      proof -
        have "?rho f g = Sup ((\<lambda>i. ?db (f i) (g i)) ` I)"
          using hIne unfolding top1_uniform_metric_on_def
          by argo
        moreover have "?db (f i) (g i) \<in> (\<lambda>i. ?db (f i) (g i)) ` I" using hi
          by blast
        ultimately show ?thesis using cSup_upper hbdd_fg
          by metis
      qed
      moreover have "?db (g i) (h i) \<le> ?rho g h"
      proof -
        have "?rho g h = Sup ((\<lambda>i. ?db (g i) (h i)) ` I)"
          using hIne unfolding top1_uniform_metric_on_def
          by presburger
        moreover have "?db (g i) (h i) \<in> (\<lambda>i. ?db (g i) (h i)) ` I" using hi
          by blast
        ultimately show ?thesis using cSup_upper hbdd_gh
          by metis
      qed
      ultimately show "?db (f i) (h i) \<le> ?rho f g + ?rho g h"
        using htri_i
        by auto
    qed
    then show "?rho f h \<le> ?rho f g + ?rho g h"
    proof -
      have hne: "(\<lambda>i. ?db (f i) (h i)) ` I \<noteq> {}" using hIne
        by fast
      have "\<forall>x\<in>(\<lambda>i. ?db (f i) (h i)) ` I. x \<le> ?rho f g + ?rho g h"
        using \<open>\<forall>i\<in>I. ?db (f i) (h i) \<le> ?rho f g + ?rho g h\<close>
        by blast
      then have "Sup ((\<lambda>i. ?db (f i) (h i)) ` I) \<le> ?rho f g + ?rho g h"
        using cSup_least[OF hne]
        by fast
      then show ?thesis using hrho_fh
        by presburger
    qed
  qed
  show ?thesis unfolding top1_metric_on_def
    using hSup_nonneg hZero hSym hTri
    by fastforce
qed

text \<open>Metric convergence iff epsilon-delta convergence.\<close>

text \<open>Helper: metric convergence preserves distance bounds.
  If a_n → a in metric Y, and d(a_n, b) ≤ c for all n ≥ N, then d(a, b) ≤ c.\<close>
lemma metric_limit_preserves_bound:
  assumes hd: "top1_metric_on Y d"
  assumes hconv: "seq_converges_to_on s a Y (top1_metric_topology_on Y d)"
  assumes hbound: "\<forall>n\<ge>N. d (s n) b \<le> c"
  assumes hbY: "b \<in> Y"
  assumes hc: "0 \<le> c"
  shows "d a b \<le> c"
proof (rule field_le_epsilon)
  fix e' :: real assume he': "0 < e'"
  have haY: "a \<in> Y"
    using hconv unfolding seq_converges_to_on_def
    
    by satx
  text \<open>Get M with d(s n, a) < e' for n ≥ M.\<close>
  have hball_open: "top1_ball_on Y d a e' \<in> top1_metric_topology_on Y d"
    using hd haY he' top1_ball_open_in_metric_topology
    
    by fast
  have ha_in_ball: "a \<in> top1_ball_on Y d a e'"
    unfolding top1_ball_on_def using haY hd he' unfolding top1_metric_on_def
    
    by fastforce
  have hnbhd: "neighborhood_of a Y (top1_metric_topology_on Y d) (top1_ball_on Y d a e')"
    unfolding neighborhood_of_def using hball_open ha_in_ball
    
    by satx
  obtain M where hM: "\<forall>n\<ge>M. s n \<in> top1_ball_on Y d a e'"
    using hconv hnbhd unfolding seq_converges_to_on_def
    
    by blast
  text \<open>Pick n = max(N, M).\<close>
  define n0 where "n0 = max N M"
  have hn0N: "n0 \<ge> N" unfolding n0_def
    
    by simp
  have hn0M: "n0 \<ge> M" unfolding n0_def
    
    by simp
  have hsn0_ball: "s n0 \<in> top1_ball_on Y d a e'"
    using hM hn0M
    
    by presburger
  have hd_a_sn0: "d a (s n0) < e'"
    using hsn0_ball unfolding top1_ball_on_def
    
    by blast
  have hd_sn0_b: "d (s n0) b \<le> c"
    using hbound hn0N
    
    by blast
  have hsn0Y: "s n0 \<in> Y"
    using hsn0_ball unfolding top1_ball_on_def
    
    by blast
  have htri: "d a b \<le> d a (s n0) + d (s n0) b"
    using hd haY hsn0Y hbY unfolding top1_metric_on_def
    
    by blast
  show "d a b \<le> c + e'"
    using htri hd_a_sn0 hd_sn0_b
    
    by argo
qed

lemma metric_seq_conv_iff:
  assumes hd: "top1_metric_on X d"
  assumes hxX: "x \<in> X"
  shows "seq_converges_to_on s x X (top1_metric_topology_on X d) \<longleftrightarrow>
    (\<forall>\<epsilon>::real. 0 < \<epsilon> \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> X \<and> d (s n) x < \<epsilon>))"
proof
  let ?TX = "top1_metric_topology_on X d"
  have hTop: "is_topology_on X ?TX"
    using hd top1_metric_topology_on_is_topology_on
    by auto
  have hTX_sub: "\<forall>U\<in>?TX. U \<subseteq> X"
    unfolding top1_metric_topology_on_def topology_generated_by_basis_def
    by blast
  assume hconv: "seq_converges_to_on s x X ?TX"
  show "\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. s n \<in> X \<and> d (s n) x < \<epsilon>"
  proof (intro allI impI)
    fix \<epsilon> :: real assume hepos: "0 < \<epsilon>"
    have hball_open: "top1_ball_on X d x \<epsilon> \<in> ?TX"
      using top1_ball_open_in_metric_topology[OF hd hxX hepos]
      by presburger
    have hdxx: "d x x = 0" using hd hxX unfolding top1_metric_on_def
      by blast
    have hx_in_ball: "x \<in> top1_ball_on X d x \<epsilon>"
      unfolding top1_ball_on_def using hxX hdxx hepos
      by auto
    have hball_nbhd: "neighborhood_of x X ?TX (top1_ball_on X d x \<epsilon>)"
      unfolding neighborhood_of_def using hball_open hx_in_ball
      by satx
    obtain N where hN: "\<forall>n\<ge>N. s n \<in> top1_ball_on X d x \<epsilon>"
      using hconv hball_nbhd unfolding seq_converges_to_on_def
      by blast
    show "\<exists>N. \<forall>n\<ge>N. s n \<in> X \<and> d (s n) x < \<epsilon>"
    proof (intro exI allI impI)
      fix n assume "N \<le> n"
      then have hsn_ball: "s n \<in> top1_ball_on X d x \<epsilon>" using hN
        by presburger
      then have hsnX: "s n \<in> X" unfolding top1_ball_on_def
        by fast
      have "d x (s n) < \<epsilon>" using hsn_ball unfolding top1_ball_on_def
        by blast
      have "d (s n) x = d x (s n)" using hd hsnX hxX unfolding top1_metric_on_def
        by blast
      then show "s n \<in> X \<and> d (s n) x < \<epsilon>" using \<open>s n \<in> X\<close> \<open>d x (s n) < \<epsilon>\<close>
        by presburger
    qed
  qed
next
  let ?TX = "top1_metric_topology_on X d"
  have hTop: "is_topology_on X ?TX"
    using hd top1_metric_topology_on_is_topology_on
    by fast
  assume heps: "\<forall>\<epsilon>::real. 0 < \<epsilon> \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. s n \<in> X \<and> d (s n) x < \<epsilon>)"
  show "seq_converges_to_on s x X ?TX"
    unfolding seq_converges_to_on_def
  proof (intro conjI allI impI)
    show "x \<in> X" by (rule hxX)
  next
    fix U assume hU: "neighborhood_of x X ?TX U"
    have hUopen: "\<exists>V\<in>?TX. x \<in> V \<and> V \<subseteq> U"
      using hU unfolding neighborhood_of_def
      by auto
    then obtain V where hV: "V \<in> ?TX" and hxV: "x \<in> V" and hVU: "V \<subseteq> U"
      by blast
    obtain r where hrpos: "0 < r" and hball_sub: "top1_ball_on X d x r \<subseteq> V"
      using top1_metric_open_contains_ball[OF hd hV hxV]
      by auto
    obtain N where hN: "\<forall>n\<ge>N. s n \<in> X \<and> d (s n) x < r" using heps hrpos
      by blast
    show "\<exists>N. \<forall>n\<ge>N. s n \<in> U"
    proof (intro exI allI impI)
      fix n assume "N \<le> n"
      have hsnX: "s n \<in> X" using hN \<open>N \<le> n\<close>
        by presburger
      have hd_sn: "d (s n) x < r" using hN \<open>N \<le> n\<close>
        by presburger
      have "d x (s n) = d (s n) x" using hd hsnX hxX unfolding top1_metric_on_def
        by blast
      then have "d x (s n) < r" using hd_sn
        by presburger
      then have "s n \<in> top1_ball_on X d x r"
        unfolding top1_ball_on_def using hsnX
        by blast
      then show "s n \<in> U" using hball_sub hVU
        by blast
    qed
  qed
qed


text \<open>In a metric space, if every convergent sequence from A has limit in A, then A is closed.\<close>
lemma metric_seq_closed_imp_closed:
  assumes hd: "top1_metric_on X d"
  assumes hAX: "A \<subseteq> X"
  assumes hSeqCl: "\<forall>s. (\<forall>n::nat. s n \<in> A) \<longrightarrow>
    (\<forall>x. seq_converges_to_on s x X (top1_metric_topology_on X d) \<longrightarrow> x \<in> A)"
  shows "closedin_on X (top1_metric_topology_on X d) A"
proof -
  let ?TX = "top1_metric_topology_on X d"
  text \<open>Show X - A is open: for x ∈ X - A, find ε-ball in X - A.\<close>
  have hXmA_open: "X - A \<in> ?TX"
  proof (rule top1_open_of_local_subsets)
    show "is_topology_on X ?TX" using hd top1_metric_topology_on_is_topology_on
      by blast
    show "X - A \<subseteq> X"
      by auto
    show "\<forall>x\<in>X - A. \<exists>U\<in>?TX. x \<in> U \<and> U \<subseteq> X - A"
    proof (intro ballI)
      fix x assume hx: "x \<in> X - A"
      have hxX: "x \<in> X" using hx
        by blast
      have hxnA: "x \<notin> A" using hx
        by blast
      text \<open>Claim: ∃ε>0 with B(x,ε) ∩ A = {}. By contradiction, for each n, ∃a_n ∈ A ∩ B(x,1/(n+1)).\<close>
      have "\<exists>\<epsilon>>0. top1_ball_on X d x \<epsilon> \<inter> A = {}"
      proof (rule ccontr)
        assume "\<not> (\<exists>\<epsilon>>0. top1_ball_on X d x \<epsilon> \<inter> A = {})"
        then have hneg: "\<forall>\<epsilon>>0. top1_ball_on X d x \<epsilon> \<inter> A \<noteq> {}"
          by auto
        text \<open>Build sequence: for each n, pick a_n ∈ A with d(x, a_n) < 1/(n+1).\<close>
        have "\<forall>n::nat. \<exists>a. a \<in> A \<and> d x a < 1 / real (Suc n)"
        proof (intro allI)
          fix n :: nat
          have hpos: "0 < 1 / real (Suc n)"
            by simp
          then have "top1_ball_on X d x (1 / real (Suc n)) \<inter> A \<noteq> {}"
            using hneg
            by presburger
          then obtain a where "a \<in> top1_ball_on X d x (1 / real (Suc n))" and "a \<in> A"
            by fast
          then have "a \<in> X \<and> d x a < 1 / real (Suc n)" unfolding top1_ball_on_def
            by blast
          then show "\<exists>a. a \<in> A \<and> d x a < 1 / real (Suc n)" using \<open>a \<in> A\<close>
            by blast
        qed
        then obtain s where hs: "\<forall>n. s n \<in> A \<and> d x (s n) < 1 / real (Suc n)"
          by meson
        have hsA: "\<forall>n. s n \<in> A" using hs
          by presburger
        text \<open>s converges to x.\<close>
        have hsconv: "seq_converges_to_on s x X ?TX"
          unfolding metric_seq_conv_iff[OF hd hxX]
        proof (intro allI impI)
          fix \<epsilon> :: real assume hepos: "0 < \<epsilon>"
          obtain N :: nat where hNe: "1 / real (Suc N) < \<epsilon>"
          proof -
            obtain k :: nat where hk: "1 / \<epsilon> < real k" using reals_Archimedean2
              by blast
            have "1 / real (Suc k) < \<epsilon>"
            proof -
              have "0 < \<epsilon>" by (rule hepos)
              have "0 < real (Suc k)"
                by simp
              have "1 / \<epsilon> < real (Suc k)" using hk
                by simp
              then show ?thesis using \<open>0 < \<epsilon>\<close> \<open>0 < real (Suc k)\<close>
                by (simp add: divide_less_eq mult.commute)
            qed
            then show ?thesis using that
              by blast
          qed
          show "\<exists>N. \<forall>n\<ge>N. s n \<in> X \<and> d (s n) x < \<epsilon>"
          proof (intro exI allI impI)
            fix n assume hnN: "N \<le> n"
            have hsnA: "s n \<in> A" using hsA
              by simp
            have hsnX: "s n \<in> X" using hsnA hAX
              by blast
            have "d x (s n) < 1 / real (Suc n)" using hs
              by simp
            also have "... \<le> 1 / real (Suc N)"
            proof -
              have "real (Suc N) \<le> real (Suc n)" using hnN
                by auto
              then show ?thesis
                using frac_le[of 1 1 "real (Suc N)" "real (Suc n)"]
                by linarith
            qed
            also have "... < \<epsilon>" by (rule hNe)
            finally have "d x (s n) < \<epsilon>"
              by presburger
            have "d (s n) x = d x (s n)"
              using hd hsnX hxX unfolding top1_metric_on_def
              by blast
            then show "s n \<in> X \<and> d (s n) x < \<epsilon>" using hsnX \<open>d x (s n) < \<epsilon>\<close>
              by presburger
          qed
        qed
        text \<open>By sequential closedness, x ∈ A. Contradiction.\<close>
        have "x \<in> A" using hSeqCl hsA hsconv
          by presburger
        then show False using hxnA
          by presburger
      qed
      then obtain \<epsilon> where hepos: "0 < \<epsilon>" and hdisj: "top1_ball_on X d x \<epsilon> \<inter> A = {}"
        by blast
      have hball_open: "top1_ball_on X d x \<epsilon> \<in> ?TX"
        using top1_ball_open_in_metric_topology[OF hd hxX hepos]
        by satx
      have hball_sub: "top1_ball_on X d x \<epsilon> \<subseteq> X - A"
        using hdisj unfolding top1_ball_on_def
        by blast
      have hx_in_ball: "x \<in> top1_ball_on X d x \<epsilon>"
        unfolding top1_ball_on_def using hxX hd hepos unfolding top1_metric_on_def
        by fastforce
      show "\<exists>U\<in>?TX. x \<in> U \<and> U \<subseteq> X - A"
        using hball_open hx_in_ball hball_sub
        by blast
    qed
  qed
  show ?thesis unfolding closedin_on_def using hAX hXmA_open
    by argo
qed

(** from \S43 Theorem 43.5 [top1.tex:6242]
    Proof: Cauchy in uniform metric \<Rightarrow> coordinatewise Cauchy in Y \<Rightarrow> coordinatewise convergent
    (by completeness of Y) \<Rightarrow> uniform convergence. **)
theorem Theorem_43_5:
  assumes hIne: "I \<noteq> {}"
  assumes hd: "top1_complete_metric_on Y d"
  shows "top1_complete_metric_on (top1_PiE I (\<lambda>_. Y)) (top1_uniform_metric_on I d)"
proof -
  let ?X = "top1_PiE I (\<lambda>_. Y)"
  let ?rho = "top1_uniform_metric_on I d"
  let ?db = "top1_bounded_metric d"
  have hdm: "top1_metric_on Y d"
    using hd unfolding top1_complete_metric_on_def
    by satx
  have hdbm: "top1_metric_on Y ?db"
    using top1_bounded_metric_on[OF hdm]
    by satx
  have hrho_m: "top1_metric_on ?X ?rho"
    using top1_uniform_metric_is_metric[OF hIne hdm]
    by satx
  text \<open>Completeness in d implies completeness in bounded d.\<close>
  have hdb_complete: "top1_complete_metric_on Y ?db"
  proof -
    have htopo_eq: "top1_metric_topology_on Y ?db = top1_metric_topology_on Y d"
      using Theorem_20_1[OF hdm]
      by satx
    show ?thesis unfolding top1_complete_metric_on_def
    proof (intro conjI allI impI)
      show "top1_metric_on Y ?db" by (rule hdbm)
    next
      fix s assume hCauchy_db: "top1_cauchy_seq_on Y ?db s"
      text \<open>db-Cauchy implies d-Cauchy (for small eps, db = d).\<close>
      have hCauchy_d: "top1_cauchy_seq_on Y d s"
        unfolding top1_cauchy_seq_on_def
      proof (intro allI impI)
        fix e :: real assume hepos: "0 < e"
        define e' where "e' = min e (1/2)"
        have he'pos: "0 < e'"
          unfolding e'_def using hepos
          by auto
        have he'le1: "e' \<le> 1" unfolding e'_def
          by linarith
        have he'le: "e' \<le> e" unfolding e'_def
          by simp
        obtain N where hN: "\<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> Y \<and> s n \<in> Y \<and> ?db (s m) (s n) < e'"
          using hCauchy_db he'pos unfolding top1_cauchy_seq_on_def
          by presburger
        show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> Y \<and> s n \<in> Y \<and> d (s m) (s n) < e"
        proof (intro exI allI impI)
          fix m n :: nat assume hmN: "N \<le> m" and hnN: "N \<le> n"
          have hsmY: "s m \<in> Y" using hN hmN hnN by presburger
          have hsnY: "s n \<in> Y" using hN hmN hnN by presburger
          have hdb_small: "?db (s m) (s n) < e'" using hN hmN hnN by presburger
          have "d (s m) (s n) < e'"
          proof -
            have "?db (s m) (s n) = min (d (s m) (s n)) 1"
              unfolding top1_bounded_metric_def
              by presburger
            then have "min (d (s m) (s n)) 1 < e'" using hdb_small
              by presburger
            then show "d (s m) (s n) < e'" using he'le1
              by auto
          qed
          then show "s m \<in> Y \<and> s n \<in> Y \<and> d (s m) (s n) < e"
            using hsmY hsnY he'le
            by simp
        qed
      qed
      text \<open>d-complete gives convergence in d-topology.\<close>
      obtain x where hxY: "x \<in> Y" and hconv_d: "seq_converges_to_on s x Y (top1_metric_topology_on Y d)"
        using hd hCauchy_d unfolding top1_complete_metric_on_def
        by blast
      text \<open>Same topology, so convergence in db-topology.\<close>
      have hconv_db: "seq_converges_to_on s x Y (top1_metric_topology_on Y ?db)"
        using hconv_d htopo_eq
        by argo
      show "\<exists>x\<in>Y. seq_converges_to_on s x Y (top1_metric_topology_on Y ?db)"
        using hxY hconv_db
        by blast
    qed
  qed
  text \<open>Every Cauchy seq in (PiE, rho) converges.\<close>
  show ?thesis unfolding top1_complete_metric_on_def
  proof (intro conjI allI impI)
    show "top1_metric_on ?X ?rho" by (rule hrho_m)
  next
    fix s assume hCauchy: "top1_cauchy_seq_on ?X ?rho s"
    text \<open>Each coordinate sequence is Cauchy.\<close>
    have hcoord_cauchy: "\<forall>\<alpha>\<in>I. top1_cauchy_seq_on Y ?db (\<lambda>n. s n \<alpha>)"
      unfolding top1_cauchy_seq_on_def
    proof (intro ballI allI impI)
      fix \<alpha> and e :: real assume h\<alpha>: "\<alpha> \<in> I" and hepos: "0 < e"
      obtain N where hN: "\<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> ?X \<and> s n \<in> ?X \<and> ?rho (s m) (s n) < e"
        using hCauchy hepos unfolding top1_cauchy_seq_on_def
        by presburger
      show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. (\<lambda>n. s n \<alpha>) m \<in> Y \<and> (\<lambda>n. s n \<alpha>) n \<in> Y \<and> ?db ((\<lambda>n. s n \<alpha>) m) ((\<lambda>n. s n \<alpha>) n) < e"
      proof (intro exI allI impI)
        fix m n :: nat assume hmN: "N \<le> m" and hnN: "N \<le> n"
        have hsm: "s m \<in> ?X" using hN hmN hnN by presburger
        have hsn: "s n \<in> ?X" using hN hmN hnN by presburger
        have hrho_mn: "?rho (s m) (s n) < e" using hN hmN hnN by presburger
        have "s m \<alpha> \<in> Y" using hsm h\<alpha> unfolding top1_PiE_def top1_Pi_def
          by blast
        moreover have "s n \<alpha> \<in> Y" using hsn h\<alpha> unfolding top1_PiE_def top1_Pi_def
          by blast
        moreover have "?db (s m \<alpha>) (s n \<alpha>) < e"
        proof -
          have hle: "?db (s m \<alpha>) (s n \<alpha>) \<le> ?rho (s m) (s n)"
          proof -
            have hrho_eq: "?rho (s m) (s n) = Sup ((\<lambda>i. ?db (s m i) (s n i)) ` I)"
              using hIne unfolding top1_uniform_metric_on_def
              by simp
            have hmem: "?db (s m \<alpha>) (s n \<alpha>) \<in> (\<lambda>i. ?db (s m i) (s n i)) ` I" using h\<alpha>
              by blast
            have hbdd: "bdd_above ((\<lambda>i. ?db (s m i) (s n i)) ` I)"
            proof (intro bdd_aboveI)
              fix x assume "x \<in> (\<lambda>i. ?db (s m i) (s n i)) ` I"
              then obtain j where hj: "j \<in> I" and hxeq: "x = ?db (s m j) (s n j)"
                by blast
              show "x \<le> 1" unfolding hxeq top1_bounded_metric_def
                by simp
            qed
            show ?thesis using cSup_upper[OF hmem hbdd] hrho_eq
              by presburger
          qed
          show ?thesis using hle hrho_mn
            by simp
        qed
        ultimately show "(\<lambda>n. s n \<alpha>) m \<in> Y \<and> (\<lambda>n. s n \<alpha>) n \<in> Y \<and> ?db ((\<lambda>n. s n \<alpha>) m) ((\<lambda>n. s n \<alpha>) n) < e"
          by presburger
      qed
    qed
    text \<open>Each coordinate converges by completeness of Y.\<close>
    have hcoord_conv: "\<forall>\<alpha>\<in>I. \<exists>y\<in>Y. seq_converges_to_on (\<lambda>n. s n \<alpha>) y Y (top1_metric_topology_on Y ?db)"
      using hdb_complete hcoord_cauchy unfolding top1_complete_metric_on_def
      by blast
    text \<open>Define limit function.\<close>
    define flim where "flim \<alpha> = (if \<alpha> \<in> I then (SOME y. y \<in> Y \<and> seq_converges_to_on (\<lambda>n. s n \<alpha>) y Y (top1_metric_topology_on Y ?db)) else undefined)" for \<alpha>
    have hflim: "\<forall>\<alpha>\<in>I. flim \<alpha> \<in> Y \<and> seq_converges_to_on (\<lambda>n. s n \<alpha>) (flim \<alpha>) Y (top1_metric_topology_on Y ?db)"
    proof (intro ballI)
      fix \<alpha> assume h\<alpha>: "\<alpha> \<in> I"
      have hex: "\<exists>y\<in>Y. seq_converges_to_on (\<lambda>n. s n \<alpha>) y Y (top1_metric_topology_on Y ?db)"
        using hcoord_conv h\<alpha>
        by blast
      then obtain y0 where hy0Y: "y0 \<in> Y" and hy0conv: "seq_converges_to_on (\<lambda>n. s n \<alpha>) y0 Y (top1_metric_topology_on Y ?db)"
        by blast
      have hP: "y0 \<in> Y \<and> seq_converges_to_on (\<lambda>n. s n \<alpha>) y0 Y (top1_metric_topology_on Y ?db)"
        using hy0Y hy0conv
        by argo
      let ?P = "\<lambda>y. y \<in> Y \<and> seq_converges_to_on (\<lambda>n. s n \<alpha>) y Y (top1_metric_topology_on Y ?db)"
      have hsome: "?P (SOME y. ?P y)"
        using someI[where P="?P" and x=y0] hP
        by linarith
      have "flim \<alpha> = (SOME y. y \<in> Y \<and> seq_converges_to_on (\<lambda>n. s n \<alpha>) y Y (top1_metric_topology_on Y ?db))"
        unfolding flim_def using h\<alpha>
        by argo
      then show "flim \<alpha> \<in> Y \<and> seq_converges_to_on (\<lambda>n. s n \<alpha>) (flim \<alpha>) Y (top1_metric_topology_on Y ?db)"
        using hsome
        by argo
    qed
    have hflim_ext: "\<forall>\<alpha>. \<alpha> \<notin> I \<longrightarrow> flim \<alpha> = undefined"
      unfolding flim_def
      by force
    have hflim_PiE: "flim \<in> ?X"
      unfolding top1_PiE_def top1_Pi_def top1_extensional_def
      using hflim hflim_ext
      by blast
    text \<open>Show s → flim in uniform metric.\<close>
    text \<open>Show s → flim in uniform metric via ε-δ characterization.\<close>
    have hconv_rho: "seq_converges_to_on s flim ?X (top1_metric_topology_on ?X ?rho)"
      unfolding metric_seq_conv_iff[OF hrho_m hflim_PiE]
    proof (intro allI impI)
      fix \<epsilon> :: real assume hepos: "0 < \<epsilon>"
      define e2 where "e2 = \<epsilon> / 2"
      have he2pos: "0 < e2" unfolding e2_def using hepos
        by auto
      obtain N where hN: "\<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> ?X \<and> s n \<in> ?X \<and> ?rho (s m) (s n) < e2"
        using hCauchy he2pos unfolding top1_cauchy_seq_on_def
        by presburger
      show "\<exists>N. \<forall>n\<ge>N. s n \<in> ?X \<and> ?rho (s n) flim < \<epsilon>"
      proof (intro exI allI impI)
        fix n assume hnN: "N \<le> n"
        have hsnX: "s n \<in> ?X" using hN hnN
          by auto
        text \<open>For each α, d̄(s_n(α), flim(α)) ≤ e2.\<close>
        have hcoord_bound: "\<forall>\<alpha>\<in>I. ?db (s n \<alpha>) (flim \<alpha>) \<le> e2"
        proof (intro ballI)
          fix \<alpha> assume h\<alpha>: "\<alpha> \<in> I"
          text \<open>d̄(s_n(α), s_m(α)) < e2 for all m ≥ N (from Cauchy).\<close>
          have hbound_m: "\<forall>m\<ge>N. ?db ((\<lambda>m. s m \<alpha>) m) (s n \<alpha>) \<le> e2"
          proof (intro allI impI)
            fix m assume hmN: "N \<le> m"
            have "?db (s m \<alpha>) (s n \<alpha>) \<le> ?rho (s m) (s n)"
            proof -
              have hsmX: "s m \<in> ?X" using hN hmN hnN
                by presburger
              have hsnX2: "s n \<in> ?X" using hsnX
                by argo
              have hrho_eq2: "?rho (s m) (s n) = Sup ((\<lambda>i. ?db (s m i) (s n i)) ` I)"
                using hIne unfolding top1_uniform_metric_on_def
                by presburger
              have hmem2: "?db (s m \<alpha>) (s n \<alpha>) \<in> (\<lambda>i. ?db (s m i) (s n i)) ` I" using h\<alpha>
                by fast
              have hbdd2: "bdd_above ((\<lambda>i. ?db (s m i) (s n i)) ` I)"
              proof (intro bdd_aboveI)
                fix x assume "x \<in> (\<lambda>i. ?db (s m i) (s n i)) ` I"
                then show "x \<le> 1" unfolding top1_bounded_metric_def
                  by force
              qed
              show ?thesis using cSup_upper[OF hmem2 hbdd2] hrho_eq2
                by presburger
            qed
            also have "... < e2" using hN hmN hnN
              by presburger
            finally show "?db ((\<lambda>m. s m \<alpha>) m) (s n \<alpha>) \<le> e2"
              by simp
          qed
          text \<open>s_m(α) → flim(α), so by limit-preserves-bound: d̄(s_n(α), flim(α)) ≤ e2.\<close>
          have hconv_\<alpha>: "seq_converges_to_on (\<lambda>m. s m \<alpha>) (flim \<alpha>) Y (top1_metric_topology_on Y ?db)"
            using hflim h\<alpha>
            by auto
          have hflim_\<alpha>Y: "flim \<alpha> \<in> Y" using hflim h\<alpha>
            by blast
          have hsn_\<alpha>Y: "s n \<alpha> \<in> Y" using hsnX h\<alpha> unfolding top1_PiE_def top1_Pi_def
            by blast
          have he2nn: "0 \<le> e2" using he2pos
            by linarith
          have "?db (flim \<alpha>) (s n \<alpha>) \<le> e2"
            using metric_limit_preserves_bound[OF hdbm hconv_\<alpha> hbound_m hsn_\<alpha>Y he2nn]
            by satx
          have "?db (s n \<alpha>) (flim \<alpha>) = ?db (flim \<alpha>) (s n \<alpha>)"
            using hdbm hsn_\<alpha>Y hflim_\<alpha>Y unfolding top1_metric_on_def
            by blast
          show "?db (s n \<alpha>) (flim \<alpha>) \<le> e2"
            using \<open>?db (flim \<alpha>) (s n \<alpha>) \<le> e2\<close> \<open>?db (s n \<alpha>) (flim \<alpha>) = ?db (flim \<alpha>) (s n \<alpha>)\<close>
            by presburger
        qed
        text \<open>rho(s_n, flim) = Sup ≤ e2 < ε.\<close>
        have hrho_bound: "?rho (s n) flim \<le> e2"
        proof -
          have hrho_eq: "?rho (s n) flim = Sup ((\<lambda>i. ?db (s n i) (flim i)) ` I)"
            using hIne unfolding top1_uniform_metric_on_def
            by presburger
          have hne: "(\<lambda>i. ?db (s n i) (flim i)) ` I \<noteq> {}" using hIne
            by fast
          show ?thesis unfolding hrho_eq
            using cSup_least[OF hne] hcoord_bound
            by blast
        qed
        show "s n \<in> ?X \<and> ?rho (s n) flim < \<epsilon>"
          using hsnX hrho_bound unfolding e2_def
          using hepos by force
      qed
    qed
    show "\<exists>x\<in>?X. seq_converges_to_on s x ?X (top1_metric_topology_on ?X ?rho)"
      using hflim_PiE hconv_rho
      by blast
  qed
qed

text \<open>Convergence in uniform metric implies pointwise uniform convergence in d.\<close>
lemma uniform_metric_conv_imp_pointwise_unif:
  assumes hXne: "X \<noteq> {}"
  assumes hd: "top1_metric_on Y d"
  assumes hf_PiE: "f \<in> top1_PiE X (\<lambda>_. Y)"
  assumes hfn_PiE: "\<forall>n::nat. fseq n \<in> top1_PiE X (\<lambda>_. Y)"
  assumes hconv: "seq_converges_to_on fseq f (top1_PiE X (\<lambda>_. Y))
    (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))"
  shows "\<forall>\<epsilon>>0. \<exists>N::nat. \<forall>n\<ge>N. \<forall>x\<in>X. d (fseq n x) (f x) < \<epsilon>"
proof (intro allI impI)
  let ?rho = "top1_uniform_metric_on X d"
  let ?db = "top1_bounded_metric d"
  let ?PX = "top1_PiE X (\<lambda>_. Y)"
  have hrho_m: "top1_metric_on ?PX ?rho"
    using top1_uniform_metric_is_metric[OF hXne hd]
    by linarith
  fix \<epsilon> :: real assume hepos: "0 < \<epsilon>"
  define e' where "e' = min \<epsilon> (1/2)"
  have he'pos: "0 < e'" unfolding e'_def using hepos
    by auto
  have he'le1: "e' \<le> 1" unfolding e'_def
    by linarith
  have he'le: "e' \<le> \<epsilon>" unfolding e'_def
    by simp
  text \<open>From metric convergence, get N with rho(f_n, f) < e'.\<close>
  have heps_conv: "\<forall>e>0. \<exists>N::nat. \<forall>n\<ge>N. fseq n \<in> ?PX \<and> ?rho (fseq n) f < e"
    using hconv unfolding metric_seq_conv_iff[OF hrho_m hf_PiE]
    by argo
  obtain N :: nat where hN: "\<forall>n\<ge>N. fseq n \<in> ?PX \<and> ?rho (fseq n) f < e'"
    using heps_conv he'pos
    by blast
  show "\<exists>N::nat. \<forall>n\<ge>N. \<forall>x\<in>X. d (fseq n x) (f x) < \<epsilon>"
  proof (intro exI allI impI ballI)
    fix n x assume hnN: "N \<le> n" and hxX: "x \<in> X"
    have hrho_small: "?rho (fseq n) f < e'" using hN hnN
      by presburger
    text \<open>d̄(f_n(x), f(x)) ≤ rho(f_n, f).\<close>
    have hdb_le: "?db (fseq n x) (f x) \<le> ?rho (fseq n) f"
    proof -
      have hrho_eq: "?rho (fseq n) f = Sup ((\<lambda>i. ?db (fseq n i) (f i)) ` X)"
        using hXne unfolding top1_uniform_metric_on_def
        by presburger
      have hmem: "?db (fseq n x) (f x) \<in> (\<lambda>i. ?db (fseq n i) (f i)) ` X" using hxX
        by blast
      have hbdd: "bdd_above ((\<lambda>i. ?db (fseq n i) (f i)) ` X)"
      proof (intro bdd_aboveI)
        fix v assume "v \<in> (\<lambda>i. ?db (fseq n i) (f i)) ` X"
        then show "v \<le> 1" unfolding top1_bounded_metric_def
          by fastforce
      qed
      show ?thesis using cSup_upper[OF hmem hbdd] hrho_eq
        by presburger
    qed
    have "?db (fseq n x) (f x) < e'" using hdb_le hrho_small
      by linarith
    text \<open>Since e' ≤ 1, d̄ = min(d, 1) < e' ≤ 1, so d < e'.\<close>
    then have "min (d (fseq n x) (f x)) 1 < e'" unfolding top1_bounded_metric_def
      by presburger
    then have "d (fseq n x) (f x) < e'" using he'le1
      by fastforce
    then show "d (fseq n x) (f x) < \<epsilon>" using he'le
      by linarith
  qed
qed

(** from \S43 Theorem 43.6 [top1.tex:6272]
    Proof: (a-b) continuous/bounded maps closed in uniform topology (uniform limit theorem).
    (c-d) Closed subsets of complete spaces are complete. **)
text \<open>Part (a): C(X,Y) is closed in Y^X under the uniform metric.\<close>
theorem Theorem_43_6a:
  assumes hd: "top1_metric_on Y d"
  assumes hTopX: "is_topology_on X TX"
  assumes hXne: "X \<noteq> {}"
  shows "closedin_on
           (top1_PiE X (\<lambda>_. Y))
           (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))
           (top1_continuous_maps_metric_on X TX Y d)"
proof (rule metric_seq_closed_imp_closed)
  show "top1_metric_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d)"
    using top1_uniform_metric_is_metric[OF hXne hd]
    by presburger
  show "top1_continuous_maps_metric_on X TX Y d \<subseteq> top1_PiE X (\<lambda>_. Y)"
    unfolding top1_continuous_maps_metric_on_def
    by blast
  show "\<forall>s. (\<forall>n::nat. s n \<in> top1_continuous_maps_metric_on X TX Y d) \<longrightarrow>
    (\<forall>x. seq_converges_to_on s x (top1_PiE X (\<lambda>_. Y))
      (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d)) \<longrightarrow>
      x \<in> top1_continuous_maps_metric_on X TX Y d)"
  proof (intro allI impI)
    fix s x
    assume hsC: "\<forall>n::nat. s n \<in> top1_continuous_maps_metric_on X TX Y d"
    assume hconv: "seq_converges_to_on s x (top1_PiE X (\<lambda>_. Y))
      (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))"
    text \<open>x ∈ PiE X Y from convergence.\<close>
    have hxPiE: "x \<in> top1_PiE X (\<lambda>_. Y)"
      using hconv unfolding seq_converges_to_on_def
      by satx
    text \<open>Each s n is continuous.\<close>
    have hscont: "\<forall>n::nat. top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) (s n)"
      using hsC unfolding top1_continuous_maps_metric_on_def
      by fast
    have hsPiE: "\<forall>n::nat. s n \<in> top1_PiE X (\<lambda>_. Y)"
      using hsC unfolding top1_continuous_maps_metric_on_def
      by blast
    text \<open>s converges to x uniformly in d.\<close>
    have hunif: "\<forall>\<epsilon>>0. \<exists>N::nat. \<forall>n\<ge>N. \<forall>xa\<in>X. d (s n xa) (x xa) < \<epsilon>"
      using uniform_metric_conv_imp_pointwise_unif[OF hXne hd hxPiE hsPiE hconv]
      by argo
    text \<open>x maps into Y.\<close>
    have hxY: "\<forall>xa\<in>X. x xa \<in> Y"
      using hxPiE unfolding top1_PiE_def top1_Pi_def
      by fast
    text \<open>By uniform limit theorem, x is continuous.\<close>
    have hxcont: "top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) x"
      using uniform_limit_continuous[OF hTopX hd hscont hunif hxY]
      by argo
    show "x \<in> top1_continuous_maps_metric_on X TX Y d"
      unfolding top1_continuous_maps_metric_on_def using hxPiE hxcont
      by force
  qed
qed

text \<open>Metric on a subset: restriction of a metric to a subset is a metric.\<close>
lemma metric_on_subset:
  assumes hd: "top1_metric_on X d"
  assumes hAX: "A \<subseteq> X"
  shows "top1_metric_on A d"
  unfolding top1_metric_on_def
  using hd hAX unfolding top1_metric_on_def
  by blast

text \<open>Convergent sequence eventually in closed set → limit in closed set.\<close>
lemma metric_conv_eventually_in_closed:
  assumes hd: "top1_metric_on X d"
  assumes hCl: "closedin_on X (top1_metric_topology_on X d) A"
  assumes hconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
  assumes hevent: "\<exists>N::nat. \<forall>n\<ge>N. s n \<in> A"
  shows "x \<in> A"
proof (rule ccontr)
  assume hxnA: "x \<notin> A"
  have hxX: "x \<in> X" using hconv unfolding seq_converges_to_on_def
    by presburger
  have hXmA_open: "X - A \<in> top1_metric_topology_on X d"
    using hCl unfolding closedin_on_def
    by presburger
  have hxXmA: "x \<in> X - A" using hxX hxnA
    by blast
  obtain r where hrpos: "0 < r" and hball_sub: "top1_ball_on X d x r \<subseteq> X - A"
    using top1_metric_open_contains_ball[OF hd hXmA_open hxXmA]
    by blast
  text \<open>s eventually in ball and eventually in A — contradiction.\<close>
  have hball_open: "top1_ball_on X d x r \<in> top1_metric_topology_on X d"
    using top1_ball_open_in_metric_topology[OF hd hxX hrpos]
    by presburger
  have "d x x = 0" using hd hxX unfolding top1_metric_on_def
    by blast
  have hx_in_ball: "x \<in> top1_ball_on X d x r"
    unfolding top1_ball_on_def using hxX \<open>d x x = 0\<close> hrpos
    by force
  have hball_nbhd: "neighborhood_of x X (top1_metric_topology_on X d) (top1_ball_on X d x r)"
    unfolding neighborhood_of_def using hball_open hx_in_ball
    by presburger
  obtain M :: nat where hM: "\<forall>n\<ge>M. s n \<in> top1_ball_on X d x r"
    using hconv hball_nbhd unfolding seq_converges_to_on_def
    by blast
  obtain N :: nat where hN: "\<forall>n\<ge>N. s n \<in> A" using hevent
    by auto
  define k where "k = max M N"
  have "s k \<in> top1_ball_on X d x r" using hM unfolding k_def
    by fastforce
  then have "s k \<in> X - A" using hball_sub
    by blast
  moreover have "s k \<in> A" using hN unfolding k_def
    by fastforce
  ultimately show False
    by blast
qed

text \<open>Closed subset of a complete metric space is complete.\<close>
lemma closed_subset_complete:
  assumes hd: "top1_metric_on X d"
  assumes hComp: "top1_complete_metric_on X d"
  assumes hCl: "closedin_on X (top1_metric_topology_on X d) A"
  shows "top1_complete_metric_on A d"
proof -
  have hAX: "A \<subseteq> X" using hCl unfolding closedin_on_def
    by presburger
  have hdA: "top1_metric_on A d" using metric_on_subset[OF hd hAX]
    by presburger
  show ?thesis unfolding top1_complete_metric_on_def
  proof (intro conjI allI impI)
    show "top1_metric_on A d" by (rule hdA)
  next
    fix s assume hCauchy_A: "top1_cauchy_seq_on A d s"
    text \<open>s is Cauchy in X.\<close>
    have hCauchy_X: "top1_cauchy_seq_on X d s"
      unfolding top1_cauchy_seq_on_def
    proof (intro allI impI)
      fix e :: real assume "0 < e"
      obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> A \<and> s n \<in> A \<and> d (s m) (s n) < e"
        using hCauchy_A \<open>0 < e\<close> unfolding top1_cauchy_seq_on_def
        by presburger
      then show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> X \<and> s n \<in> X \<and> d (s m) (s n) < e"
        using hAX
        by auto
    qed
    obtain x where hxX: "x \<in> X" and hconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
      using hComp hCauchy_X unfolding top1_complete_metric_on_def
      by blast
    text \<open>s is eventually in A (from Cauchy).\<close>
    have hevent: "\<exists>N::nat. \<forall>n\<ge>N. s n \<in> A"
    proof -
      obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> A \<and> s n \<in> A \<and> d (s m) (s n) < 1"
        using hCauchy_A unfolding top1_cauchy_seq_on_def
        by fastforce
      then show ?thesis
        by blast
    qed
    text \<open>x ∈ A by closedness.\<close>
    have hxA: "x \<in> A"
      using metric_conv_eventually_in_closed[OF hd hCl hconv hevent]
      by presburger
    text \<open>Convergence in subspace = convergence with restricted carrier.\<close>
    have hconv_A: "seq_converges_to_on s x A (top1_metric_topology_on A d)"
      unfolding metric_seq_conv_iff[OF hdA hxA]
    proof (intro allI impI)
      fix \<epsilon> :: real assume hepos: "0 < \<epsilon>"
      have hconv_eps: "\<forall>\<epsilon>>0. \<exists>N::nat. \<forall>n\<ge>N. s n \<in> X \<and> d (s n) x < \<epsilon>"
        using hconv unfolding metric_seq_conv_iff[OF hd hxX]
        by argo
      obtain N1 :: nat where hN1: "\<forall>n\<ge>N1. s n \<in> X \<and> d (s n) x < \<epsilon>"
        using hconv_eps hepos
        by presburger
      obtain N2 :: nat where hN2: "\<forall>n\<ge>N2. s n \<in> A"
        using hevent
        by blast
      show "\<exists>N::nat. \<forall>n\<ge>N. s n \<in> A \<and> d (s n) x < \<epsilon>"
      proof (intro exI allI impI)
        fix n assume "max N1 N2 \<le> n"
        then have hN1n: "N1 \<le> n" by simp
        have hN2n: "N2 \<le> n" using \<open>max N1 N2 \<le> n\<close> by simp
        show "s n \<in> A \<and> d (s n) x < \<epsilon>" using hN1 hN2 hN1n hN2n by presburger
      qed
    qed
    show "\<exists>x\<in>A. seq_converges_to_on s x A (top1_metric_topology_on A d)"
      using hxA hconv_A
      by blast
  qed
qed

text \<open>Part (c): C(X,Y) complete when Y complete. Uses 43.5 + 43.6a + closed-subset-complete.\<close>
theorem Theorem_43_6c:
  assumes hd: "top1_metric_on Y d"
  assumes hTopX: "is_topology_on X TX"
  assumes hXne: "X \<noteq> {}"
  assumes hYcomp: "top1_complete_metric_on Y d"
  shows "top1_complete_metric_on (top1_continuous_maps_metric_on X TX Y d) (top1_uniform_metric_on X d)"
proof -
  let ?PX = "top1_PiE X (\<lambda>_. Y)"
  let ?rho = "top1_uniform_metric_on X d"
  have hrho_m: "top1_metric_on ?PX ?rho"
    using top1_uniform_metric_is_metric[OF hXne hd]
    by blast
  have hPX_complete: "top1_complete_metric_on ?PX ?rho"
    using Theorem_43_5[OF hXne hYcomp]
    by satx
  have hClosed: "closedin_on ?PX (top1_metric_topology_on ?PX ?rho) (top1_continuous_maps_metric_on X TX Y d)"
    using Theorem_43_6a[OF hd hTopX hXne]
    by argo
  show ?thesis
    using closed_subset_complete[OF hrho_m hPX_complete hClosed]
    by argo
qed

text \<open>Part (b): B(X,Y) is closed in Y^X under uniform metric.\<close>
theorem Theorem_43_6b:
  assumes hd: "top1_metric_on Y d"
  assumes hXne: "X \<noteq> {}"
  shows "closedin_on
           (top1_PiE X (\<lambda>_. Y))
           (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))
           (top1_bounded_maps_metric_on X Y d)"
proof (rule metric_seq_closed_imp_closed)
  show hrho_m: "top1_metric_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d)"
    using top1_uniform_metric_is_metric[OF hXne hd]
    by satx
  show "top1_bounded_maps_metric_on X Y d \<subseteq> top1_PiE X (\<lambda>_. Y)"
    unfolding top1_bounded_maps_metric_on_def
    by blast
  show "\<forall>s. (\<forall>n::nat. s n \<in> top1_bounded_maps_metric_on X Y d) \<longrightarrow>
    (\<forall>x. seq_converges_to_on s x (top1_PiE X (\<lambda>_. Y))
      (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d)) \<longrightarrow>
      x \<in> top1_bounded_maps_metric_on X Y d)"
  proof (intro allI impI)
    fix s x
    assume hsB: "\<forall>n::nat. s n \<in> top1_bounded_maps_metric_on X Y d"
    assume hconv: "seq_converges_to_on s x (top1_PiE X (\<lambda>_. Y))
      (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))"
    have hxPiE: "x \<in> top1_PiE X (\<lambda>_. Y)"
      using hconv unfolding seq_converges_to_on_def
      by satx
    have hsPiE: "\<forall>n::nat. s n \<in> top1_PiE X (\<lambda>_. Y)"
      using hsB unfolding top1_bounded_maps_metric_on_def
      by fast
    text \<open>Get uniform convergence.\<close>
    have hunif: "\<forall>\<epsilon>>0. \<exists>N::nat. \<forall>n\<ge>N. \<forall>xa\<in>X. d (s n xa) (x xa) < \<epsilon>"
      using uniform_metric_conv_imp_pointwise_unif[OF hXne hd hxPiE hsPiE hconv]
      by argo
    obtain N :: nat where hN: "\<forall>xa\<in>X. d (s N xa) (x xa) < 1/2"
    proof -
      have "0 < (1::real)/2"
        by simp
      then obtain N :: nat where "\<forall>n\<ge>N. \<forall>xa\<in>X. d (s n xa) (x xa) < 1/2"
        using hunif
        by presburger
      then have "\<forall>xa\<in>X. d (s N xa) (x xa) < 1/2"
        by blast
      then show ?thesis using that
        by blast
    qed
    have hsBound: "top1_bounded_map_on X Y d (s N)"
      using hsB unfolding top1_bounded_maps_metric_on_def
      by blast
    obtain y0 M where hy0: "y0 \<in> Y" and hM: "\<forall>xa\<in>X. d y0 (s N xa) \<le> M"
      using hsBound unfolding top1_bounded_map_on_def
      by blast
    have hxBound: "top1_bounded_map_on X Y d x"
      unfolding top1_bounded_map_on_def
    proof (intro bexI exI ballI)
      fix xa assume hxa: "xa \<in> X"
      have hxaY: "x xa \<in> Y" using hxPiE hxa unfolding top1_PiE_def top1_Pi_def
        by blast
      have hsNxaY: "s N xa \<in> Y" using hsPiE hxa unfolding top1_PiE_def top1_Pi_def
        by blast
      have htri: "d y0 (x xa) \<le> d y0 (s N xa) + d (s N xa) (x xa)"
        using hd hy0 hsNxaY hxaY unfolding top1_metric_on_def
        by blast
      show "d y0 (x xa) \<le> M + 1 / 2"
        using htri hM hxa hN hxa
        by fastforce
    next
      show "y0 \<in> Y" by (rule hy0)
    qed
    show "x \<in> top1_bounded_maps_metric_on X Y d"
      unfolding top1_bounded_maps_metric_on_def using hxPiE hxBound
      by fast
  qed
qed

text \<open>Part (d): B(X,Y) complete when Y complete.\<close>
theorem Theorem_43_6d:
  assumes hd: "top1_metric_on Y d"
  assumes hXne: "X \<noteq> {}"
  assumes hYcomp: "top1_complete_metric_on Y d"
  shows "top1_complete_metric_on (top1_bounded_maps_metric_on X Y d) (top1_uniform_metric_on X d)"
proof -
  let ?PX = "top1_PiE X (\<lambda>_. Y)"
  let ?rho = "top1_uniform_metric_on X d"
  have hrho_m: "top1_metric_on ?PX ?rho"
    using top1_uniform_metric_is_metric[OF hXne hd]
    by presburger
  have hPX_complete: "top1_complete_metric_on ?PX ?rho"
    using Theorem_43_5[OF hXne hYcomp]
    by blast
  have hClosed: "closedin_on ?PX (top1_metric_topology_on ?PX ?rho) (top1_bounded_maps_metric_on X Y d)"
    using Theorem_43_6b[OF hd hXne]
    by blast
  show ?thesis
    using closed_subset_complete[OF hrho_m hPX_complete hClosed]
    by argo
qed

definition top1_isometry_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real)
    \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_isometry_on X d Y dY e \<longleftrightarrow>
     (\<forall>x\<in>X. e x \<in> Y) \<and> (\<forall>x\<in>X. \<forall>x'\<in>X. dY (e x) (e x') = d x x')"

(** from \S43 Theorem 43.7 (Completion) [top1.tex:6312]
    Proof: Embed X isometrically into the complete space of bounded continuous functions
    X \<rightarrow> R via x \<mapsto> d(x, \<cdot>). The closure of the image is the completion. **)
theorem Theorem_43_7:
  assumes hd: "top1_metric_on X d"
  shows "\<exists>Y dY e. top1_complete_metric_on Y dY \<and> top1_isometry_on X d Y dY e"
  sorry

section \<open>*\<S>44 A Space-Filling Curve\<close>

(** from \S44 Theorem 44.1 (Peano curve) [top1.tex:6444] **)
theorem Theorem_44_1:
  shows "\<exists>f::real \<Rightarrow> (real \<times> real).
    top1_continuous_map_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)
      ((top1_closed_interval 0 1) \<times> (top1_closed_interval 0 1))
      (product_topology_on (top1_closed_interval_topology 0 1) (top1_closed_interval_topology 0 1)) f
    \<and> f ` (top1_closed_interval 0 1) = (top1_closed_interval 0 1) \<times> (top1_closed_interval 0 1)"
  sorry

section \<open>\<S>45 Compactness in Metric Spaces\<close>

definition top1_totally_bounded_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "top1_totally_bounded_on X d \<longleftrightarrow>
     (\<forall>e>0. \<exists>F. finite F \<and> F \<subseteq> X \<and> X \<subseteq> (\<Union>x\<in>F. top1_ball_on X d x e))"

(** from \S45 Theorem 45.1 [top1.tex:6560] **)
theorem Theorem_45_1:
  assumes hd: "top1_metric_on X d"
  shows "top1_compact_on X (top1_metric_topology_on X d)
    \<longleftrightarrow> (top1_complete_metric_on X d \<and> top1_totally_bounded_on X d)"
  sorry

definition top1_equicontinuous_family_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set \<Rightarrow> bool" where
  "top1_equicontinuous_family_on X TX Y d \<F> \<longleftrightarrow>
     (\<forall>f\<in>\<F>. \<forall>x\<in>X. f x \<in> Y)
     \<and> (\<forall>x0\<in>X. \<forall>\<epsilon>>0. \<exists>U\<in>TX. x0 \<in> U \<and> (\<forall>f\<in>\<F>. \<forall>x\<in>U. d (f x) (f x0) < \<epsilon>))"

definition top1_metric_bounded_subset_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_metric_bounded_subset_on Y d A \<longleftrightarrow> (\<exists>y0\<in>Y. \<exists>M. \<forall>y\<in>A. d y0 y \<le> M)"

definition top1_pointwise_bounded_family_on ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set \<Rightarrow> bool" where
  "top1_pointwise_bounded_family_on X Y d \<F> \<longleftrightarrow> (\<forall>x\<in>X. top1_metric_bounded_subset_on Y d ((\<lambda>f. f x) ` \<F>))"

(** from \S45 Lemma 45.2 [top1.tex:6586] **)
lemma Lemma_45_2:
  assumes hTotB: "top1_totally_bounded_on \<F> (top1_uniform_metric_on X d)"
  shows "top1_equicontinuous_family_on X TX Y d \<F>"
  sorry

(** from \S45 Lemma 45.3 [top1.tex:6618] **)
lemma Lemma_45_3:
  assumes hCompX: "top1_compact_on X TX"
  assumes hCompY: "top1_compact_on Y TY"
  assumes hEqui: "top1_equicontinuous_family_on X TX Y d \<F>"
  shows "top1_totally_bounded_on \<F> (top1_uniform_metric_on X d)"
  sorry

(** from \S45 Theorem 45.4 (Ascoli's theorem, classical version) [top1.tex:6655] **)
theorem Theorem_45_4:
  assumes hCompX: "top1_compact_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hFsub: "\<F> \<subseteq> top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)"
  shows
    "top1_compact_on
       (closure_on
          (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
          (subspace_topology
             (top1_PiE X (\<lambda>_. Y))
             (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))
             (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)))
          \<F>)
       (subspace_topology
          (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
          (subspace_topology
             (top1_PiE X (\<lambda>_. Y))
             (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))
             (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)))
          (closure_on
             (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
             (subspace_topology
                (top1_PiE X (\<lambda>_. Y))
                (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))
                (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)))
             \<F>))
    \<longleftrightarrow> (top1_equicontinuous_family_on X TX Y d \<F> \<and> top1_pointwise_bounded_family_on X Y d \<F>)"
  sorry

(** from \S45 Corollary 45.5 [top1.tex:6679] **)
corollary Corollary_45_5:
  assumes hCompX: "top1_compact_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hFsub: "\<F> \<subseteq> top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)"
  shows
    "top1_compact_on \<F>
       (subspace_topology
          (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
          (subspace_topology
             (top1_PiE X (\<lambda>_. Y))
             (top1_sup_topology_on X Y d)
             (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)))
          \<F>)
    \<longleftrightarrow>
    (closedin_on
       (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
       (subspace_topology
          (top1_PiE X (\<lambda>_. Y))
          (top1_sup_topology_on X Y d)
          (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)))
       \<F>
     \<and> top1_metric_bounded_subset_on (top1_PiE X (\<lambda>_. Y)) (top1_sup_metric_on X d) \<F>
     \<and> top1_equicontinuous_family_on X TX Y d \<F>)"
  sorry

section \<open>\<S>46 Pointwise and Compact Convergence\<close>

definition top1_pointwise_topology_on ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) set set" where
  "top1_pointwise_topology_on X Y TY =
     top1_product_topology_on X (\<lambda>_. Y) (\<lambda>_. TY)"

(** from \S46 Theorem 46.1 [top1.tex:6754] **)
theorem Theorem_46_1:
  assumes hTopY: "is_topology_on Y TY"
  assumes hf: "f \<in> top1_PiE X (\<lambda>_. Y)"
  assumes hs: "\<forall>n. fseq n \<in> top1_PiE X (\<lambda>_. Y)"
  shows "seq_converges_to_on fseq f (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y TY)
    \<longleftrightarrow> (\<forall>x\<in>X. seq_converges_to_on (\<lambda>n. fseq n x) (f x) Y TY)"
proof -
  have hTop: "\<forall>x\<in>X. is_topology_on Y TY"
    using hTopY by simp

  have hEquiv:
    "seq_converges_to_on fseq f (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y TY)
      \<longleftrightarrow>
      (f \<in> top1_PiE X (\<lambda>_. Y)
        \<and> (\<forall>x\<in>X. seq_converges_to_on (\<lambda>n. fseq n x) (f x) Y TY))"
    unfolding top1_pointwise_topology_on_def
    using Lemma_43_3[of X "\<lambda>_. Y" "\<lambda>_. TY" fseq f] hTop hs by simp

  show ?thesis
    using hEquiv hf by simp
qed

definition top1_compactly_generated_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_compactly_generated_on X TX \<longleftrightarrow>
     is_topology_on X TX
     \<and> (\<forall>A. A \<subseteq> X \<longrightarrow>
          (A \<in> TX \<longleftrightarrow>
            (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
                 \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C)))"

definition top1_compact_convergence_basis_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set set" where
  "top1_compact_convergence_basis_on X TX Y d =
     { {g \<in> top1_PiE X (\<lambda>_. Y).
          (if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C)) < \<epsilon>}
       | f C \<epsilon>. f \<in> top1_PiE X (\<lambda>_. Y)
          \<and> top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X \<and> 0 < \<epsilon> }"

definition top1_compact_convergence_topology_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set set" where
  "top1_compact_convergence_topology_on X TX Y d =
     topology_generated_by_basis (top1_PiE X (\<lambda>_. Y)) (top1_compact_convergence_basis_on X TX Y d)"

definition top1_uniform_topology_on ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) set set" where
  "top1_uniform_topology_on X Y d =
     top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d)"

definition top1_continuous_funcs_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "top1_continuous_funcs_on X TX Y TY =
     {f \<in> top1_PiE X (\<lambda>_. Y). top1_continuous_map_on X TX Y TY f}"

definition top1_compact_open_subbasis_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) set set" where
  "top1_compact_open_subbasis_on X TX Y TY =
     { {f \<in> top1_continuous_funcs_on X TX Y TY. f ` C \<subseteq> U}
       | C U. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X \<and> U \<in> TY }"

definition top1_compact_open_topology_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('a \<Rightarrow> 'b) set set" where
  "top1_compact_open_topology_on X TX Y TY =
     topology_generated_by_subbasis (top1_continuous_funcs_on X TX Y TY) (top1_compact_open_subbasis_on X TX Y TY)"

(** from \S46 Theorem 46.2 [top1.tex:6787] **)
theorem Theorem_46_2:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  shows "seq_converges_to_on fseq f (top1_PiE X (\<lambda>_. Y)) (top1_compact_convergence_topology_on X TX Y d)
    \<longleftrightarrow>
      (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X \<longrightarrow>
        (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>C. d (fseq n x) (f x) < \<epsilon>))"
  sorry

(** from \S46 Lemma 46.3 [top1.tex:6793] **)
lemma Lemma_46_3:
  assumes hLC: "top1_locally_compact_on X TX"
  shows "top1_compactly_generated_on X TX"
proof -
  have hTopX: "is_topology_on X TX"
    using hLC unfolding top1_locally_compact_on_def by simp

  have hLCprop:
    "\<forall>x\<in>X. \<exists>U. neighborhood_of x X TX U \<and> U \<subseteq> X
        \<and> top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
    using hLC unfolding top1_locally_compact_on_def by simp

  show ?thesis
    unfolding top1_compactly_generated_on_def
  proof (intro conjI allI impI)
    show "is_topology_on X TX"
      by (rule hTopX)

    fix A
    assume hAX: "A \<subseteq> X"

    show "A \<in> TX \<longleftrightarrow>
        (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
              \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C)"
    proof (intro iffI)
      assume hA: "A \<in> TX"
      show "\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
              \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C"
      proof (intro allI impI)
        fix C
        assume hC: "top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X"
        have "A \<inter> C = C \<inter> A"
          by (simp add: Int_commute)
        also have "... \<in> subspace_topology X TX C"
          unfolding subspace_topology_def using hA by blast
        finally show "A \<inter> C \<in> subspace_topology X TX C" .
      qed
    next
      assume hInter:
        "\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
              \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C"

      have hLoc: "\<forall>x\<in>A. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> A"
      proof (intro ballI)
        fix x
        assume hxA: "x \<in> A"
        have hxX: "x \<in> X"
          using hAX hxA by blast

        obtain U0 where hU0: "neighborhood_of x X TX U0"
          and hU0subX: "U0 \<subseteq> X"
          and hCompCl: "top1_compact_on (closure_on X TX U0) (subspace_topology X TX (closure_on X TX U0))"
          using hLCprop hxX by blast

        define C0 where "C0 = closure_on X TX U0"
        have hC0subX: "C0 \<subseteq> X"
          unfolding C0_def by (rule closure_on_subset_carrier[OF hTopX hU0subX])

        have hAintC0:
          "A \<inter> C0 \<in> subspace_topology X TX C0"
          using hInter hCompCl hC0subX unfolding C0_def by blast

        obtain W where hW: "W \<in> TX" and hEq: "A \<inter> C0 = C0 \<inter> W"
          using hAintC0 unfolding subspace_topology_def by blast

        have hxU0: "x \<in> U0"
          using hU0 unfolding neighborhood_of_def by simp
        have hxC0: "x \<in> C0"
          unfolding C0_def by (rule subsetD[OF subset_closure_on hxU0])
        have hxAintC0: "x \<in> A \<inter> C0"
          using hxA hxC0 by simp
        have hxW: "x \<in> W"
          using hxAintC0 unfolding hEq by simp

        let ?U = "U0 \<inter> W"
        have hUin: "?U \<in> TX"
          by (rule topology_inter2[OF hTopX], rule conjunct1[OF hU0[unfolded neighborhood_of_def]], rule hW)
        have hxU: "x \<in> ?U"
          using hxU0 hxW by simp

        have hUsubA: "?U \<subseteq> A"
        proof
          fix y
          assume hy: "y \<in> ?U"
          have hyU0: "y \<in> U0"
            using hy by simp
          have hyC0: "y \<in> C0"
            unfolding C0_def by (rule subsetD[OF subset_closure_on hyU0])
          have hyW: "y \<in> W"
            using hy by simp
          have "y \<in> C0 \<inter> W"
            using hyC0 hyW by simp
          hence "y \<in> A \<inter> C0"
            unfolding hEq by simp
          thus "y \<in> A"
            by simp
        qed

        show "\<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> A"
          using hUin hxU hUsubA by blast
      qed

      show "A \<in> TX"
        by (rule top1_open_of_local_subsets[OF hTopX hAX hLoc])
    qed
  qed
qed

(** from \S46 Lemma 46.4 [top1.tex:6807] **)
lemma Lemma_46_4:
  assumes hCG: "top1_compactly_generated_on X TX"
  shows "\<forall>f. (\<forall>C. top1_compact_on C (subspace_topology X TX C)
              \<longrightarrow> top1_continuous_map_on C (subspace_topology X TX C) Y TY f)
          \<longrightarrow> top1_continuous_map_on X TX Y TY f"
proof (intro allI impI)
  fix f
  assume hC:
    "(\<forall>C. top1_compact_on C (subspace_topology X TX C)
          \<longrightarrow> top1_continuous_map_on C (subspace_topology X TX C) Y TY f)"

  have hTopX: "is_topology_on X TX"
    using hCG unfolding top1_compactly_generated_on_def by simp

  have hChar:
    "\<And>A. A \<subseteq> X \<Longrightarrow>
      (A \<in> TX \<longleftrightarrow>
        (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
            \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C))"
  proof -
    fix A
    assume hAX: "A \<subseteq> X"
    have hAll:
      "\<forall>A. A \<subseteq> X \<longrightarrow>
        (A \<in> TX \<longleftrightarrow>
          (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
              \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C))"
      using hCG unfolding top1_compactly_generated_on_def by simp
    have hImp:
      "A \<subseteq> X \<longrightarrow>
        (A \<in> TX \<longleftrightarrow>
          (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
              \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C))"
      using hAll by (rule allE[where x=A])
    show
      "A \<in> TX \<longleftrightarrow>
        (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
            \<longrightarrow> A \<inter> C \<in> subspace_topology X TX C)"
      using hImp hAX by simp
  qed

  have hMap: "\<forall>x\<in>X. f x \<in> Y"
  proof (intro ballI)
    fix x
    assume hxX: "x \<in> X"
    have hcomp: "top1_compact_on {x} (subspace_topology X TX {x})"
    proof -
      have hsub: "{x} \<subseteq> X"
        by (simp add: hxX)
      have hfin: "finite {x}"
        by simp
      show ?thesis
        by (rule top1_compact_on_finite_subspace[OF hTopX hsub hfin])
    qed
    have hcont: "top1_continuous_map_on {x} (subspace_topology X TX {x}) Y TY f"
      using hC hcomp by blast
    have hMapS: "\<forall>z\<in>{x}. f z \<in> Y"
      using hcont unfolding top1_continuous_map_on_def by (rule conjunct1)
    show "f x \<in> Y"
      using hMapS by simp
  qed

  have hPre: "\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX"
  proof (intro ballI)
    fix V
    assume hV: "V \<in> TY"
    let ?A = "{x\<in>X. f x \<in> V}"
    have hAsubX: "?A \<subseteq> X"
      by blast

    have hRHS:
      "\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
          \<longrightarrow> ?A \<inter> C \<in> subspace_topology X TX C"
    proof (intro allI impI)
      fix C
      assume hC': "top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X"
      have hcompC: "top1_compact_on C (subspace_topology X TX C)"
        using hC' by simp
      have hCX: "C \<subseteq> X"
        using hC' by simp

      have hcontC: "top1_continuous_map_on C (subspace_topology X TX C) Y TY f"
        using hC hcompC by blast

      have hpreC: "{x\<in>C. f x \<in> V} \<in> subspace_topology X TX C"
        using hcontC hV unfolding top1_continuous_map_on_def by blast

      have hEq: "?A \<inter> C = {x\<in>C. f x \<in> V}"
      proof (rule equalityI)
        show "?A \<inter> C \<subseteq> {x\<in>C. f x \<in> V}"
        proof
          fix x
          assume hx: "x \<in> ?A \<inter> C"
          have hxC: "x \<in> C"
            using hx by simp
          have hfxV: "f x \<in> V"
            using hx by simp
          show "x \<in> {x\<in>C. f x \<in> V}"
            using hxC hfxV by simp
        qed
        show "{x\<in>C. f x \<in> V} \<subseteq> ?A \<inter> C"
        proof
          fix x
          assume hx: "x \<in> {x\<in>C. f x \<in> V}"
          have hxC: "x \<in> C"
            using hx by simp
          have hxX: "x \<in> X"
            using hCX hxC by blast
          have hfxV: "f x \<in> V"
            using hx by simp
          have hxA: "x \<in> ?A"
            using hxX hfxV by simp
          show "x \<in> ?A \<inter> C"
            using hxA hxC by simp
        qed
      qed

      show "?A \<inter> C \<in> subspace_topology X TX C"
        unfolding hEq by (rule hpreC)
    qed

    have "?A \<in> TX \<longleftrightarrow>
        (\<forall>C. top1_compact_on C (subspace_topology X TX C) \<and> C \<subseteq> X
            \<longrightarrow> ?A \<inter> C \<in> subspace_topology X TX C)"
      by (rule hChar[OF hAsubX])
    thus "?A \<in> TX"
      using hRHS by simp
  qed

  show "top1_continuous_map_on X TX Y TY f"
    unfolding top1_continuous_map_on_def
    apply (intro conjI)
     apply (rule hMap)
    apply (rule hPre)
    done
qed

(** from \S46 Theorem 46.5 [top1.tex:6816] **)
theorem Theorem_46_5:
  assumes hCG: "top1_compactly_generated_on X TX"
  assumes hd: "top1_metric_on Y d"
  shows "closedin_on (top1_PiE X (\<lambda>_. Y))
    (top1_compact_convergence_topology_on X TX Y d)
    {f. top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) f}"
  sorry

(** from \S46 Corollary 46.6 [top1.tex:6820] **)
corollary Corollary_46_6:
  assumes hCG: "top1_compactly_generated_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hcont: "\<forall>n. top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) (fseq n)"
  assumes hconv:
    "seq_converges_to_on fseq f (top1_PiE X (\<lambda>_. Y)) (top1_compact_convergence_topology_on X TX Y d)"
  shows "top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) f"
proof -
  let ?X' = "top1_PiE X (\<lambda>_. Y)"
  let ?T' = "top1_compact_convergence_topology_on X TX Y d"
  let ?S = "{g. top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) g}"

  have hS_closed: "closedin_on ?X' ?T' ?S"
    by (rule Theorem_46_5[OF hCG hd])

  have hfX': "f \<in> ?X'"
    using hconv unfolding seq_converges_to_on_def by (rule conjunct1)

  have hseqS: "\<forall>n. fseq n \<in> ?S"
    using hcont by blast

  show ?thesis
  proof (rule ccontr)
    assume hNot: "\<not> top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) f"
    have hfNotS: "f \<notin> ?S"
      using hNot by simp

    have hSsubX': "?S \<subseteq> ?X'"
      using hS_closed unfolding closedin_on_def by (rule conjunct1)

    have hCompOpen: "?X' - ?S \<in> ?T'"
      using hS_closed unfolding closedin_on_def by (rule conjunct2)

    have hfComp: "f \<in> ?X' - ?S"
      using hfX' hfNotS by simp

    have hNbh: "neighborhood_of f ?X' ?T' (?X' - ?S)"
      unfolding neighborhood_of_def using hCompOpen hfComp by simp

    have hConv: "\<forall>U. neighborhood_of f ?X' ?T' U \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. fseq n \<in> U)"
      using hconv unfolding seq_converges_to_on_def by (rule conjunct2)

    obtain N where hN: "\<forall>n\<ge>N. fseq n \<in> (?X' - ?S)"
      using hConv hNbh by blast

    have "fseq N \<in> ?X' - ?S"
      using hN by simp
    then have "fseq N \<notin> ?S"
      by simp
    then show False
      using hseqS by blast
  qed
qed

(** from \S46 Theorem 46.7 [top1.tex:6824] **)
lemma top1_bounded_metric_lt_imp_lt:
  assumes hlt: "top1_bounded_metric d x y < r"
  assumes hr: "r \<le> 1"
  shows "d x y < r"
proof -
  have "d x y < r \<or> 1 < r"
    using hlt unfolding top1_bounded_metric_def
    by (simp add: min_less_iff_disj)
  thus ?thesis
    using hr by linarith
qed

lemma top1_compact_convergence_topology_on_superset_pointwise:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  shows "top1_compact_convergence_topology_on X TX Y d
    \<supseteq> top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)"
proof -
  let ?Xfun = "top1_PiE X (\<lambda>_. Y)"
  let ?Bpw = "top1_product_basis_on X (\<lambda>_. Y) (\<lambda>_. top1_metric_topology_on Y d)"
  let ?Bcc = "top1_compact_convergence_basis_on X TX Y d"

  have hpw_sub_cc:
    "topology_generated_by_basis ?Xfun ?Bpw \<subseteq> topology_generated_by_basis ?Xfun ?Bcc"
  proof (rule topology_generated_by_basis_mono_via_basis_elems)
    fix b
    assume hb: "b \<in> ?Bpw"
    obtain U where
      hbdef: "b = top1_PiE X U"
      and hU: "\<forall>x\<in>X. U x \<in> top1_metric_topology_on Y d \<and> U x \<subseteq> Y"
      and hfin: "finite {x \<in> X. U x \<noteq> Y}"
      using hb unfolding top1_product_basis_on_def by blast

    let ?S = "{x \<in> X. U x \<noteq> Y}"
    have hSfin: "finite ?S"
      using hfin by simp
    have hSsubX: "?S \<subseteq> X"
      by blast

    have hb_sub: "b \<subseteq> ?Xfun"
    proof -
      have hmono: "\<forall>x\<in>X. U x \<subseteq> Y"
        using hU by simp
      have "top1_PiE X U \<subseteq> top1_PiE X (\<lambda>_. Y)"
        by (rule top1_PiE_mono[OF hmono])
      thus ?thesis
        unfolding hbdef by simp
    qed

    show "b \<in> topology_generated_by_basis ?Xfun ?Bcc"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> ?Xfun"
        by (rule hb_sub)

      show "\<forall>g\<in>b. \<exists>bc\<in>?Bcc. g \<in> bc \<and> bc \<subseteq> b"
      proof (intro ballI)
        fix g
        assume hg: "g \<in> b"
        have hgU: "g \<in> top1_PiE X U"
          using hg unfolding hbdef by simp
        have hgXfun: "g \<in> ?Xfun"
          using hb_sub hg by blast

        have hScomp: "top1_compact_on ?S (subspace_topology X TX ?S)"
          by (rule top1_compact_on_finite_subspace[OF hTopX hSsubX hSfin])

        have hBall_each: "\<forall>x\<in>?S. \<exists>e>0. top1_ball_on Y d (g x) e \<subseteq> U x"
        proof (intro ballI)
          fix x
          assume hxS: "x \<in> ?S"
          have hxX: "x \<in> X"
            using hxS by simp
          have hUx: "U x \<in> top1_metric_topology_on Y d"
            using hU hxX by simp
          have hgxUx: "g x \<in> U x"
            using hgU hxX unfolding top1_PiE_iff by blast
          show "\<exists>e>0. top1_ball_on Y d (g x) e \<subseteq> U x"
            by (rule top1_metric_open_contains_ball[OF hd hUx hgxUx])
        qed

        have hBall_each':
          "\<forall>x\<in>?S. \<exists>e. 0 < e \<and> top1_ball_on Y d (g x) e \<subseteq> U x"
          using hBall_each by simp

        have hex_eps:
          "\<exists>eps. \<forall>x\<in>?S. 0 < eps x \<and> top1_ball_on Y d (g x) (eps x) \<subseteq> U x"
          by (rule bchoice[OF hBall_each'])

        obtain eps where heps:
          "\<forall>x\<in>?S. 0 < eps x \<and> top1_ball_on Y d (g x) (eps x) \<subseteq> U x"
          using hex_eps
          by (erule exE)

        define e where
          "e = (if ?S = {} then 1/2 else min (Min (eps ` ?S)) (1/2))"

        have hepos: "0 < e"
        proof (cases "?S = {}")
          case True
          show ?thesis
            unfolding e_def True by simp
        next
          case False
          have hSimg_fin: "finite (eps ` ?S)"
            using hSfin by simp
          have hSimg_ne: "eps ` ?S \<noteq> {}"
            using False by simp
          have hSimg_pos: "\<forall>r\<in>eps ` ?S. 0 < r"
            using heps by blast
	          have hMin_mem: "Min (eps ` ?S) \<in> eps ` ?S"
	            by (rule Min_in[OF hSimg_fin hSimg_ne])
	          have hMin_pos: "0 < Min (eps ` ?S)"
	            by (rule bspec[OF hSimg_pos hMin_mem])
	          show ?thesis
	            unfolding e_def using False hMin_pos by simp
	        qed

        have hele1: "e \<le> 1"
        proof (cases "?S = {}")
          case True
          show ?thesis
            unfolding e_def True by simp
        next
          case False
          have "e \<le> (1 / 2 :: real)"
            unfolding e_def using False by simp
          thus ?thesis
            by simp
        qed

        have hele_eps: "\<forall>x\<in>?S. e \<le> eps x"
        proof (intro ballI)
          fix x
          assume hxS: "x \<in> ?S"
          show "e \<le> eps x"
          proof (cases "?S = {}")
            case True
            show ?thesis
              using hxS True by simp
	          next
	            case False
	            have hSimg_fin: "finite (eps ` ?S)"
	              using hSfin by simp
	            have hxmem: "eps x \<in> eps ` ?S"
	              by (rule imageI[OF hxS])
	            have hMin_le: "Min (eps ` ?S) \<le> eps x"
	              by (rule Min_le[OF hSimg_fin hxmem])
	            have he_alt: "e = min (Min (eps ` ?S)) (1 / 2)"
	              unfolding e_def by (rule if_not_P[OF False])
	            have hle_Min: "e \<le> Min (eps ` ?S)"
	              unfolding he_alt by simp
	            show ?thesis
	              by (rule order_trans[OF hle_Min hMin_le])
	          qed
	        qed

	        have hball_mono:
	          "\<And>x (r::real) (r'::real). r \<le> r' \<Longrightarrow> top1_ball_on Y d (g x) r \<subseteq> top1_ball_on Y d (g x) r'"
	        proof -
	          fix x and r :: real and r' :: real
	          assume hr: "r \<le> r'"
	          show "top1_ball_on Y d (g x) r \<subseteq> top1_ball_on Y d (g x) r'"
	          unfolding top1_ball_on_def
	          using hr by (intro subsetI; simp; linarith)
	        qed

        have hball_subU: "\<forall>x\<in>?S. top1_ball_on Y d (g x) e \<subseteq> U x"
        proof (intro ballI)
          fix x
	          assume hxS: "x \<in> ?S"
	          have hsub1: "top1_ball_on Y d (g x) e \<subseteq> top1_ball_on Y d (g x) (eps x)"
	            by (rule hball_mono[OF hele_eps[rule_format, OF hxS]])
	          have hsub2: "top1_ball_on Y d (g x) (eps x) \<subseteq> U x"
	            using heps hxS by simp
	          show "top1_ball_on Y d (g x) e \<subseteq> U x"
	            by (rule subset_trans[OF hsub1 hsub2])
	        qed

        let ?bc =
          "{h \<in> ?Xfun.
              (if ?S = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (g x) (h x)) ` ?S)) < e}"

	        have hbc_inB: "?bc \<in> ?Bcc"
	          unfolding top1_compact_convergence_basis_on_def
	          apply (rule CollectI)
	          apply (rule exI[where x=g])
	          apply (rule exI[where x="{x \<in> X. U x \<noteq> Y}"])
	          apply (rule exI[where x=e])
	          apply (intro conjI)
	             apply simp
	             apply (rule hgXfun)
	            apply (rule hScomp)
	           apply (rule hSsubX)
	          apply (rule hepos)
	          done

        have hg_in_bc: "g \<in> ?bc"
        proof -
          have h0iff: "\<forall>x\<in>Y. \<forall>y\<in>Y. d x y = 0 \<longleftrightarrow> x = y"
            using hd unfolding top1_metric_on_def by blast
          have hvals0: "\<forall>x\<in>X. top1_bounded_metric d (g x) (g x) = 0"
          proof (intro ballI)
            fix x assume hxX: "x \<in> X"
            have hgx: "g x \<in> Y"
              using hgXfun hxX unfolding top1_PiE_iff by blast
            have "d (g x) (g x) = 0"
              using h0iff hgx by simp
            thus "top1_bounded_metric d (g x) (g x) = 0"
              unfolding top1_bounded_metric_def by simp
          qed
          have hdist0:
            "(if ?S = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (g x) (g x)) ` ?S)) = 0"
          proof (cases "?S = {}")
            case True
            show ?thesis
              using True by simp
          next
            case False
            let ?T = "((\<lambda>x. top1_bounded_metric d (g x) (g x)) ` ?S)"
            have hTsub: "?T \<subseteq> {0}"
            proof
              fix t assume ht: "t \<in> ?T"
              then obtain x where hxS: "x \<in> ?S" and htdef: "t = top1_bounded_metric d (g x) (g x)"
                by blast
              have hxX: "x \<in> X"
                using hxS by simp
              have "top1_bounded_metric d (g x) (g x) = 0"
                using hvals0 hxX by blast
              thus "t \<in> {0}"
                unfolding htdef by simp
            qed
            have hTne: "?T \<noteq> {}"
            proof -
              obtain x0 where hx0: "x0 \<in> ?S"
                using False by blast
              have "top1_bounded_metric d (g x0) (g x0) \<in> ?T"
                by (rule imageI[OF hx0])
              thus ?thesis by blast
            qed
            have hSup_le0: "Sup ?T \<le> 0"
            proof (rule cSup_least[OF hTne])
              fix t assume ht: "t \<in> ?T"
              have "t \<in> {0}"
                using hTsub ht by blast
              thus "t \<le> 0"
                by simp
            qed
            have hSup_ge0: "0 \<le> Sup ?T"
            proof -
              obtain x0 where hx0: "x0 \<in> ?S"
                using False by blast
              have hmem0: "0 \<in> ?T"
                using hvals0 hx0 by force
	              have hbdd: "bdd_above ?T"
	                unfolding bdd_above_def
	                apply (rule exI[where x=1])
	                apply (intro ballI)
	                apply (erule imageE)
	                apply (simp add: top1_bounded_metric_def)
	                done
              have "0 \<le> Sup ?T"
                using cSup_upper[OF hmem0 hbdd] by simp
              thus ?thesis .
            qed
            have "Sup ?T = 0"
              using hSup_le0 hSup_ge0 by linarith
            thus ?thesis
              using False by simp
          qed
          have hcond: "(if ?S = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (g x) (g x)) ` ?S)) < e"
            using hdist0 hepos by simp
          show ?thesis
            using hgXfun hcond by simp
        qed

        have hbc_sub_b: "?bc \<subseteq> b"
        proof (rule subsetI)
          fix h
          assume hh: "h \<in> ?bc"
          have hhXfun: "h \<in> ?Xfun"
            using hh by simp
          have hsup: "(if ?S = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (g x) (h x)) ` ?S)) < e"
            using hh by simp

          have hcoords: "\<forall>x\<in>X. h x \<in> U x"
          proof (intro ballI)
            fix x
            assume hxX: "x \<in> X"
            show "h x \<in> U x"
            proof (cases "x \<in> ?S")
              case False
              have hUx: "U x = Y"
                using False hxX by simp
              have hhxY: "h x \<in> Y"
                using hhXfun hxX unfolding top1_PiE_iff by blast
              show ?thesis
                unfolding hUx using hhxY .
            next
              case True
              have hxS: "x \<in> ?S"
                using True .

	              have hSne: "?S \<noteq> {}"
	                using hxS by blast
	              have hSup_lt: "Sup ((\<lambda>t. top1_bounded_metric d (g t) (h t)) ` ?S) < e"
	                using hsup unfolding if_not_P[OF hSne] by assumption

	              let ?T = "((\<lambda>t. top1_bounded_metric d (g t) (h t)) ` ?S)"
	              have hbdd: "bdd_above ?T"
	                unfolding bdd_above_def
	                apply (rule exI[where x=1])
	                apply (intro ballI)
	                apply (erule imageE)
	                apply (simp add: top1_bounded_metric_def)
	                done
              have hmem: "top1_bounded_metric d (g x) (h x) \<in> ?T"
                by (rule imageI[OF hxS])
              have hleSup: "top1_bounded_metric d (g x) (h x) \<le> Sup ?T"
                by (rule cSup_upper[OF hmem hbdd])
              have hlt_bdd: "top1_bounded_metric d (g x) (h x) < e"
                using hleSup hSup_lt by linarith

              have hlt_d: "d (g x) (h x) < e"
                by (rule top1_bounded_metric_lt_imp_lt[OF hlt_bdd hele1])

              have hhx_ball: "h x \<in> top1_ball_on Y d (g x) e"
              proof -
                have hhxY: "h x \<in> Y"
                  using hhXfun hxX unfolding top1_PiE_iff by blast
                show ?thesis
                  unfolding top1_ball_on_def using hhxY hlt_d by blast
              qed

              have hsubU: "top1_ball_on Y d (g x) e \<subseteq> U x"
                using hball_subU hxS by blast

              show ?thesis
                by (rule subsetD[OF hsubU hhx_ball])
            qed
          qed

          have hext: "\<forall>x. x \<notin> X \<longrightarrow> h x = undefined"
            using hhXfun unfolding top1_PiE_iff by blast

          show "h \<in> b"
            unfolding hbdef top1_PiE_iff using hcoords hext by blast
        qed

        show "\<exists>bc\<in>?Bcc. g \<in> bc \<and> bc \<subseteq> b"
          apply (rule bexI[where x="?bc"])
           apply (intro conjI)
            apply (rule hg_in_bc)
           apply (rule hbc_sub_b)
          apply (rule hbc_inB)
          done
      qed
    qed
  qed

  show ?thesis
    unfolding top1_compact_convergence_topology_on_def top1_pointwise_topology_on_def top1_product_topology_on_def
    using hpw_sub_cc by simp
qed

text \<open>
  Proof idea for @{thm top1_compact_convergence_topology_on_superset_pointwise}: unfold both sides
  as topologies generated by bases. Use @{thm topology_generated_by_basis_mono_via_basis_elems} with
  the product basis on @{term "top1_PiE X (\<lambda>_. Y)"} as \<open>B1\<close> and the compact-convergence basis as
  \<open>B2\<close>. For a product-basis element @{term "top1_PiE X U"} and a point @{term g} in it, let
  @{term "F = {x \<in> X. U x \<noteq> Y}"} (finite), pick radii around @{term "g x"} inside each @{term "U x"},
  and use the compact set @{term F} to build a compact-convergence basic neighborhood contained in the
  cylinder.
\<close>

lemma top1_uniform_topology_on_superset_compact_convergence:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  shows "top1_uniform_topology_on X Y d \<supseteq> top1_compact_convergence_topology_on X TX Y d"
proof -
  let ?Xfun = "top1_PiE X (\<lambda>_. Y)"
  let ?Buni = "top1_metric_basis_on ?Xfun (top1_uniform_metric_on X d)"
  let ?Bcc = "top1_compact_convergence_basis_on X TX Y d"

  have hcc_sub_uni:
    "topology_generated_by_basis ?Xfun ?Bcc \<subseteq> topology_generated_by_basis ?Xfun ?Buni"
  proof (rule topology_generated_by_basis_mono_via_basis_elems)
    fix b
    assume hb: "b \<in> ?Bcc"
    obtain f C \<epsilon> where
      hbdef: "b = {g \<in> ?Xfun.
        (if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C)) < \<epsilon>}"
      and hf: "f \<in> ?Xfun"
      and hcomp: "top1_compact_on C (subspace_topology X TX C)"
      and hCX: "C \<subseteq> X"
      and heps: "0 < \<epsilon>"
      using hb unfolding top1_compact_convergence_basis_on_def by blast

    show "b \<in> topology_generated_by_basis ?Xfun ?Buni"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> ?Xfun"
        unfolding hbdef by blast

      show "\<forall>g\<in>b. \<exists>bu\<in>?Buni. g \<in> bu \<and> bu \<subseteq> b"
      proof (intro ballI)
        fix g
        assume hg: "g \<in> b"
        have hgX: "g \<in> ?Xfun"
          using hg unfolding hbdef by blast
        have hdist_fg:
          "(if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C)) < \<epsilon>"
          using hg unfolding hbdef by blast

        define \<alpha> where
          "\<alpha> = (if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C))"
        have halpha_lt: "\<alpha> < \<epsilon>"
          unfolding \<alpha>_def using hdist_fg by simp

        define \<delta> where "\<delta> = (\<epsilon> - \<alpha>) / 2"
        have hdelta_pos: "\<delta> > 0"
          unfolding \<delta>_def using halpha_lt by simp

        let ?bu = "top1_ball_on ?Xfun (top1_uniform_metric_on X d) g \<delta>"

        have hbu_mem: "?bu \<in> ?Buni"
          unfolding top1_metric_basis_on_def
          apply (rule CollectI)
          apply (rule exI[where x=g])
          apply (rule exI[where x=\<delta>])
          using hgX hdelta_pos by simp

        have hgg_in: "g \<in> ?bu"
        proof -
          have h0iff: "\<forall>x\<in>Y. \<forall>y\<in>Y. d x y = 0 \<longleftrightarrow> x = y"
            using hd unfolding top1_metric_on_def by blast

          have hvals0: "\<forall>x\<in>X. top1_bounded_metric d (g x) (g x) = 0"
          proof (intro ballI)
            fix x assume hx: "x \<in> X"
            have hgx: "g x \<in> Y"
              using hgX hx unfolding top1_PiE_iff by blast
            have hdx: "d (g x) (g x) = 0"
              using h0iff hgx by simp
            show "top1_bounded_metric d (g x) (g x) = 0"
              unfolding top1_bounded_metric_def using hdx by simp
          qed

          let ?S = "((\<lambda>x. top1_bounded_metric d (g x) (g x)) ` X)"
          have hSsub: "?S \<subseteq> {0}"
          proof
            fix t assume ht: "t \<in> ?S"
            then obtain x where hxX: "x \<in> X" and htdef: "t = top1_bounded_metric d (g x) (g x)"
              by blast
            have "top1_bounded_metric d (g x) (g x) = 0"
              using hvals0 hxX by blast
            then show "t \<in> {0}"
              unfolding htdef by simp
          qed

          have "top1_uniform_metric_on X d g g < \<delta>"
          proof (cases "X = {}")
            case True
            show ?thesis
              unfolding top1_uniform_metric_on_def True using hdelta_pos by simp
          next
            case False
            have hSne: "?S \<noteq> {}"
              using False by simp
            have hSup_le0: "Sup ?S \<le> 0"
            proof (rule cSup_least[OF hSne])
              fix t
              assume ht: "t \<in> ?S"
              have "t \<in> {0}"
                using hSsub ht by blast
              thus "t \<le> 0"
                by simp
            qed
            have "top1_uniform_metric_on X d g g = Sup ?S"
              unfolding top1_uniform_metric_on_def using False by simp
            then show ?thesis
              using hSup_le0 hdelta_pos by linarith
          qed
          then show ?thesis
            unfolding top1_ball_on_def using hgX by simp
        qed

        have hbu_sub: "?bu \<subseteq> b"
        proof
          fix h
          assume hh: "h \<in> ?bu"
          have hhX: "h \<in> ?Xfun"
            using hh unfolding top1_ball_on_def by blast
          have hgh: "top1_uniform_metric_on X d g h < \<delta>"
            using hh unfolding top1_ball_on_def by blast

          have hdist_fh:
            "(if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (h x)) ` C)) < \<epsilon>"
          proof (cases "C = {}")
            case True
            show ?thesis
              using heps unfolding True by simp
          next
            case False
            let ?Sfg = "((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C)"
            let ?SghX = "((\<lambda>x. top1_bounded_metric d (g x) (h x)) ` X)"
            let ?Sfh = "((\<lambda>x. top1_bounded_metric d (f x) (h x)) ` C)"

            have hSfg_bdd: "bdd_above ?Sfg"
              unfolding bdd_above_def
              apply (rule exI[where x=1])
              apply (intro ballI)
              subgoal for t
              proof -
                assume ht: "t \<in> ?Sfg"
                obtain x where hxC: "x \<in> C" and htdef: "t = top1_bounded_metric d (f x) (g x)"
                  using ht by blast
                show "t \<le> 1"
                  unfolding htdef top1_bounded_metric_def by simp
              qed
              done

            have hSghX_bdd: "bdd_above ?SghX"
              unfolding bdd_above_def
              apply (rule exI[where x=1])
              apply (intro ballI)
              subgoal for t
              proof -
                assume ht: "t \<in> ?SghX"
                obtain x where hxX: "x \<in> X" and htdef: "t = top1_bounded_metric d (g x) (h x)"
                  using ht by blast
                show "t \<le> 1"
                  unfolding htdef top1_bounded_metric_def by simp
              qed
              done

            have hSfh_ne: "?Sfh \<noteq> {}"
            proof -
              obtain x0 where hx0: "x0 \<in> C"
                using False by blast
              have "top1_bounded_metric d (f x0) (h x0) \<in> ?Sfh"
                by (rule imageI[OF hx0])
              thus ?thesis
                by blast
            qed

            have htri_bdd: "top1_metric_on Y (top1_bounded_metric d)"
              by (rule top1_bounded_metric_on[OF hd])

            have halpha_eq: "\<alpha> = Sup ?Sfg"
              unfolding \<alpha>_def using False by simp

            have hSup_fh_le: "Sup ?Sfh \<le> \<alpha> + Sup ?SghX"
            proof (rule cSup_least[OF hSfh_ne])
              fix t
              assume ht: "t \<in> ?Sfh"
              obtain x where hxC: "x \<in> C" and htdef: "t = top1_bounded_metric d (f x) (h x)"
                using ht by blast
              have hxX: "x \<in> X"
                using hCX hxC by blast

              have hfx: "f x \<in> Y"
                using hf hxX unfolding top1_PiE_iff by blast
              have hgx: "g x \<in> Y"
                using hgX hxX unfolding top1_PiE_iff by blast
              have hhx: "h x \<in> Y"
                using hhX hxX unfolding top1_PiE_iff by blast

              have htri:
                "top1_bounded_metric d (f x) (h x)
                  \<le> top1_bounded_metric d (f x) (g x) + top1_bounded_metric d (g x) (h x)"
                using htri_bdd hfx hgx hhx unfolding top1_metric_on_def by blast

              have hfg_le: "top1_bounded_metric d (f x) (g x) \<le> \<alpha>"
              proof -
                have hmem: "top1_bounded_metric d (f x) (g x) \<in> ?Sfg"
                  by (rule imageI[OF hxC])
                show ?thesis
                  unfolding halpha_eq
                  by (rule cSup_upper[OF hmem hSfg_bdd])
              qed

              have hgh_le: "top1_bounded_metric d (g x) (h x) \<le> Sup ?SghX"
              proof -
                have hmem: "top1_bounded_metric d (g x) (h x) \<in> ?SghX"
                  by (rule imageI[OF hxX])
                show ?thesis
                  by (rule cSup_upper[OF hmem hSghX_bdd])
              qed

              have "top1_bounded_metric d (f x) (h x) \<le> \<alpha> + Sup ?SghX"
                using htri hfg_le hgh_le by linarith
              thus "t \<le> \<alpha> + Sup ?SghX"
                unfolding htdef by simp
            qed

            have hXne: "X \<noteq> {}"
            proof
              assume hX: "X = {}"
              have "C = {}"
                using hCX hX by blast
              with False show False
                by contradiction
            qed

            have hSup_gh_lt: "Sup ?SghX < \<delta>"
              using hgh unfolding top1_uniform_metric_on_def using hXne by simp

            have hSup_fh_lt_mid: "Sup ?Sfh < (\<alpha> + \<epsilon>) / 2"
            proof -
              have "Sup ?Sfh \<le> \<alpha> + Sup ?SghX"
                by (rule hSup_fh_le)
              also have "... < \<alpha> + \<delta>"
                using hSup_gh_lt by linarith
              also have "... = (\<alpha> + \<epsilon>) / 2"
                unfolding \<delta>_def by (simp add: field_simps algebra_simps)
              finally show ?thesis .
            qed

            have hmid_lt: "(\<alpha> + \<epsilon>) / 2 < \<epsilon>"
              using halpha_lt by simp

            have hif: "(if C = {} then 0 else Sup ?Sfh) = Sup ?Sfh"
              using False by simp
            show ?thesis
              unfolding hif using hSup_fh_lt_mid hmid_lt by linarith
          qed

          show "h \<in> b"
            unfolding hbdef using hhX hdist_fh by simp
        qed

        show "\<exists>bu\<in>?Buni. g \<in> bu \<and> bu \<subseteq> b"
        proof -
          show ?thesis
            apply (rule bexI[where x="?bu"])
             apply (intro conjI)
              apply (rule hgg_in)
             apply (rule hbu_sub)
            apply (rule hbu_mem)
            done
        qed
      qed
    qed
  qed

  show ?thesis
    unfolding top1_uniform_topology_on_def top1_compact_convergence_topology_on_def top1_metric_topology_on_def
    using hcc_sub_uni by simp
qed

theorem Theorem_46_7:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  shows "top1_uniform_topology_on X Y d \<supseteq> top1_compact_convergence_topology_on X TX Y d
    \<and> top1_compact_convergence_topology_on X TX Y d \<supseteq> top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)"
proof -
  have h1: "top1_uniform_topology_on X Y d \<supseteq> top1_compact_convergence_topology_on X TX Y d"
    by (rule top1_uniform_topology_on_superset_compact_convergence[OF hTopX hd])
  have h2: "top1_compact_convergence_topology_on X TX Y d
      \<supseteq> top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)"
    by (rule top1_compact_convergence_topology_on_superset_pointwise[OF hTopX hd])
  show ?thesis
    using h1 h2 by simp
qed

(*
proof -
  let ?Xfun = "top1_PiE X (\<lambda>_. Y)"
  let ?Buni = "top1_metric_basis_on ?Xfun (top1_uniform_metric_on X d)"
  let ?Bcc = "top1_compact_convergence_basis_on X TX Y d"
  let ?Bpw = "top1_product_basis_on X (\<lambda>_. Y) (\<lambda>_. top1_metric_topology_on Y d)"

  have hcc_sub_uni:
    "topology_generated_by_basis ?Xfun ?Bcc \<subseteq> topology_generated_by_basis ?Xfun ?Buni"
  proof (rule topology_generated_by_basis_mono_via_basis_elems)
    fix b
    assume hb: "b \<in> ?Bcc"
    obtain f C \<epsilon> where
      hbdef: "b = {g \<in> ?Xfun.
        (if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C)) < \<epsilon>}"
      and hf: "f \<in> ?Xfun"
      and hcomp: "top1_compact_on C (subspace_topology X TX C)"
      and hCX: "C \<subseteq> X"
      and heps: "0 < \<epsilon>"
      using hb unfolding top1_compact_convergence_basis_on_def by blast

    show "b \<in> topology_generated_by_basis ?Xfun ?Buni"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> ?Xfun"
        unfolding hbdef by blast

      show "\<forall>g\<in>b. \<exists>bu\<in>?Buni. g \<in> bu \<and> bu \<subseteq> b"
      proof (intro ballI)
        fix g
        assume hg: "g \<in> b"
        have hgX: "g \<in> ?Xfun"
          using hg unfolding hbdef by blast
        have hdist_fg:
          "(if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C)) < \<epsilon>"
          using hg unfolding hbdef by blast

        define \<alpha> where
          "\<alpha> = (if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C))"
        have halpha_lt: "\<alpha> < \<epsilon>"
          unfolding \<alpha>_def using hdist_fg by simp

        define \<delta> where "\<delta> = (\<epsilon> - \<alpha>) / 2"
        have hdelta_pos: "\<delta> > 0"
          unfolding \<delta>_def using halpha_lt by simp

        let ?bu = "top1_ball_on ?Xfun (top1_uniform_metric_on X d) g \<delta>"

        have hbu_mem: "?bu \<in> ?Buni"
          unfolding top1_metric_basis_on_def
          apply (rule CollectI)
          apply (rule exI[where x=g])
          apply (rule exI[where x=\<delta>])
          using hgX hdelta_pos by simp

        have hgg_in: "g \<in> ?bu"
        proof -
          have hvals0: "\<forall>x\<in>X. top1_bounded_metric d (g x) (g x) = 0"
          proof (intro ballI)
            fix x assume hx: "x \<in> X"
            have hgx: "g x \<in> Y"
              using hgX hx unfolding top1_PiE_iff by blast
            have hdx: "d (g x) (g x) = 0"
              using hd hgx unfolding top1_metric_on_def by blast
            show "top1_bounded_metric d (g x) (g x) = 0"
              unfolding top1_bounded_metric_def using hdx by simp
          qed

          let ?S = "((\<lambda>x. top1_bounded_metric d (g x) (g x)) ` X)"
          have hSsub: "?S \<subseteq> {0}"
          proof
            fix t assume ht: "t \<in> ?S"
            then obtain x where hxX: "x \<in> X" and htdef: "t = top1_bounded_metric d (g x) (g x)"
              by blast
            have "top1_bounded_metric d (g x) (g x) = 0"
              using hvals0 hxX by blast
            then show "t \<in> {0}"
              unfolding htdef by simp
          qed

          have "top1_uniform_metric_on X d g g < \<delta>"
          proof (cases "X = {}")
            case True
            show ?thesis
              unfolding top1_uniform_metric_on_def True using hdelta_pos by simp
          next
            case False
            have hSne: "?S \<noteq> {}"
              using False by simp
            have hSup_le0: "Sup ?S \<le> 0"
            proof (rule cSup_least[OF hSne])
              fix t
              assume ht: "t \<in> ?S"
              have "t \<in> {0}"
                using hSsub ht by blast
              thus "t \<le> 0"
                by simp
            qed
            have "top1_uniform_metric_on X d g g = Sup ?S"
              unfolding top1_uniform_metric_on_def using False by simp
            then show ?thesis
              using hSup_le0 hdelta_pos by linarith
          qed
          thus ?thesis
            unfolding top1_ball_on_def using hgX by blast
        qed

        have hbu_sub: "?bu \<subseteq> b"
        proof
          fix h
          assume hh: "h \<in> ?bu"
          have hhX: "h \<in> ?Xfun"
            using hh unfolding top1_ball_on_def by blast
          have hgh: "top1_uniform_metric_on X d g h < \<delta>"
            using hh unfolding top1_ball_on_def by blast

          have hdist_fh:
            "(if C = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (f x) (h x)) ` C)) < \<epsilon>"
          proof (cases "C = {}")
            case True
            show ?thesis
              using heps unfolding True by simp
          next
            case False
            let ?Sfg = "((\<lambda>x. top1_bounded_metric d (f x) (g x)) ` C)"
            let ?SghX = "((\<lambda>x. top1_bounded_metric d (g x) (h x)) ` X)"
            let ?Sfh = "((\<lambda>x. top1_bounded_metric d (f x) (h x)) ` C)"

            have hSfg_bdd: "bdd_above ?Sfg"
            proof -
              show ?thesis
                unfolding bdd_above_def
              proof (rule exI[where x=1], intro ballI)
                fix t
                assume ht: "t \<in> ?Sfg"
                then obtain x where hxC: "x \<in> C" and htdef: "t = top1_bounded_metric d (f x) (g x)"
                  by blast
                show "t \<le> 1"
                  unfolding htdef top1_bounded_metric_def by simp
              qed
            qed

            have hSghX_bdd: "bdd_above ?SghX"
            proof -
              show ?thesis
                unfolding bdd_above_def
              proof (rule exI[where x=1], intro ballI)
                fix t
                assume ht: "t \<in> ?SghX"
                then obtain x where hxX: "x \<in> X" and htdef: "t = top1_bounded_metric d (g x) (h x)"
                  by blast
                show "t \<le> 1"
                  unfolding htdef top1_bounded_metric_def by simp
              qed
            qed

            have hSfh_ne: "?Sfh \<noteq> {}"
            proof -
              obtain x0 where hx0: "x0 \<in> C"
                using False by blast
              have "top1_bounded_metric d (f x0) (h x0) \<in> ?Sfh"
                by (rule imageI[OF hx0])
              thus ?thesis
                by blast
            qed

            have htri_bdd: "top1_metric_on Y (top1_bounded_metric d)"
              by (rule top1_bounded_metric_on[OF hd])

            have halpha_eq: "\<alpha> = Sup ?Sfg"
              unfolding \<alpha>_def using False by simp

            have hSup_fh_le: "Sup ?Sfh \<le> \<alpha> + Sup ?SghX"
            proof (rule cSup_least[OF hSfh_ne])
              fix t
              assume ht: "t \<in> ?Sfh"
              obtain x where hxC: "x \<in> C" and htdef: "t = top1_bounded_metric d (f x) (h x)"
                using ht by blast
              have hxX: "x \<in> X"
                using hCX hxC by blast

              have hfx: "f x \<in> Y"
                using hf hxX unfolding top1_PiE_iff by blast
              have hgx: "g x \<in> Y"
                using hgX hxX unfolding top1_PiE_iff by blast
              have hhx: "h x \<in> Y"
                using hhX hxX unfolding top1_PiE_iff by blast

              have htri:
                "top1_bounded_metric d (f x) (h x)
                  \<le> top1_bounded_metric d (f x) (g x) + top1_bounded_metric d (g x) (h x)"
                using htri_bdd hfx hgx hhx unfolding top1_metric_on_def by blast

              have hfg_le: "top1_bounded_metric d (f x) (g x) \<le> \<alpha>"
              proof -
                have hmem: "top1_bounded_metric d (f x) (g x) \<in> ?Sfg"
                  by (rule imageI[OF hxC])
                show ?thesis
                  unfolding halpha_eq
                  by (rule cSup_upper[OF hmem hSfg_bdd])
              qed

              have hgh_le: "top1_bounded_metric d (g x) (h x) \<le> Sup ?SghX"
              proof -
                have hmem: "top1_bounded_metric d (g x) (h x) \<in> ?SghX"
                  by (rule imageI[OF hxX])
                show ?thesis
                  by (rule cSup_upper[OF hmem hSghX_bdd])
              qed

              have "top1_bounded_metric d (f x) (h x) \<le> \<alpha> + Sup ?SghX"
                using htri hfg_le hgh_le by linarith
              thus "t \<le> \<alpha> + Sup ?SghX"
                unfolding htdef by simp
            qed

            have hXne: "X \<noteq> {}"
            proof
              assume hX: "X = {}"
              have "C = {}"
                using hCX hX by blast
              with False show False
                by contradiction
            qed
            have hSup_gh_lt: "Sup ?SghX < \<delta>"
              using hgh unfolding top1_uniform_metric_on_def using hXne by simp

            have hSup_fh_lt_mid: "Sup ?Sfh < (\<alpha> + \<epsilon>) / 2"
            proof -
              have "Sup ?Sfh \<le> \<alpha> + Sup ?SghX"
                by (rule hSup_fh_le)
              also have "... < \<alpha> + \<delta>"
                using hSup_gh_lt by linarith
              also have "... = (\<alpha> + \<epsilon>) / 2"
                unfolding \<delta>_def by (simp add: field_simps algebra_simps)
              finally show ?thesis .
            qed

            have hmid_lt: "(\<alpha> + \<epsilon>) / 2 < \<epsilon>"
              using halpha_lt by simp

            show ?thesis
            proof -
              have hif: "(if C = {} then 0 else Sup ?Sfh) = Sup ?Sfh"
                using False by simp
              show ?thesis
                unfolding hif using hSup_fh_lt_mid hmid_lt by linarith
            qed
          qed

          show "h \<in> b"
            unfolding hbdef using hhX hdist_fh by blast
        qed

        show "\<exists>bu\<in>?Buni. g \<in> bu \<and> bu \<subseteq> b"
          using hbu_mem hgg_in hbu_sub by blast
      qed
    qed
  qed

  have hpw_sub_cc:
    "topology_generated_by_basis ?Xfun ?Bpw \<subseteq> topology_generated_by_basis ?Xfun ?Bcc"
  proof (rule topology_generated_by_basis_mono_via_basis_elems)
    fix b
    assume hb: "b \<in> ?Bpw"
    obtain U where
      hbdef: "b = top1_PiE X U"
      and hU: "\<forall>x\<in>X. U x \<in> top1_metric_topology_on Y d \<and> U x \<subseteq> Y"
      and hfin: "finite {x \<in> X. U x \<noteq> Y}"
      using hb unfolding top1_product_basis_on_def by blast

    let ?S = "{x \<in> X. U x \<noteq> Y}"

    have hb_sub: "b \<subseteq> ?Xfun"
    proof -
      have hmono: "\<forall>x\<in>X. U x \<subseteq> Y"
        using hU by simp
      have "top1_PiE X U \<subseteq> top1_PiE X (\<lambda>_. Y)"
        by (rule top1_PiE_mono[OF hmono])
      thus ?thesis
        unfolding hbdef by simp
    qed

    show "b \<in> topology_generated_by_basis ?Xfun ?Bcc"
      unfolding topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "b \<subseteq> ?Xfun"
        by (rule hb_sub)

      show "\<forall>g\<in>b. \<exists>bc\<in>?Bcc. g \<in> bc \<and> bc \<subseteq> b"
      proof (intro ballI)
        fix g
        assume hg: "g \<in> b"
        have hgU: "g \<in> top1_PiE X U"
          using hg unfolding hbdef by simp
        have hgXfun: "g \<in> ?Xfun"
          using hb_sub hg by blast

        have hSfin: "finite ?S"
          using hfin by simp
        have hSsubX: "?S \<subseteq> X"
          by blast

        have hScomp: "top1_compact_on ?S (subspace_topology X TX ?S)"
          by (rule top1_compact_on_finite_subspace[OF hTopX hSsubX hSfin])

        have hBall_each: "\<forall>x\<in>?S. \<exists>e>0. top1_ball_on Y d (g x) e \<subseteq> U x"
        proof (intro ballI)
          fix x
          assume hxS: "x \<in> ?S"
          have hxX: "x \<in> X"
            using hxS by simp
          have hUx: "U x \<in> top1_metric_topology_on Y d"
            using hU hxX by simp
          have hgxUx: "g x \<in> U x"
            using hgU hxX unfolding top1_PiE_iff by blast
          show "\<exists>e>0. top1_ball_on Y d (g x) e \<subseteq> U x"
            by (rule top1_metric_open_contains_ball[OF hd hUx hgxUx])
        qed

        have hBall_all: "\<exists>e>0. e \<le> (1::real) \<and> (\<forall>x\<in>?S. top1_ball_on Y d (g x) e \<subseteq> U x)"
        proof -
          have hBall_all_aux:
            "\<And>S. finite S
              \<Longrightarrow> (\<forall>x\<in>S. \<exists>e>0. top1_ball_on Y d (g x) e \<subseteq> U x)
              \<Longrightarrow> (\<exists>e>0. e \<le> (1::real) \<and> (\<forall>x\<in>S. top1_ball_on Y d (g x) e \<subseteq> U x))"
          proof -
            fix S :: "'a set"
            assume hSfin0: "finite S"
            assume hBallS: "\<forall>x\<in>S. \<exists>e>0. top1_ball_on Y d (g x) e \<subseteq> U x"
            show "\<exists>e>0. e \<le> (1::real) \<and> (\<forall>x\<in>S. top1_ball_on Y d (g x) e \<subseteq> U x)"
              using hSfin0 hBallS
            proof (induction S rule: finite_induct)
              case empty
              show ?case
                apply (rule exI[where x="1/2"])
                by simp
            next
            case (insert x S')
            obtain e1 where he1: "e1 > 0" and he1sub: "top1_ball_on Y d (g x) e1 \<subseteq> U x"
              using insert.prems by blast
            have hBallS': "\<forall>y\<in>S'. \<exists>e>0. top1_ball_on Y d (g y) e \<subseteq> U y"
              using insert.prems by blast
            obtain e2 where he2: "e2 > 0" and he2le: "e2 \<le> (1::real)"
              and he2sub: "\<forall>y\<in>S'. top1_ball_on Y d (g y) e2 \<subseteq> U y"
              using insert.IH[OF hBallS'] by blast

            define e where "e = min (min e1 e2) (1/2)"
            have hepos: "e > 0"
              unfolding e_def using he1 he2 by simp
            have hele1: "e \<le> (1::real)"
              unfolding e_def by simp

            have hsub1: "top1_ball_on Y d (g x) e \<subseteq> U x"
            proof -
              have hele: "e \<le> e1"
                unfolding e_def by simp
              have "top1_ball_on Y d (g x) e \<subseteq> top1_ball_on Y d (g x) e1"
              proof
                fix z
                assume hz: "z \<in> top1_ball_on Y d (g x) e"
                have hzY: "z \<in> Y" and hdist: "d (g x) z < e"
                  using hz unfolding top1_ball_on_def by blast+
                have "d (g x) z < e1"
                  using hdist hele by linarith
                show "z \<in> top1_ball_on Y d (g x) e1"
                  unfolding top1_ball_on_def using hzY \<open>d (g x) z < e1\<close> by blast
              qed
              thus ?thesis
                using he1sub by blast
            qed

            have hsub2: "\<forall>y\<in>S'. top1_ball_on Y d (g y) e \<subseteq> U y"
            proof (intro ballI)
              fix y
              assume hy: "y \<in> S'"
              have hele: "e \<le> e2"
                unfolding e_def by simp
              have "top1_ball_on Y d (g y) e \<subseteq> top1_ball_on Y d (g y) e2"
              proof
                fix z
                assume hz: "z \<in> top1_ball_on Y d (g y) e"
                have hzY: "z \<in> Y" and hdist: "d (g y) z < e"
                  using hz unfolding top1_ball_on_def by blast+
                have "d (g y) z < e2"
                  using hdist hele by linarith
                show "z \<in> top1_ball_on Y d (g y) e2"
                  unfolding top1_ball_on_def using hzY \<open>d (g y) z < e2\<close> by blast
              qed
              have hsubU2: "top1_ball_on Y d (g y) e2 \<subseteq> U y"
                using he2sub hy by blast
              show "top1_ball_on Y d (g y) e \<subseteq> U y"
                by (rule subset_trans[OF \<open>top1_ball_on Y d (g y) e \<subseteq> top1_ball_on Y d (g y) e2\<close> hsubU2])
            qed

            show ?case
              apply (rule exI[where x=e])
              using hepos hele1 hsub1 hsub2 by simp
            qed
          qed

          show ?thesis
            by (rule hBall_all_aux[OF hSfin hBall_each])
        qed

        obtain e where hepos: "e > 0" and hele1: "e \<le> (1::real)"
          and hballU: "\<forall>x\<in>?S. top1_ball_on Y d (g x) e \<subseteq> U x"
          using hBall_all by blast

        let ?bc =
          "{h \<in> ?Xfun.
             (if ?S = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (g x) (h x)) ` ?S)) < e}"

        have hbc_mem: "?bc \<in> ?Bcc"
          unfolding top1_compact_convergence_basis_on_def
          apply (rule CollectI)
          apply (rule exI[where x=g])
          apply (rule exI[where x="?S"])
          apply (rule exI[where x=e])
          apply (intro conjI)
           apply simp
          apply (rule hgXfun)
          apply (rule hScomp)
          apply (rule hSsubX)
          apply (rule hepos)
          done

        have hgbc: "g \<in> ?bc"
        proof -
          have hvals0: "\<forall>x\<in>?S. top1_bounded_metric d (g x) (g x) = 0"
          proof (intro ballI)
            fix x assume hxS: "x \<in> ?S"
            have hxX: "x \<in> X"
              using hxS by simp
            have hgx: "g x \<in> Y"
              using hgXfun hxX unfolding top1_PiE_iff by blast
            have hdx: "d (g x) (g x) = 0"
              using hd hgx unfolding top1_metric_on_def by blast
            show "top1_bounded_metric d (g x) (g x) = 0"
              unfolding top1_bounded_metric_def using hdx by simp
          qed
          have hSup0:
            "(if ?S = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (g x) (g x)) ` ?S)) < e"
          proof (cases "?S = {}")
            case True
            show ?thesis
              using hepos unfolding True by simp
          next
            case False
            let ?S0 = "((\<lambda>x. top1_bounded_metric d (g x) (g x)) ` ?S)"
            have hS0ne: "?S0 \<noteq> {}"
              using False by simp
            have hS0sub: "?S0 \<subseteq> {0}"
            proof
              fix t assume ht: "t \<in> ?S0"
              then obtain x where hxS: "x \<in> ?S" and htdef: "t = top1_bounded_metric d (g x) (g x)"
                by blast
              have "top1_bounded_metric d (g x) (g x) = 0"
                using hvals0 hxS by blast
              thus "t \<in> {0}"
                unfolding htdef by simp
            qed
            have hSup_le0: "Sup ?S0 \<le> 0"
              by (rule cSup_least[OF hS0ne], blast intro: hS0sub)
            show ?thesis
              unfolding False using hSup_le0 hepos by linarith
          qed

          show ?thesis
            using hgXfun hSup0 by simp
        qed

        have hbc_sub_b: "?bc \<subseteq> b"
        proof
          fix h
          assume hh: "h \<in> ?bc"
          have hhXfun: "h \<in> ?Xfun"
            using hh by blast
          have hSup:
            "(if ?S = {} then 0 else Sup ((\<lambda>x. top1_bounded_metric d (g x) (h x)) ` ?S)) < e"
            using hh by blast

          have hh_in_b: "h \<in> top1_PiE X U"
          proof -
            have hall:
              "(\<forall>x\<in>X. h x \<in> U x) \<and> (\<forall>x. x \<notin> X \<longrightarrow> h x = undefined)"
            proof (intro conjI)
              show "\<forall>x\<in>X. h x \<in> U x"
              proof (intro ballI)
                fix x assume hxX: "x \<in> X"
                show "h x \<in> U x"
                proof (cases "x \<in> ?S")
                  case True
                  have hSup': "Sup ((\<lambda>y. top1_bounded_metric d (g y) (h y)) ` ?S) < e"
                    using hSup unfolding True by simp
                  have hbdd_img: "bdd_above ((\<lambda>y. top1_bounded_metric d (g y) (h y)) ` ?S)"
                    unfolding bdd_above_def
                    apply (rule exI[where x=1])
                    apply (intro ballI)
                    unfolding top1_bounded_metric_def
                    by simp
                  have hx_le: "top1_bounded_metric d (g x) (h x) \<le> Sup ((\<lambda>y. top1_bounded_metric d (g y) (h y)) ` ?S)"
                    by (rule cSup_upper[OF imageI[OF True] hbdd_img])
                  have hx_lt: "top1_bounded_metric d (g x) (h x) < e"
                    using hx_le hSup' by linarith
                  have hhx: "h x \<in> Y"
                    using hhXfun hxX unfolding top1_PiE_iff by blast
                  have hgx: "g x \<in> Y"
                    using hgXfun hxX unfolding top1_PiE_iff by blast
                  have hx_ball: "h x \<in> top1_ball_on Y (top1_bounded_metric d) (g x) e"
                    unfolding top1_ball_on_def using hhx hx_lt by blast
                  have hball_eq: "top1_ball_on Y (top1_bounded_metric d) (g x) e = top1_ball_on Y d (g x) e"
                    by (rule top1_ball_on_bounded_metric_eq[OF hele1])
                  have hx_ball': "h x \<in> top1_ball_on Y d (g x) e"
                    using hx_ball unfolding hball_eq by simp
                  have hsubU: "top1_ball_on Y d (g x) e \<subseteq> U x"
                    using hballU True by blast
                  show ?thesis
                    using hsubU hx_ball' by blast
                next
                  case False
                  have hUx: "U x = Y"
                    using hxX False by simp
                  have hhx: "h x \<in> Y"
                    using hhXfun hxX unfolding top1_PiE_iff by blast
                  show ?thesis
                    unfolding hUx using hhx .
                qed
              qed

              show "\<forall>x. x \<notin> X \<longrightarrow> h x = undefined"
                using hhXfun unfolding top1_PiE_iff by blast
            qed
            show ?thesis
              unfolding top1_PiE_iff using hall by blast
          qed
          show "h \<in> b"
            unfolding hbdef using hh_in_b by simp
        qed

        show "\<exists>bc\<in>?Bcc. g \<in> bc \<and> bc \<subseteq> b"
          using hbc_mem hgbc hbc_sub_b by blast
      qed
    qed
  qed

  have hTcc_sub_Tuni:
    "top1_compact_convergence_topology_on X TX Y d \<subseteq> top1_uniform_topology_on X Y d"
    unfolding top1_compact_convergence_topology_on_def top1_uniform_topology_on_def top1_metric_topology_on_def
    using hcc_sub_uni by simp

  have hTpw_sub_Tcc:
    "top1_pointwise_topology_on X Y (top1_metric_topology_on Y d) \<subseteq> top1_compact_convergence_topology_on X TX Y d"
    unfolding top1_pointwise_topology_on_def top1_product_topology_on_def top1_compact_convergence_topology_on_def
    using hpw_sub_cc by simp

  show ?thesis
    using hTcc_sub_Tuni hTpw_sub_Tcc by blast
qed
*)

(** from \S46 Theorem 46.8 [top1.tex:6839] **)
theorem Theorem_46_8:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  shows "subspace_topology (top1_PiE X (\<lambda>_. Y))
           (top1_compact_convergence_topology_on X TX Y d)
           (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
       =
       top1_compact_open_topology_on X TX Y (top1_metric_topology_on Y d)"
  sorry

(** from \S46 Corollary 46.9 [top1.tex:6859] **)
corollary Corollary_46_9:
  assumes hTopX: "is_topology_on X TX"
  assumes hd1: "top1_metric_on Y d1"
  assumes hd2: "top1_metric_on Y d2"
  assumes hTopEq: "top1_metric_topology_on Y d1 = top1_metric_topology_on Y d2"
  shows
    "subspace_topology (top1_PiE X (\<lambda>_. Y))
       (top1_compact_convergence_topology_on X TX Y d1)
       (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d1))
     =
     subspace_topology (top1_PiE X (\<lambda>_. Y))
       (top1_compact_convergence_topology_on X TX Y d2)
       (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d2))"
    and
    "top1_compact_on X TX \<longrightarrow>
       (subspace_topology (top1_PiE X (\<lambda>_. Y)) (top1_uniform_topology_on X Y d1)
          (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d1))
        =
        subspace_topology (top1_PiE X (\<lambda>_. Y)) (top1_uniform_topology_on X Y d2)
          (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d2)))"
  sorry

(** from \S46 Theorem 46.10 [top1.tex:6863] **)
theorem Theorem_46_10:
  assumes hLC: "top1_locally_compact_on X TX"
  assumes hHausX: "is_hausdorff_on X TX"
  assumes hTopY: "is_topology_on Y TY"
  shows "top1_continuous_map_on
           (X \<times> top1_continuous_funcs_on X TX Y TY)
           (product_topology_on TX (top1_compact_open_topology_on X TX Y TY))
           Y TY
           (\<lambda>p. (snd p) (fst p))"
proof -
  let ?C = "top1_continuous_funcs_on X TX Y TY"
  let ?Tco = "top1_compact_open_topology_on X TX Y TY"
  let ?eval = "(\<lambda>p. (snd p) (fst p))"

  have hTopX: "is_topology_on X TX"
    using hHausX unfolding is_hausdorff_on_def by blast

  have hShrink:
    "\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
        (\<exists>V. neighborhood_of x X TX V \<and>
             top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
             \<and> closure_on X TX V \<subseteq> U)"
  proof -
    have hIff:
      "top1_locally_compact_on X TX \<longleftrightarrow>
        (\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
            (\<exists>V. neighborhood_of x X TX V \<and>
                 top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
                 \<and> closure_on X TX V \<subseteq> U))"
      by (rule Theorem_29_2[OF hHausX])
    show ?thesis
      by (rule iffD1[OF hIff hLC])
  qed

  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>p\<in>X \<times> ?C. ?eval p \<in> Y"
    proof (intro ballI)
      fix p
      assume hp: "p \<in> X \<times> ?C"
      obtain x f where hp': "p = (x, f)"
        by (cases p) simp
      have hxX: "x \<in> X"
        using hp unfolding hp' by simp
      have hfC: "f \<in> ?C"
        using hp unfolding hp' by simp
      have hfPi: "f \<in> top1_PiE X (\<lambda>_. Y)"
        using hfC unfolding top1_continuous_funcs_on_def by simp
      have hfxY: "f x \<in> Y"
        using hfPi hxX unfolding top1_PiE_iff by blast
      show "?eval p \<in> Y"
        using hfxY unfolding hp' by simp
    qed

    show "\<forall>V\<in>TY. {p \<in> X \<times> ?C. ?eval p \<in> V} \<in> product_topology_on TX ?Tco"
    proof (intro ballI)
      fix V
      assume hV: "V \<in> TY"
      let ?P = "{p \<in> X \<times> ?C. ?eval p \<in> V}"
      show "?P \<in> product_topology_on TX ?Tco"
        unfolding product_topology_on_def topology_generated_by_basis_def
      proof (rule CollectI, intro conjI)
        show "?P \<subseteq> (UNIV :: ('a \<times> ('a \<Rightarrow> 'b)) set)"
          by simp

        show "\<forall>p\<in>?P. \<exists>b\<in>product_basis TX ?Tco. p \<in> b \<and> b \<subseteq> ?P"
        proof (intro ballI)
          fix p
          assume hpP: "p \<in> ?P"
          obtain x f where hp': "p = (x, f)"
            by (cases p) simp
          have hxX: "x \<in> X"
            using hpP unfolding hp' by simp
          have hfC: "f \<in> ?C"
            using hpP unfolding hp' by simp
          have hfxV: "f x \<in> V"
            using hpP unfolding hp' by simp

          have hfcont: "top1_continuous_map_on X TX Y TY f"
            using hfC unfolding top1_continuous_funcs_on_def by simp

          define N where "N = {x\<in>X. f x \<in> V}"
          have hNT: "N \<in> TX"
            using hfcont hV unfolding top1_continuous_map_on_def N_def by blast
          have hxN: "x \<in> N"
            unfolding N_def using hxX hfxV by simp
          have hNbhN: "neighborhood_of x X TX N"
            unfolding neighborhood_of_def using hNT hxN by blast

          obtain W where hWnbh: "neighborhood_of x X TX W"
            and hKcomp: "top1_compact_on (closure_on X TX W) (subspace_topology X TX (closure_on X TX W))"
            and hclWsub: "closure_on X TX W \<subseteq> N"
            using hShrink hxX hNbhN by blast

          define K where "K = closure_on X TX W"
          have hWsubK: "W \<subseteq> K"
            unfolding K_def by (rule subset_closure_on)
          have hKsubN: "K \<subseteq> N"
            unfolding K_def using hclWsub by simp
          have hKsubX: "K \<subseteq> X"
            using hKsubN unfolding N_def by blast

          have hxW: "x \<in> W"
            using hWnbh unfolding neighborhood_of_def by blast

          have hKimg: "f ` K \<subseteq> V"
          proof
            fix y
            assume hy: "y \<in> f ` K"
            then obtain x0 where hx0K: "x0 \<in> K" and hy': "y = f x0"
              by blast
            have hx0N: "x0 \<in> N"
              using hKsubN hx0K by blast
            have "f x0 \<in> V"
              using hx0N unfolding N_def by simp
            show "y \<in> V"
              using hy' \<open>f x0 \<in> V\<close> by simp
          qed

          define WV where "WV = {g \<in> ?C. g ` K \<subseteq> V}"

          have hWVsubbasis: "WV \<in> top1_compact_open_subbasis_on X TX Y TY"
            unfolding top1_compact_open_subbasis_on_def WV_def
            apply (rule CollectI)
            apply (rule exI[where x=K])
            apply (rule exI[where x=V])
            apply (intro conjI)
             apply simp
            apply (simp add: K_def)
            apply (rule hKcomp)
            apply (rule hKsubX)
            apply (rule hV)
            done

          have hWVopen: "WV \<in> ?Tco"
            unfolding top1_compact_open_topology_on_def
            by (rule topology_generated_by_subbasis_contains[OF hWVsubbasis])

          have hWopen: "W \<in> TX"
            using hWnbh unfolding neighborhood_of_def by blast

          have hbasis: "W \<times> WV \<in> product_basis TX ?Tco"
            unfolding product_basis_def
            apply (rule CollectI)
            apply (rule exI[where x=W])
            apply (rule exI[where x=WV])
            apply (intro conjI)
              apply simp
             apply (rule hWopen)
            apply (rule hWVopen)
            done

          have hp_in: "p \<in> W \<times> WV"
          proof -
            have hfWV: "f \<in> WV"
              unfolding WV_def using hfC hKimg by blast
            show ?thesis
              using hxW hfWV unfolding hp' by simp
          qed

          have hsub: "W \<times> WV \<subseteq> ?P"
          proof
            fix q
            assume hq: "q \<in> W \<times> WV"
            obtain x1 g where hq': "q = (x1, g)"
              by (cases q) simp
            have hx1W: "x1 \<in> W"
              using hq unfolding hq' by simp
            have hgWV: "g \<in> WV"
              using hq unfolding hq' by simp
            have hx1K: "x1 \<in> K"
              using hWsubK hx1W by blast
            have hx1X: "x1 \<in> X"
              using hKsubX hx1K by blast
            have hgC: "g \<in> ?C"
              using hgWV unfolding WV_def by simp
            have hgK: "g ` K \<subseteq> V"
              using hgWV unfolding WV_def by simp
            have "g x1 \<in> V"
            proof -
              have "g x1 \<in> g ` K"
                using hx1K by blast
              thus ?thesis
                using hgK by blast
            qed
            show "q \<in> ?P"
              unfolding hq'
              by (simp add: hx1X hgC \<open>g x1 \<in> V\<close>)
          qed

          show "\<exists>b\<in>product_basis TX ?Tco. p \<in> b \<and> b \<subseteq> ?P"
            apply (rule bexI[where x="W \<times> WV"])
             apply (intro conjI)
              apply (rule hp_in)
             apply (rule hsub)
            apply (rule hbasis)
            done
        qed
      qed
    qed
  qed
qed

(** from \S46 Theorem 46.11 (Exponential law) [top1.tex:6888] **)
theorem Theorem_46_11:
  assumes hLC: "top1_locally_compact_on X TX"
  assumes hHausX: "is_hausdorff_on X TX"
  assumes hTopZ: "is_topology_on Z TZ"
  assumes hTopY: "is_topology_on Y TY"
  shows "(\<forall>f. top1_continuous_map_on (X \<times> Z) (product_topology_on TX TZ) Y TY f
        \<longrightarrow> top1_continuous_map_on Z TZ (top1_continuous_funcs_on X TX Y TY)
              (top1_compact_open_topology_on X TX Y TY) (\<lambda>z x. if x \<in> X then f (x, z) else undefined))"
    and "(\<forall>F. top1_continuous_map_on Z TZ (top1_continuous_funcs_on X TX Y TY)
              (top1_compact_open_topology_on X TX Y TY) F
          \<longrightarrow> top1_continuous_map_on (X \<times> Z) (product_topology_on TX TZ) Y TY (\<lambda>p. (F (snd p)) (fst p)))"
proof -
  let ?C = "top1_continuous_funcs_on X TX Y TY"
  let ?S = "top1_compact_open_subbasis_on X TX Y TY"
  let ?Tco = "top1_compact_open_topology_on X TX Y TY"
  let ?TPXZ = "product_topology_on TX TZ"

  have hTopX: "is_topology_on X TX"
    using hHausX unfolding is_hausdorff_on_def by blast

  show "(\<forall>f. top1_continuous_map_on (X \<times> Z) ?TPXZ Y TY f
        \<longrightarrow> top1_continuous_map_on Z TZ ?C ?Tco (\<lambda>z x. if x \<in> X then f (x, z) else undefined))"
  proof (intro allI impI)
    fix f
    assume hf: "top1_continuous_map_on (X \<times> Z) ?TPXZ Y TY f"

    define F where "F = (\<lambda>z x. if x \<in> X then f (x, z) else undefined)"

    have hFmem: "\<forall>z\<in>Z. F z \<in> ?C"
    proof (intro ballI)
      fix z
      assume hz: "z \<in> Z"

      have hidX: "top1_continuous_map_on X TX X TX id"
        by (rule top1_continuous_map_on_id[OF hTopX])

      have hconstz: "top1_continuous_map_on X TX Z TZ (\<lambda>x. z)"
        by (rule top1_continuous_map_on_const[OF hTopX hTopZ hz])

      have hjz: "top1_continuous_map_on X TX (X \<times> Z) ?TPXZ (\<lambda>x. (x, z))"
      proof -
        have hEq1: "pi1 \<circ> (\<lambda>x. (x, z)) = id"
          by (rule ext) (simp add: o_def pi1_def)
        have hEq2: "pi2 \<circ> (\<lambda>x. (x, z)) = (\<lambda>x. z)"
          by (rule ext) (simp add: o_def pi2_def)
        have hpair:
          "top1_continuous_map_on X TX (X \<times> Z) ?TPXZ (\<lambda>x. (x, z))
            \<longleftrightarrow>
              (top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, z)))
               \<and> top1_continuous_map_on X TX Z TZ (pi2 \<circ> (\<lambda>x. (x, z))))"
          by (rule Theorem_18_4[OF hTopX hTopX hTopZ])
        have hpi1j: "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, z)))"
        proof -
          have hEq: "\<forall>x\<in>X. (pi1 \<circ> (\<lambda>x. (x, z))) x = id x"
            unfolding hEq1 by simp
          show ?thesis
            using top1_continuous_map_on_cong[OF hEq] hidX by blast
        qed

        have hpi2j: "top1_continuous_map_on X TX Z TZ (pi2 \<circ> (\<lambda>x. (x, z)))"
        proof -
          have hEq: "\<forall>x\<in>X. (pi2 \<circ> (\<lambda>x. (x, z))) x = (\<lambda>x. z) x"
            unfolding hEq2 by simp
          show ?thesis
            using top1_continuous_map_on_cong[OF hEq] hconstz by blast
        qed

        have hconj:
          "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, z)))
           \<and> top1_continuous_map_on X TX Z TZ (pi2 \<circ> (\<lambda>x. (x, z)))"
          using hpi1j hpi2j by simp

        show ?thesis
          by (rule iffD2[OF hpair hconj])
      qed

      have hcomp: "top1_continuous_map_on X TX Y TY (f \<circ> (\<lambda>x. (x, z)))"
        by (rule top1_continuous_map_on_comp[OF hjz hf])

      have hcur: "top1_continuous_map_on X TX Y TY (\<lambda>x. f (x, z))"
      proof -
        have hEq: "f \<circ> (\<lambda>x. (x, z)) = (\<lambda>x. f (x, z))"
          by (rule ext) (simp add: o_def)
        show ?thesis
          using hcomp unfolding hEq .
      qed

      have hEqOn: "\<forall>x\<in>X. (\<lambda>x. f (x, z)) x = F z x"
        unfolding F_def by simp

      have hFcont: "top1_continuous_map_on X TX Y TY (F z)"
        using top1_continuous_map_on_cong[OF hEqOn] hcur by blast

      have hFmap: "\<forall>x\<in>X. F z x \<in> Y"
        using hFcont unfolding top1_continuous_map_on_def by blast
      have hFext: "\<forall>x. x \<notin> X \<longrightarrow> F z x = undefined"
        unfolding F_def by simp

      have hFpi: "F z \<in> top1_PiE X (\<lambda>_. Y)"
        unfolding top1_PiE_iff using hFmap hFext by blast

      show "F z \<in> ?C"
        unfolding top1_continuous_funcs_on_def
        using hFpi hFcont by simp
    qed

    have hPreSub: "\<forall>W\<in>?S. {z \<in> Z. F z \<in> W} \<in> TZ"
    proof (intro ballI)
      fix W
      assume hW: "W \<in> ?S"

      obtain C0 U0 where hWeq: "W = {g \<in> ?C. g ` C0 \<subseteq> U0}"
        and hC0: "top1_compact_on C0 (subspace_topology X TX C0)"
        and hC0subX: "C0 \<subseteq> X"
        and hU0: "U0 \<in> TY"
        using hW unfolding top1_compact_open_subbasis_on_def by blast

      define P where "P = {z \<in> Z. F z \<in> W}"

      have hPsubZ: "P \<subseteq> Z"
        unfolding P_def by blast

      have hLoc: "\<forall>z0\<in>P. \<exists>U\<in>TZ. z0 \<in> U \<and> U \<subseteq> P"
      proof (intro ballI)
        fix z0
        assume hz0: "z0 \<in> P"
        have hz0Z: "z0 \<in> Z"
          using hz0 unfolding P_def by simp
        have hFz0W: "F z0 \<in> W"
          using hz0 unfolding P_def by simp

        have hFz0sub: "F z0 ` C0 \<subseteq> U0"
          using hFz0W unfolding hWeq by simp

        let ?TC0 = "subspace_topology X TX C0"
        have hTopC0: "is_topology_on C0 ?TC0"
          by (rule subspace_topology_is_topology_on[OF hTopX hC0subX])

        have hPi1: "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) Z TZ pi1"
          by (rule top1_continuous_pi1[OF hTopZ hTopC0])

        have hPi2C: "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) C0 ?TC0 pi2"
          by (rule top1_continuous_pi2[OF hTopZ hTopC0])

        have hInc: "top1_continuous_map_on C0 ?TC0 X TX id"
          unfolding top1_continuous_map_on_def
        proof (intro conjI)
          show "\<forall>x\<in>C0. id x \<in> X"
          proof (intro ballI)
            fix x
            assume hx: "x \<in> C0"
            have hxX: "x \<in> X"
              using hC0subX hx by blast
            show "id x \<in> X"
              using hxX by simp
          qed
          show "\<forall>V\<in>TX. {x \<in> C0. id x \<in> V} \<in> ?TC0"
          proof (intro ballI)
            fix V
            assume hV: "V \<in> TX"
            have hEq: "{x \<in> C0. id x \<in> V} = C0 \<inter> V"
              by (rule set_eqI) simp
            show "{x \<in> C0. id x \<in> V} \<in> ?TC0"
              unfolding subspace_topology_def
              apply (rule CollectI)
              apply (rule exI[where x=V])
              using hEq hV by simp
          qed
        qed

        have hPi2X': "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) X TX (id \<circ> pi2)"
          by (rule top1_continuous_map_on_comp[OF hPi2C hInc])

        have hPi2X: "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) X TX pi2"
        proof -
          have hEq: "\<forall>p\<in>Z \<times> C0. (id \<circ> pi2) p = pi2 p"
            by (intro ballI) (simp add: o_def)
          show ?thesis
            using top1_continuous_map_on_cong[OF hEq] hPi2X' by blast
        qed

        have hs:
          "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) (X \<times> Z) ?TPXZ (\<lambda>p. (pi2 p, pi1 p))"
        proof -
          have hTopDom: "is_topology_on (Z \<times> C0) (product_topology_on TZ ?TC0)"
            by (rule product_topology_on_is_topology_on[OF hTopZ hTopC0])

          have hEq1: "pi1 \<circ> (\<lambda>p. (pi2 p, pi1 p)) = pi2"
            by (rule ext) (simp add: o_def pi1_def)
          have hEq2: "pi2 \<circ> (\<lambda>p. (pi2 p, pi1 p)) = pi1"
            by (rule ext) (simp add: o_def pi2_def)

          have hpair:
            "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) (X \<times> Z) ?TPXZ (\<lambda>p. (pi2 p, pi1 p))
              \<longleftrightarrow>
                (top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) X TX (pi1 \<circ> (\<lambda>p. (pi2 p, pi1 p)))
                 \<and> top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) Z TZ (pi2 \<circ> (\<lambda>p. (pi2 p, pi1 p))))"
            by (rule Theorem_18_4[OF hTopDom hTopX hTopZ])

          show ?thesis
          proof -
            have h1: "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) X TX (pi1 \<circ> (\<lambda>p. (pi2 p, pi1 p)))"
            proof -
              have hEqAll: "\<forall>p. (pi1 \<circ> (\<lambda>p. (pi2 p, pi1 p))) p = pi2 p"
                using hEq1 by (simp add: fun_eq_iff)
              have hEq: "\<forall>p\<in>Z \<times> C0. (pi1 \<circ> (\<lambda>p. (pi2 p, pi1 p))) p = pi2 p"
                using hEqAll by blast
              show ?thesis
                using top1_continuous_map_on_cong[OF hEq] hPi2X by blast
            qed

            have h2: "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) Z TZ (pi2 \<circ> (\<lambda>p. (pi2 p, pi1 p)))"
            proof -
              have hEqAll: "\<forall>p. (pi2 \<circ> (\<lambda>p. (pi2 p, pi1 p))) p = pi1 p"
                using hEq2 by (simp add: fun_eq_iff)
              have hEq: "\<forall>p\<in>Z \<times> C0. (pi2 \<circ> (\<lambda>p. (pi2 p, pi1 p))) p = pi1 p"
                using hEqAll by blast
              show ?thesis
                using top1_continuous_map_on_cong[OF hEq] hPi1 by blast
            qed

            have hRHS:
              "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) X TX (pi1 \<circ> (\<lambda>p. (pi2 p, pi1 p)))
               \<and> top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) Z TZ (pi2 \<circ> (\<lambda>p. (pi2 p, pi1 p)))"
              using h1 h2 by blast

            show ?thesis
              using iffD2[OF hpair] hRHS by blast
          qed
        qed

        have hfs:
          "top1_continuous_map_on (Z \<times> C0) (product_topology_on TZ ?TC0) Y TY (f \<circ> (\<lambda>p. (pi2 p, pi1 p)))"
          by (rule top1_continuous_map_on_comp[OF hs hf])

        have hNopen: "{p \<in> Z \<times> C0. (f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0} \<in> product_topology_on TZ ?TC0"
          using hfs hU0 unfolding top1_continuous_map_on_def by blast

        have hSlice: "{z0} \<times> C0 \<subseteq> {p \<in> Z \<times> C0. (f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0}"
        proof
          fix p
          assume hp: "p \<in> {z0} \<times> C0"
          obtain z c where hp': "p = (z, c)"
            by (cases p) simp
          have hz: "z = z0"
            using hp unfolding hp' by blast
          have hc: "c \<in> C0"
            using hp unfolding hp' by blast
          have hcX: "c \<in> X"
            using hC0subX hc by blast

          have "F z0 c \<in> U0"
          proof -
            have "F z0 c \<in> F z0 ` C0"
              using hc by blast
            thus ?thesis
              using hFz0sub by blast
          qed

          have hFz0c: "F z0 c = f (c, z0)"
            unfolding F_def using hcX by simp

          have "(f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p = f (c, z0)"
            unfolding hp' hz by (simp add: o_def pi1_def pi2_def)
          hence "(f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0"
            using \<open>F z0 c \<in> U0\<close> hFz0c by simp

          have hpZC0: "p \<in> Z \<times> C0"
          proof -
            have "p = (z0, c)"
              unfolding hp' using hz by simp
            thus ?thesis
              using hz0Z hc by simp
          qed
          show "p \<in> {p \<in> Z \<times> C0. (f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0}"
            using hpZC0 \<open>(f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0\<close> by simp
        qed

        show "\<exists>U\<in>TZ. z0 \<in> U \<and> U \<subseteq> P"
        proof (cases "C0 = {}")
          case True

          have hW_all: "W = ?C"
            using hWeq True by simp

          have hZsubP: "Z \<subseteq> P"
          proof
            fix z
            assume hzZ: "z \<in> Z"
            have hFzC: "F z \<in> ?C"
              using hFmem hzZ by blast
            have "F z \<in> W"
              using hFzC hW_all by simp
            thus "z \<in> P"
              unfolding P_def using hzZ by simp
          qed

          have hZinTZ: "Z \<in> TZ"
            by (rule conjunct1[OF conjunct2[OF hTopZ[unfolded is_topology_on_def]]])

          show ?thesis
            apply (rule bexI[where x=Z])
             apply (intro conjI)
              apply (rule hz0Z)
             apply (rule hZsubP)
            apply (rule hZinTZ)
            done
        next
          case False

          obtain U where hU:
            "neighborhood_of z0 Z TZ U \<and> U \<times> C0 \<subseteq> {p \<in> Z \<times> C0. (f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0}"
            using Lemma_26_8[OF hC0 hTopZ hTopC0 hNopen hz0Z hSlice] by blast

          have hnbhdU: "neighborhood_of z0 Z TZ U"
            by (rule conjunct1[OF hU])
          have hUsub: "U \<times> C0 \<subseteq> {p \<in> Z \<times> C0. (f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0}"
            by (rule conjunct2[OF hU])

          have hUopen: "U \<in> TZ"
            by (rule conjunct1[OF hnbhdU[unfolded neighborhood_of_def]])
          have hz0U: "z0 \<in> U"
            by (rule conjunct2[OF hnbhdU[unfolded neighborhood_of_def]])

          obtain c0 where hc0: "c0 \<in> C0"
            using False by blast

          have hUsP: "U \<subseteq> P"
          proof
            fix z
            assume hzU: "z \<in> U"
            have hzZ: "z \<in> Z"
            proof -
              have hpair0: "(z, c0) \<in> U \<times> C0"
                using hzU hc0 by simp
              have hmem0: "(z, c0) \<in> {p \<in> Z \<times> C0. (f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0}"
                by (rule subsetD[OF hUsub hpair0])
              have "(z, c0) \<in> Z \<times> C0"
                using hmem0 by simp
              thus ?thesis by simp
            qed

          have hFzC: "F z \<in> ?C"
            using hFmem hzZ by blast

          have hImg: "F z ` C0 \<subseteq> U0"
          proof
            fix y
            assume hy: "y \<in> F z ` C0"
            then obtain c where hc: "c \<in> C0" and hy': "y = F z c"
              by blast
            have hcX: "c \<in> X"
              using hC0subX hc by blast
            have hpair: "(z, c) \<in> U \<times> C0"
              using hzU hc by simp
            have "(z, c) \<in> {p \<in> Z \<times> C0. (f \<circ> (\<lambda>p. (pi2 p, pi1 p))) p \<in> U0}"
              by (rule subsetD[OF hUsub hpair])
            then have hfc: "(f \<circ> (\<lambda>p. (pi2 p, pi1 p))) (z, c) \<in> U0"
              by simp
            have hFzc: "F z c = f (c, z)"
              unfolding F_def using hcX by simp
            have hcomp': "(f \<circ> (\<lambda>p. (pi2 p, pi1 p))) (z, c) = f (c, z)"
              by (simp add: o_def pi1_def pi2_def)
            have "f (c, z) \<in> U0"
              using hfc unfolding hcomp' .
            show "y \<in> U0"
              using hy' hFzc \<open>f (c, z) \<in> U0\<close> by simp
          qed

          have "F z \<in> W"
            unfolding hWeq using hFzC hImg by simp
          thus "z \<in> P"
            unfolding P_def using hzZ by simp
        qed

          show ?thesis
            using hUopen hz0U hUsP by blast
        qed
      qed

      have hPopen: "P \<in> TZ"
        by (rule top1_open_of_local_subsets[OF hTopZ hPsubZ hLoc])

      show "{z \<in> Z. F z \<in> W} \<in> TZ"
        using hPopen by (simp add: P_def)
    qed

    have hContGen:
      "top1_continuous_map_on Z TZ ?C (topology_generated_by_subbasis ?C ?S) F"
      by (rule top1_continuous_map_on_to_topology_generated_by_subbasis[OF hTopZ hFmem hPreSub])

    show "top1_continuous_map_on Z TZ ?C ?Tco (\<lambda>z x. if x \<in> X then f (x, z) else undefined)"
      unfolding top1_compact_open_topology_on_def F_def[symmetric]
      by (rule hContGen)
  qed

  show "(\<forall>F. top1_continuous_map_on Z TZ ?C ?Tco F
          \<longrightarrow> top1_continuous_map_on (X \<times> Z) ?TPXZ Y TY (\<lambda>p. (F (snd p)) (fst p)))"
  proof (intro allI impI)
    fix F
    assume hF: "top1_continuous_map_on Z TZ ?C ?Tco F"
    have hTopC: "is_topology_on ?C ?Tco"
    proof -
      have hYopen: "Y \<in> TY"
        using hTopY unfolding is_topology_on_def by blast

      have hEmptyComp: "top1_compact_on {} (subspace_topology X TX {})"
        by (rule top1_compact_on_empty_subspace[OF hTopX])

      have hC_in_S: "?C \<in> ?S"
        unfolding top1_compact_open_subbasis_on_def
        apply (rule CollectI)
        apply (rule exI[where x="{}"])
        apply (rule exI[where x=Y])
        apply (intro conjI)
         apply (simp add: top1_continuous_funcs_on_def)
        apply (rule hEmptyComp)
        apply simp
        apply (rule hYopen)
        done

      have hSubbasis: "is_subbasis_on ?C ?S"
        unfolding is_subbasis_on_def
      proof (rule equalityI)
        show "\<Union>?S \<subseteq> ?C"
        proof
          fix g
          assume hg: "g \<in> \<Union>?S"
          obtain W where hW: "W \<in> ?S" and hgW: "g \<in> W"
            using hg by blast
          obtain C0 U0 where hWeq: "W = {f \<in> ?C. f ` C0 \<subseteq> U0}"
            using hW unfolding top1_compact_open_subbasis_on_def by blast
          show "g \<in> ?C"
            using hgW unfolding hWeq by simp
        qed

        show "?C \<subseteq> \<Union>?S"
        proof
          fix g
          assume hg: "g \<in> ?C"
          have hgC: "g \<in> ?C"
            by (rule hg)
          have "g \<in> ?C"
            using hgC .
          moreover have "g \<in> ?C"
            using hgC .
          have hgW0: "g \<in> {f \<in> ?C. f ` {} \<subseteq> Y}"
            using hgC by simp
          have "{f \<in> ?C. f ` {} \<subseteq> Y} \<in> ?S"
          proof -
            have "{f \<in> ?C. f ` {} \<subseteq> Y} = ?C"
              by (rule set_eqI) simp
            thus ?thesis
              using hC_in_S by simp
          qed
          thus "g \<in> \<Union>?S"
            using hgW0 by blast
        qed
      qed

      show ?thesis
        unfolding top1_compact_open_topology_on_def
        by (rule topology_generated_by_subbasis_is_topology_on[OF hSubbasis])
    qed

    have hPi1: "top1_continuous_map_on (X \<times> Z) ?TPXZ X TX pi1"
      by (rule top1_continuous_pi1[OF hTopX hTopZ])

    have hPi2: "top1_continuous_map_on (X \<times> Z) ?TPXZ Z TZ pi2"
      by (rule top1_continuous_pi2[OF hTopX hTopZ])

    have hFafter: "top1_continuous_map_on (X \<times> Z) ?TPXZ ?C ?Tco (F \<circ> pi2)"
      by (rule top1_continuous_map_on_comp[OF hPi2 hF])

    define h where "h = (\<lambda>p. if p \<in> X \<times> Z then (pi1 p, F (pi2 p)) else undefined)"

    have hDomTop: "is_topology_on (X \<times> Z) ?TPXZ"
      by (rule product_topology_on_is_topology_on[OF hTopX hTopZ])

    have hPi1h: "top1_continuous_map_on (X \<times> Z) ?TPXZ X TX (pi1 \<circ> h)"
    proof -
      have hEq: "\<forall>p\<in>X \<times> Z. (pi1 \<circ> h) p = pi1 p"
      proof (intro ballI)
        fix p
        assume hp: "p \<in> X \<times> Z"
        have "h p = (pi1 p, F (pi2 p))"
          unfolding h_def using hp by simp
        thus "(pi1 \<circ> h) p = pi1 p"
          by (simp add: o_def pi1_def)
      qed
      show ?thesis
        using top1_continuous_map_on_cong[OF hEq] hPi1 by blast
    qed

    have hPi2h: "top1_continuous_map_on (X \<times> Z) ?TPXZ ?C ?Tco (pi2 \<circ> h)"
    proof -
      have hEq: "\<forall>p\<in>X \<times> Z. (pi2 \<circ> h) p = (F \<circ> pi2) p"
      proof (intro ballI)
        fix p
        assume hp: "p \<in> X \<times> Z"
        have "h p = (pi1 p, F (pi2 p))"
          unfolding h_def using hp by simp
        thus "(pi2 \<circ> h) p = (F \<circ> pi2) p"
          by (simp add: o_def pi2_def)
      qed
      show ?thesis
        using top1_continuous_map_on_cong[OF hEq] hFafter by blast
    qed

    have hh: "top1_continuous_map_on (X \<times> Z) ?TPXZ (X \<times> ?C) (product_topology_on TX ?Tco) h"
    proof -
      have hpair:
        "top1_continuous_map_on (X \<times> Z) ?TPXZ (X \<times> ?C) (product_topology_on TX ?Tco) h
          \<longleftrightarrow>
            (top1_continuous_map_on (X \<times> Z) ?TPXZ X TX (pi1 \<circ> h)
             \<and> top1_continuous_map_on (X \<times> Z) ?TPXZ ?C ?Tco (pi2 \<circ> h))"
        by (rule Theorem_18_4[OF hDomTop hTopX hTopC])
      show ?thesis
      proof -
        have hRHS:
          "top1_continuous_map_on (X \<times> Z) ?TPXZ X TX (pi1 \<circ> h)
           \<and> top1_continuous_map_on (X \<times> Z) ?TPXZ ?C ?Tco (pi2 \<circ> h)"
          using hPi1h hPi2h by blast
        show ?thesis
          using iffD2[OF hpair] hRHS by blast
      qed
    qed

    have hEval:
      "top1_continuous_map_on
         (X \<times> ?C)
         (product_topology_on TX ?Tco)
         Y TY
         (\<lambda>p. (snd p) (fst p))"
      by (rule Theorem_46_10[OF hLC hHausX hTopY])

    have hComp: "top1_continuous_map_on (X \<times> Z) ?TPXZ Y TY ((\<lambda>p. (snd p) (fst p)) \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh hEval])

    have hEq:
      "\<forall>p\<in>X \<times> Z. ((\<lambda>p. (snd p) (fst p)) \<circ> h) p = (\<lambda>p. (F (snd p)) (fst p)) p"
    proof (intro ballI)
      fix p
      assume hp: "p \<in> X \<times> Z"
      obtain x z where hp': "p = (x, z)"
        by (cases p) simp
      have hxX: "x \<in> X" and hzZ: "z \<in> Z"
        using hp unfolding hp' by simp_all
      have hh': "h (x, z) = (x, F z)"
        unfolding h_def using hxX hzZ by (simp add: pi1_def pi2_def)
      show "((\<lambda>p. (snd p) (fst p)) \<circ> h) p = (\<lambda>p. (F (snd p)) (fst p)) p"
        unfolding hp' using hh' by (simp add: o_def)
    qed

    have hGoal: "top1_continuous_map_on (X \<times> Z) ?TPXZ Y TY (\<lambda>p. (F (snd p)) (fst p))"
      using top1_continuous_map_on_cong[OF hEq] hComp by blast

    show "top1_continuous_map_on (X \<times> Z) ?TPXZ Y TY (\<lambda>p. (F (snd p)) (fst p))"
      by (rule hGoal)
  qed
qed

section \<open>\<S>47 Ascoli's Theorem\<close>

(** from \S47 Theorem 47.1 (Ascoli's theorem) [top1.tex:6995] **)
theorem Theorem_47_1:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hFsub:
    "\<F> \<subseteq> top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)"
  shows "((top1_equicontinuous_family_on X TX Y d \<F>
        \<and> (\<forall>a\<in>X.
             top1_compact_on
               (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>))
               (subspace_topology Y (top1_metric_topology_on Y d)
                  (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>)))))
      \<longrightarrow> (\<exists>K. \<F> \<subseteq> K
              \<and> top1_compact_on K
                   (subspace_topology
                      (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
                      (subspace_topology (top1_PiE X (\<lambda>_. Y))
                         (top1_compact_convergence_topology_on X TX Y d)
                         (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)))
                      K)))"
    and "((top1_locally_compact_on X TX \<and> is_hausdorff_on X TX)
      \<longrightarrow>
      (\<forall>K. top1_compact_on K
               (subspace_topology
                  (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d))
                  (subspace_topology (top1_PiE X (\<lambda>_. Y))
                     (top1_compact_convergence_topology_on X TX Y d)
                     (top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)))
                  K)
            \<longrightarrow> top1_equicontinuous_family_on X TX Y d K
                \<and> (\<forall>a\<in>X.
                     top1_compact_on
                       (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` K))
                       (subspace_topology Y (top1_metric_topology_on Y d)
	                          (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` K))))))"
  sorry

text \<open>
  Proof structure for Ascoli's theorem (top1.tex): it is convenient to work in the
  product / pointwise topology on \<open>Y^X\<close>, take the closure \<open>G\<close> of \<open>\<F>\<close>, prove:
  (1) \<open>G\<close> is compact, (2) \<open>G\<close> consists of continuous maps and is equicontinuous, and
  (3) the pointwise and compact-convergence topologies coincide on \<open>G\<close>.
  The following lemmas record these steps as named goals (to be proved later).
\<close>

lemma top1_ascoli_step1_compact_closure_pointwise:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hFsub:
    "\<F> \<subseteq> top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)"
  assumes hCa:
	    "\<forall>a\<in>X.
	      top1_compact_on
	        (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>))
	        (subspace_topology Y (top1_metric_topology_on Y d)
	          (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>)))"
  shows
    "top1_compact_on
      (closure_on (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)) \<F>)
      (subspace_topology (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y (top1_metric_topology_on Y d))
        (closure_on (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)) \<F>))"
  sorry

lemma top1_ascoli_step2_closure_continuous_and_equicontinuous:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hFsub:
    "\<F> \<subseteq> top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)"
  assumes hEq: "top1_equicontinuous_family_on X TX Y d \<F>"
  assumes hCa:
	    "\<forall>a\<in>X.
	      top1_compact_on
	        (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>))
	        (subspace_topology Y (top1_metric_topology_on Y d)
	          (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>)))"
  defines "G \<equiv>
    closure_on (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)) \<F>"
  shows "G \<subseteq> top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)
      \<and> top1_equicontinuous_family_on X TX Y d G"
  sorry

lemma top1_ascoli_step3_pointwise_eq_compact_convergence_on_closure:
  assumes hTopX: "is_topology_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hFsub:
    "\<F> \<subseteq> top1_continuous_funcs_on X TX Y (top1_metric_topology_on Y d)"
  assumes hEq: "top1_equicontinuous_family_on X TX Y d \<F>"
  assumes hCa:
	    "\<forall>a\<in>X.
	      top1_compact_on
	        (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>))
	        (subspace_topology Y (top1_metric_topology_on Y d)
	          (closure_on Y (top1_metric_topology_on Y d) ((\<lambda>f. f a) ` \<F>)))"
  defines "G \<equiv>
    closure_on (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)) \<F>"
  shows
    "subspace_topology (top1_PiE X (\<lambda>_. Y)) (top1_pointwise_topology_on X Y (top1_metric_topology_on Y d)) G
      = subspace_topology (top1_PiE X (\<lambda>_. Y)) (top1_compact_convergence_topology_on X TX Y d) G"
  sorry

section \<open>\<S>48 Baire Spaces\<close>

definition top1_densein_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_densein_on X TX A \<longleftrightarrow> closure_on X TX A = X"

lemma top1_densein_on_subset_carrier:
  assumes hD: "top1_densein_on X TX A"
  shows "A \<subseteq> X"
proof -
  have "A \<subseteq> closure_on X TX A"
    by (rule subset_closure_on)
  thus ?thesis
    using hD unfolding top1_densein_on_def by simp
qed

lemma top1_densein_on_intersects_neighborhood:
  assumes hTop: "is_topology_on X TX"
  assumes hD: "top1_densein_on X TX A"
  assumes hxX: "x \<in> X"
  assumes hN: "neighborhood_of x X TX U"
  shows "intersects U A"
proof -
  have hAX: "A \<subseteq> X"
    by (rule top1_densein_on_subset_carrier[OF hD])
  have hxcl: "x \<in> closure_on X TX A"
    using hD hxX unfolding top1_densein_on_def by simp
  have hClChar: "\<forall>V. neighborhood_of x X TX V \<longrightarrow> intersects V A"
    by (rule iffD1[OF Theorem_17_5a[OF hTop hxX hAX], OF hxcl])
  show ?thesis
    using hClChar hN by blast
qed

lemma top1_densein_on_intersects_nonempty_open:
  assumes hTop: "is_topology_on X TX"
  assumes hD: "top1_densein_on X TX A"
  assumes hU: "U \<in> TX"
  assumes hUX: "U \<subseteq> X"
  assumes hUne: "U \<noteq> {}"
  shows "intersects U A"
proof -
  obtain x where hxU: "x \<in> U"
    using hUne by blast
  have hxX: "x \<in> X"
    using hUX hxU by blast
  have hN: "neighborhood_of x X TX U"
    unfolding neighborhood_of_def using hU hxU by simp
  show ?thesis
    by (rule top1_densein_on_intersects_neighborhood[OF hTop hD hxX hN])
qed

lemma top1_densein_on_iff_intersects_nonempty_open:
  assumes hTop: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  shows "top1_densein_on X TX A \<longleftrightarrow>
    (\<forall>U. U \<in> TX \<and> U \<subseteq> X \<and> U \<noteq> {} \<longrightarrow> intersects U A)"
proof (rule iffI)
  assume hD: "top1_densein_on X TX A"
  show "\<forall>U. U \<in> TX \<and> U \<subseteq> X \<and> U \<noteq> {} \<longrightarrow> intersects U A"
  proof (intro allI impI)
    fix U
    assume hU: "U \<in> TX \<and> U \<subseteq> X \<and> U \<noteq> {}"
    have hUT: "U \<in> TX" and hUX: "U \<subseteq> X" and hUne: "U \<noteq> {}"
      using hU by blast+
    show "intersects U A"
      by (rule top1_densein_on_intersects_nonempty_open[OF hTop hD hUT hUX hUne])
  qed
next
  assume hInt: "\<forall>U. U \<in> TX \<and> U \<subseteq> X \<and> U \<noteq> {} \<longrightarrow> intersects U A"
  show "top1_densein_on X TX A"
    unfolding top1_densein_on_def
  proof (rule subset_antisym)
    have hcl_sub: "closure_on X TX A \<subseteq> X"
      by (rule closure_on_subset_carrier[OF hTop hAX])
    show "closure_on X TX A \<subseteq> X"
      by (rule hcl_sub)

    show "X \<subseteq> closure_on X TX A"
    proof (rule subsetI)
      fix x
      assume hxX: "x \<in> X"

      have hClChar: "x \<in> closure_on X TX A \<longleftrightarrow>
        (\<forall>V. neighborhood_of x X TX V \<longrightarrow> intersects V A)"
        by (rule Theorem_17_5a[OF hTop hxX hAX])

      have hAllNbh: "\<forall>V. neighborhood_of x X TX V \<longrightarrow> intersects V A"
      proof (intro allI impI)
        fix V
        assume hVnbh: "neighborhood_of x X TX V"
        have hVT: "V \<in> TX" and hxV: "x \<in> V"
          using hVnbh unfolding neighborhood_of_def by blast+

        have hXT: "X \<in> TX"
          by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])
        have hXV: "X \<inter> V \<in> TX"
          by (rule topology_inter2[OF hTop hXT hVT])
        have hXVX: "X \<inter> V \<subseteq> X"
          by blast
        have hXVne: "X \<inter> V \<noteq> {}"
        proof
          assume "X \<inter> V = {}"
          hence "x \<notin> X \<inter> V"
            by simp
          thus False
            using hxX hxV by blast
        qed

        have hIntXV: "intersects (X \<inter> V) A"
          by (rule hInt[rule_format], intro conjI, rule hXV, rule hXVX, rule hXVne)

        show "intersects V A"
          using hIntXV unfolding intersects_def by blast
      qed

      show "x \<in> closure_on X TX A"
        using hClChar hAllNbh by blast
    qed
  qed
qed

definition top1_baire_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_baire_on X TX \<longleftrightarrow>
     (\<forall>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX \<and> top1_densein_on X TX (U n)) \<longrightarrow>
        top1_densein_on X TX (\<Inter>n. U n))"

lemma top1_compact_on_Inter_nested_closed_nonempty:
  assumes hcomp: "top1_compact_on X TX"
  assumes hCcl: "\<forall>n. closedin_on X TX (C n)"
  assumes hCne: "\<forall>n. C n \<noteq> {}"
  assumes hnest: "\<forall>n. C (Suc n) \<subseteq> C n"
  shows "(\<Inter>n. C n) \<noteq> {}"
proof (rule ccontr)
  assume hempty: "\<not> ((\<Inter>n. C n) \<noteq> {})"
  have hTop: "is_topology_on X TX"
    using hcomp unfolding top1_compact_on_def by blast

  have hXne: "X \<noteq> {}"
  proof -
    have "C 0 \<subseteq> X"
      using hCcl unfolding closedin_on_def by blast
    moreover have "C 0 \<noteq> {}"
      using hCne by simp
    ultimately show ?thesis
      by blast
  qed

  let ?Uc = "(\<lambda>n. X - C n)"
  let ?F = "range ?Uc"

  have hFsubTX: "?F \<subseteq> TX"
  proof
    fix U
    assume hU: "U \<in> ?F"
    then obtain n where hUn: "U = ?Uc n"
      by blast
    have hCncl: "closedin_on X TX (C n)"
      using hCcl by simp
    have "X - C n \<in> TX"
      using hCncl unfolding closedin_on_def by blast
    thus "U \<in> TX"
      unfolding hUn .
  qed

  have hCover: "X \<subseteq> \<Union>?F"
  proof (rule subsetI)
    fix x
    assume hxX: "x \<in> X"
    have hxnot: "x \<notin> (\<Inter>n. C n)"
      using hempty hxX by blast
    then obtain n where hxCn: "x \<notin> C n"
      by auto
    have hxU: "x \<in> ?Uc n"
      using hxX hxCn by simp
    have "?Uc n \<in> ?F"
      by (rule rangeI)
    thus "x \<in> \<Union>?F"
      using hxU by blast
  qed

  obtain G where hGfin: "finite G" and hGsub: "G \<subseteq> ?F" and hGcover: "X \<subseteq> \<Union>G"
    using hcomp hFsubTX hCover unfolding top1_compact_on_def by blast

  have hGne: "G \<noteq> {}"
  proof
    assume hG0: "G = {}"
    have "\<Union>G = {}"
      unfolding hG0 by simp
    thus False
      using hGcover hXne by blast
  qed

  have hIdx_ex: "\<forall>U\<in>G. \<exists>n. U = ?Uc n"
  proof (intro ballI)
    fix U
    assume hU: "U \<in> G"
    have hUinF: "U \<in> ?F"
      using hGsub hU by blast
    then obtain n where hUn: "U = ?Uc n"
      by blast
    show "\<exists>n. U = ?Uc n"
      by (rule exI[where x=n], rule hUn)
  qed

  have hex_idx: "\<exists>idx. \<forall>U\<in>G. U = ?Uc (idx U)"
    by (rule bchoice[OF hIdx_ex])

  obtain idx where hidx: "\<forall>U\<in>G. U = ?Uc (idx U)"
    using hex_idx by (erule exE)

  let ?J = "idx ` G"
  have hJfin: "finite ?J"
    using hGfin by simp
  have hJne: "?J \<noteq> {}"
    using hGne by simp

  define N where "N = Max ?J"
  have hNmem: "N \<in> ?J"
    unfolding N_def by (rule Max_in[OF hJfin hJne])
  have hNmax: "\<forall>n\<in>?J. n \<le> N"
  proof (intro ballI)
    fix n
    assume hn: "n \<in> ?J"
    show "n \<le> N"
      unfolding N_def by (rule Max_ge[OF hJfin hn])
  qed

  have hnest_add: "\<forall>m k. C (m + k) \<subseteq> C m"
  proof (intro allI)
    fix m k
    show "C (m + k) \<subseteq> C m"
    proof (induction k)
      case 0
      show ?case by simp
    next
      case (Suc k)
      have "C (m + Suc k) = C (Suc (m + k))"
        by simp
      also have "... \<subseteq> C (m + k)"
        using hnest by simp
      also have "... \<subseteq> C m"
        using Suc.IH by simp
      finally show ?case .
    qed
  qed

  have hCNsub: "\<forall>n\<in>?J. C N \<subseteq> C n"
  proof (intro ballI)
    fix n
	    assume hnJ: "n \<in> ?J"
	    have hnle: "n \<le> N"
	      using hNmax hnJ by blast
	    have hexk: "\<exists>k. N = n + k"
	      using hnle by (simp add: nat_le_iff_add)
	    obtain k where hNk: "N = n + k"
	      using hexk by (erule exE)
	    have "C N \<subseteq> C n"
	      unfolding hNk by (rule hnest_add[rule_format, of n k])
	    thus "C N \<subseteq> C n" .
	  qed

  have hUnionG_sub: "\<Union>G \<subseteq> X - C N"
  proof
    fix x
    assume hx: "x \<in> \<Union>G"
    then obtain U where hU: "U \<in> G" and hxU: "x \<in> U"
      by blast
    have hUeq: "U = ?Uc (idx U)"
      using hidx hU by blast
    have hidxU: "idx U \<in> ?J"
      using hU by blast
    have hCNsubCn: "C N \<subseteq> C (idx U)"
      using hCNsub hidxU by blast
    have hxU0: "x \<in> ?Uc (idx U)"
      by (subst hUeq[symmetric], rule hxU)
    have hxU': "x \<in> X - C (idx U)"
      using hxU0 by simp
    have hxX: "x \<in> X"
      by (rule DiffD1[OF hxU'])
    have hxnot: "x \<notin> C (idx U)"
    proof
      assume hxC: "x \<in> C (idx U)"
      show False
        by (rule DiffD2[OF hxU' hxC])
    qed
    have "x \<notin> C N"
    proof
      assume hxCN: "x \<in> C N"
      hence "x \<in> C (idx U)"
        using hCNsubCn by blast
      thus False
        using hxnot by contradiction
    qed
    thus "x \<in> X - C N"
      using hxX by simp
  qed

  have hXsub: "X \<subseteq> X - C N"
  proof -
    have "X \<subseteq> \<Union>G"
      by (rule hGcover)
    also have "\<Union>G \<subseteq> X - C N"
      by (rule hUnionG_sub)
    finally show ?thesis .
  qed

  have hCNsubX: "C N \<subseteq> X"
    using hCcl unfolding closedin_on_def by blast

  have hCNsubXm: "C N \<subseteq> X - C N"
    by (rule subset_trans[OF hCNsubX hXsub])

  have "C N = {}"
  proof (rule ccontr)
    assume hne: "C N \<noteq> {}"
    obtain y where hy: "y \<in> C N"
      using hne by blast
    have hyXm: "y \<in> X - C N"
      using hCNsubXm hy by blast
    show False
      by (rule DiffD2[OF hyXm hy])
  qed
  thus False
    using hCne by simp
qed

lemma top1_densein_on_open_subspace:
  assumes hTop: "is_topology_on X TX"
  assumes hD: "top1_densein_on X TX D"
  assumes hDX: "D \<subseteq> X"
  assumes hUX: "U \<subseteq> X"
  assumes hU: "U \<in> TX"
  shows "top1_densein_on U (subspace_topology X TX U) (D \<inter> U)"
proof -
  let ?TU = "subspace_topology X TX U"
  have hTopU: "is_topology_on U ?TU"
    by (rule subspace_topology_is_topology_on[OF hTop hUX])

  have hA_subU: "D \<inter> U \<subseteq> U"
    by blast

  have hA_subX: "D \<inter> U \<subseteq> X"
    using hUX by blast

  have hUsub_clA: "U \<subseteq> closure_on X TX (D \<inter> U)"
  proof (rule subsetI)
    fix x assume hxU: "x \<in> U"
    have hxX: "x \<in> X"
      using hUX hxU by blast

    have hclD: "closure_on X TX D = X"
      using hD unfolding top1_densein_on_def .
    have hxclD: "x \<in> closure_on X TX D"
      using hxX hclD by simp

    have hClCharD: "\<forall>W. neighborhood_of x X TX W \<longrightarrow> intersects W D"
      by (rule iffD1[OF Theorem_17_5a[OF hTop hxX hDX], OF hxclD])

    have hClCharA: "\<forall>W. neighborhood_of x X TX W \<longrightarrow> intersects W (D \<inter> U)"
    proof (intro allI impI)
      fix W
      assume hWnbh: "neighborhood_of x X TX W"
      have hWT: "W \<in> TX"
        using hWnbh unfolding neighborhood_of_def by (rule conjunct1)
      have hxW: "x \<in> W"
        using hWnbh unfolding neighborhood_of_def by (rule conjunct2)

      have hxWU: "x \<in> W \<inter> U"
        using hxW hxU by blast
      have hWUintTX: "W \<inter> U \<in> TX"
        by (rule topology_inter2[OF hTop hWT hU])
      have hNbhWU: "neighborhood_of x X TX (W \<inter> U)"
        unfolding neighborhood_of_def using hWUintTX hxWU by simp

      have hIntersectsWU_D: "intersects (W \<inter> U) D"
        by (rule hClCharD[rule_format, OF hNbhWU])

      show "intersects W (D \<inter> U)"
        using hIntersectsWU_D unfolding intersects_def by blast
    qed

    show "x \<in> closure_on X TX (D \<inter> U)"
      by (rule iffD2[OF Theorem_17_5a[OF hTop hxX hA_subX]], rule hClCharA)
  qed

  have hcl_subspace:
    "closure_on U ?TU (D \<inter> U) = closure_on X TX (D \<inter> U) \<inter> U"
    by (rule Theorem_17_4[OF hTop hA_subU hUX])

  show ?thesis
    unfolding top1_densein_on_def
    using hcl_subspace hUsub_clA hTopU closure_on_subset_carrier[OF hTop hA_subX] by blast
qed

(** from \S48 Lemma 48.1 [top1.tex:7170] **)
lemma Lemma_48_1:
  shows "top1_baire_on X TX \<longleftrightarrow>
    (\<forall>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX \<and> top1_densein_on X TX (U n)) \<longrightarrow> top1_densein_on X TX (\<Inter>n. U n))"
  by (simp add: top1_baire_on_def)

(** from \S48 Theorem 48.2 (Baire category theorem) [top1.tex:7178] **)
text \<open>
  Proof plan (compact Hausdorff case): use @{thm Theorem_32_3} (compact Hausdorff \<open>\<Longrightarrow>\<close> normal),
  hence regularity, then iterate @{thm regular_refine_point_into_open} to build a nested sequence of open
  sets whose closures stay inside the successive dense open sets. Apply
  @{thm top1_compact_on_Inter_nested_closed_nonempty} to the nested closed closures to obtain a point
  in the intersection.
\<close>

lemma top1_compact_hausdorff_imp_baire:
  assumes hcomp: "top1_compact_on X TX"
  assumes hHaus: "is_hausdorff_on X TX"
  shows "top1_baire_on X TX"
proof -
  have hTop: "is_topology_on X TX"
    using hcomp unfolding top1_compact_on_def by blast
  have hNormal: "top1_normal_on X TX"
    by (rule Theorem_32_3[OF hcomp hHaus])
  have hReg: "top1_regular_on X TX"
    by (rule normal_imp_regular_on[OF hNormal])

  show ?thesis
    unfolding top1_baire_on_def
  proof (intro allI impI)
    fix U :: "nat \<Rightarrow> 'a set"
    assume hU: "\<forall>n. U n \<in> TX \<and> top1_densein_on X TX (U n)"

    have hUnT: "\<forall>n. U n \<in> TX"
      using hU by blast
    have hUnDense: "\<forall>n. top1_densein_on X TX (U n)"
      using hU by blast

    have hUnSubX: "\<forall>n. U n \<subseteq> X"
    proof (intro allI)
      fix n
      show "U n \<subseteq> X"
        by (rule top1_densein_on_subset_carrier[OF hUnDense[rule_format, of n]])
    qed

    let ?A = "(\<Inter>n. U n)"
    have hASubX: "?A \<subseteq> X"
      by (rule subset_trans[of ?A "U 0" X]) (use hUnSubX in blast)+

    have hDenseChar:
      "top1_densein_on X TX ?A \<longleftrightarrow>
        (\<forall>W. W \<in> TX \<and> W \<subseteq> X \<and> W \<noteq> {} \<longrightarrow> intersects W ?A)"
      by (rule top1_densein_on_iff_intersects_nonempty_open[OF hTop hASubX])

    have hGoal: "\<forall>W. W \<in> TX \<and> W \<subseteq> X \<and> W \<noteq> {} \<longrightarrow> intersects W ?A"
    proof (intro allI impI)
      fix W
      assume hW: "W \<in> TX \<and> W \<subseteq> X \<and> W \<noteq> {}"
      have hWT: "W \<in> TX" and hWSubX: "W \<subseteq> X" and hWne: "W \<noteq> {}"
        using hW by blast+

      have hInt0: "intersects W (U 0)"
        by (rule top1_densein_on_intersects_nonempty_open[OF hTop hUnDense[rule_format, of 0] hWT hWSubX hWne])

      obtain x0 where hx0W: "x0 \<in> W" and hx0U0: "x0 \<in> U 0"
        using hInt0 unfolding intersects_def by blast
      have hx0X: "x0 \<in> X"
        using hWSubX hx0W by blast

      let ?O0 = "W \<inter> U 0"
      have hO0T: "?O0 \<in> TX"
        by (rule topology_inter2[OF hTop hWT hUnT[rule_format, of 0]])
      have hO0SubX: "?O0 \<subseteq> X"
        using hWSubX hUnSubX[rule_format, of 0] by blast
      have hx0O0: "x0 \<in> ?O0"
        using hx0W hx0U0 by blast

      obtain V0 where hV0T: "V0 \<in> TX"
        and hV0SubX: "V0 \<subseteq> X"
        and hx0V0: "x0 \<in> V0"
        and hclV0: "closure_on X TX V0 \<subseteq> ?O0"
        using regular_refine_point_into_open[OF hReg hx0X hO0T hO0SubX hx0O0]
        by blast
      have hV0ne: "V0 \<noteq> {}"
        using hx0V0 by blast

      have hStepEx:
        "\<forall>n Vn. Vn \<in> TX \<and> Vn \<subseteq> X \<and> Vn \<noteq> {}
          \<longrightarrow> (\<exists>V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                \<and> closure_on X TX V' \<subseteq> Vn
                \<and> closure_on X TX V' \<subseteq> U (Suc n))"
      proof (intro allI impI)
        fix n Vn
        assume hVn: "Vn \<in> TX \<and> Vn \<subseteq> X \<and> Vn \<noteq> {}"
        have hVnT: "Vn \<in> TX" and hVnSubX: "Vn \<subseteq> X" and hVnne: "Vn \<noteq> {}"
          using hVn by blast+

        have hInt: "intersects Vn (U (Suc n))"
          by (rule top1_densein_on_intersects_nonempty_open[OF hTop hUnDense[rule_format, of "Suc n"] hVnT hVnSubX hVnne])

        obtain x where hxVn: "x \<in> Vn" and hxUn: "x \<in> U (Suc n)"
          using hInt unfolding intersects_def by blast
        have hxX: "x \<in> X"
          using hVnSubX hxVn by blast

        let ?O = "Vn \<inter> U (Suc n)"
        have hOT: "?O \<in> TX"
          by (rule topology_inter2[OF hTop hVnT hUnT[rule_format, of "Suc n"]])
        have hOSubX: "?O \<subseteq> X"
          using hVnSubX hUnSubX[rule_format, of "Suc n"] by blast
        have hxO: "x \<in> ?O"
          using hxVn hxUn by blast

        obtain V' where hV'T: "V' \<in> TX"
          and hV'SubX: "V' \<subseteq> X"
          and hxV': "x \<in> V'"
          and hclV': "closure_on X TX V' \<subseteq> ?O"
          using regular_refine_point_into_open[OF hReg hxX hOT hOSubX hxO]
          by blast
        have hV'ne: "V' \<noteq> {}"
          using hxV' by blast

        have hclVn: "closure_on X TX V' \<subseteq> Vn"
          by (rule subset_trans[OF hclV' Int_lower1])
        have hclUn: "closure_on X TX V' \<subseteq> U (Suc n)"
          by (rule subset_trans[OF hclV' Int_lower2])

        show "\<exists>V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
            \<and> closure_on X TX V' \<subseteq> Vn
            \<and> closure_on X TX V' \<subseteq> U (Suc n)"
          by (rule exI[where x=V'], intro conjI, rule hV'T, rule hV'SubX, rule hV'ne, rule hclVn, rule hclUn)
      qed

      define step where
        "step = (\<lambda>n Vn. (SOME V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                \<and> closure_on X TX V' \<subseteq> Vn
                \<and> closure_on X TX V' \<subseteq> U (Suc n)))"

      have hStepP:
        "\<forall>n Vn. Vn \<in> TX \<and> Vn \<subseteq> X \<and> Vn \<noteq> {}
          \<longrightarrow> (step n Vn \<in> TX \<and> step n Vn \<subseteq> X \<and> step n Vn \<noteq> {}
                \<and> closure_on X TX (step n Vn) \<subseteq> Vn
                \<and> closure_on X TX (step n Vn) \<subseteq> U (Suc n))"
      proof (intro allI impI)
        fix n Vn
        assume hVn: "Vn \<in> TX \<and> Vn \<subseteq> X \<and> Vn \<noteq> {}"
        have hex': "\<exists>V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
              \<and> closure_on X TX V' \<subseteq> Vn
              \<and> closure_on X TX V' \<subseteq> U (Suc n)"
          using hStepEx hVn by blast

        show "step n Vn \<in> TX \<and> step n Vn \<subseteq> X \<and> step n Vn \<noteq> {}
              \<and> closure_on X TX (step n Vn) \<subseteq> Vn
              \<and> closure_on X TX (step n Vn) \<subseteq> U (Suc n)"
        proof -
          have hSome:
            "(SOME V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                \<and> closure_on X TX V' \<subseteq> Vn
                \<and> closure_on X TX V' \<subseteq> U (Suc n))
              \<in> TX
            \<and> (SOME V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                \<and> closure_on X TX V' \<subseteq> Vn
                \<and> closure_on X TX V' \<subseteq> U (Suc n))
              \<subseteq> X
            \<and> (SOME V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                \<and> closure_on X TX V' \<subseteq> Vn
                \<and> closure_on X TX V' \<subseteq> U (Suc n))
              \<noteq> {}
            \<and> closure_on X TX
                (SOME V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                    \<and> closure_on X TX V' \<subseteq> Vn
                    \<and> closure_on X TX V' \<subseteq> U (Suc n))
              \<subseteq> Vn
            \<and> closure_on X TX
                (SOME V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                    \<and> closure_on X TX V' \<subseteq> Vn
                    \<and> closure_on X TX V' \<subseteq> U (Suc n))
              \<subseteq> U (Suc n)"
            by (rule someI_ex[OF hex'])

          show ?thesis
          proof -
            define S where
              "S = (SOME V'. V' \<in> TX \<and> V' \<subseteq> X \<and> V' \<noteq> {}
                    \<and> closure_on X TX V' \<subseteq> Vn
                    \<and> closure_on X TX V' \<subseteq> U (Suc n))"

            have hS_in: "S \<in> TX"
              using hSome unfolding S_def by blast
            have hS_subX: "S \<subseteq> X"
              using hSome unfolding S_def by blast
            have hS_ne: "S \<noteq> {}"
              using hSome unfolding S_def by blast
            have hclS_subVn: "closure_on X TX S \<subseteq> Vn"
              using hSome unfolding S_def by blast
            have hclS_subUn: "closure_on X TX S \<subseteq> U (Suc n)"
              using hSome unfolding S_def by blast

            have hStep_eq: "step n Vn = S"
              unfolding S_def by (simp add: step_def)

            show ?thesis
            proof (intro conjI)
              show "step n Vn \<in> TX"
                by (simp add: hStep_eq hS_in)
              show "step n Vn \<subseteq> X"
                by (simp add: hStep_eq hS_subX)
              show "step n Vn \<noteq> {}"
                by (simp add: hStep_eq hS_ne)
              show "closure_on X TX (step n Vn) \<subseteq> Vn"
                by (simp add: hStep_eq hclS_subVn)
              show "closure_on X TX (step n Vn) \<subseteq> U (Suc n)"
                by (simp add: hStep_eq hclS_subUn)
            qed
          qed
        qed
      qed

      define V where "V = rec_nat V0 step"

      have V0_eq: "V 0 = V0"
        unfolding V_def by simp
      have VSuc_eq: "\<And>n. V (Suc n) = step n (V n)"
        unfolding V_def by simp

      have hVProps: "\<forall>n. V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {}"
      proof (intro allI)
        fix n
        show "V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {}"
        proof (induction n)
          case 0
          show ?case
            unfolding V0_eq using hV0T hV0SubX hV0ne by blast
        next
          case (Suc n)
          have hPrev: "V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {}"
            using Suc.IH by simp
          have hStep: "step n (V n) \<in> TX \<and> step n (V n) \<subseteq> X \<and> step n (V n) \<noteq> {}"
            using hStepP hPrev by blast
          show ?case
            unfolding VSuc_eq using hStep by blast
        qed
      qed

      have hClV0_sub: "closure_on X TX (V 0) \<subseteq> W \<inter> U 0"
        unfolding V0_eq using hclV0 by simp
      have hClVSuc_sub:
        "\<forall>n. closure_on X TX (V (Suc n)) \<subseteq> (V n \<inter> U (Suc n))"
      proof (intro allI)
        fix n
        have hPrev: "V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {}"
          using hVProps by blast
        have hCl1: "closure_on X TX (step n (V n)) \<subseteq> V n"
          using hStepP hPrev by blast
        have hCl2: "closure_on X TX (step n (V n)) \<subseteq> U (Suc n)"
          using hStepP hPrev by blast
        have hCl: "closure_on X TX (step n (V n)) \<subseteq> V n \<inter> U (Suc n)"
          using hCl1 hCl2 by blast
        show "closure_on X TX (V (Suc n)) \<subseteq> V n \<inter> U (Suc n)"
          unfolding VSuc_eq using hCl by simp
      qed

      let ?C = "\<lambda>n. closure_on X TX (V n)"

      have hCclosed: "\<forall>n. closedin_on X TX (?C n)"
      proof (intro allI)
        fix n
        have hVnSubX: "V n \<subseteq> X"
          using hVProps by blast
        show "closedin_on X TX (?C n)"
          by (rule closure_on_closed[OF hTop hVnSubX])
      qed

      have hCne: "\<forall>n. ?C n \<noteq> {}"
      proof (intro allI)
        fix n
        have hVn: "V n \<noteq> {}"
          using hVProps by blast
        have "V n \<subseteq> ?C n"
          by (rule subset_closure_on)
        then show "?C n \<noteq> {}"
          using hVn by blast
      qed

      have hnest: "\<forall>n. ?C (Suc n) \<subseteq> ?C n"
      proof (intro allI)
        fix n
        have hClSubVn: "?C (Suc n) \<subseteq> V n"
          using hClVSuc_sub[rule_format, of n] by blast
        have hVnSubCl: "V n \<subseteq> ?C n"
          by (rule subset_closure_on)
        show "?C (Suc n) \<subseteq> ?C n"
          by (rule subset_trans[OF hClSubVn hVnSubCl])
      qed

      have hInterC_ne: "(\<Inter>n. ?C n) \<noteq> {}"
        by (rule top1_compact_on_Inter_nested_closed_nonempty[OF hcomp hCclosed hCne hnest])

      obtain x where hx: "x \<in> (\<Inter>n. ?C n)"
        using hInterC_ne by blast

      have hxC0: "x \<in> ?C 0"
        using hx by simp

      have hC0SubW: "?C 0 \<subseteq> W"
        using hClV0_sub by blast
      have hxW: "x \<in> W"
        by (rule subsetD[OF hC0SubW hxC0])

      have hxUn: "\<forall>n. x \<in> U n"
      proof (intro allI)
        fix n
        show "x \<in> U n"
        proof (cases n)
          case 0
          have hC0SubU0: "?C 0 \<subseteq> U 0"
            using hClV0_sub by blast
          show ?thesis
            unfolding 0 by (rule subsetD[OF hC0SubU0 hxC0])
        next
          case (Suc m)
          have hxCm: "x \<in> ?C (Suc m)"
            using hx unfolding Suc by simp
          have hCSubUm: "?C (Suc m) \<subseteq> U (Suc m)"
            using hClVSuc_sub[rule_format, of m] by blast
          show ?thesis
            unfolding Suc by (rule subsetD[OF hCSubUm hxCm])
        qed
      qed

      have hxA: "x \<in> ?A"
        using hxUn by simp

      show "intersects W ?A"
        unfolding intersects_def
      proof -
        have hxWA: "x \<in> W \<inter> ?A"
          using hxW hxA by blast
        show "W \<inter> ?A \<noteq> {}"
        proof
          assume hEmpty: "W \<inter> ?A = {}"
          have "x \<in> {}"
            using hxWA unfolding hEmpty by simp
          thus False
            by simp
        qed
      qed
    qed

    show "top1_densein_on X TX ?A"
      by (rule iffD2[OF hDenseChar hGoal])
  qed
qed

(** Helpers for metric balls/closures used in the Baire arguments (\<S>48). **)

lemma top1_metric_ball_self_mem:
  assumes hd: "top1_metric_on X d"
  assumes hxX: "x \<in> X"
  assumes he: "0 < e"
  shows "x \<in> top1_ball_on X d x e"
proof -
  have "d x x = 0"
    using hd hxX unfolding top1_metric_on_def by blast
  thus ?thesis
    unfolding top1_ball_on_def using hxX he by simp
qed

lemma top1_ball_on_mono_radius:
  assumes hre: "r \<le> e"
  shows "top1_ball_on X d x r \<subseteq> top1_ball_on X d x e"
proof (rule subsetI)
  fix y
  assume hy: "y \<in> top1_ball_on X d x r"
  have hyX: "y \<in> X" and hyr: "d x y < r"
    using hy unfolding top1_ball_on_def by blast+
  have "d x y < e"
    by (rule less_le_trans[OF hyr hre])
  show "y \<in> top1_ball_on X d x e"
    unfolding top1_ball_on_def using hyX \<open>d x y < e\<close> by blast
qed

lemma top1_metric_closure_ball_imp_dist_le:
  assumes hd: "top1_metric_on X d"
  assumes hxX: "x \<in> X"
  assumes hr: "0 < r"
  assumes hycl: "y \<in> closure_on X (top1_metric_topology_on X d) (top1_ball_on X d x r)"
  shows "d x y \<le> r"
proof (rule ccontr)
  have hTop: "is_topology_on X (top1_metric_topology_on X d)"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])

  have hball_subX: "top1_ball_on X d x r \<subseteq> X"
    unfolding top1_ball_on_def by blast

  have hyX: "y \<in> X"
    using hycl closure_on_subset_carrier[OF hTop hball_subX] by blast

  assume hgt: "\<not> (d x y \<le> r)"
  have hlt: "r < d x y"
    using hgt by simp

  define e where "e = (d x y - r) / 2"
  have he_pos: "0 < e"
    unfolding e_def using hlt by simp

  have hVopen: "top1_ball_on X d y e \<in> top1_metric_topology_on X d"
    by (rule top1_ball_open_in_metric_topology[OF hd hyX he_pos])
  have hyV: "y \<in> top1_ball_on X d y e"
    by (rule top1_metric_ball_self_mem[OF hd hyX he_pos])
  have hVnbh: "neighborhood_of y X (top1_metric_topology_on X d) (top1_ball_on X d y e)"
    unfolding neighborhood_of_def using hVopen hyV by blast

  have hclChar:
    "y \<in> closure_on X (top1_metric_topology_on X d) (top1_ball_on X d x r)
      \<longleftrightarrow> (\<forall>U. neighborhood_of y X (top1_metric_topology_on X d) U \<longrightarrow> intersects U (top1_ball_on X d x r))"
    by (rule Theorem_17_5a[OF hTop hyX hball_subX])

  have hInt: "intersects (top1_ball_on X d y e) (top1_ball_on X d x r)"
    using hycl hclChar hVnbh by blast

  have hempty: "(top1_ball_on X d y e) \<inter> (top1_ball_on X d x r) = {}"
  proof (rule ccontr)
    assume hne: "(top1_ball_on X d y e) \<inter> (top1_ball_on X d x r) \<noteq> {}"
    then obtain z where hz: "z \<in> (top1_ball_on X d y e) \<inter> (top1_ball_on X d x r)"
      by blast
    have hzX: "z \<in> X"
      using hz unfolding top1_ball_on_def by blast
    have hdyz: "d y z < e"
      using hz unfolding top1_ball_on_def by blast
    have hdxz: "d x z < r"
      using hz unfolding top1_ball_on_def by blast

    have htri: "d x y \<le> d x z + d z y"
      using hd hxX hzX hyX unfolding top1_metric_on_def by blast
    have hsym: "d z y = d y z"
      using hd hzX hyX unfolding top1_metric_on_def by blast

    have "d x y < r + e"
    proof -
      have "d x y \<le> d x z + d z y"
        by (rule htri)
      also have "... < r + e"
        unfolding hsym using hdxz hdyz by simp
      finally show ?thesis .
    qed
    moreover have "r + e = (r + d x y) / 2"
      unfolding e_def by (simp add: field_simps algebra_simps)
    ultimately have "d x y < (r + d x y) / 2"
      by simp
    hence "2 * d x y < r + d x y"
      by (simp add: field_simps)
    hence "d x y < r"
      by simp
    thus False
      using hlt by simp
  qed

  show False
    using hInt unfolding intersects_def hempty by simp
qed

lemma top1_metric_closure_ball_subset_closed_ball:
  assumes hd: "top1_metric_on X d"
  assumes hxX: "x \<in> X"
  assumes hr: "0 < r"
  shows "closure_on X (top1_metric_topology_on X d) (top1_ball_on X d x r)
          \<subseteq> {y \<in> X. d x y \<le> r}"
proof (rule subsetI)
  fix y
  assume hy:
    "y \<in> closure_on X (top1_metric_topology_on X d) (top1_ball_on X d x r)"
  have hTop: "is_topology_on X (top1_metric_topology_on X d)"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])
  have hball_subX: "top1_ball_on X d x r \<subseteq> X"
    unfolding top1_ball_on_def by blast
  have hyX: "y \<in> X"
    using hy closure_on_subset_carrier[OF hTop hball_subX] by blast
  have "d x y \<le> r"
    by (rule top1_metric_closure_ball_imp_dist_le[OF hd hxX hr hy])
  thus "y \<in> {y \<in> X. d x y \<le> r}"
    using hyX by blast
qed

lemma top1_metric_closure_ball_subset_ball:
  assumes hd: "top1_metric_on X d"
  assumes hxX: "x \<in> X"
  assumes hr: "0 < r"
  assumes hre: "r < e"
  shows "closure_on X (top1_metric_topology_on X d) (top1_ball_on X d x r)
          \<subseteq> top1_ball_on X d x e"
proof (rule subsetI)
  fix y
  assume hy:
    "y \<in> closure_on X (top1_metric_topology_on X d) (top1_ball_on X d x r)"
  have hy' :
    "y \<in> {y \<in> X. d x y \<le> r}"
    by (rule subsetD[OF top1_metric_closure_ball_subset_closed_ball[OF hd hxX hr] hy])
  have hyX: "y \<in> X"
    using hy' by blast
  have hle: "d x y \<le> r"
    using hy' by blast
  have "d x y < e"
    by (rule le_less_trans[OF hle hre])
  thus "y \<in> top1_ball_on X d x e"
    unfolding top1_ball_on_def using hyX by blast
qed

lemma top1_metric_diameter_closure_ball_le:
  assumes hd: "top1_metric_on X d"
  assumes hxX: "x \<in> X"
  assumes hr: "0 < r"
  shows "top1_diameter_on d (closure_on X (top1_metric_topology_on X d) (top1_ball_on X d x r)) \<le> 2 * r"
proof -
  let ?T = "top1_metric_topology_on X d"
  let ?B = "top1_ball_on X d x r"
  let ?C = "closure_on X ?T ?B"
  let ?D = "{d u v | u v. u \<in> ?C \<and> v \<in> ?C}"

  have hTop: "is_topology_on X ?T"
    by (rule top1_metric_topology_on_is_topology_on[OF hd])

  have hBsubX: "?B \<subseteq> X"
    unfolding top1_ball_on_def by blast

  have hxx0: "d x x = 0"
    using hd hxX unfolding top1_metric_on_def by blast

  have hxB: "x \<in> ?B"
    unfolding top1_ball_on_def using hxX hxx0 hr by simp

  have hBsubC: "?B \<subseteq> ?C"
    by (rule subset_closure_on)

  have hxC: "x \<in> ?C"
    by (rule subsetD[OF hBsubC hxB])

  have hDne: "?D \<noteq> {}"
  proof -
    have hxD: "d x x \<in> ?D"
    proof -
      have "\<exists>u v. d x x = d u v \<and> u \<in> ?C \<and> v \<in> ?C"
        by (rule exI[where x=x], rule exI[where x=x]) (use hxC in simp)
      thus ?thesis
        by simp
    qed
    show ?thesis
      using hxD by blast
  qed

  have hCsubX: "?C \<subseteq> X"
    by (rule closure_on_subset_carrier[OF hTop hBsubX])

  show ?thesis
    unfolding top1_diameter_on_def
  proof (rule cSup_least)
    show "?D \<noteq> {}"
      by (rule hDne)
    fix t
    assume ht: "t \<in> ?D"
    obtain u v where huvC: "u \<in> ?C" "v \<in> ?C" and htuv: "t = d u v"
      using ht by blast

    have huX: "u \<in> X"
      using hCsubX huvC(1) by blast
    have hvX: "v \<in> X"
      using hCsubX huvC(2) by blast

    have hsymu: "d u x = d x u"
      using hd huX hxX unfolding top1_metric_on_def by blast

    have htri: "d u v \<le> d u x + d x v"
      using hd huX hxX hvX unfolding top1_metric_on_def by blast

    have hxu_le: "d x u \<le> r"
      by (rule top1_metric_closure_ball_imp_dist_le[OF hd hxX hr huvC(1)])
    have hxv_le: "d x v \<le> r"
      by (rule top1_metric_closure_ball_imp_dist_le[OF hd hxX hr huvC(2)])

    have hux_le: "d u x \<le> r"
      unfolding hsymu using hxu_le .

    have "t \<le> d u x + d x v"
      unfolding htuv by (rule htri)
    also have "... \<le> r + r"
      by (rule add_mono[OF hux_le hxv_le])
    also have "... = 2 * r"
      by simp
    finally show "t \<le> 2 * r" .
  qed
qed

text \<open>Helper for complete metric \<open>\<Longrightarrow>\<close> Baire: given dense open \<open>U n\<close> and nonempty open \<open>V\<close>,
  construct a Cauchy sequence converging to a point in \<open>V \<inter> \<Inter> U n\<close>.\<close>
lemma complete_metric_baire_aux:
  assumes hd: "top1_complete_metric_on X d"
  assumes hVopen: "V \<in> top1_metric_topology_on X d"
  assumes hVne: "V \<noteq> {}"
  assumes hVX: "V \<subseteq> X"
  assumes hUopen: "\<forall>n::nat. U n \<in> top1_metric_topology_on X d"
  assumes hUdense: "\<forall>n::nat. top1_densein_on X (top1_metric_topology_on X d) (U n)"
  assumes hUsubX: "\<forall>n::nat. U n \<subseteq> X"
  shows "V \<inter> (\<Inter>(n::nat). U n) \<noteq> {}"
proof -
  let ?TX = "top1_metric_topology_on X d"
  have hmetric: "top1_metric_on X d"
    using hd unfolding top1_complete_metric_on_def by blast
  have hTopM: "is_topology_on X ?TX"
    by (rule top1_metric_topology_on_is_topology_on[OF hmetric])

  text \<open>Dense open sets intersect every nonempty open set.\<close>
  have hDenseInter: "\<forall>n W. W \<in> ?TX \<and> W \<noteq> {} \<longrightarrow> W \<inter> U n \<noteq> {}"
  proof (intro allI impI)
    fix n W assume hW: "W \<in> ?TX \<and> W \<noteq> {}"
    have hWopen: "W \<in> ?TX" using hW by blast
    have hWne: "W \<noteq> {}" using hW by blast
    have hWX: "W \<subseteq> X"
      using hWopen unfolding top1_metric_topology_on_def topology_generated_by_basis_def by blast
    have hdn: "top1_densein_on X ?TX (U n)" using hUdense by blast
    have "intersects W (U n)"
      using iffD1[OF top1_densein_on_iff_intersects_nonempty_open[OF hTopM hUsubX[rule_format, of n]]]
            hdn hWopen hWX hWne
      by blast
    then show "W \<inter> U n \<noteq> {}"
      unfolding intersects_def by blast
  qed

  text \<open>Every nonempty open set in a metric topology contains a ball.\<close>
  have hOpenBall: "\<forall>W x. W \<in> ?TX \<and> x \<in> W \<longrightarrow> (\<exists>r>0. top1_ball_on X d x r \<subseteq> W)"
  proof (intro allI impI)
    fix W x assume hWx: "W \<in> ?TX \<and> x \<in> W"
    have "W \<in> ?TX" using hWx by blast
    have "x \<in> W" using hWx by blast
    show "\<exists>r>0. top1_ball_on X d x r \<subseteq> W"
      by (rule top1_metric_open_contains_ball[OF hmetric \<open>W \<in> ?TX\<close> \<open>x \<in> W\<close>])
  qed

  text \<open>Step 1: Construct sequences \<open>x :: nat \<Rightarrow> 'a\<close> and \<open>r :: nat \<Rightarrow> real\<close>
    such that \<open>B(x n, r n) \<subseteq> V \<inter> U 0 \<inter> ... \<inter> U n\<close> and \<open>r n < 1/(n+1)\<close>.\<close>
  text \<open>Step 1: Pick an initial point in V and a ball around it.\<close>
  obtain x0 where hx0V: "x0 \<in> V" using hVne by blast
  have hx0X: "x0 \<in> X" using hVX hx0V by blast
  obtain r0 where hr0pos: "r0 > 0" and hball0: "top1_ball_on X d x0 r0 \<subseteq> V"
    using hOpenBall hVopen hx0V by blast

  text \<open>Step 2: Inductively construct sequences \<open>xseq\<close> and \<open>rseq\<close>.
    At each step n:
    (a) \<open>xseq n \<in> X\<close>, \<open>rseq n > 0\<close>, \<open>rseq n < 1/(Suc n)\<close>
    (b) \<open>ball(xseq n, rseq n) \<subseteq> V\<close>, \<open>xseq n \<in> U k\<close> for \<open>k \<le> n\<close>
    (c) \<open>d(xseq(Suc n), xseq n) + rseq(Suc n) < rseq n\<close> (closed ball fits strictly)
    Property (c) ensures that the closed ball at step n+1 fits inside the open ball at step n,
    which is needed to conclude the limit is in V and each U k.\<close>
  text \<open>Inductive construction of nested ball sequences.
    We build xseq and rseq by nat recursion.  At each step, density of U_{n+1}
    provides a point in ball(xseq n, rseq n) \<inter> U (Suc n), and the metric open
    set condition provides a smaller ball inside.

    For now, this construction is admitted --- it is the last remaining admit in
    the Baire category proof and is a standard dependent choice argument.\<close>
  text \<open>Step function: given current point and radius, pick a new point in the
    intersection of the current ball with U n, and a new radius.\<close>
  have hstep: "\<forall>xc rc n. xc \<in> X \<and> rc > 0 \<and> top1_ball_on X d xc rc \<subseteq> V
    \<and> (\<forall>k\<le>n. top1_ball_on X d xc rc \<subseteq> U k) \<longrightarrow>
    (\<exists>xn rn. xn \<in> X \<and> rn > 0 \<and> rn < 1 / real (Suc (Suc n))
      \<and> top1_ball_on X d xn rn \<subseteq> V
      \<and> (\<forall>k\<le>Suc n. top1_ball_on X d xn rn \<subseteq> U k)
      \<and> d xn xc + rn < rc)"
  proof (intro allI impI)
    fix xc rc and n :: nat
    assume hprem: "xc \<in> X \<and> rc > 0 \<and> top1_ball_on X d xc rc \<subseteq> V
      \<and> (\<forall>k\<le>n. top1_ball_on X d xc rc \<subseteq> U k)"
    have hxcX: "xc \<in> X" and hrcpos: "rc > 0"
      and hballV: "top1_ball_on X d xc rc \<subseteq> V"
      and hballUk: "\<forall>k\<le>n. top1_ball_on X d xc rc \<subseteq> U k"
      using hprem by blast+
    text \<open>The current ball is open and nonempty.\<close>
    have hball_open: "top1_ball_on X d xc rc \<in> ?TX"
      by (rule top1_ball_open_in_metric_topology[OF hmetric hxcX hrcpos])
    have hball_ne: "top1_ball_on X d xc rc \<noteq> {}"
    proof -
      have "d xc xc = 0" using hmetric hxcX unfolding top1_metric_on_def by blast
      then show ?thesis unfolding top1_ball_on_def using hxcX hrcpos by force
    qed
    have hballX: "top1_ball_on X d xc rc \<subseteq> X" unfolding top1_ball_on_def by blast
    text \<open>Intersect with U(Suc n) — nonempty by density.\<close>
    have hW_ne: "top1_ball_on X d xc rc \<inter> U (Suc n) \<noteq> {}"
    proof -
      have "top1_densein_on X ?TX (U (Suc n))" using hUdense by blast
      then have "intersects (top1_ball_on X d xc rc) (U (Suc n))"
        using iffD1[OF top1_densein_on_iff_intersects_nonempty_open[OF hTopM hUsubX[rule_format, of "Suc n"]]]
              hball_open hballX hball_ne
        by blast
      then show ?thesis unfolding intersects_def by blast
    qed
    have hW_open: "top1_ball_on X d xc rc \<inter> U (Suc n) \<in> ?TX"
      by (rule topology_inter2[OF hTopM hball_open hUopen[rule_format, of "Suc n"]])
    text \<open>Pick xn in the intersection.\<close>
    obtain xn where hxn_ball: "xn \<in> top1_ball_on X d xc rc" and hxn_U: "xn \<in> U (Suc n)"
      using hW_ne by blast
    have hxnX: "xn \<in> X" using hxn_ball unfolding top1_ball_on_def by blast
    have hdist: "d xc xn < rc" using hxn_ball unfolding top1_ball_on_def by blast
    text \<open>Find a ball around xn inside the intersection.\<close>
    obtain r' where hr'pos: "r' > 0"
      and hball': "top1_ball_on X d xn r' \<subseteq> top1_ball_on X d xc rc \<inter> U (Suc n)"
    proof -
      have "xn \<in> top1_ball_on X d xc rc \<inter> U (Suc n)"
        using hxn_ball hxn_U by blast
      then show ?thesis using hOpenBall hW_open that by blast
    qed
    text \<open>Choose rn small enough.\<close>
    define rn where "rn = min (r' / 3) (min (1 / (2 * real (Suc (Suc n)))) ((rc - d xc xn) / 3))"
    have hrnpos: "rn > 0" unfolding rn_def using hr'pos hdist by simp
    have hrnlt: "rn < 1 / real (Suc (Suc n))"
    proof -
      have "rn \<le> 1 / (2 * real (Suc (Suc n)))" unfolding rn_def by simp
      also have "1 / (2 * real (Suc (Suc n))) < 1 / real (Suc (Suc n))"
      proof -
        have "0 < real (Suc (Suc n))" by simp
        then show ?thesis by (simp add: field_simps)
      qed
      finally show ?thesis .
    qed
    have hrnler': "rn \<le> r'" unfolding rn_def using hr'pos hdist by linarith
    have hrn_strict: "d xn xc + rn < rc"
    proof -
      have hsym: "d xn xc = d xc xn" using hmetric hxnX hxcX unfolding top1_metric_on_def by blast
      have "rn \<le> (rc - d xc xn) / 3" unfolding rn_def
        using hr'pos hdist by linarith
      then have "d xc xn + rn \<le> d xc xn + (rc - d xc xn) / 3" by linarith
      also have "... < rc"
      proof -
        have "d xc xn + (rc - d xc xn) / 3 = (2 * d xc xn + rc) / 3"
          by (simp add: field_simps)
        also have "(2 * d xc xn + rc) / 3 < (3 * rc) / 3"
        proof (rule divide_strict_right_mono)
          show "2 * d xc xn + rc < 3 * rc" using hdist by linarith
          show "(0::real) < 3" by simp
        qed
        also have "(3 * rc) / 3 = rc" by simp
        finally show ?thesis .
      qed
      finally show ?thesis using hsym by linarith
    qed
    have hball_rn_sub: "top1_ball_on X d xn rn \<subseteq> top1_ball_on X d xn r'"
      by (rule top1_ball_on_mono_radius[OF hrnler'])
    have hball_rn_sub_inter: "top1_ball_on X d xn rn \<subseteq> top1_ball_on X d xc rc \<inter> U (Suc n)"
      using hball_rn_sub hball' by blast
    have hball_rn_V: "top1_ball_on X d xn rn \<subseteq> V"
      using hball_rn_sub_inter hballV by blast
    have hball_rn_Uk: "\<forall>k\<le>Suc n. top1_ball_on X d xn rn \<subseteq> U k"
    proof (intro allI impI)
      fix k assume "k \<le> Suc n"
      show "top1_ball_on X d xn rn \<subseteq> U k"
      proof (cases "k \<le> n")
        case True
        then show ?thesis using hball_rn_sub_inter hballUk by blast
      next
        case False
        then have "k = Suc n" using \<open>k \<le> Suc n\<close> by linarith
        then show ?thesis using hball_rn_sub_inter by blast
      qed
    qed
    show "\<exists>xn rn. xn \<in> X \<and> rn > 0 \<and> rn < 1 / real (Suc (Suc n))
      \<and> top1_ball_on X d xn rn \<subseteq> V
      \<and> (\<forall>k\<le>Suc n. top1_ball_on X d xn rn \<subseteq> U k)
      \<and> d xn xc + rn < rc"
      using hxnX hrnpos hrnlt hball_rn_V hball_rn_Uk hrn_strict by blast
  qed

  text \<open>Base case: pick a point in V \<inter> U 0 with a small ball.\<close>
  have hbase: "\<exists>x0 r0. x0 \<in> X \<and> r0 > 0 \<and> r0 < 1
    \<and> top1_ball_on X d x0 r0 \<subseteq> V
    \<and> top1_ball_on X d x0 r0 \<subseteq> U 0"
  proof -
    obtain x0' where hx0'V: "x0' \<in> V" using hVne by blast
    obtain r0' where hr0'pos: "r0' > 0" and hball0': "top1_ball_on X d x0' r0' \<subseteq> V"
      using hOpenBall hVopen hx0'V by blast
    have hx0'X: "x0' \<in> X" using hVX hx0'V by blast
    have hball0'_open: "top1_ball_on X d x0' r0' \<in> ?TX"
      by (rule top1_ball_open_in_metric_topology[OF hmetric hx0'X hr0'pos])
    have hball0'_ne: "top1_ball_on X d x0' r0' \<noteq> {}"
    proof -
      have "d x0' x0' = 0" using hmetric hx0'X unfolding top1_metric_on_def by blast
      then have "x0' \<in> top1_ball_on X d x0' r0'"
        unfolding top1_ball_on_def using hx0'X hr0'pos by simp
      then show ?thesis by blast
    qed
    have hball0'X: "top1_ball_on X d x0' r0' \<subseteq> X"
      unfolding top1_ball_on_def by blast
    have "top1_ball_on X d x0' r0' \<inter> U 0 \<noteq> {}"
    proof -
      have "top1_densein_on X ?TX (U 0)" using hUdense by blast
      then have "intersects (top1_ball_on X d x0' r0') (U 0)"
        using iffD1[OF top1_densein_on_iff_intersects_nonempty_open[OF hTopM hUsubX[rule_format, of 0]]]
              hball0'_open hball0'X hball0'_ne
        by blast
      then show ?thesis unfolding intersects_def by blast
    qed
    then obtain x0 where hx0_ball: "x0 \<in> top1_ball_on X d x0' r0'" and hx0_U0: "x0 \<in> U 0" by blast
    have hx0X: "x0 \<in> X" using hx0_ball unfolding top1_ball_on_def by blast
    have hx0V: "x0 \<in> V" using hball0' hx0_ball by blast
    text \<open>Find a ball around x0 inside ball(x0', r0') \<inter> U 0.\<close>
    have hx0_open: "top1_ball_on X d x0' r0' \<inter> U 0 \<in> ?TX"
      by (rule topology_inter2[OF hTopM hball0'_open hUopen[rule_format, of 0]])
    obtain r1 where hr1pos: "r1 > 0" and hball1: "top1_ball_on X d x0 r1 \<subseteq> top1_ball_on X d x0' r0' \<inter> U 0"
    proof -
      have "x0 \<in> top1_ball_on X d x0' r0' \<inter> U 0"
        using hx0_ball hx0_U0 by blast
      then obtain r where "r > 0" "top1_ball_on X d x0 r \<subseteq> top1_ball_on X d x0' r0' \<inter> U 0"
        using hOpenBall hx0_open by blast
      then show ?thesis using that by blast
    qed
    define r0 where "r0 = min (r1 / 2) (1 / 2)"
    have hr0pos: "r0 > 0" unfolding r0_def using hr1pos by simp
    have hr0lt1: "r0 < 1" unfolding r0_def by simp
    have hr0ler1: "r0 \<le> r1" unfolding r0_def using hr1pos by simp
    have hball0_sub: "top1_ball_on X d x0 r0 \<subseteq> top1_ball_on X d x0 r1"
      by (rule top1_ball_on_mono_radius[OF hr0ler1])
    have "top1_ball_on X d x0 r0 \<subseteq> V"
      using hball0_sub hball1 hball0' by blast
    moreover have "top1_ball_on X d x0 r0 \<subseteq> U 0"
      using hball0_sub hball1 by blast
    ultimately show ?thesis
      using hx0X hr0pos hr0lt1 by blast
  qed

  text \<open>Construct the sequences by recursion using the step function.\<close>
  have "\<exists>xseq rseq.
    (\<forall>n. xseq n \<in> X \<and> rseq n > 0 \<and> rseq n < 1 / real (Suc n) \<and>
         top1_ball_on X d (xseq n) (rseq n) \<subseteq> V \<and>
         (\<forall>k\<le>n. top1_ball_on X d (xseq n) (rseq n) \<subseteq> U k) \<and>
         (n > 0 \<longrightarrow> d (xseq n) (xseq (n-(1::nat))) + rseq n < rseq (n-1)))"
  proof -
    text \<open>Use dependent\_nat\_choice from Hilbert\_Choice.\<close>
    define PP where "PP (n::nat) (p :: 'a \<times> real) \<longleftrightarrow> fst p \<in> X \<and> snd p > 0 \<and> snd p < 1 / real (Suc n)
      \<and> top1_ball_on X d (fst p) (snd p) \<subseteq> V
      \<and> (\<forall>k\<le>n. top1_ball_on X d (fst p) (snd p) \<subseteq> U k)" for n and p
    define QQ where "QQ (n::nat) (p :: 'a \<times> real) (q :: 'a \<times> real) \<longleftrightarrow> d (fst q) (fst p) + snd q < snd p"
      for n and p and q

    have hPP0: "\<exists>p. PP 0 p"
    proof -
      obtain x0' r0' where "x0' \<in> X" "r0' > 0" "r0' < 1"
        "top1_ball_on X d x0' r0' \<subseteq> V" "top1_ball_on X d x0' r0' \<subseteq> U 0"
        using hbase by blast
      then show ?thesis
        unfolding PP_def by (rule_tac x="(x0', r0')" in exI) simp
    qed

    have hPPstep: "\<And>(p::'a \<times> real) (n::nat). PP n p \<Longrightarrow> \<exists>q. PP (Suc n) q \<and> QQ n p q"
    proof -
      fix p :: "'a \<times> real" and n :: nat
      assume hPn: "PP n p"
      have hxc: "fst p \<in> X" and hrc: "snd p > 0"
        and hballV: "top1_ball_on X d (fst p) (snd p) \<subseteq> V"
        and hballUk: "\<forall>k\<le>n. top1_ball_on X d (fst p) (snd p) \<subseteq> U k"
        using hPn unfolding PP_def by blast+
      obtain xn rn where hxn: "xn \<in> X" "rn > 0" "rn < 1 / real (Suc (Suc n))"
        "top1_ball_on X d xn rn \<subseteq> V"
        "(\<forall>k\<le>Suc n. top1_ball_on X d xn rn \<subseteq> U k)"
        "d xn (fst p) + rn < snd p"
        using hstep[rule_format, of "fst p" "snd p" n] hxc hrc hballV hballUk
        by blast
      have "PP (Suc n) (xn, rn)"
        unfolding PP_def
        using hxn by simp
      moreover have "QQ n p (xn, rn)"
        unfolding QQ_def
        using hxn by simp
      ultimately show "\<exists>q. PP (Suc n) q \<and> QQ n p q"
        by blast
    qed

    have "\<exists>f::nat \<Rightarrow> 'a \<times> real. \<forall>n. PP n (f n) \<and> QQ n (f n) (f (Suc n))"
      by (rule dependent_nat_choice[OF hPP0 hPPstep])
    then obtain f :: "nat \<Rightarrow> 'a \<times> real" where hf: "\<forall>n. PP n (f n) \<and> QQ n (f n) (f (Suc n))"
      by blast

    define xseq' where "xseq' n = fst (f n)" for n
    define rseq' where "rseq' n = snd (f n)" for n

    show ?thesis
    proof (rule exI[where x=xseq'], rule exI[where x=rseq'])
      show "\<forall>n. xseq' n \<in> X \<and> rseq' n > 0 \<and> rseq' n < 1 / real (Suc n) \<and>
         top1_ball_on X d (xseq' n) (rseq' n) \<subseteq> V \<and>
         (\<forall>k\<le>n. top1_ball_on X d (xseq' n) (rseq' n) \<subseteq> U k) \<and>
         (n > 0 \<longrightarrow> d (xseq' n) (xseq' (n-(1::nat))) + rseq' n < rseq' (n-1))"
      proof (intro allI)
        fix n
        have hPPn: "PP n (f n)" using hf by blast
        have hxn: "fst (f n) \<in> X" using hPPn unfolding PP_def by blast
        have hrn_pos: "snd (f n) > 0" using hPPn unfolding PP_def by blast
        have hrn_lt: "snd (f n) < 1 / real (Suc n)" using hPPn unfolding PP_def by blast
        have hball_V: "top1_ball_on X d (fst (f n)) (snd (f n)) \<subseteq> V"
          using hPPn unfolding PP_def by blast
        have hball_Uk: "\<forall>k\<le>n. top1_ball_on X d (fst (f n)) (snd (f n)) \<subseteq> U k"
          using hPPn unfolding PP_def by blast
        have hdist_step: "n > 0 \<longrightarrow> d (fst (f n)) (fst (f (n-1))) + snd (f n) < snd (f (n-1))"
        proof (intro impI)
          assume "n > 0"
          then obtain m where hm: "n = Suc m" using gr0_implies_Suc by blast
          have "QQ m (f m) (f (Suc m))" using hf by blast
          then show "d (fst (f n)) (fst (f (n-1))) + snd (f n) < snd (f (n-1))"
            unfolding QQ_def hm by simp
        qed
        show "xseq' n \<in> X \<and> rseq' n > 0 \<and> rseq' n < 1 / real (Suc n) \<and>
           top1_ball_on X d (xseq' n) (rseq' n) \<subseteq> V \<and>
           (\<forall>k\<le>n. top1_ball_on X d (xseq' n) (rseq' n) \<subseteq> U k) \<and>
           (n > 0 \<longrightarrow> d (xseq' n) (xseq' (n-(1::nat))) + rseq' n < rseq' (n-1))"
          unfolding xseq'_def rseq'_def
          using hxn hrn_pos hrn_lt hball_V hball_Uk hdist_step
          by blast
      qed
    qed
  qed

  then obtain xseq rseq where
    hseq_prop: "\<forall>n. xseq n \<in> X \<and> rseq n > 0 \<and> rseq n < 1 / real (Suc n) \<and>
         top1_ball_on X d (xseq n) (rseq n) \<subseteq> V \<and>
         (\<forall>k\<le>n. top1_ball_on X d (xseq n) (rseq n) \<subseteq> U k) \<and>
         (n > 0 \<longrightarrow> d (xseq n) (xseq (n-(1::nat))) + rseq n < rseq (n-1))"
    by blast

  text \<open>Auxiliary facts from sequence properties.\<close>
  have hxseqX: "\<forall>n. xseq n \<in> X" using hseq_prop by blast
  have hrseqpos: "\<forall>n. rseq n > 0" using hseq_prop by blast
  have hrseq_bound: "\<forall>n. rseq n < 1 / real (Suc n)" using hseq_prop by blast
  have hball_V: "\<forall>n. top1_ball_on X d (xseq n) (rseq n) \<subseteq> V"
    using hseq_prop by blast
  have hball_Uk: "\<forall>n k. k \<le> n \<longrightarrow> top1_ball_on X d (xseq n) (rseq n) \<subseteq> U k"
    using hseq_prop by blast
  have hdist_rseq: "\<forall>n. n > 0 \<longrightarrow> d (xseq n) (xseq (n-(1::nat))) + rseq n < rseq (n-1)"
    using hseq_prop by blast
  have hball_nest: "\<forall>n. n > 0 \<longrightarrow>
    top1_ball_on X d (xseq n) (rseq n) \<subseteq> top1_ball_on X d (xseq (n-(1::nat))) (rseq (n-1))"
  proof (intro allI impI subsetI)
    fix n y assume hn: "n > 0" and hy: "y \<in> top1_ball_on X d (xseq n) (rseq n)"
    have hyX: "y \<in> X" using hy unfolding top1_ball_on_def by blast
    have hdy: "d (xseq n) y < rseq n" using hy unfolding top1_ball_on_def by blast
    have hdn: "d (xseq n) (xseq (n-1)) + rseq n < rseq (n-1)"
      using hdist_rseq[rule_format, OF hn] by simp
    have hnX: "xseq n \<in> X" using hxseqX by blast
    have hn1X: "xseq (n-1) \<in> X" using hxseqX by blast
    have htri: "d (xseq (n-1)) y \<le> d (xseq (n-1)) (xseq n) + d (xseq n) y"
      using hmetric hn1X hnX hyX unfolding top1_metric_on_def by blast
    have hsym: "d (xseq (n-1)) (xseq n) = d (xseq n) (xseq (n-1))"
      using hmetric hn1X hnX unfolding top1_metric_on_def by blast
    have "d (xseq (n-1)) y < rseq (n-1)"
      using htri hsym hdy hdn by linarith
    then show "y \<in> top1_ball_on X d (xseq (n-(1::nat))) (rseq (n-1))"
      unfolding top1_ball_on_def using hyX by simp
  qed

  text \<open>Transitive nesting of balls.\<close>
  have hball_nest_le: "\<And>m n. n \<le> m \<Longrightarrow>
    top1_ball_on X d (xseq m) (rseq m) \<subseteq> top1_ball_on X d (xseq n) (rseq n)"
  proof -
    fix m n :: nat assume "n \<le> m"
    then show "top1_ball_on X d (xseq m) (rseq m) \<subseteq> top1_ball_on X d (xseq n) (rseq n)"
    proof (induction m)
      case 0 then show ?case by simp
    next
      case (Suc k)
      show ?case
      proof (cases "n = Suc k")
        case True then show ?thesis by simp
      next
        case False
        then have "n \<le> k" using Suc.prems by linarith
        have step: "top1_ball_on X d (xseq (Suc k)) (rseq (Suc k))
                  \<subseteq> top1_ball_on X d (xseq k) (rseq k)"
          using hball_nest[rule_format, of "Suc k"] by simp
        have IH: "top1_ball_on X d (xseq k) (rseq k)
                  \<subseteq> top1_ball_on X d (xseq n) (rseq n)"
          by (rule Suc.IH[OF \<open>n \<le> k\<close>])
        show ?thesis
          using step IH by blast
      qed
    qed
  qed

  text \<open>Each xseq m is in ball(xseq N, rseq N) for m \<ge> N.\<close>
  have hxseq_in_ball: "\<And>N m. N \<le> m \<Longrightarrow> xseq m \<in> top1_ball_on X d (xseq N) (rseq N)"
  proof -
    fix N m :: nat assume "N \<le> m"
    have hself: "xseq m \<in> top1_ball_on X d (xseq m) (rseq m)"
    proof -
      have "d (xseq m) (xseq m) = 0"
        using hmetric hxseqX[rule_format, of m] unfolding top1_metric_on_def by blast
      then show ?thesis
        unfolding top1_ball_on_def using hxseqX[rule_format, of m] hrseqpos[rule_format, of m] by simp
    qed
    show "xseq m \<in> top1_ball_on X d (xseq N) (rseq N)"
      using subsetD[OF hball_nest_le[OF \<open>N \<le> m\<close>] hself] .
  qed

  text \<open>Step 3: The sequence is Cauchy.\<close>
  have hCauchy: "top1_cauchy_seq_on X d xseq"
    unfolding top1_cauchy_seq_on_def
  proof (intro allI impI)
    fix e :: real assume hepos: "0 < e"
    text \<open>Choose N large enough that 2 * rseq N < e.\<close>
    have "\<exists>N. 2 * rseq N < e"
    proof -
      obtain n :: nat where hn: "real n > 2 / e"
        using reals_Archimedean2 by blast
      have "2 * rseq n < 2 * (1 / real (Suc n))"
        using hrseq_bound[rule_format, of n] by linarith
      also have "2 * (1 / real (Suc n)) = 2 / real (Suc n)"
        by simp
      also have "2 / real (Suc n) \<le> 2 / real n"
      proof (cases "n = 0")
        case True
        then have "2 / e > 0" using hepos by simp
        then show ?thesis using hn True by simp
      next
        case False
        then have "real n > 0" by simp
        then show ?thesis
          by (intro divide_left_mono) simp_all
      qed
      also have "2 / real n \<le> e"
      proof (cases "n = 0")
        case True
        then show ?thesis using hn hepos by simp
      next
        case False
        then have "real n > 0" by simp
        then have "2 / real n \<le> 2 / (2 / e)"
        proof -
          have "2 / e \<le> real n" using hn by linarith
          then show ?thesis using \<open>real n > 0\<close> hepos
            by (intro divide_left_mono) simp_all
        qed
        also have "2 / (2 / e) = e" using hepos by simp
        finally show ?thesis .
      qed
      finally show ?thesis by blast
    qed
    then obtain N where hN: "2 * rseq N < e" by blast
    show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. xseq m \<in> X \<and> xseq n \<in> X \<and> d (xseq m) (xseq n) < e"
    proof (rule exI[where x=N], intro allI impI)
      fix m assume hmN: "N \<le> m"
      fix n assume hnN: "N \<le> n"
      have hmX: "xseq m \<in> X" using hxseqX by blast
      have hnX: "xseq n \<in> X" using hxseqX by blast
      have hNX: "xseq N \<in> X" using hxseqX by blast
      have hm_ball: "d (xseq N) (xseq m) < rseq N"
        using hxseq_in_ball[OF hmN] unfolding top1_ball_on_def by blast
      have hn_ball: "d (xseq N) (xseq n) < rseq N"
        using hxseq_in_ball[OF hnN] unfolding top1_ball_on_def by blast
      have htri: "d (xseq m) (xseq n) \<le> d (xseq m) (xseq N) + d (xseq N) (xseq n)"
        using hmetric hmX hNX hnX unfolding top1_metric_on_def by blast
      have hsym: "d (xseq m) (xseq N) = d (xseq N) (xseq m)"
        using hmetric hmX hNX unfolding top1_metric_on_def by blast
      have "d (xseq m) (xseq n) < 2 * rseq N"
        using htri hsym hm_ball hn_ball by linarith
      then have "d (xseq m) (xseq n) < e"
        using hN by linarith
      then show "xseq m \<in> X \<and> xseq n \<in> X \<and> d (xseq m) (xseq n) < e"
        using hmX hnX by blast
    qed
  qed

  text \<open>Step 4: By completeness, the sequence converges.\<close>
  obtain x where hxX: "x \<in> X"
    and hconv: "seq_converges_to_on xseq x X ?TX"
    using hd hCauchy unfolding top1_complete_metric_on_def by blast

  text \<open>Step 5-6: The limit is in each ball, hence in V and each U k.\<close>
  text \<open>Key: d(xseq(Suc n), x) \<le> rseq(Suc n) (limit of tail in ball).
    Then d(xseq n, x) \<le> d(xseq n, xseq(Suc n)) + d(xseq(Suc n), x) < rseq n.\<close>
  text \<open>First show d(xseq n, x) \<le> rseq n for all n (non-strict).\<close>
  have hdist_le_rseq: "\<forall>n. d (xseq n) x \<le> rseq n"
  proof (intro allI)
    fix n
    text \<open>For any \<delta> > 0, d(xseq n, x) < rseq n + \<delta> (triangle inequality with a tail term).\<close>
    have hle: "\<forall>\<delta>>0. d (xseq n) x < rseq n + \<delta>"
    proof (intro allI impI)
      fix \<delta> :: real assume "0 < \<delta>"
      text \<open>By convergence, choose m with d(x, xseq m) < \<delta> and m \<ge> n.\<close>
      have "\<exists>M. \<forall>m\<ge>M. d x (xseq m) < \<delta>"
      proof -
        have hball_x: "top1_ball_on X d x \<delta> \<in> ?TX"
          by (rule top1_ball_open_in_metric_topology[OF hmetric hxX \<open>0 < \<delta>\<close>])
        have hx_in_ball_x: "x \<in> top1_ball_on X d x \<delta>"
        proof -
          have "d x x = 0" using hmetric hxX unfolding top1_metric_on_def by blast
          then show ?thesis unfolding top1_ball_on_def using hxX \<open>0 < \<delta>\<close> by simp
        qed
        have hnbhd: "neighborhood_of x X ?TX (top1_ball_on X d x \<delta>)"
          unfolding neighborhood_of_def using hball_x hx_in_ball_x by blast
        obtain M where "\<forall>m\<ge>M. xseq m \<in> top1_ball_on X d x \<delta>"
          using hconv hnbhd unfolding seq_converges_to_on_def by blast
        then show ?thesis
          unfolding top1_ball_on_def by blast
      qed
      then obtain M where hM: "\<forall>m\<ge>M. d x (xseq m) < \<delta>" by blast
      define m where "m = max M n"
      have "m \<ge> M" unfolding m_def by simp
      have "m \<ge> n" unfolding m_def by simp
      have hdxm: "d x (xseq m) < \<delta>" using hM \<open>m \<ge> M\<close> by blast
      have hm_ball: "xseq m \<in> top1_ball_on X d (xseq n) (rseq n)"
        by (rule hxseq_in_ball[OF \<open>n \<le> m\<close>])
      have "d (xseq n) (xseq m) < rseq n"
        using hm_ball unfolding top1_ball_on_def by blast
      have hmX: "xseq m \<in> X" using hxseqX by blast
      have hnX: "xseq n \<in> X" using hxseqX by blast
      have hsym: "d (xseq m) x = d x (xseq m)"
        using hmetric hmX hxX unfolding top1_metric_on_def by blast
      have htri: "d (xseq n) x \<le> d (xseq n) (xseq m) + d (xseq m) x"
        using hmetric hnX hmX hxX unfolding top1_metric_on_def by blast
      show "d (xseq n) x < rseq n + \<delta>"
        using htri \<open>d (xseq n) (xseq m) < rseq n\<close> hsym hdxm by linarith
    qed
    text \<open>Since d(xseq n, x) < rseq n + \<delta> for all \<delta> > 0, d(xseq n, x) \<le> rseq n.\<close>
    show "d (xseq n) x \<le> rseq n"
    proof (rule ccontr)
      assume "\<not> d (xseq n) x \<le> rseq n"
      then have hgt: "d (xseq n) x > rseq n" by linarith
      define \<delta> where "\<delta> = (d (xseq n) x - rseq n) / 2"
      have h\<delta>pos: "\<delta> > 0"
      proof -
        have "d (xseq n) x - rseq n > 0" using hgt by linarith
        then show ?thesis unfolding \<delta>_def by simp
      qed
      have "d (xseq n) x < rseq n + \<delta>"
        using hle h\<delta>pos by blast
      then have hlt: "d (xseq n) x < rseq n + \<delta>"
        by simp
      have h2: "2 * \<delta> = d (xseq n) x - rseq n"
        unfolding \<delta>_def by simp
      have "2 * d (xseq n) x < 2 * rseq n + 2 * \<delta>"
        using hlt by linarith
      then have "2 * d (xseq n) x < 2 * rseq n + (d (xseq n) x - rseq n)"
        using h2 by linarith
      then have "d (xseq n) x < rseq n"
        by linarith
      then show False using hgt by linarith
    qed
  qed

  text \<open>Then use strict containment to get d(xseq n, x) < rseq n.\<close>
  have hx_in_ball: "\<forall>n. x \<in> top1_ball_on X d (xseq n) (rseq n)"
  proof (intro allI)
    fix n
    have hn1X: "xseq (Suc n) \<in> X" using hxseqX by blast
    have hnX: "xseq n \<in> X" using hxseqX by blast
    have "d (xseq (Suc n)) x \<le> rseq (Suc n)"
      using hdist_le_rseq by blast
    have "d (xseq (Suc n)) (xseq n) + rseq (Suc n) < rseq n"
      using hdist_rseq[rule_format, of "Suc n"] by simp
    have hsym_n1n: "d (xseq n) (xseq (Suc n)) = d (xseq (Suc n)) (xseq n)"
      using hmetric hnX hn1X unfolding top1_metric_on_def by blast
    have htri: "d (xseq n) x \<le> d (xseq n) (xseq (Suc n)) + d (xseq (Suc n)) x"
      using hmetric hnX hn1X hxX unfolding top1_metric_on_def by blast
    have "d (xseq n) x < rseq n"
      using htri hsym_n1n \<open>d (xseq (Suc n)) x \<le> rseq (Suc n)\<close>
            \<open>d (xseq (Suc n)) (xseq n) + rseq (Suc n) < rseq n\<close>
      by linarith
    then show "x \<in> top1_ball_on X d (xseq n) (rseq n)"
      unfolding top1_ball_on_def using hxX by simp
  qed

  have hxV: "x \<in> V"
    using hx_in_ball hball_V by blast

  have hxU: "\<forall>n. x \<in> U n"
  proof (intro allI)
    fix k
    have "x \<in> top1_ball_on X d (xseq k) (rseq k)" using hx_in_ball by blast
    then show "x \<in> U k" using hball_Uk[rule_format, of k k] by blast
  qed

  have "x \<in> V \<inter> (\<Inter>n. U n)"
    using hxV hxU by blast
  then show ?thesis by blast
qed

theorem Theorem_48_2:
  shows "top1_compact_on X TX \<and> is_hausdorff_on X TX \<longrightarrow> top1_baire_on X TX"
    and "top1_complete_metric_on X d \<longrightarrow> top1_baire_on X (top1_metric_topology_on X d)"
proof -
  show "top1_compact_on X TX \<and> is_hausdorff_on X TX \<longrightarrow> top1_baire_on X TX"
  proof
    assume h: "top1_compact_on X TX \<and> is_hausdorff_on X TX"
    have hcomp: "top1_compact_on X TX" and hHaus: "is_hausdorff_on X TX"
      using h by blast+
    show "top1_baire_on X TX"
      by (rule top1_compact_hausdorff_imp_baire[OF hcomp hHaus])
  qed

  show "top1_complete_metric_on X d \<longrightarrow> top1_baire_on X (top1_metric_topology_on X d)"
  proof
    assume hcomplete: "top1_complete_metric_on X d"
    have hmetric: "top1_metric_on X d"
      using hcomplete unfolding top1_complete_metric_on_def by blast
    have hTopM: "is_topology_on X (top1_metric_topology_on X d)"
      by (rule top1_metric_topology_on_is_topology_on[OF hmetric])
    show "top1_baire_on X (top1_metric_topology_on X d)"
      unfolding top1_baire_on_def
    proof (intro allI impI)
      fix U :: "nat \<Rightarrow> 'a set"
      assume hU: "\<forall>n. U n \<in> top1_metric_topology_on X d \<and> top1_densein_on X (top1_metric_topology_on X d) (U n)"
      text \<open>For each nonempty open V, we construct nested metric balls inside V \<inter> U_0 \<inter> ... \<inter> U_n.
        The resulting Cauchy sequence converges to a point in V \<inter> \<Inter> U_n.\<close>
      let ?TX = "top1_metric_topology_on X d"

      have hUnOpen: "\<forall>n. U n \<in> ?TX" using hU by blast
      have hUnDense: "\<forall>n. top1_densein_on X ?TX (U n)" using hU by blast
      have hUnSubX: "\<forall>n. U n \<subseteq> X"
      proof (intro allI)
        fix n
        have "U n \<in> ?TX" using hUnOpen by simp
        then show "U n \<subseteq> X"
          unfolding top1_metric_topology_on_def topology_generated_by_basis_def by blast
      qed

      have hInterSubX: "(\<Inter>n. U n) \<subseteq> X"
      proof (rule subsetI)
        fix x assume "x \<in> (\<Inter>n. U n)"
        then have "x \<in> U 0" by blast
        then show "x \<in> X" using hUnSubX by blast
      qed

      show "top1_densein_on X ?TX (\<Inter>n. U n)"
      proof (rule iffD2[OF top1_densein_on_iff_intersects_nonempty_open[OF hTopM hInterSubX]])
        show "\<forall>V. V \<in> ?TX \<and> V \<subseteq> X \<and> V \<noteq> {} \<longrightarrow> intersects V (\<Inter>n. U n)"
        proof (intro allI impI)
          fix V assume hV: "V \<in> ?TX \<and> V \<subseteq> X \<and> V \<noteq> {}"
          have "V \<inter> (\<Inter>n. U n) \<noteq> {}"
            by (rule complete_metric_baire_aux[OF hcomplete])
               (use hV hUnOpen hUnDense hUnSubX in blast)+
          then show "intersects V (\<Inter>n. U n)"
            unfolding intersects_def by blast
        qed
      qed
    qed
  qed
qed

text \<open>Helper for Baire: complete metric spaces are Baire.
  The proof constructs nested balls using density and metric open sets,
  then uses completeness to find a limit point in the intersection.
  This is a placeholder for the detailed nested-ball construction.\<close>

(** Helper: distance set of a metric subset is bdd_above when diameter is finite. **)
lemma top1_metric_dist_set_bdd_above:
  assumes hd: "top1_metric_on X d"
  assumes hAX: "A \<subseteq> X"
  assumes hxA: "x \<in> A"
  assumes hbound: "\<exists>M. \<forall>a\<in>A. d x a \<le> M"
  shows "bdd_above {d a b | a b. a \<in> A \<and> b \<in> A}"
proof -
  obtain M where hM: "\<forall>a\<in>A. d x a \<le> M" using hbound by blast
  have hxX: "x \<in> X" using hAX hxA by blast
  show ?thesis
    unfolding bdd_above_def
  proof (rule exI[where x="M + M"], intro ballI)
    fix s assume "s \<in> {d a b | a b. a \<in> A \<and> b \<in> A}"
    then obtain a b where haA: "a \<in> A" and hbA: "b \<in> A" and hs: "s = d a b" by blast
    have haX: "a \<in> X" using hAX haA by blast
    have hbX: "b \<in> X" using hAX hbA by blast
    have "d a b \<le> d a x + d x b"
      using hd haX hxX hbX unfolding top1_metric_on_def by blast
    have "d a x = d x a"
      using hd haX hxX unfolding top1_metric_on_def by blast
    have "d x a \<le> M" using hM haA by blast
    have "d x b \<le> M" using hM hbA by blast
    have "d a b \<le> d x a + d x b"
      using \<open>d a b \<le> d a x + d x b\<close> \<open>d a x = d x a\<close> by linarith
    then have "d a b \<le> M + M"
      using \<open>d x a \<le> M\<close> \<open>d x b \<le> M\<close> by linarith
    then show "s \<le> M + M" unfolding hs by simp
  qed
qed

(** Helper: diameter control implies pairwise distance control. **)
lemma top1_diameter_on_lt_imp_dist_lt:
  assumes hd: "top1_metric_on X d"
  assumes hAX: "A \<subseteq> X"
  assumes hxA: "x \<in> A"
  assumes hyA: "y \<in> A"
  assumes hdiam: "top1_diameter_on d A < e"
  assumes hbdd: "bdd_above {d a b | a b. a \<in> A \<and> b \<in> A}"
  shows "d x y < e"
proof -
  let ?S = "{d a b | a b. a \<in> A \<and> b \<in> A}"
  have "d x y \<in> ?S" using hxA hyA by blast
  then have "d x y \<le> Sup ?S"
    by (rule cSup_upper[OF _ hbdd])
  also have "Sup ?S = top1_diameter_on d A"
    unfolding top1_diameter_on_def by simp
  also have "... < e" using hdiam by simp
  finally show "d x y < e" .
qed

(** from \S48 Lemma 48.3 [top1.tex:7208] **)
lemma Lemma_48_3:
  assumes hd: "top1_complete_metric_on X d"
  assumes hCne: "\<forall>n. C n \<noteq> {}"
  assumes hCcl: "\<forall>n. closedin_on X (top1_metric_topology_on X d) (C n)"
  assumes hnest: "\<forall>n. C (Suc n) \<subseteq> C n"
  assumes hdiam: "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. top1_diameter_on d (C n) < e"
  assumes hbdd: "\<forall>n. bdd_above {d a b | a b. a \<in> C n \<and> b \<in> C n}"
  shows "(\<Inter>n. C n) \<noteq> {}"
proof -
  have hmetric: "top1_metric_on X d"
    using hd unfolding top1_complete_metric_on_def by blast
  have hTop: "is_topology_on X (top1_metric_topology_on X d)"
    by (rule top1_metric_topology_on_is_topology_on[OF hmetric])

  have hCsubX: "\<forall>n. C n \<subseteq> X"
    using hCcl unfolding closedin_on_def by blast

  obtain s0 where hs0: "\<forall>n. s0 n \<in> C n"
  proof -
    have hchoose: "\<forall>n. \<exists>x. x \<in> C n"
    proof (intro allI)
      fix n
      have "C n \<noteq> {}"
        using hCne by simp
      thus "\<exists>x. x \<in> C n"
        by blast
    qed
    obtain s0 where hs0: "\<forall>n. s0 n \<in> C n"
      using choice[OF hchoose] by blast
    show ?thesis
      by (rule that[OF hs0])
  qed

  define s where "s = s0"
  have hsC: "\<forall>n. s n \<in> C n"
    unfolding s_def using hs0 by blast

  have hnest_add: "\<forall>n k. C (n + k) \<subseteq> C n"
  proof (intro allI)
    fix n k
    show "C (n + k) \<subseteq> C n"
    proof (induction k)
      case 0
      show ?case
        by simp
    next
      case (Suc k)
      have "C (n + Suc k) = C (Suc (n + k))"
        by simp
      also have "... \<subseteq> C (n + k)"
        using hnest by simp
      also have "... \<subseteq> C n"
        using Suc.IH by simp
      finally show ?case .
    qed
  qed

  have hnest_le: "\<forall>m n. n \<le> m \<longrightarrow> C m \<subseteq> C n"
  proof (intro allI impI)
    fix m n :: nat
    assume hnm: "n \<le> m"
    have "\<exists>k. m = n + k"
      using hnm by (simp add: nat_le_iff_add)
    then obtain k where hmk: "m = n + k"
      by blast
    show "C m \<subseteq> C n"
      unfolding hmk by (rule hnest_add[rule_format, of n k])
  qed

  have hcauchy: "top1_cauchy_seq_on X d s"
    unfolding top1_cauchy_seq_on_def
  proof (intro allI impI)
    fix e :: real
    assume he: "0 < e"
    obtain N where hN: "\<forall>n\<ge>N. top1_diameter_on d (C n) < e"
      using hdiam he by blast
    show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. s m \<in> X \<and> s n \<in> X \<and> d (s m) (s n) < e"
    proof (rule exI[where x=N], intro allI impI)
      fix m assume hm: "m \<ge> N"
      fix n assume hn: "n \<ge> N"

      have hsmCN: "s m \<in> C N"
      proof -
        have hsmCm: "s m \<in> C m"
          using hsC by simp
        have hCm_sub: "C m \<subseteq> C N"
        proof -
          have hall: "\<forall>n. n \<le> m \<longrightarrow> C m \<subseteq> C n"
            by (rule allE[OF hnest_le, of m])
          have himp: "N \<le> m \<longrightarrow> C m \<subseteq> C N"
            by (rule allE[OF hall, of N])
          have hNle: "N \<le> m"
            using hm by simp
          show ?thesis
            using himp hNle by blast
        qed
        show ?thesis
          by (rule subsetD[OF hCm_sub hsmCm])
      qed
      have hsnCN: "s n \<in> C N"
      proof -
        have hsnCn: "s n \<in> C n"
          using hsC by simp
        have hCn_sub: "C n \<subseteq> C N"
        proof -
          have hall: "\<forall>m'. m' \<le> n \<longrightarrow> C n \<subseteq> C m'"
            by (rule allE[OF hnest_le, of n])
          have himp: "N \<le> n \<longrightarrow> C n \<subseteq> C N"
            by (rule allE[OF hall, of N])
          have hNle: "N \<le> n"
            using hn by simp
          show ?thesis
            using himp hNle by blast
        qed
        show ?thesis
          by (rule subsetD[OF hCn_sub hsnCn])
      qed

      have hsNX: "s m \<in> X" and htNX: "s n \<in> X"
        using hCsubX hsmCN hsnCN by blast+

      have hdiamN: "top1_diameter_on d (C N) < e"
        using hN by simp
      have hbdd_CN: "bdd_above {d a b | a b. a \<in> C N \<and> b \<in> C N}"
        using hbdd by simp
      have hdist: "d (s m) (s n) < e"
        by (rule top1_diameter_on_lt_imp_dist_lt[OF hmetric hCsubX[rule_format, of N] hsmCN hsnCN hdiamN hbdd_CN])

      show "s m \<in> X \<and> s n \<in> X \<and> d (s m) (s n) < e"
        using hsNX htNX hdist by simp
    qed
  qed

  obtain x where hxX: "x \<in> X"
    and hconv: "seq_converges_to_on s x X (top1_metric_topology_on X d)"
    using hd hcauchy unfolding top1_complete_metric_on_def by blast

  have hxAll: "\<forall>k. x \<in> C k"
  proof (intro allI)
    fix k
    have hCk_subX: "C k \<subseteq> X"
      using hCsubX by simp

    have hClChar:
      "x \<in> closure_on X (top1_metric_topology_on X d) (C k)
        \<longleftrightarrow> (\<forall>U. neighborhood_of x X (top1_metric_topology_on X d) U \<longrightarrow> intersects U (C k))"
      by (rule Theorem_17_5a[OF hTop hxX hCk_subX])

    have hxcl: "x \<in> closure_on X (top1_metric_topology_on X d) (C k)"
    proof (rule iffD2[OF hClChar], intro allI impI)
      fix U
      assume hU: "neighborhood_of x X (top1_metric_topology_on X d) U"
      obtain N where hNU: "\<forall>n\<ge>N. s n \<in> U"
        using hconv hU unfolding seq_converges_to_on_def by blast
      define m where "m = max N k"
      have hmN: "N \<le> m" and hmk: "k \<le> m"
        unfolding m_def by simp_all
      have hsmU: "s m \<in> U"
        by (rule hNU[rule_format, OF hmN])
      have hsmCm: "s m \<in> C m"
        using hsC by simp
      have hCm_sub: "C m \<subseteq> C k"
      proof -
        have hall: "\<forall>k'. k' \<le> m \<longrightarrow> C m \<subseteq> C k'"
          by (rule allE[OF hnest_le, of m])
        have himp: "k \<le> m \<longrightarrow> C m \<subseteq> C k"
          by (rule allE[OF hall, of k])
        show ?thesis
          using himp hmk by blast
      qed
      have hsmCk: "s m \<in> C k"
        by (rule subsetD[OF hCm_sub hsmCm])
      show "intersects U (C k)"
        unfolding intersects_def
      proof
        assume hempty: "U \<inter> C k = {}"
        have hsmUC: "s m \<in> U \<inter> C k"
          using hsmU hsmCk by blast
        have "s m \<in> {}"
          using hsmUC unfolding hempty by simp
        thus False
          by simp
      qed
    qed

    have hcl_sub: "closure_on X (top1_metric_topology_on X d) (C k) \<subseteq> C k"
      unfolding closure_on_def
    proof (rule Inter_lower)
      show "C k \<in> {C'. closedin_on X (top1_metric_topology_on X d) C' \<and> C k \<subseteq> C'}"
        using hCcl by blast
    qed
    show "x \<in> C k"
      by (rule subsetD[OF hcl_sub hxcl])
  qed

  have hxInter: "x \<in> (\<Inter>n. C n)"
    using hxAll by simp
  show "(\<Inter>n. C n) \<noteq> {}"
    using hxInter by blast
qed

(** from \S48 Lemma 48.4 [top1.tex:7216] **)
lemma Lemma_48_4:
  assumes hTop: "is_topology_on X TX"
  assumes hB: "top1_baire_on X TX"
  assumes hUX: "U \<subseteq> X"
  assumes hU: "U \<in> TX"
  shows "top1_baire_on U (subspace_topology X TX U)"
proof -
  let ?TU = "subspace_topology X TX U"
  have hTopU: "is_topology_on U ?TU"
    by (rule subspace_topology_is_topology_on[OF hTop hUX])

  have hClU_closed: "closedin_on X TX (closure_on X TX U)"
    by (rule closure_on_closed[OF hTop hUX])
  have hXminusClU_open: "X - closure_on X TX U \<in> TX"
    using hClU_closed unfolding closedin_on_def by blast

  show ?thesis
    unfolding top1_baire_on_def
  proof (intro allI impI)
    fix V :: "nat \<Rightarrow> 'a set"
    assume hV: "\<forall>n. V n \<in> ?TU \<and> top1_densein_on U ?TU (V n)"

    have hVsubU: "\<forall>n. V n \<subseteq> U"
    proof (intro allI)
      fix n
      have hVnTU: "V n \<in> ?TU"
        using hV by blast
      then obtain A where hA: "V n = U \<inter> A"
        unfolding subspace_topology_def by blast
      show "V n \<subseteq> U"
        unfolding hA by blast
    qed

    have hVopenX: "\<forall>n. V n \<in> TX"
    proof (intro allI)
      fix n
      have hVnTU: "V n \<in> ?TU"
        using hV by blast
      then obtain A where hA: "V n = U \<inter> A" and hAT: "A \<in> TX"
        unfolding subspace_topology_def by blast
      have "U \<inter> A \<in> TX"
        by (rule topology_inter2[OF hTop hU hAT])
      thus "V n \<in> TX"
        unfolding hA .
    qed

    define D where "D n = V n \<union> (X - closure_on X TX U)" for n

    have hDopen: "\<forall>n. D n \<in> TX"
    proof (intro allI)
      fix n
      show "D n \<in> TX"
        unfolding D_def
        by (rule topology_union2[OF hTop hVopenX[rule_format, of n] hXminusClU_open])
    qed

    have hUsub_clV: "\<forall>n. closure_on X TX U \<subseteq> closure_on X TX (V n)"
    proof (intro allI)
      fix n
      have hVn_denseU: "closure_on U ?TU (V n) = U"
        using hV unfolding top1_densein_on_def by blast

      have hcl_subspace:
        "closure_on U ?TU (V n) = closure_on X TX (V n) \<inter> U"
        by (rule Theorem_17_4[OF hTop hVsubU[rule_format, of n] hUX])

      have hUsub_clVn: "U \<subseteq> closure_on X TX (V n)"
      proof -
        have "U = closure_on X TX (V n) \<inter> U"
          using hVn_denseU hcl_subspace by simp
        thus ?thesis
          by blast
      qed

      have hclV_closed: "closedin_on X TX (closure_on X TX (V n))"
      proof -
        have hVnX: "V n \<subseteq> X"
          using hVsubU hUX by blast
        show ?thesis
          by (rule closure_on_closed[OF hTop hVnX])
      qed

      show "closure_on X TX U \<subseteq> closure_on X TX (V n)"
        by (rule closure_on_subset_of_closed[OF hclV_closed], rule hUsub_clVn)
    qed

    have hDdense: "\<forall>n. top1_densein_on X TX (D n)"
    proof (intro allI)
      fix n

      have hVn_sub_Dn: "V n \<subseteq> D n"
        unfolding D_def by blast

      have hclVn_sub_clDn: "closure_on X TX (V n) \<subseteq> closure_on X TX (D n)"
        by (rule closure_on_mono[OF hVn_sub_Dn])

      have hClU_sub_clDn: "closure_on X TX U \<subseteq> closure_on X TX (D n)"
        using hUsub_clV hclVn_sub_clDn by blast

      have hXminus_sub_Dn: "X - closure_on X TX U \<subseteq> D n"
        unfolding D_def by blast

      have hXminus_sub_clDn: "X - closure_on X TX U \<subseteq> closure_on X TX (D n)"
        by (rule subset_trans[OF hXminus_sub_Dn subset_closure_on])

      have hDn_sub_X: "D n \<subseteq> X"
        unfolding D_def using hVsubU hUX by blast

      have hclDn_sub_X: "closure_on X TX (D n) \<subseteq> X"
        by (rule closure_on_subset_carrier[OF hTop hDn_sub_X])

      have hX_sub_clDn: "X \<subseteq> closure_on X TX (D n)"
      proof (rule subsetI)
        fix x assume hx: "x \<in> X"
        have "x \<in> closure_on X TX U \<or> x \<in> X - closure_on X TX U"
          using hx by blast
        thus "x \<in> closure_on X TX (D n)"
        proof
          assume hxclU: "x \<in> closure_on X TX U"
          show ?thesis
            using hClU_sub_clDn hxclU by blast
        next
          assume hxnot: "x \<in> X - closure_on X TX U"
          show ?thesis
            using hXminus_sub_clDn hxnot by blast
        qed
      qed

      show "top1_densein_on X TX (D n)"
        unfolding top1_densein_on_def
        by (rule equalityI[OF hclDn_sub_X hX_sub_clDn])
    qed

    have hDenseX: "top1_densein_on X TX (\<Inter>n. D n)"
    proof -
      have hCond: "\<forall>n. D n \<in> TX \<and> top1_densein_on X TX (D n)"
        using hDopen hDdense by blast
      have hB': "\<forall>U0::nat \<Rightarrow> 'a set. (\<forall>n. U0 n \<in> TX \<and> top1_densein_on X TX (U0 n))
          \<longrightarrow> top1_densein_on X TX (\<Inter>n. U0 n)"
        using hB unfolding top1_baire_on_def by blast
      show ?thesis
        using hB'[rule_format, of D] hCond by blast
    qed

    have hIntDU: "(\<Inter>n. D n) \<inter> U = (\<Inter>n. V n)"
    proof -
      have hUsubClU: "U \<subseteq> closure_on X TX U"
        by (rule subset_closure_on)
      have hXminusClU_disj_U: "(X - closure_on X TX U) \<inter> U = {}"
        using hUsubClU by blast
      have hDnIntU: "\<forall>n. D n \<inter> U = V n"
      proof (intro allI)
        fix n
        show "D n \<inter> U = V n"
          unfolding D_def using hVsubU hXminusClU_disj_U by blast
      qed
      show ?thesis
        using hDnIntU by blast
    qed

    have hIntD_subX: "(\<Inter>n. D n) \<subseteq> X"
    proof -
      have "\<forall>n. D n \<subseteq> X"
        unfolding D_def using hVsubU hUX by blast
      thus ?thesis
        by blast
    qed

    have hDenseU: "top1_densein_on U ?TU ((\<Inter>n. D n) \<inter> U)"
      by (rule top1_densein_on_open_subspace[OF hTop hDenseX hIntD_subX hUX hU])

    show "top1_densein_on U ?TU (\<Inter>n. V n)"
      using hDenseU hIntDU by simp
  qed
qed

(** from \S48 Theorem 48.5 [top1.tex:7222] **)
text \<open>Helper for Theorem 48.5: A_N(ε) = {x ∈ X | ∀n,m ≥ N. d(f_n(x), f_m(x)) ≤ ε}.\<close>
definition top1_AN_48 :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "top1_AN_48 fseq d N e X = {x \<in> X. \<forall>n\<ge>N. \<forall>m\<ge>N. d (fseq n x) (fseq m x) \<le> e}"

theorem Theorem_48_5:
  assumes hTop: "is_topology_on X TX"
  assumes hTsub: "\<forall>U\<in>TX. U \<subseteq> X"
  assumes hB: "top1_baire_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hfn: "\<forall>n. top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) (f n)"
  assumes hptw: "\<forall>x\<in>X. seq_converges_to_on (\<lambda>n. f n x) (g x) Y (top1_metric_topology_on Y d)"
  shows "top1_densein_on X TX {x \<in> X. top1_continuous_at_on X TX Y (top1_metric_topology_on Y d) g x}"
proof -
  let ?TY = "top1_metric_topology_on Y d"

  text \<open>Define A_N(ε) and U(ε).\<close>
  define AN where "AN N e = top1_AN_48 f d N e X" for N :: nat and e :: real
  define U where "U e = (\<Union>N. interior_on X TX (AN N e))" for e :: real

  text \<open>U(ε) is open and dense in X for each ε > 0.\<close>
  have hU_open_dense: "\<forall>e > 0. U e \<in> TX \<and> top1_densein_on X TX (U e)"
  proof (intro allI impI conjI)
    fix e :: real assume hepos: "0 < e"
    text \<open>AN N e is closed (intersection of preimages of {≤e} under continuous maps).\<close>
    have hAN_closed: "\<forall>N. closedin_on X TX (AN N e)"
    proof (intro allI)
      fix N
      text \<open>AN N e = ∩_{n,m ≥ N} {x ∈ X | d(f_n(x), f_m(x)) ≤ e}.
            Show each {x ∈ X | d(f_n(x), f_m(x)) ≤ e} is closed.\<close>
      define Snm where "Snm n m = {x \<in> X. d (f n x) (f m x) \<le> e}" for n m :: nat
      have hSnm_closed: "\<forall>n m. closedin_on X TX (Snm n m)"
      proof (intro allI)
        fix n m
        let ?TY = "top1_metric_topology_on Y d"
        have hfn_cont: "top1_continuous_map_on X TX Y ?TY (f n)"
          using hfn
          
          by presburger
        have hfm_cont: "top1_continuous_map_on X TX Y ?TY (f m)"
          using hfn
          
          by auto
        have hfn_map: "\<forall>x\<in>X. f n x \<in> Y"
          using hfn_cont unfolding top1_continuous_map_on_def
          
          by satx
        have hfm_map: "\<forall>x\<in>X. f m x \<in> Y"
          using hfm_cont unfolding top1_continuous_map_on_def
          
          by presburger
        have hfn_pre: "\<forall>V\<in>?TY. {x\<in>X. f n x \<in> V} \<in> TX"
          using hfn_cont unfolding top1_continuous_map_on_def
          
          by presburger
        have hfm_pre: "\<forall>V\<in>?TY. {x\<in>X. f m x \<in> V} \<in> TX"
          using hfm_cont unfolding top1_continuous_map_on_def
          
          by presburger
        text \<open>Show complement is open: for x₀ with d(f_n(x₀), f_m(x₀)) > e, find open neighborhood.\<close>
        have hcompl_open: "X - Snm n m \<in> TX"
        proof (rule top1_open_of_local_subsets[OF hTop])
          show "X - Snm n m \<subseteq> X"
            
            by simp
          show "\<forall>x\<in>X - Snm n m. \<exists>U\<in>TX. x \<in> U \<and> U \<subseteq> X - Snm n m"
          proof (intro ballI)
            fix x0 assume hx0: "x0 \<in> X - Snm n m"
            have hx0X: "x0 \<in> X" using hx0
              
              by blast
            have hdgt: "d (f n x0) (f m x0) > e" using hx0 unfolding Snm_def
              
              by force
            define \<delta> where "\<delta> = (d (f n x0) (f m x0) - e) / 3"
            have h\<delta>pos: "0 < \<delta>" unfolding \<delta>_def using hdgt
              
              by auto
            text \<open>Preimage of ball around f_n(x₀) is open and contains x₀.\<close>
            have hball_n_open: "top1_ball_on Y d (f n x0) \<delta> \<in> ?TY"
              using hd hfn_map hx0X h\<delta>pos top1_ball_open_in_metric_topology
              
              by fast
            define U1 where "U1 = {x\<in>X. f n x \<in> top1_ball_on Y d (f n x0) \<delta>}"
            have hU1_open: "U1 \<in> TX" unfolding U1_def
              using hfn_pre hball_n_open
              
              by blast
            have hx0U1: "x0 \<in> U1" unfolding U1_def top1_ball_on_def
              using hx0X hfn_map hd h\<delta>pos unfolding top1_metric_on_def
              
              by fastforce
            text \<open>Similarly for f_m.\<close>
            have hball_m_open: "top1_ball_on Y d (f m x0) \<delta> \<in> ?TY"
              using hd hfm_map hx0X h\<delta>pos top1_ball_open_in_metric_topology
              
              by fast
            define U2 where "U2 = {x\<in>X. f m x \<in> top1_ball_on Y d (f m x0) \<delta>}"
            have hU2_open: "U2 \<in> TX" unfolding U2_def
              using hfm_pre hball_m_open
              
              by blast
            have hx0U2: "x0 \<in> U2" unfolding U2_def top1_ball_on_def
              using hx0X hfm_map hd h\<delta>pos unfolding top1_metric_on_def
              
              by fastforce
            text \<open>U1 ∩ U2 is open and ⊆ complement.\<close>
            have hU12_open: "U1 \<inter> U2 \<in> TX"
              using topology_inter2[OF hTop hU1_open hU2_open]
              
              by presburger
            have hU12_sub: "U1 \<inter> U2 \<subseteq> X - Snm n m"
            proof (rule subsetI)
              fix x assume hx: "x \<in> U1 \<inter> U2"
              have hxX: "x \<in> X" using hx unfolding U1_def
                
                by blast
              have hdn: "d (f n x0) (f n x) < \<delta>"
                using hx unfolding U1_def top1_ball_on_def
                
                by blast
              have hdm: "d (f m x0) (f m x) < \<delta>"
                using hx unfolding U2_def top1_ball_on_def
                
                by blast
              text \<open>Reverse triangle: d(f_n(x), f_m(x)) ≥ d(f_n(x₀), f_m(x₀)) - d(f_n(x),f_n(x₀)) - d(f_m(x),f_m(x₀)).\<close>
              have htri1: "d (f n x0) (f m x0) \<le> d (f n x0) (f n x) + d (f n x) (f m x0)"
                using hd hfn_map hfm_map hx0X hxX unfolding top1_metric_on_def
                
                by metis
              have htri2: "d (f n x) (f m x0) \<le> d (f n x) (f m x) + d (f m x) (f m x0)"
                using hd hfn_map hfm_map hx0X hxX unfolding top1_metric_on_def
                
                by meson
              have hdsym_m: "d (f m x) (f m x0) = d (f m x0) (f m x)"
                using hd hfm_map hx0X hxX unfolding top1_metric_on_def
                
                by metis
              have "d (f n x) (f m x) \<ge> d (f n x0) (f m x0) - d (f n x0) (f n x) - d (f m x0) (f m x)"
                using htri1 htri2 hdsym_m
                
                by argo
              then have "d (f n x) (f m x) > e"
                using hdgt hdn hdm unfolding \<delta>_def
                
                by fastforce
              then show "x \<in> X - Snm n m" unfolding Snm_def using hxX
                
                by simp
            qed
            show "\<exists>U\<in>TX. x0 \<in> U \<and> U \<subseteq> X - Snm n m"
              using hU12_open hx0U1 hx0U2 hU12_sub
              
              by (metis hx0U1 hU12_sub hU12_open hx0U2 IntI)
          qed
        qed
        show "closedin_on X TX (Snm n m)"
          unfolding closedin_on_def using hcompl_open unfolding Snm_def
          
          by force
      qed
      have hAN_eq: "AN N e = (\<Inter>n\<in>{N..}. \<Inter>m\<in>{N..}. Snm n m)"
        unfolding AN_def top1_AN_48_def Snm_def
        
        by blast
      have "\<forall>n\<in>{N..}. \<forall>m\<in>{N..}. closedin_on X TX (Snm n m)"
        using hSnm_closed
        
        by blast
      text \<open>Intersection of closed sets is closed.\<close>
      have hANsub: "AN N e \<subseteq> X" unfolding AN_def top1_AN_48_def
        
        by blast
      have hXmAN: "X - AN N e \<in> TX"
      proof -
        have "X - AN N e = (\<Union>n\<in>{N..}. \<Union>m\<in>{N..}. X - Snm n m)"
          unfolding hAN_eq
          
          by blast
        also have "\<dots> \<in> TX"
        proof -
          have "\<forall>n m. X - Snm n m \<in> TX" using hSnm_closed unfolding closedin_on_def
            
            by blast
          then have hsub_TX: "(\<lambda>(n,m). X - Snm n m) ` ({N..} \<times> {N..}) \<subseteq> TX"
            by fast
          have "(\<Union>n\<in>{N..}. \<Union>m\<in>{N..}. X - Snm n m) = \<Union>((\<lambda>(n,m). X - Snm n m) ` ({N..} \<times> {N..}))"
            
            by blast
          then show ?thesis using hTop hsub_TX unfolding is_topology_on_def
            
            by presburger
        qed
        finally show ?thesis .
      qed
      show "closedin_on X TX (AN N e)"
        unfolding closedin_on_def using hANsub hXmAN
        
        by argo
    qed
    text \<open>∪_N AN N e = X.\<close>
    have hAN_covers: "X = (\<Union>N. AN N e)"
    proof (rule equalityI)
      show "(\<Union>N. AN N e) \<subseteq> X" unfolding AN_def top1_AN_48_def
        
        by fast
      show "X \<subseteq> (\<Union>N. AN N e)"
      proof (rule subsetI)
        fix x assume hxX: "x \<in> X"
        have hconv: "seq_converges_to_on (\<lambda>n. f n x) (g x) Y ?TY"
          using hptw hxX
          
          by blast
        have "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. d (f n x) (f m x) \<le> e"
        proof -
          have hgxY: "g x \<in> Y"
            using hconv unfolding seq_converges_to_on_def
            
            by satx
          have he2pos: "0 < e / 2" using hepos
            
            by simp
          have hball_open: "top1_ball_on Y d (g x) (e / 2) \<in> ?TY"
            using hd hgxY he2pos top1_ball_open_in_metric_topology
            
            by metis
          have hgx_in_ball: "g x \<in> top1_ball_on Y d (g x) (e / 2)"
            unfolding top1_ball_on_def using hgxY hd he2pos unfolding top1_metric_on_def
            
            by fastforce
          have hnbhd: "neighborhood_of (g x) Y ?TY (top1_ball_on Y d (g x) (e / 2))"
            unfolding neighborhood_of_def using hball_open hgx_in_ball
            
            by presburger
          obtain N where hN: "\<forall>n\<ge>N. f n x \<in> top1_ball_on Y d (g x) (e / 2)"
            using hconv hnbhd unfolding seq_converges_to_on_def
            
            by blast
          show ?thesis
          proof (rule exI[where x=N], intro allI impI)
            fix n m assume hn: "N \<le> n" and hm: "N \<le> m"
            have hfnball: "d (g x) (f n x) < e / 2"
              using hN hn unfolding top1_ball_on_def
              
              by blast
            have hfmball: "d (g x) (f m x) < e / 2"
              using hN hm unfolding top1_ball_on_def
              
              by blast
            have hfnY: "f n x \<in> Y"
              using hfn hxX unfolding top1_continuous_map_on_def
              
              by blast
            have hfmY: "f m x \<in> Y"
              using hfn hxX unfolding top1_continuous_map_on_def
              
              by blast
            have htri: "d (f n x) (f m x) \<le> d (f n x) (g x) + d (g x) (f m x)"
              using hd hfnY hgxY hfmY unfolding top1_metric_on_def
              
              by blast
            have hdsym: "d (f n x) (g x) = d (g x) (f n x)"
              using hd hfnY hgxY unfolding top1_metric_on_def
              
              by blast
            show "d (f n x) (f m x) \<le> e"
              using htri hdsym hfnball hfmball
              
              by force
          qed
        qed
        then show "x \<in> (\<Union>N. AN N e)"
          unfolding AN_def top1_AN_48_def using hxX
          
          by blast
      qed
    qed
    text \<open>U(e) = ∪_N Int(AN N e) is open.\<close>
    have hInt_open: "\<forall>N. interior_on X TX (AN N e) \<in> TX"
    proof (intro allI)
      fix N
      have "{U \<in> TX. U \<subseteq> AN N e} \<subseteq> TX"
        
        by fast
      then show "interior_on X TX (AN N e) \<in> TX"
        unfolding interior_on_def using hTop unfolding is_topology_on_def
        
        by blast
    qed
    show "U e \<in> TX"
    proof -
      have "range (\<lambda>N. interior_on X TX (AN N e)) \<subseteq> TX"
        using hInt_open
        
        by blast
      then show ?thesis unfolding U_def using hTop unfolding is_topology_on_def
        
        by blast
    qed
    text \<open>U(e) is dense: uses Baire.\<close>
    show "top1_densein_on X TX (U e)"
    proof -
      text \<open>Show U e meets every nonempty open V.\<close>
      have hU_meets: "\<forall>V. V \<in> TX \<and> V \<noteq> {} \<longrightarrow> V \<inter> U e \<noteq> {}"
      proof (intro allI impI)
        fix V assume hVprop: "V \<in> TX \<and> V \<noteq> {}"
        have hV: "V \<in> TX" and hVne: "V \<noteq> {}" using hVprop
          
          by presburger+
        have hVX: "V \<subseteq> X"
          using hV hTsub
          
          by simp
        let ?TV = "subspace_topology X TX V"
        have hV_Baire: "top1_baire_on V ?TV"
          using Lemma_48_4[OF hTop hB hVX hV]
          
          by presburger
        text \<open>V ∩ AN covers V.\<close>
        have hVAN_covers: "V = (\<Union>N. V \<inter> AN N e)"
          using hAN_covers hVX
          
          by blast
        text \<open>V ∩ AN N e is closed in V.\<close>
        have hVAN_closed: "\<forall>N. closedin_on V ?TV (V \<inter> AN N e)"
        proof (intro allI)
          fix N
          have "closedin_on V ?TV (V \<inter> AN N e) \<longleftrightarrow> (\<exists>C. closedin_on X TX C \<and> V \<inter> AN N e = C \<inter> V)"
            using Theorem_17_2[OF hTop hVX]
            
            by presburger
          moreover have "closedin_on X TX (AN N e) \<and> V \<inter> AN N e = AN N e \<inter> V"
            using hAN_closed
            
            by blast
          ultimately show "closedin_on V ?TV (V \<inter> AN N e)"
            
            by blast
        qed
        text \<open>Baire dual: some V ∩ AN M has nonempty interior in V.\<close>
        have "\<exists>M. interior_on V ?TV (V \<inter> AN M e) \<noteq> {}"
        proof (rule ccontr)
          assume "\<not> (\<exists>M. interior_on V ?TV (V \<inter> AN M e) \<noteq> {})"
          then have hall_empty: "\<forall>M. interior_on V ?TV (V \<inter> AN M e) = {}"
            
            by presburger
          text \<open>Then V - (V ∩ AN M e) = open dense in V for each M.\<close>
          define DN where "DN M = V - V \<inter> AN M e" for M :: nat
          have hDN_open: "\<forall>M. DN M \<in> ?TV"
            unfolding DN_def using hVAN_closed unfolding closedin_on_def
            
            by presburger
          have hDN_dense: "\<forall>M. top1_densein_on V ?TV (DN M)"
          proof (intro allI)
            fix M
            have hint_empty: "interior_on V ?TV (V \<inter> AN M e) = {}"
              using hall_empty
              
              by presburger
            show "top1_densein_on V ?TV (DN M)"
              unfolding top1_densein_on_def
            proof (rule equalityI)
              have hTopV: "is_topology_on V ?TV"
                using subspace_topology_is_topology_on[OF hTop hVX]
                
                by blast
              show "closure_on V ?TV (DN M) \<subseteq> V"
                using closure_on_subset_carrier[OF hTopV] unfolding DN_def
                
                by simp
              show "V \<subseteq> closure_on V ?TV (DN M)"
              proof (rule subsetI)
                fix x assume hxV: "x \<in> V"
                show "x \<in> closure_on V ?TV (DN M)"
                  unfolding closure_on_def
                proof (rule InterI)
                  fix C assume hC: "C \<in> {C. closedin_on V ?TV C \<and> DN M \<subseteq> C}"
                  then have hCcl: "closedin_on V ?TV C" and hDNsub: "DN M \<subseteq> C"
                    
                    by blast+
                  have hCsubV: "C \<subseteq> V" using hCcl unfolding closedin_on_def
                    
                    by presburger
                  text \<open>V - C is open in V and V - C ⊆ V ∩ AN M e (from DN M ⊆ C).\<close>
                  have hVmC_open: "V - C \<in> ?TV" using hCcl unfolding closedin_on_def
                    
                    by satx
                  have hVmC_sub: "V - C \<subseteq> V \<inter> AN M e"
                    unfolding DN_def using hDNsub hCsubV
                    
                    using DN_def by blast
                  text \<open>If x ∉ C, then x ∈ V - C. V - C open and ⊆ V ∩ AN M →
                         V - C ⊆ interior(V ∩ AN M) = {}. So V - C = {} → x ∈ C.\<close>
                  show "x \<in> C"
                  proof (rule ccontr)
                    assume "x \<notin> C"
                    then have "x \<in> V - C" using hxV
                      
                      by blast
                    then have "V - C \<noteq> {}"
                      
                      by blast
                    have "V - C \<subseteq> interior_on V ?TV (V \<inter> AN M e)"
                      unfolding interior_on_def using hVmC_open hVmC_sub
                      
                      by blast
                    then have "interior_on V ?TV (V \<inter> AN M e) \<noteq> {}" using \<open>V - C \<noteq> {}\<close>
                      
                      by blast
                    then show False using hint_empty
                      
                      by order
                  qed
                qed
              qed
            qed
          qed
          have hDN_inter: "(\<Inter>M. DN M) = {}"
            unfolding DN_def using hVAN_covers
            
            by blast
          text \<open>But Baire on V: ∩DN dense in V, hence nonempty (V ≠ {}).\<close>
          have hDN_all: "\<forall>M. DN M \<in> ?TV \<and> top1_densein_on V ?TV (DN M)"
            using hDN_open hDN_dense
            
            by simp
          have "top1_densein_on V ?TV (\<Inter>M. DN M)"
            using hV_Baire hDN_all unfolding top1_baire_on_def
            
            by presburger
          then have "(\<Inter>M. DN M) \<noteq> {}"
          proof -
            assume hdense: "top1_densein_on V ?TV (\<Inter>M. DN M)"
            have "(\<Inter>M. DN M) \<subseteq> V" using top1_densein_on_subset_carrier[OF hdense]
              
              by order
            have "closure_on V ?TV (\<Inter>M. DN M) = V" using hdense unfolding top1_densein_on_def
              
              by order
            then have "V \<subseteq> closure_on V ?TV (\<Inter>M. DN M)"
              
              by blast
            moreover have "(\<Inter>M. DN M) \<subseteq> closure_on V ?TV (\<Inter>M. DN M)"
              using subset_closure_on
              
              by metis
            ultimately show "(\<Inter>M. DN M) \<noteq> {}" using hVne
            proof -
              assume h1: "V \<subseteq> closure_on V ?TV (\<Inter>M. DN M)"
              assume h2: "(\<Inter>M. DN M) \<subseteq> closure_on V ?TV (\<Inter>M. DN M)"
              assume hne: "V \<noteq> {}"
              show "(\<Inter>M. DN M) \<noteq> {}"
              proof (rule ccontr)
                assume "\<not> (\<Inter>M. DN M) \<noteq> {}"
                then have hempty: "(\<Inter>M. DN M) = {}"
                  
                  by argo
                have "closure_on V ?TV {} = {}"
                  using closure_on_subset_of_closed
                  
                  by (simp add: hTop hVX subspace_topology_is_topology_on top1_closure_on_empty)
                then have "V \<subseteq> {}" using h1 hempty
                  
                  by argo
                then show False using hne
                  
                  by force
              qed
            qed
          qed
          then show False using hDN_inter
            
            by order
        qed
        then obtain M where hM: "interior_on V ?TV (V \<inter> AN M e) \<noteq> {}"
          
          by presburger
        text \<open>Get nonempty open W ⊆ V ∩ AN M e in V.\<close>
        obtain w where hwint: "w \<in> interior_on V ?TV (V \<inter> AN M e)"
          using hM
          
          by blast
        have hw_in_V_AN: "w \<in> V \<inter> AN M e"
          using hwint unfolding interior_on_def
          
          by fast
        obtain W where hW_TV: "W \<in> ?TV" and hWsub: "W \<subseteq> V \<inter> AN M e" and hwW: "w \<in> W"
          using hwint unfolding interior_on_def
          
          by blast
        text \<open>W open in V (subspace) → W open in X (V open).\<close>
        have hWne: "W \<noteq> {}" using hwW
          
          by blast
        have hW_TX: "W \<in> TX"
        proof -
          obtain U' where hU': "U' \<in> TX" and hWeq: "W = V \<inter> U'"
            using hW_TV unfolding subspace_topology_def
            
            by blast
          show ?thesis unfolding hWeq
            using topology_inter2[OF hTop hV hU']
            
            by presburger
        qed
        text \<open>W ⊆ AN M e and W ∈ TX → W ⊆ Int(AN M e) ⊆ U(e).\<close>
        have "W \<subseteq> AN M e" using hWsub
          
          by blast
        then have "W \<subseteq> interior_on X TX (AN M e)" using hW_TX
          unfolding interior_on_def
          
          by blast
        then have "W \<subseteq> U e" unfolding U_def
          
          by blast
        moreover have "W \<subseteq> V" using hWsub
          
          by simp
        ultimately show "V \<inter> U e \<noteq> {}" using hWne
          
          by auto
      qed
      show ?thesis
        unfolding top1_densein_on_def
      proof (rule equalityI)
        have hUsubX: "U e \<subseteq> X"
          unfolding U_def interior_on_def
          using hTsub
          
          by blast
        show "closure_on X TX (U e) \<subseteq> X"
          using closure_on_subset_carrier[OF hTop hUsubX]
          
          by order
        show "X \<subseteq> closure_on X TX (U e)"
          unfolding closure_on_def
        proof (rule subsetI)
          fix x assume hxX: "x \<in> X"
          show "x \<in> \<Inter>{C. closedin_on X TX C \<and> U e \<subseteq> C}"
          proof (rule InterI)
            fix C assume hC: "C \<in> {C. closedin_on X TX C \<and> U e \<subseteq> C}"
            then have hCcl: "closedin_on X TX C" and hUC: "U e \<subseteq> C"
              
              by force+
            show "x \<in> C"
            proof (rule ccontr)
              assume "x \<notin> C"
              have hCX: "C \<subseteq> X" using hCcl unfolding closedin_on_def
                
                by presburger
              have hXmC: "X - C \<in> TX" using hCcl unfolding closedin_on_def
                
                by argo
              have hXmCne: "X - C \<noteq> {}" using hxX \<open>x \<notin> C\<close>
                
                by blast
              have "(X - C) \<inter> U e \<noteq> {}"
                using hU_meets hXmC hXmCne
                
                by presburger
              then show False using hUC
                
                by auto
            qed
          qed
        qed
      qed
    qed
  qed

  text \<open>f is continuous at each point of C = ∩_k U(1/(k+1)).\<close>
  define C where "C = (\<Inter>k::nat. U (1 / real (Suc k)))"
  have hC_dense: "top1_densein_on X TX C"
  proof -
    define Uk where "Uk (k::nat) = U (1 / real (Suc k))" for k
    have hUk: "\<forall>k. Uk k \<in> TX \<and> top1_densein_on X TX (Uk k)"
    proof (intro allI conjI)
      fix k
      have hpos: "0 < 1 / real (Suc k)"
        
        by auto
      show "Uk k \<in> TX" unfolding Uk_def using hU_open_dense hpos
        
        by blast
      show "top1_densein_on X TX (Uk k)" unfolding Uk_def using hU_open_dense hpos
        
        by blast
    qed
    have "C = (\<Inter>k. Uk k)" unfolding C_def Uk_def
      
      by argo
    then show ?thesis using hB hUk unfolding top1_baire_on_def
      
      by blast
  qed

  have hC_sub_cont: "C \<subseteq> {x \<in> X. top1_continuous_at_on X TX Y ?TY g x}"
  proof (rule subsetI)
    fix x0 assume hx0C: "x0 \<in> C"
    have hx0X: "x0 \<in> X"
      using hx0C unfolding C_def U_def AN_def top1_AN_48_def interior_on_def
      
      by blast
    show "x0 \<in> {x \<in> X. top1_continuous_at_on X TX Y ?TY g x}"
    proof (intro CollectI conjI)
      show "x0 \<in> X" by (rule hx0X)
      show "top1_continuous_at_on X TX Y ?TY g x0"
        unfolding top1_continuous_at_on_def
      proof (intro conjI)
        show "x0 \<in> X" by (rule hx0X)
        show "\<forall>V. neighborhood_of (g x0) Y ?TY V \<longrightarrow> (\<exists>U. neighborhood_of x0 X TX U \<and> g ` U \<subseteq> V)"
        proof (intro allI impI)
          fix V assume hVnbhd: "neighborhood_of (g x0) Y ?TY V"
          have hgx0Y: "g x0 \<in> Y"
            using hptw hx0X unfolding seq_converges_to_on_def
            
            by blast
          text \<open>Get ε-ball inside V.\<close>
          obtain U0 where hU0: "U0 \<in> ?TY" and hgx0U0: "g x0 \<in> U0" and hU0V: "U0 \<subseteq> V"
            using hVnbhd unfolding neighborhood_of_def
            
            by blast
          obtain \<epsilon> where heps: "0 < \<epsilon>" and hball_sub: "top1_ball_on Y d (g x0) \<epsilon> \<subseteq> U0"
            using top1_metric_open_contains_ball[OF hd hU0 hgx0U0]
            
            by blast
          have hball_sub_V: "top1_ball_on Y d (g x0) \<epsilon> \<subseteq> V"
            using hball_sub hU0V
            
            by order
          text \<open>Pick k with 1/(Suc k) < ε/3.\<close>
          have heps3: "0 < \<epsilon> / 3" using heps
            
            by simp
          obtain k where hk: "1 / real (Suc k) < \<epsilon> / 3"
          proof -
            obtain n :: nat where "3 / \<epsilon> < real n"
              using reals_Archimedean2 heps3
              
              by blast
            then have "1 / real (Suc n) < \<epsilon> / 3"
              using heps by (simp add: field_simps)
            then show ?thesis using that
              
              by blast
          qed
          text \<open>x0 ∈ C → x0 ∈ U(1/(Suc k)) → x0 ∈ Int(AN N0 (1/(Suc k))) for some N0.\<close>
          have "x0 \<in> U (1 / real (Suc k))" using hx0C unfolding C_def
            
            by fast
          then obtain N0 where hx0_int: "x0 \<in> interior_on X TX (AN N0 (1 / real (Suc k)))"
            unfolding U_def
            
            by blast
          have hx0_AN: "x0 \<in> AN N0 (1 / real (Suc k))"
            using hx0_int unfolding interior_on_def
            
            by blast
          have hint_open: "interior_on X TX (AN N0 (1 / real (Suc k))) \<in> TX"
          proof -
            have "{U \<in> TX. U \<subseteq> AN N0 (1 / real (Suc k))} \<subseteq> TX"
              
              by blast
            then show ?thesis unfolding interior_on_def using hTop unfolding is_topology_on_def
              
              by presburger
          qed
          text \<open>f_{N0} continuous → preimage of ball(f_{N0}(x0), ε/3) is open.\<close>
          have hfN0_cont: "top1_continuous_map_on X TX Y ?TY (f N0)"
            using hfn
            
            by simp
          have hfN0x0Y: "f N0 x0 \<in> Y"
            using hfN0_cont hx0X unfolding top1_continuous_map_on_def
            
            by blast
          define W1 where "W1 = {x \<in> X. f N0 x \<in> top1_ball_on Y d (f N0 x0) (\<epsilon> / 3)}"
          have hW1_open: "W1 \<in> TX"
            unfolding W1_def using hfN0_cont top1_ball_open_in_metric_topology[OF hd hfN0x0Y heps3]
            unfolding top1_continuous_map_on_def
            
            by blast
          have hx0W1: "x0 \<in> W1"
            unfolding W1_def top1_ball_on_def using hx0X hfN0x0Y hd heps3 unfolding top1_metric_on_def
            
            by fastforce
          text \<open>W = W1 ∩ Int(AN N0) is a neighborhood of x0.\<close>
          define W where "W = W1 \<inter> interior_on X TX (AN N0 (1 / real (Suc k)))"
          have hW_open: "W \<in> TX"
            unfolding W_def using topology_inter2[OF hTop hW1_open hint_open]
            
            by presburger
          have hx0W: "x0 \<in> W"
            unfolding W_def using hx0W1 hx0_int
            
            by blast
          have hW_nbhd: "neighborhood_of x0 X TX W"
            unfolding neighborhood_of_def using hW_open hx0W
            
            by presburger
          text \<open>g maps W into ball(g(x0), ε).\<close>
          have hg_image: "g ` W \<subseteq> top1_ball_on Y d (g x0) \<epsilon>"
          proof (rule subsetI)
            fix y assume "y \<in> g ` W"
            then obtain x where hxW: "x \<in> W" and hyeq: "y = g x"
              
              by blast
            have hxX: "x \<in> X" using hxW unfolding W_def W1_def
              
              by blast
            have hxAN: "x \<in> AN N0 (1 / real (Suc k))"
            proof -
              have "x \<in> interior_on X TX (AN N0 (1 / real (Suc k)))"
                using hxW unfolding W_def
                
                by blast
              then show ?thesis unfolding interior_on_def
                
                by fast
            qed
            have hxW1: "x \<in> W1" using hxW unfolding W_def
              
              by blast
            text \<open>d(f_{N0}(x), f_{N0}(x0)) < ε/3.\<close>
            have "d (f N0 x0) (f N0 x) < \<epsilon> / 3"
              using hxW1 unfolding W1_def top1_ball_on_def
              
              by blast
            have hfN0xY: "f N0 x \<in> Y"
              using hfN0_cont hxX unfolding top1_continuous_map_on_def
              
              by blast
            have hd_fN0: "d (f N0 x) (f N0 x0) < \<epsilon> / 3"
              using \<open>d (f N0 x0) (f N0 x) < \<epsilon> / 3\<close> hd hfN0xY hfN0x0Y unfolding top1_metric_on_def
              
              by force
            text \<open>d(g(x), f_{N0}(x)) ≤ 1/(Suc k) from limit.\<close>
            have hAN_bound: "\<forall>n\<ge>N0. d (f n x) (f N0 x) \<le> 1 / real (Suc k)"
              using hxAN unfolding AN_def top1_AN_48_def
              
              by blast
            have hgxY: "g x \<in> Y"
              using hptw hxX unfolding seq_converges_to_on_def
              
              by blast
            have hfN0xY: "f N0 x \<in> Y"
              using hfN0_cont hxX unfolding top1_continuous_map_on_def
              
              by blast
            have hconv_x: "seq_converges_to_on (\<lambda>n. f n x) (g x) Y ?TY"
              using hptw hxX
              
              by blast
            have hAN_bound': "\<forall>n\<ge>N0. d ((\<lambda>n. f n x) n) (f N0 x) \<le> 1 / real (Suc k)"
              using hAN_bound
              
              by argo
            have hd_gx_fN0: "d (g x) (f N0 x) \<le> 1 / real (Suc k)"
              using metric_limit_preserves_bound[OF hd hconv_x hAN_bound' hfN0xY]
              
              by simp
            text \<open>Similarly d(g(x0), f_{N0}(x0)) ≤ 1/(Suc k).\<close>
            have hAN_bound_x0: "\<forall>n\<ge>N0. d (f n x0) (f N0 x0) \<le> 1 / real (Suc k)"
              using hx0_AN unfolding AN_def top1_AN_48_def
              
              by blast
            have hconv_x0: "seq_converges_to_on (\<lambda>n. f n x0) (g x0) Y ?TY"
              using hptw hx0X
              
              by blast
            have hAN_bound_x0': "\<forall>n\<ge>N0. d ((\<lambda>n. f n x0) n) (f N0 x0) \<le> 1 / real (Suc k)"
              using hAN_bound_x0
              
              by argo
            have hd_gx0_fN0: "d (g x0) (f N0 x0) \<le> 1 / real (Suc k)"
              using metric_limit_preserves_bound[OF hd hconv_x0 hAN_bound_x0' hfN0x0Y]
              
              by auto
            text \<open>Triangle: d(g(x), g(x0)) < ε.\<close>
            have htri1: "d (g x) (g x0) \<le> d (g x) (f N0 x) + d (f N0 x) (g x0)"
              using hd hgxY hfN0xY hgx0Y unfolding top1_metric_on_def
              
              by fast
            have htri2: "d (f N0 x) (g x0) \<le> d (f N0 x) (f N0 x0) + d (f N0 x0) (g x0)"
              using hd hfN0xY hfN0x0Y hgx0Y unfolding top1_metric_on_def
              
              by blast
            have hdsym: "d (f N0 x0) (g x0) = d (g x0) (f N0 x0)"
              using hd hfN0x0Y hgx0Y unfolding top1_metric_on_def
              
              by blast
            have "d (g x) (g x0) < \<epsilon>"
              using htri1 htri2 hdsym hd_gx_fN0 hd_fN0 hd_gx0_fN0 hk
              
              by linarith
            have "d (g x0) (g x) < \<epsilon>"
              using \<open>d (g x) (g x0) < \<epsilon>\<close> hd hgxY hgx0Y unfolding top1_metric_on_def
              
              by simp
            then show "y \<in> top1_ball_on Y d (g x0) \<epsilon>"
              unfolding hyeq top1_ball_on_def using hgxY
              
              by blast
          qed
          show "\<exists>U. neighborhood_of x0 X TX U \<and> g ` U \<subseteq> V"
            using hW_nbhd hg_image hball_sub_V
            
            by fast
        qed
      qed
    qed
  qed

  show ?thesis
    unfolding top1_densein_on_def
  proof -
    have "X = closure_on X TX C"
      using hC_dense unfolding top1_densein_on_def
      
      by presburger
    also have "... \<subseteq> closure_on X TX {x \<in> X. top1_continuous_at_on X TX Y ?TY g x}"
      using closure_on_mono[OF hC_sub_cont]
      
      by fast
    finally have "X \<subseteq> closure_on X TX {x \<in> X. top1_continuous_at_on X TX Y ?TY g x}"
      
      by satx
    moreover have "closure_on X TX {x \<in> X. top1_continuous_at_on X TX Y ?TY g x} \<subseteq> X"
      using closure_on_subset_carrier[OF hTop]
      
      by auto
    ultimately show "closure_on X TX {x \<in> X. top1_continuous_at_on X TX Y ?TY g x} = X"
      
      by fast
  qed
qed

section \<open>*\<S>49 A Nowhere-Differentiable Function\<close>

(** from \S49 Theorem 49.1 [top1.tex:7345] **)
theorem Theorem_49_1:
  fixes h :: "real \<Rightarrow> real"
  assumes hcont: "continuous_on (top1_closed_interval 0 1) h"
  assumes heps: "0 < \<epsilon>"
  shows "\<exists>g. continuous_on (top1_closed_interval 0 1) g
        \<and> (\<forall>x\<in>top1_closed_interval 0 1. \<bar>h x - g x\<bar> < \<epsilon>)
        \<and> (\<forall>x\<in>{0<..<1}. \<not> (g differentiable (at x)))"
  sorry

text \<open>
  Proof skeleton for \S49 (Baire category argument in \<open>\<C>([0,1],\<real>)\<close> with the sup metric).
  We introduce the difference-quotient functional \<open>\<Delta> f(x,h)\<close>, the infimum \<open>\<Delta>\<^sub>h f\<close>,
  and the open dense sets \<open>U n\<close> used in the standard construction.  The detailed analysis
  proofs are left for later; the declarations below are meant to clarify the remaining scope.
\<close>

abbreviation top1_I01 :: "real set" where
  "top1_I01 \<equiv> top1_closed_interval 0 1"

definition top1_Delta49 :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "top1_Delta49 f x h =
     (if 0 < h \<and> h \<le> 1/2 then
        max (if x + h \<in> top1_I01 then \<bar>(f (x + h) - f x) / h\<bar> else 0)
            (if x - h \<in> top1_I01 then \<bar>(f (x - h) - f x) / h\<bar> else 0)
      else 0)"

definition top1_Delta_h49 :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "top1_Delta_h49 f h = Inf ((\<lambda>x. top1_Delta49 f x h) ` top1_I01)"

definition top1_C01 :: "(real \<Rightarrow> real) set" where
  "top1_C01 = {f. continuous_on top1_I01 f}"

lemma top1_C01_nonempty: "top1_C01 \<noteq> {}"
proof -
  have hex: "\<exists>f. f \<in> top1_C01"
  proof (rule exI[where x="(\<lambda>x. (0::real))"])
    show "(\<lambda>x. (0::real)) \<in> top1_C01"
      unfolding top1_C01_def by (simp add: continuous_on_const)
  qed
  show ?thesis
    using hex by (simp add: ex_in_conv)
qed

definition top1_rho49 :: "(real \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "top1_rho49 f g = Sup ((\<lambda>x. \<bar>f x - g x\<bar>) ` top1_I01)"

definition top1_U49 :: "nat \<Rightarrow> (real \<Rightarrow> real) set" where
  "top1_U49 n =
     {f \<in> top1_C01.
        \<exists>h. 0 < h \<and> h \<le> 1 / real (Suc (Suc n)) \<and> top1_Delta_h49 f h > real (Suc (Suc n))}"

lemma top1_U49_subset_C01:
  shows "top1_U49 n \<subseteq> top1_C01"
proof
  fix f
  assume hf: "f \<in> top1_U49 n"
  show "f \<in> top1_C01"
    using hf unfolding top1_U49_def by simp
qed

lemma top1_Inter_U49_subset_C01:
  shows "(\<Inter>n. top1_U49 n) \<subseteq> top1_C01"
proof
  fix f
  assume hf: "f \<in> (\<Inter>n. top1_U49 n)"
  have hf0: "f \<in> top1_U49 0"
    using hf by simp
  show "f \<in> top1_C01"
  proof -
    have "top1_U49 0 \<subseteq> top1_C01"
      by (rule top1_U49_subset_C01)
    show ?thesis
      by (rule subsetD[OF \<open>top1_U49 0 \<subseteq> top1_C01\<close> hf0])
  qed
qed

lemma top1_U49_open:
  assumes hrho: "top1_metric_on top1_C01 top1_rho49"
  shows "top1_U49 n \<in> top1_metric_topology_on top1_C01 top1_rho49"
  sorry

lemma top1_U49_dense:
  assumes hrho: "top1_metric_on top1_C01 top1_rho49"
  shows "top1_densein_on top1_C01 (top1_metric_topology_on top1_C01 top1_rho49) (top1_U49 n)"
  sorry

lemma top1_Inter_U49_dense:
  assumes hrho: "top1_metric_on top1_C01 top1_rho49"
  assumes hB: "top1_baire_on top1_C01 (top1_metric_topology_on top1_C01 top1_rho49)"
  shows "top1_densein_on top1_C01 (top1_metric_topology_on top1_C01 top1_rho49) (\<Inter>n. top1_U49 n)"
proof -
  let ?T = "top1_metric_topology_on top1_C01 top1_rho49"

  have hAll: "\<forall>n. top1_U49 n \<in> ?T \<and> top1_densein_on top1_C01 ?T (top1_U49 n)"
  proof (intro allI conjI)
    fix n
    show "top1_U49 n \<in> ?T"
      by (rule top1_U49_open[OF hrho])
    show "top1_densein_on top1_C01 ?T (top1_U49 n)"
      by (rule top1_U49_dense[OF hrho])
  qed

  have hBdef:
    "\<forall>U::nat \<Rightarrow> (real \<Rightarrow> real) set.
      (\<forall>n. U n \<in> ?T \<and> top1_densein_on top1_C01 ?T (U n)) \<longrightarrow>
        top1_densein_on top1_C01 ?T (\<Inter>n. U n)"
    using hB unfolding top1_baire_on_def by blast

  show ?thesis
    using hBdef hAll by blast
qed

lemma top1_Inter_U49_nowhere_differentiable:
  assumes hf: "f \<in> (\<Inter>n. top1_U49 n)"
  shows "\<forall>x\<in>{0<..<1}. \<not> (f differentiable (at x))"
  sorry

section \<open>\<S>50 Introduction to Dimension Theory\<close>

definition top1_cover_order_le_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_cover_order_le_on X \<A> m \<longleftrightarrow>
     (\<forall>x\<in>X. finite {U\<in>\<A>. x \<in> U} \<and> card {U\<in>\<A>. x \<in> U} \<le> Suc m)"

definition top1_dim_le_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_dim_le_on X TX m \<longleftrightarrow>
     (\<forall>\<A>. top1_open_covering_on X TX \<A>
        \<longrightarrow> (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_cover_order_le_on X \<B> m))"

definition top1_finite_dimensional_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_finite_dimensional_on X TX \<longleftrightarrow> (\<exists>m. top1_dim_le_on X TX m)"

definition top1_dim_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat" where
  "top1_dim_on X TX = (LEAST m. top1_dim_le_on X TX m)"

(** Basic monotonicity properties of cover order / dimension predicates. **)
lemma top1_cover_order_le_on_subset:
  assumes h: "top1_cover_order_le_on X \<A> m"
  assumes hsub: "\<A>' \<subseteq> \<A>"
  shows "top1_cover_order_le_on X \<A>' m"
proof (unfold top1_cover_order_le_on_def, intro ballI)
  fix x
  assume hxX: "x \<in> X"
  have hfin: "finite {U \<in> \<A>. x \<in> U}"
    using h hxX unfolding top1_cover_order_le_on_def by blast
  have hcard: "card {U \<in> \<A>. x \<in> U} \<le> Suc m"
    using h hxX unfolding top1_cover_order_le_on_def by blast

  have hsub': "{U \<in> \<A>'. x \<in> U} \<subseteq> {U \<in> \<A>. x \<in> U}"
    using hsub by blast
  have hfin': "finite {U \<in> \<A>'. x \<in> U}"
    by (rule finite_subset[OF hsub' hfin])

  have hcard': "card {U \<in> \<A>'. x \<in> U} \<le> card {U \<in> \<A>. x \<in> U}"
    by (rule card_mono[OF hfin hsub'])

  show "finite {U \<in> \<A>'. x \<in> U} \<and> card {U \<in> \<A>'. x \<in> U} \<le> Suc m"
  proof
    show "finite {U \<in> \<A>'. x \<in> U}"
      by (rule hfin')
    have "card {U \<in> \<A>'. x \<in> U} \<le> card {U \<in> \<A>. x \<in> U}"
      by (rule hcard')
    also have "... \<le> Suc m"
      by (rule hcard)
    finally show "card {U \<in> \<A>'. x \<in> U} \<le> Suc m" .
  qed
qed

lemma top1_cover_order_le_on_mono_m:
  assumes h: "top1_cover_order_le_on X \<A> m"
  assumes hmn: "m \<le> n"
  shows "top1_cover_order_le_on X \<A> n"
proof (unfold top1_cover_order_le_on_def, intro ballI)
  fix x
  assume hxX: "x \<in> X"
  have hfin: "finite {U \<in> \<A>. x \<in> U}"
    using h hxX unfolding top1_cover_order_le_on_def by blast
  have hcard: "card {U \<in> \<A>. x \<in> U} \<le> Suc m"
    using h hxX unfolding top1_cover_order_le_on_def by blast
  have hSuc: "Suc m \<le> Suc n"
    using hmn by simp
  have "card {U \<in> \<A>. x \<in> U} \<le> Suc n"
    by (rule order_trans[OF hcard hSuc])
  thus "finite {U \<in> \<A>. x \<in> U} \<and> card {U \<in> \<A>. x \<in> U} \<le> Suc n"
    using hfin by blast
qed

lemma top1_cover_order_le_on_mono_X:
  assumes h: "top1_cover_order_le_on X \<A> m"
  assumes hX: "X' \<subseteq> X"
  shows "top1_cover_order_le_on X' \<A> m"
proof (unfold top1_cover_order_le_on_def, intro ballI)
  fix x
  assume hxX': "x \<in> X'"
  have hxX: "x \<in> X"
    using hX hxX' by blast
  have hfin: "finite {U\<in>\<A>. x \<in> U}"
    using h hxX unfolding top1_cover_order_le_on_def by blast
  have hcard: "card {U\<in>\<A>. x \<in> U} \<le> Suc m"
    using h hxX unfolding top1_cover_order_le_on_def by blast
  show "finite {U\<in>\<A>. x \<in> U} \<and> card {U\<in>\<A>. x \<in> U} \<le> Suc m"
    using hfin hcard by blast
qed

lemma top1_dim_le_on_mono_m:
  assumes hdim: "top1_dim_le_on X TX m"
  assumes hmn: "m \<le> n"
  shows "top1_dim_le_on X TX n"
proof (unfold top1_dim_le_on_def, intro allI impI)
  fix \<A>
  assume hCov: "top1_open_covering_on X TX \<A>"
  have hdim':
    "\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow>
      (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_cover_order_le_on X \<B> m)"
    by (rule hdim[unfolded top1_dim_le_on_def])

  have hEx:
    "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_cover_order_le_on X \<B> m"
    by (rule hdim'[rule_format, of \<A>], rule hCov)

  obtain \<B> where hBcov: "top1_open_covering_on X TX \<B>"
    and hBref: "top1_refines \<B> \<A>"
    and hBord: "top1_cover_order_le_on X \<B> m"
    using hEx
    apply (elim exE conjE)
    apply assumption+
    done

  have hBord': "top1_cover_order_le_on X \<B> n"
    by (rule top1_cover_order_le_on_mono_m[OF hBord hmn])

  show "\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_cover_order_le_on X \<B> n"
  proof (rule exI[where x=\<B>], intro conjI)
    show "top1_open_covering_on X TX \<B>"
      by (rule hBcov)
    show "top1_refines \<B> \<A>"
      by (rule hBref)
    show "top1_cover_order_le_on X \<B> n"
      by (rule hBord')
  qed
qed

lemma top1_dim_le_on_imp_finite_dimensional:
  assumes hdim: "top1_dim_le_on X TX m"
  shows "top1_finite_dimensional_on X TX"
  unfolding top1_finite_dimensional_on_def
  by (rule exI[where x=m]) (rule hdim)

lemma top1_dim_on_le_of_dim_le':
  assumes hdim: "top1_dim_le_on X TX m"
  shows "top1_dim_on X TX \<le> m"
  unfolding top1_dim_on_def
  by (rule Least_le) (rule hdim)

lemma top1_dim_on_le_of_dim_le:
  assumes hex: "top1_finite_dimensional_on X TX"
  assumes hdim: "top1_dim_le_on X TX m"
  shows "top1_dim_on X TX \<le> m"
proof -
  have hex': "\<exists>k. top1_dim_le_on X TX k"
    by (rule hex[unfolded top1_finite_dimensional_on_def])
  show ?thesis
    by (rule top1_dim_on_le_of_dim_le'[OF hdim])
qed

lemma top1_dim_le_on_dim_on:
  assumes hex: "\<exists>m. top1_dim_le_on X TX m"
  shows "top1_dim_le_on X TX (top1_dim_on X TX)"
  unfolding top1_dim_on_def
  by (rule LeastI_ex) (rule hex)

lemma top1_dim_le_on_dim_on_finite:
  assumes hfd: "top1_finite_dimensional_on X TX"
  shows "top1_dim_le_on X TX (top1_dim_on X TX)"
proof -
  have hex: "\<exists>m. top1_dim_le_on X TX m"
    by (rule hfd[unfolded top1_finite_dimensional_on_def])
  show ?thesis
    by (rule top1_dim_le_on_dim_on[OF hex])
qed

lemma top1_dim_le_on_iff_dim_on_le:
  assumes hfd: "top1_finite_dimensional_on X TX"
  shows "top1_dim_le_on X TX m \<longleftrightarrow> top1_dim_on X TX \<le> m"
proof
  assume hdim: "top1_dim_le_on X TX m"
  show "top1_dim_on X TX \<le> m"
    by (rule top1_dim_on_le_of_dim_le[OF hfd hdim])
next
  assume hle: "top1_dim_on X TX \<le> m"
  have hdim0: "top1_dim_le_on X TX (top1_dim_on X TX)"
    by (rule top1_dim_le_on_dim_on_finite[OF hfd])
  show "top1_dim_le_on X TX m"
    by (rule top1_dim_le_on_mono_m[OF hdim0 hle])
qed

(** Dimension is monotone for closed subspaces (top1.tex: \S50, used in Theorem 50.1). **)
lemma top1_dim_le_on_closedin_subspace:
  assumes hdim: "top1_dim_le_on X TX m"
  assumes hClosed: "closedin_on X TX Y"
  shows "top1_dim_le_on Y (subspace_topology X TX Y) m"
proof -
  let ?TY = "subspace_topology X TX Y"

  have hYsubX: "Y \<subseteq> X"
    by (rule closedin_sub[OF hClosed])

  have hXminusY_open: "X - Y \<in> TX"
    by (rule closedin_diff_open[OF hClosed])

  have hdim_def:
    "\<forall>\<A>. top1_open_covering_on X TX \<A>
      \<longrightarrow> (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_cover_order_le_on X \<B> m)"
    using hdim unfolding top1_dim_le_on_def by blast

  show ?thesis
    unfolding top1_dim_le_on_def
  proof (intro allI impI)
    fix \<A>
    assume hCovY: "top1_open_covering_on Y ?TY \<A>"

    have hAsubTY: "\<A> \<subseteq> ?TY"
      using hCovY unfolding top1_open_covering_on_def by blast
    have hYcov: "Y \<subseteq> \<Union>\<A>"
      using hCovY unfolding top1_open_covering_on_def by blast

    define Lift where "Lift = {U \<in> TX. Y \<inter> U \<in> \<A>}"
    define \<A>X where "\<A>X = insert (X - Y) Lift"

    have hLift_subTX: "Lift \<subseteq> TX"
      unfolding Lift_def by blast

    have hAX_subTX: "\<A>X \<subseteq> TX"
      unfolding \<A>X_def using hXminusY_open hLift_subTX by blast

    have hXcov: "X \<subseteq> \<Union>\<A>X"
    proof (rule subsetI)
      fix x
      assume hxX: "x \<in> X"
      show "x \<in> \<Union>\<A>X"
      proof (cases "x \<in> Y")
        case True
        have hxU: "x \<in> \<Union>\<A>"
          using hYcov True by blast
        then obtain W where hW: "W \<in> \<A>" and hxW: "x \<in> W"
          by blast
        have hWsubY: "W \<subseteq> Y"
        proof -
          have "W \<subseteq> Y"
          proof
            fix z assume hz: "z \<in> W"
            have "W \<in> ?TY"
              using hAsubTY hW by blast
            then obtain U where hU: "U \<in> TX" and hWeq: "W = Y \<inter> U"
              unfolding subspace_topology_def by blast
            have "z \<in> Y"
              using hz unfolding hWeq by blast
            thus "z \<in> Y" .
          qed
          thus ?thesis .
        qed
        have hxY: "x \<in> Y"
          by (rule True)

        obtain U where hU: "U \<in> TX" and hWeq: "W = Y \<inter> U"
          using hAsubTY hW unfolding subspace_topology_def by blast

        have hxU': "x \<in> U"
        proof -
          have hxYU: "x \<in> Y \<inter> U"
            using hxW unfolding hWeq by simp
          thus ?thesis
            by simp
        qed

        have hUinLift: "U \<in> Lift"
          unfolding Lift_def
          apply (intro CollectI conjI)
           apply (rule hU)
          apply (subst hWeq[symmetric])
          apply (rule hW)
          done

        have "U \<in> \<A>X"
          unfolding \<A>X_def using hUinLift by blast
        thus ?thesis
          using hxU' by blast
      next
        case False
        have hx: "x \<in> X - Y"
          using hxX False by blast
        have "X - Y \<in> \<A>X"
          unfolding \<A>X_def by blast
        thus ?thesis
          using hx by blast
      qed
    qed

    have hCovX: "top1_open_covering_on X TX \<A>X"
      unfolding top1_open_covering_on_def
      using hAX_subTX hXcov by blast

    obtain \<B>X where hBXcov: "top1_open_covering_on X TX \<B>X"
      and hBXref: "top1_refines \<B>X \<A>X"
      and hBXord: "top1_cover_order_le_on X \<B>X m"
      using hdim_def hCovX by blast

    have hBXsubTX: "\<B>X \<subseteq> TX"
      using hBXcov unfolding top1_open_covering_on_def by blast
    have hBXcovX: "X \<subseteq> \<Union>\<B>X"
      using hBXcov unfolding top1_open_covering_on_def by blast

    define \<B> where "\<B> = {Y \<inter> B | B. B \<in> \<B>X \<and> Y \<inter> B \<noteq> {}}"

    have hBsubTY: "\<B> \<subseteq> ?TY"
    proof (rule subsetI)
      fix V
      assume hV: "V \<in> \<B>"
      obtain B where hB: "B \<in> \<B>X" and hVeq: "V = Y \<inter> B" and hVne: "Y \<inter> B \<noteq> {}"
        using hV unfolding \<B>_def by blast
      have hBTX: "B \<in> TX"
        using hBXsubTX hB by blast
      show "V \<in> ?TY"
        unfolding hVeq subspace_topology_def using hBTX by blast
    qed

    have hYcovB: "Y \<subseteq> \<Union>\<B>"
    proof (rule subsetI)
      fix y
      assume hyY: "y \<in> Y"
      have hyX: "y \<in> X"
        using hYsubX hyY by blast
      have hyU: "y \<in> \<Union>\<B>X"
        using hBXcovX hyX by blast
      then obtain B where hB: "B \<in> \<B>X" and hyB: "y \<in> B"
        by blast
      have hyYB: "y \<in> Y \<inter> B"
        using hyY hyB by blast
      have hYBne: "Y \<inter> B \<noteq> {}"
        using hyYB by blast
      have "Y \<inter> B \<in> \<B>"
        unfolding \<B>_def using hB hYBne by blast
      thus "y \<in> \<Union>\<B>"
        using hyYB by blast
    qed

    have hCovB: "top1_open_covering_on Y ?TY \<B>"
      unfolding top1_open_covering_on_def
      using hBsubTY hYcovB by blast

    have hBref: "top1_refines \<B> \<A>"
    proof (unfold top1_refines_def, intro ballI)
      fix V
      assume hV: "V \<in> \<B>"
      obtain B where hBin: "B \<in> \<B>X" and hVeq: "V = Y \<inter> B" and hVne: "Y \<inter> B \<noteq> {}"
        using hV unfolding \<B>_def by blast

      obtain U where hUAX: "U \<in> \<A>X" and hBsubU: "B \<subseteq> U"
        using hBXref hBin unfolding top1_refines_def by blast

      have hUnot: "U \<noteq> X - Y"
      proof
        assume hUeq: "U = X - Y"
        have "V \<subseteq> Y \<inter> (X - Y)"
          unfolding hVeq using hBsubU unfolding hUeq by blast
        hence "V \<subseteq> {}"
          by blast
        hence "V = {}"
          by blast
        thus False
          using hVne unfolding hVeq by simp
      qed

      have hUinLift: "U \<in> Lift"
        using hUAX hUnot unfolding \<A>X_def by blast

      have hYUinA: "Y \<inter> U \<in> \<A>"
        using hUinLift unfolding Lift_def by blast

      have hVsub: "V \<subseteq> Y \<inter> U"
        unfolding hVeq using hBsubU by blast

      show "\<exists>A0\<in>\<A>. V \<subseteq> A0"
        by (rule bexI[where x="Y \<inter> U"]) (rule hVsub, rule hYUinA)
    qed

    have hBord: "top1_cover_order_le_on Y \<B> m"
    proof (unfold top1_cover_order_le_on_def, intro ballI)
      fix y
      assume hyY: "y \<in> Y"
      have hyX: "y \<in> X"
        using hYsubX hyY by blast

      have hfinX: "finite {U \<in> \<B>X. y \<in> U}"
        using hBXord hyX unfolding top1_cover_order_le_on_def by blast
      have hcardX: "card {U \<in> \<B>X. y \<in> U} \<le> Suc m"
        using hBXord hyX unfolding top1_cover_order_le_on_def by blast

      have hEq:
        "{V \<in> \<B>. y \<in> V} = (\<lambda>U. Y \<inter> U) ` {U \<in> \<B>X. y \<in> U}"
      proof (rule subset_antisym)
        show "{V \<in> \<B>. y \<in> V} \<subseteq> (\<lambda>U. Y \<inter> U) ` {U \<in> \<B>X. y \<in> U}"
        proof
          fix V
          assume hV: "V \<in> {V \<in> \<B>. y \<in> V}"
          have hVin: "V \<in> \<B>" and hyV: "y \<in> V"
            using hV by blast+
          obtain U where hU: "U \<in> \<B>X" and hVeq: "V = Y \<inter> U" and hVne: "Y \<inter> U \<noteq> {}"
            using hVin unfolding \<B>_def by blast
          have hyU: "y \<in> U"
            using hyV unfolding hVeq by simp
          have hUset: "U \<in> {U \<in> \<B>X. y \<in> U}"
            using hU hyU by blast
          show "V \<in> (\<lambda>U. Y \<inter> U) ` {U \<in> \<B>X. y \<in> U}"
            unfolding hVeq using hUset by blast
        qed
      next
        show "(\<lambda>U. Y \<inter> U) ` {U \<in> \<B>X. y \<in> U} \<subseteq> {V \<in> \<B>. y \<in> V}"
        proof
          fix V
          assume hV: "V \<in> (\<lambda>U. Y \<inter> U) ` {U \<in> \<B>X. y \<in> U}"
          then obtain U where hUset: "U \<in> {U \<in> \<B>X. y \<in> U}" and hVeq: "V = Y \<inter> U"
            by blast
          have hU: "U \<in> \<B>X" and hyU: "y \<in> U"
            using hUset by blast+
          have hyV: "y \<in> V"
            unfolding hVeq using hyY hyU by blast
          have hVne: "Y \<inter> U \<noteq> {}"
            using hyV unfolding hVeq by blast
          have hVin: "V \<in> \<B>"
            unfolding \<B>_def hVeq using hU hVne by blast
          show "V \<in> {V \<in> \<B>. y \<in> V}"
            using hVin hyV by blast
        qed
      qed

      have hfin: "finite {V \<in> \<B>. y \<in> V}"
        unfolding hEq by (rule finite_imageI[OF hfinX])
      have hcard_img: "card ((\<lambda>U. Y \<inter> U) ` {U \<in> \<B>X. y \<in> U}) \<le> card {U \<in> \<B>X. y \<in> U}"
        by (rule card_image_le[OF hfinX])
      have hcard: "card {V \<in> \<B>. y \<in> V} \<le> Suc m"
        unfolding hEq
        apply (rule order_trans)
         apply (rule hcard_img)
        apply (rule hcardX)
        done

      show "finite {V \<in> \<B>. y \<in> V} \<and> card {V \<in> \<B>. y \<in> V} \<le> Suc m"
        using hfin hcard by blast
    qed

    show "\<exists>\<B>. top1_open_covering_on Y ?TY \<B> \<and> top1_refines \<B> \<A> \<and> top1_cover_order_le_on Y \<B> m"
      by (rule exI[where x=\<B>], intro conjI, rule hCovB, rule hBref, rule hBord)
  qed
qed

(** from \S50 Theorem 50.1 [top1.tex:7556] **)
theorem Theorem_50_1:
  assumes hdim: "top1_finite_dimensional_on X TX"
  assumes hClosed: "closedin_on X TX Y"
  shows "top1_finite_dimensional_on Y (subspace_topology X TX Y)
    \<and> top1_dim_on Y (subspace_topology X TX Y) \<le> top1_dim_on X TX"
proof -
  let ?TY = "subspace_topology X TX Y"
  define mX where "mX = top1_dim_on X TX"

  have hdimX: "top1_dim_le_on X TX mX"
    unfolding mX_def
    by (rule top1_dim_le_on_dim_on_finite[OF hdim])

  have hdimY: "top1_dim_le_on Y ?TY mX"
    by (rule top1_dim_le_on_closedin_subspace[OF hdimX hClosed])

  have hfdY: "top1_finite_dimensional_on Y ?TY"
    by (rule top1_dim_le_on_imp_finite_dimensional[OF hdimY])

  have hdim_on: "top1_dim_on Y ?TY \<le> mX"
    by (rule top1_dim_on_le_of_dim_le'[OF hdimY])

  show ?thesis
  proof -
    have hdim_on': "top1_dim_on Y ?TY \<le> top1_dim_on X TX"
      using hdim_on unfolding mX_def by simp
    show ?thesis
      using hfdY hdim_on' by blast
  qed
qed

(** from \S50 Theorem 50.2 [top1.tex:7566] **)
theorem Theorem_50_2:
  assumes hYX: "X = Y \<union> Z"
  assumes hYcl: "closedin_on X TX Y"
  assumes hZcl: "closedin_on X TX Z"
  assumes hdimY: "top1_finite_dimensional_on Y (subspace_topology X TX Y)"
  assumes hdimZ: "top1_finite_dimensional_on Z (subspace_topology X TX Z)"
  shows "top1_dim_on X TX = max (top1_dim_on Y (subspace_topology X TX Y)) (top1_dim_on Z (subspace_topology X TX Z))"
  sorry

(** from \S50 Corollary 50.3 [top1.tex:7598] **)
corollary Corollary_50_3:
  assumes hcov: "X = (\<Union>i\<in>{0..<k}. Y i)"
  assumes hClosed: "\<forall>i<k. closedin_on X TX (Y i)"
  assumes hdim: "\<forall>i<k. top1_finite_dimensional_on (Y i) (subspace_topology X TX (Y i))"
  shows "top1_dim_on X TX = (Max ((\<lambda>i. top1_dim_on (Y i) (subspace_topology X TX (Y i))) ` {0..<k}))"
  sorry

(** A convenient sup metric on the concrete model \<open>\<real>^N\<close> (as extensional functions). **)
definition top1_Rpow_sup_dist :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real" where
  "top1_Rpow_sup_dist N x y = Sup ((\<lambda>i. \<bar>x i - y i\<bar>) ` {0..<N})"

(** Placeholder predicate for “general position” in \<open>\<real>^N\<close>.
    The intended meaning is that every subfamily of size \<open>N+1\<close> is affinely independent. **)
definition top1_general_position_in_Rpow :: "nat \<Rightarrow> (nat \<Rightarrow> real) set \<Rightarrow> bool" where
  "top1_general_position_in_Rpow N S \<longleftrightarrow>
     finite S \<and> S \<subseteq> top1_Rpow_set N"

(** from \S50 Lemma 50.4 (General position approximation) [top1.tex:7700] **)
lemma Lemma_50_4:
  assumes hFin: "finite A"
  assumes hA: "A \<subseteq> top1_Rpow_set N"
  assumes hdelta: "0 < \<delta>"
  shows "\<exists>f. inj_on f A
        \<and> (\<forall>x\<in>A. f x \<in> top1_Rpow_set N \<and> top1_Rpow_sup_dist N x (f x) < \<delta>)
        \<and> top1_general_position_in_Rpow N (f ` A)"
  sorry

(** from \S50 Theorem 50.5 (The imbedding theorem) [top1.tex:7710] **)
theorem Theorem_50_5:
  assumes hComp: "top1_compact_on X TX"
  assumes hMet: "top1_metrizable_on X TX"
  assumes hdim: "top1_dim_le_on X TX m"
  shows "\<exists>F. top1_embedding_on X TX (top1_Rpow_set (2 * m + 1)) (top1_Rpow_topology (2 * m + 1)) F"
  sorry

(** from \S50 Theorem 50.6 [top1.tex:7808] **)
theorem Theorem_50_6:
  assumes hComp: "top1_compact_on X (subspace_topology (top1_Rpow_set N) (top1_Rpow_topology N) X)"
  shows "top1_dim_le_on X (subspace_topology (top1_Rpow_set N) (top1_Rpow_topology N) X) N"
  sorry

(** from \S50 Corollary 50.7 [top1.tex:7839] **)
corollary Corollary_50_7:
  assumes hComp: "top1_compact_on X TX"
  assumes hMan: "top1_m_manifold_on m X TX"
  shows "top1_dim_le_on X TX m"
  sorry

(** from \S50 Corollary 50.8 [top1.tex:7841] **)
corollary Corollary_50_8:
  assumes hComp: "top1_compact_on X TX"
  assumes hMan: "top1_m_manifold_on m X TX"
  shows "\<exists>F. top1_embedding_on X TX (top1_Rpow_set (2 * m + 1)) (top1_Rpow_topology (2 * m + 1)) F"
  sorry

(** from \S50 Corollary 50.9 [top1.tex:7843] **)
corollary Corollary_50_9:
  assumes hComp: "top1_compact_on X TX"
  assumes hMet: "top1_metrizable_on X TX"
  shows "(\<exists>N F. top1_embedding_on X TX (top1_Rpow_set N) (top1_Rpow_topology N) F)
    \<longleftrightarrow> top1_finite_dimensional_on X TX"
  sorry


end
