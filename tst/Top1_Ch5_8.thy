theory Top1_Ch5_8
  imports Top1_Ch4
begin

section \<open>\<S>37 The Tychonoff Theorem\<close>

text \<open>
  Status note: the top-level definitions/lemmas/theorems for \<open>\<S>37\<close>--\<open>\<S>50\<close> are now present in
  this theory (using \<open>sorry\<close> where appropriate).  Remaining admits are concentrated in the main results:
  \<open>\<S>37\<close>: 1, \<open>\<S>38\<close>: 3, \<open>\<S>39\<close>: 1, \<open>\<S>40\<close>: 3, \<open>\<S>41\<close>: 8, \<open>\<S>42\<close>: 1, \<open>\<S>43\<close>: 4, \<open>\<S>44\<close>: 1,
  \<open>\<S>45\<close>: 5, \<open>\<S>46\<close>: 4, \<open>\<S>47\<close>: 4, \<open>\<S>48\<close>: 3, \<open>\<S>49\<close>: 4, \<open>\<S>50\<close>: 8.
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

(** from \S37 Theorem 37.3 (Tychonoff theorem) [top1.tex:5253] **)
theorem Theorem_37_3:
  assumes hIne: "I \<noteq> {}"
  assumes hComp: "\<forall>i\<in>I. top1_compact_on (X i) (TX i)"
  shows "top1_compact_on (top1_PiE I X) (top1_product_topology_on I X TX)"
  sorry

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
lemma Lemma_39_2:
  assumes hMet: "top1_metrizable_on X TX"
  assumes hCov: "top1_open_covering_on X TX \<A>"
  shows "\<exists>\<E>. top1_open_covering_on X TX \<E> \<and> top1_refines \<E> \<A> \<and> top1_sigma_locally_finite_family_on X TX \<E>"
  sorry

section \<open>\<S>40 The Nagata-Smirnov Metrization Theorem\<close>

definition top1_G_delta_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_G_delta_on X TX A \<longleftrightarrow> A \<subseteq> X \<and> (\<exists>U::nat \<Rightarrow> 'a set. (\<forall>n. U n \<in> TX) \<and> A = (\<Inter>n. U n))"

(** from \S40 Lemma 40.1 [top1.tex:5675] **)
lemma Lemma_40_1:
  assumes hReg: "top1_regular_on X TX"
  assumes hBasis: "basis_for X \<B> TX"
  assumes hCLF: "top1_sigma_locally_finite_family_on X TX \<B>"
  shows "top1_normal_on X TX \<and> (\<forall>A. closedin_on X TX A \<longrightarrow> top1_G_delta_on X TX A)"
  sorry

(** from \S40 Lemma 40.2 [top1.tex:5724] **)
lemma Lemma_40_2:
  assumes hN: "top1_normal_on X TX"
  assumes hA: "closedin_on X TX A"
  assumes hG: "top1_G_delta_on X TX A"
  shows "\<exists>f::'a \<Rightarrow> real.
    top1_continuous_map_on X TX (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1) f
    \<and> (\<forall>x\<in>A. f x = 0) \<and> (\<forall>x\<in>X - A. 0 < f x)"
  sorry

(** from \S40 Theorem 40.3 (Nagata-Smirnov metrization theorem) [top1.tex:5727] **)
theorem Theorem_40_3:
  shows "top1_metrizable_on X TX \<longleftrightarrow>
    (top1_regular_on X TX \<and> (\<exists>\<B>. basis_for X \<B> TX \<and> top1_sigma_locally_finite_family_on X TX \<B>))"
  sorry

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
theorem Theorem_41_1:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hHaus: "is_hausdorff_on X TX"
  shows "top1_normal_on X TX"
  sorry

(** from \S41 Theorem 41.2 [top1.tex:5851] **)
theorem Theorem_41_2:
  assumes hPara: "top1_paracompact_on X TX"
  assumes hClosed: "closedin_on X TX A"
  shows "top1_paracompact_on A (subspace_topology X TX A)"
  sorry

(** from \S41 Lemma 41.3 [top1.tex:5864] **)
lemma Lemma_41_3:
  assumes hReg: "top1_regular_on X TX"
  shows "(\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow> (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B>)) \<longleftrightarrow>
        (\<forall>\<A>. top1_open_covering_on X TX \<A> \<longrightarrow> (\<exists>\<B>. top1_open_covering_on X TX \<B> \<and> top1_refines \<B> \<A> \<and> top1_locally_finite_family_on X TX \<B> \<and> (\<forall>B\<in>\<B>. closure_on X TX B \<subseteq> (SOME A. A \<in> \<A> \<and> B \<subseteq> A))))"
  sorry

(** from \S41 Theorem 41.4 [top1.tex:5953] **)
theorem Theorem_41_4:
  assumes hMet: "top1_metrizable_on X TX"
  shows "top1_paracompact_on X TX"
  sorry

(** from \S41 Theorem 41.5 [top1.tex:5956] **)
theorem Theorem_41_5:
  assumes hReg: "top1_regular_on X TX"
  assumes hLind: "top1_lindelof_on X TX"
  shows "top1_paracompact_on X TX"
  sorry

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
  sorry

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

(** from \S43 Theorem 43.4 [top1.tex:6194] **)
theorem Theorem_43_4:
  shows "\<exists>D.
    top1_complete_metric_on (top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set))) D
    \<and> top1_metric_topology_on (top1_PiE (UNIV::nat set) (\<lambda>_. (UNIV::real set))) D
        = top1_product_topology_on (UNIV::nat set) (\<lambda>_. (UNIV::real set))
            (\<lambda>_. top1_metric_topology_on (UNIV::real set) (top1_bounded_metric (\<lambda>x y. \<bar>x - y\<bar>)))"
  sorry

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

(** from \S43 Theorem 43.5 [top1.tex:6242] **)
theorem Theorem_43_5:
  assumes hIne: "I \<noteq> {}"
  assumes hd: "top1_complete_metric_on Y d"
  shows "top1_complete_metric_on (top1_PiE I (\<lambda>_. Y)) (top1_uniform_metric_on I d)"
  sorry

(** from \S43 Theorem 43.6 [top1.tex:6272] **)
theorem Theorem_43_6:
  assumes hd: "top1_metric_on Y d"
  shows "closedin_on
           (top1_PiE X (\<lambda>_. Y))
           (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))
           (top1_continuous_maps_metric_on X TX Y d)"
    and "closedin_on
           (top1_PiE X (\<lambda>_. Y))
           (top1_metric_topology_on (top1_PiE X (\<lambda>_. Y)) (top1_uniform_metric_on X d))
           (top1_bounded_maps_metric_on X Y d)"
    and "top1_complete_metric_on Y d
          \<longrightarrow> top1_complete_metric_on (top1_continuous_maps_metric_on X TX Y d) (top1_uniform_metric_on X d)"
    and "top1_complete_metric_on Y d
          \<longrightarrow> top1_complete_metric_on (top1_bounded_maps_metric_on X Y d) (top1_uniform_metric_on X d)"
  sorry

definition top1_isometry_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real)
    \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_isometry_on X d Y dY e \<longleftrightarrow>
     (\<forall>x\<in>X. e x \<in> Y) \<and> (\<forall>x\<in>X. \<forall>x'\<in>X. dY (e x) (e x') = d x x')"

(** from \S43 Theorem 43.7 (Completion) [top1.tex:6312] **)
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
    sorry

qed

(** Helper: diameter control implies pairwise distance control (intended meaning of diameter). **)
lemma top1_diameter_on_lt_imp_dist_lt:
  assumes hd: "top1_metric_on X d"
  assumes hAX: "A \<subseteq> X"
  assumes hxA: "x \<in> A"
  assumes hyA: "y \<in> A"
  assumes hdiam: "top1_diameter_on d A < e"
  shows "d x y < e"
  sorry

(** from \S48 Lemma 48.3 [top1.tex:7208] **)
lemma Lemma_48_3:
  assumes hd: "top1_complete_metric_on X d"
  assumes hCne: "\<forall>n. C n \<noteq> {}"
  assumes hCcl: "\<forall>n. closedin_on X (top1_metric_topology_on X d) (C n)"
  assumes hnest: "\<forall>n. C (Suc n) \<subseteq> C n"
  assumes hdiam: "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. top1_diameter_on d (C n) < e"
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
      have hdist: "d (s m) (s n) < e"
        by (rule top1_diameter_on_lt_imp_dist_lt[OF hmetric hCsubX[rule_format, of N] hsmCN hsnCN hdiamN])

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
theorem Theorem_48_5:
  assumes hB: "top1_baire_on X TX"
  assumes hd: "top1_metric_on Y d"
  assumes hfn: "\<forall>n. top1_continuous_map_on X TX Y (top1_metric_topology_on Y d) (f n)"
  assumes hptw: "\<forall>x\<in>X. seq_converges_to_on (\<lambda>n. f n x) (g x) Y (top1_metric_topology_on Y d)"
  shows "top1_densein_on X TX {x \<in> X. top1_continuous_at_on X TX Y (top1_metric_topology_on Y d) g x}"
  sorry

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
