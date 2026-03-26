theory Top1_Ch3
  imports Top1_Ch2
begin

section \<open>\<S>23 Connected Spaces\<close>

definition top1_connected_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_connected_on X T \<longleftrightarrow>
     is_topology_on X T \<and>
     (\<nexists>U V. U \<in> T \<and> V \<in> T \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X)"

(** Separation predicate (used for connectedness proofs). **)
definition top1_is_separation_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_is_separation_on X T U V \<longleftrightarrow>
     U \<in> T \<and> V \<in> T \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"

(** from \S23 Lemma 23.1 (Separation and connectedness) [top1.tex:2607] **)
lemma Lemma_23_1:
  "top1_connected_on X T \<longleftrightarrow> is_topology_on X T \<and> (\<nexists>U V. top1_is_separation_on X T U V)"
  unfolding top1_connected_on_def top1_is_separation_on_def by blast

(** from \S23 Lemma 23.2 [top1.tex:~2635] **)
lemma Lemma_23_2:
  assumes hTX: "is_topology_on X TX"
  assumes hsep: "top1_is_separation_on X TX C D"
  assumes hYX: "Y \<subseteq> X"
  assumes hconn: "top1_connected_on Y (subspace_topology X TX Y)"
  shows "Y \<subseteq> C \<or> Y \<subseteq> D"
proof -
  define TY where "TY = subspace_topology X TX Y"

  have hNoSepY:
    "\<nexists>U V. U \<in> TY \<and> V \<in> TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
    using hconn unfolding top1_connected_on_def TY_def by blast

  have hC: "C \<in> TX"
    using hsep unfolding top1_is_separation_on_def by simp
  have hD: "D \<in> TX"
    using hsep unfolding top1_is_separation_on_def by simp
  have hdisj: "C \<inter> D = {}"
    using hsep unfolding top1_is_separation_on_def by simp
  have hunion: "C \<union> D = X"
    using hsep unfolding top1_is_separation_on_def by simp

  have hYC_open: "Y \<inter> C \<in> TY"
    unfolding TY_def subspace_topology_def using hC by blast
  have hYD_open: "Y \<inter> D \<in> TY"
    unfolding TY_def subspace_topology_def using hD by blast
  have hdisjY: "(Y \<inter> C) \<inter> (Y \<inter> D) = {}"
    using hdisj by blast
  have hcoverY: "(Y \<inter> C) \<union> (Y \<inter> D) = Y"
  proof (rule equalityI)
    show "(Y \<inter> C) \<union> (Y \<inter> D) \<subseteq> Y" by blast
    show "Y \<subseteq> (Y \<inter> C) \<union> (Y \<inter> D)"
    proof (rule subsetI)
      fix y assume hyY: "y \<in> Y"
      have hyX: "y \<in> X"
        using hYX hyY by blast
      have "y \<in> C \<or> y \<in> D"
        using hunion hyX by blast
      thus "y \<in> (Y \<inter> C) \<union> (Y \<inter> D)"
        using hyY by blast
    qed
  qed

  show ?thesis
  proof (rule classical)
    show "Y \<subseteq> C \<or> Y \<subseteq> D"
    proof (rule ccontr)
      assume h:
        "\<not> (Y \<subseteq> C \<or> Y \<subseteq> D)"
      have hnotC: "\<not> Y \<subseteq> C"
      proof
        assume hYC: "Y \<subseteq> C"
        have "Y \<subseteq> C \<or> Y \<subseteq> D"
          using hYC by blast
        thus False
          using h by blast
      qed
      have hnotD: "\<not> Y \<subseteq> D"
      proof
        assume hYD: "Y \<subseteq> D"
        have "Y \<subseteq> C \<or> Y \<subseteq> D"
          using hYD by blast
        thus False
          using h by blast
      qed

      have hYCne: "Y \<inter> C \<noteq> {}"
      proof
        assume hemp: "Y \<inter> C = {}"
        have "Y \<subseteq> D"
        proof (rule subsetI)
          fix y assume hyY: "y \<in> Y"
          have hyX: "y \<in> X"
            using hYX hyY by blast
          have "y \<in> C \<or> y \<in> D"
            using hunion hyX by blast
          thus "y \<in> D"
            using hemp hyY by blast
        qed
        thus False
          using hnotD by blast
      qed

      have hYDne: "Y \<inter> D \<noteq> {}"
      proof
        assume hemp: "Y \<inter> D = {}"
        have "Y \<subseteq> C"
        proof (rule subsetI)
          fix y assume hyY: "y \<in> Y"
          have hyX: "y \<in> X"
            using hYX hyY by blast
          have "y \<in> C \<or> y \<in> D"
            using hunion hyX by blast
          thus "y \<in> C"
            using hemp hyY by blast
        qed
        thus False
          using hnotC by blast
      qed

      have "\<exists>U V. U \<in> TY \<and> V \<in> TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
        apply (rule exI[where x="Y \<inter> C"])
        apply (rule exI[where x="Y \<inter> D"])
        using hYC_open hYD_open hYCne hYDne hdisjY hcoverY by blast
      thus False
        using hNoSepY by blast
    qed
  qed
qed

(** from \S23 Theorem 23.3 [top1.tex:2647] **)
theorem Theorem_23_3:
  fixes A :: "'i \<Rightarrow> 'a set"
  assumes hTX: "is_topology_on X TX"
  assumes hI: "I \<noteq> {}"
  assumes hA: "\<forall>i\<in>I. A i \<subseteq> X"
  assumes hconnA: "\<forall>i\<in>I. top1_connected_on (A i) (subspace_topology X TX (A i))"
  assumes hp: "p \<in> \<Inter>(A ` I)"
  defines "Y \<equiv> (\<Union>i\<in>I. A i)"
  shows "top1_connected_on Y (subspace_topology X TX Y)"
proof -
  have hYX: "Y \<subseteq> X"
    unfolding Y_def using hA by blast
  have hTopY: "is_topology_on Y (subspace_topology X TX Y)"
    by (rule subspace_topology_is_topology_on[OF hTX hYX])

  show ?thesis
    unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on Y (subspace_topology X TX Y)"
      by (rule hTopY)
    show "\<nexists>U V.
        U \<in> subspace_topology X TX Y \<and>
        V \<in> subspace_topology X TX Y \<and>
        U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
    proof (rule notI)
      assume hsep:
        "\<exists>U V.
          U \<in> subspace_topology X TX Y \<and>
          V \<in> subspace_topology X TX Y \<and>
          U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
      then obtain U V where hUV: "top1_is_separation_on Y (subspace_topology X TX Y) U V"
        unfolding top1_is_separation_on_def by blast

	      have hUopen: "U \<in> subspace_topology X TX Y"
	        using hUV unfolding top1_is_separation_on_def by simp
	      have hVopen: "V \<in> subspace_topology X TX Y"
	        using hUV unfolding top1_is_separation_on_def by simp
	      have hUne: "U \<noteq> {}"
	        using hUV unfolding top1_is_separation_on_def by simp
	      have hVne: "V \<noteq> {}"
	        using hUV unfolding top1_is_separation_on_def by simp
	      have hdisj: "U \<inter> V = {}"
	        using hUV unfolding top1_is_separation_on_def by simp
	      have hUVY: "U \<union> V = Y"
	        using hUV unfolding top1_is_separation_on_def by simp

      have hpY: "p \<in> Y"
      proof -
        obtain i0 where hi0: "i0 \<in> I"
          using hI by blast
        have "p \<in> A i0"
          using hp hi0 by blast
        thus ?thesis
          unfolding Y_def using hi0 by blast
      qed
      have hpUorV: "p \<in> U \<or> p \<in> V"
        using hUVY hpY by blast

      show False
      proof (cases "p \<in> U")
        case True
        have hAllU: "\<forall>i\<in>I. A i \<subseteq> U"
        proof (intro ballI)
          fix i assume hi: "i \<in> I"
          have hAiY: "A i \<subseteq> Y"
            unfolding Y_def using hi by blast
          have hconnAi: "top1_connected_on (A i) (subspace_topology X TX (A i))"
            using hconnA hi by blast
          have hTopEq:
            "subspace_topology Y (subspace_topology X TX Y) (A i) = subspace_topology X TX (A i)"
            by (rule subspace_topology_trans[OF hAiY])
          have hconnAiY: "top1_connected_on (A i) (subspace_topology Y (subspace_topology X TX Y) (A i))"
            using hconnAi by (simp add: hTopEq[symmetric])

          have hAi_subU_or_V:
            "A i \<subseteq> U \<or> A i \<subseteq> V"
            by (rule Lemma_23_2[OF hTopY hUV hAiY hconnAiY])
          have hpAi: "p \<in> A i"
            using hp hi by blast
          have hpnotV: "p \<notin> V"
            using True hdisj by blast
          show "A i \<subseteq> U"
          proof (rule disjE[OF hAi_subU_or_V])
            assume hsubU: "A i \<subseteq> U"
            show ?thesis by (rule hsubU)
          next
            assume hsubV: "A i \<subseteq> V"
            have "p \<in> V"
              using hsubV hpAi by blast
            thus ?thesis
              using hpnotV by blast
          qed
        qed
        have hYsubU: "Y \<subseteq> U"
          unfolding Y_def using hAllU by blast
        have hVsubU: "V \<subseteq> U"
          using hYsubU hUVY by blast
        have hVemp: "V = {}"
          using hdisj hVsubU by blast
        show False
          using hVne hVemp by blast
      next
        case False
        have hpV: "p \<in> V"
          using hpUorV False by blast
        have hAllV: "\<forall>i\<in>I. A i \<subseteq> V"
        proof (intro ballI)
          fix i assume hi: "i \<in> I"
          have hAiY: "A i \<subseteq> Y"
            unfolding Y_def using hi by blast
          have hconnAi: "top1_connected_on (A i) (subspace_topology X TX (A i))"
            using hconnA hi by blast
          have hTopEq:
            "subspace_topology Y (subspace_topology X TX Y) (A i) = subspace_topology X TX (A i)"
            by (rule subspace_topology_trans[OF hAiY])
          have hconnAiY: "top1_connected_on (A i) (subspace_topology Y (subspace_topology X TX Y) (A i))"
            using hconnAi by (simp add: hTopEq[symmetric])
          have hAi_subU_or_V:
            "A i \<subseteq> U \<or> A i \<subseteq> V"
            by (rule Lemma_23_2[OF hTopY hUV hAiY hconnAiY])
          have hpAi: "p \<in> A i"
            using hp hi by blast
          have hpnotU: "p \<notin> U"
            using hpV hdisj by blast
          show "A i \<subseteq> V"
          proof (rule disjE[OF hAi_subU_or_V])
            assume hsubU: "A i \<subseteq> U"
            have "p \<in> U"
              using hsubU hpAi by blast
            thus ?thesis
              using hpnotU by blast
          next
            assume hsubV: "A i \<subseteq> V"
            show ?thesis by (rule hsubV)
          qed
        qed
        have hYsubV: "Y \<subseteq> V"
          unfolding Y_def using hAllV by blast
        have hUsubV: "U \<subseteq> V"
          using hYsubV hUVY by blast
        have hUemp: "U = {}"
          using hdisj hUsubV by blast
        show False
          using hUne hUemp by blast
      qed
    qed
  qed
qed

(** from \S23 Theorem 23.4 [top1.tex:2651] **)
theorem Theorem_23_4:
  assumes hTX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hBX: "B \<subseteq> X"
  assumes hAB: "A \<subseteq> B"
  assumes hBcl: "B \<subseteq> closure_on X TX A"
  assumes hconnA: "top1_connected_on A (subspace_topology X TX A)"
  shows "top1_connected_on B (subspace_topology X TX B)"
proof -
  have hTopB: "is_topology_on B (subspace_topology X TX B)"
    by (rule subspace_topology_is_topology_on[OF hTX hBX])

  show ?thesis
    unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on B (subspace_topology X TX B)"
      by (rule hTopB)
    show "\<nexists>U V.
        U \<in> subspace_topology X TX B \<and>
        V \<in> subspace_topology X TX B \<and>
        U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = B"
    proof (rule notI)
      assume hsep:
        "\<exists>U V.
          U \<in> subspace_topology X TX B \<and>
          V \<in> subspace_topology X TX B \<and>
          U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = B"
      then obtain C D where hCD: "top1_is_separation_on B (subspace_topology X TX B) C D"
        unfolding top1_is_separation_on_def by blast

	      have hCopen: "C \<in> subspace_topology X TX B"
	        using hCD unfolding top1_is_separation_on_def by simp
	      have hDopen: "D \<in> subspace_topology X TX B"
	        using hCD unfolding top1_is_separation_on_def by simp
	      have hCne: "C \<noteq> {}"
	        using hCD unfolding top1_is_separation_on_def by simp
	      have hDne: "D \<noteq> {}"
	        using hCD unfolding top1_is_separation_on_def by simp
	      have hdisj: "C \<inter> D = {}"
	        using hCD unfolding top1_is_separation_on_def by simp
	      have hCDU: "C \<union> D = B"
	        using hCD unfolding top1_is_separation_on_def by simp

      have hTopEq:
        "subspace_topology B (subspace_topology X TX B) A = subspace_topology X TX A"
        by (rule subspace_topology_trans[OF hAB])

      have hconnA_B: "top1_connected_on A (subspace_topology B (subspace_topology X TX B) A)"
        using hconnA by (simp add: hTopEq[symmetric])

      have hA_subC_or_D: "A \<subseteq> C \<or> A \<subseteq> D"
        by (rule Lemma_23_2[OF hTopB hCD hAB hconnA_B])

      have hD_eq: "D = B - C"
        using hdisj hCDU by blast

      have hC_closed_B: "closedin_on B (subspace_topology X TX B) C"
      proof (rule closedin_intro)
        show "C \<subseteq> B"
          using hCDU by blast
        show "B - C \<in> subspace_topology X TX B"
          using hDopen by (simp add: hD_eq[symmetric])
      qed

      have hclC_B_eq: "closure_on B (subspace_topology X TX B) C = C"
      proof (rule equalityI)
        show "closure_on B (subspace_topology X TX B) C \<subseteq> C"
          by (rule closure_on_subset_of_closed[OF hC_closed_B], rule subset_refl)
        show "C \<subseteq> closure_on B (subspace_topology X TX B) C"
          by (rule subset_closure_on)
      qed

      have hclC_subspace:
        "closure_on B (subspace_topology X TX B) C = closure_on X TX C \<inter> B"
      proof -
        have hCB: "C \<subseteq> B"
          using hCDU by blast
        show ?thesis
          by (rule Theorem_17_4[OF hTX hCB hBX])
      qed

      have hclC_X_eq: "closure_on X TX C \<inter> B = C"
        using hclC_B_eq hclC_subspace by simp

      have hD_disj_clC: "D \<inter> closure_on X TX C = {}"
        using hclC_X_eq hCDU hdisj by blast

      show False
      proof (rule disjE[OF hA_subC_or_D])
        assume hAsubC: "A \<subseteq> C"
        have hclA_sub_clC: "closure_on X TX A \<subseteq> closure_on X TX C"
          by (rule closure_on_mono[OF hAsubC])
        have hB_sub_clC: "B \<subseteq> closure_on X TX C"
          using hBcl hclA_sub_clC by blast
        have hD_sub_clC: "D \<subseteq> closure_on X TX C"
          using hB_sub_clC hCDU by blast
        have hDemp: "D = {}"
          using hD_disj_clC hD_sub_clC by blast
        show False using hDne hDemp by blast
      next
        assume hAsubD: "A \<subseteq> D"
        have hclA_sub_clD: "closure_on X TX A \<subseteq> closure_on X TX D"
          by (rule closure_on_mono[OF hAsubD])
        have hB_sub_clD: "B \<subseteq> closure_on X TX D"
          using hBcl hclA_sub_clD by blast

        have hC_eq: "C = B - D"
          using hdisj hCDU by blast
        have hD_closed_B: "closedin_on B (subspace_topology X TX B) D"
	        proof (rule closedin_intro)
	          show "D \<subseteq> B"
	            using hCDU by blast
	          show "B - D \<in> subspace_topology X TX B"
	            using hCopen by (simp add: hC_eq[symmetric])
	        qed
        have hclD_B_eq: "closure_on B (subspace_topology X TX B) D = D"
        proof (rule equalityI)
          show "closure_on B (subspace_topology X TX B) D \<subseteq> D"
            by (rule closure_on_subset_of_closed[OF hD_closed_B], rule subset_refl)
          show "D \<subseteq> closure_on B (subspace_topology X TX B) D"
            by (rule subset_closure_on)
        qed
	        have hclD_subspace:
	          "closure_on B (subspace_topology X TX B) D = closure_on X TX D \<inter> B"
	        proof -
	          have hDB: "D \<subseteq> B"
	            using hCDU by blast
	          show ?thesis
	            by (rule Theorem_17_4[OF hTX hDB hBX])
	        qed
        have hclD_X_eq: "closure_on X TX D \<inter> B = D"
          using hclD_B_eq hclD_subspace by simp
        have hC_disj_clD: "C \<inter> closure_on X TX D = {}"
          using hclD_X_eq hCDU hdisj by blast
        have hC_sub_clD: "C \<subseteq> closure_on X TX D"
          using hB_sub_clD hCDU by blast
        have hCemp: "C = {}"
          using hC_disj_clD hC_sub_clD by blast
        show False using hCne hCemp by blast
      qed
    qed
  qed
qed

(** from \S23 Theorem 23.5 [top1.tex:2656] **)
theorem Theorem_23_5:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hconn: "top1_connected_on X TX"
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
  shows "top1_connected_on (f ` X) (subspace_topology Y TY (f ` X))"
proof -
  have hmap: "\<forall>x\<in>X. f x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hfXsub: "f ` X \<subseteq> Y"
    apply (rule subsetI)
    apply (erule imageE)
    apply (simp only: hmap)
    done

  have hsub_top: "is_topology_on (f ` X) (subspace_topology Y TY (f ` X))"
    by (rule subspace_topology_is_topology_on[OF hTY hfXsub])

  have hconn_nosep:
    "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    using hconn unfolding top1_connected_on_def by blast

  show ?thesis
    unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on (f ` X) (subspace_topology Y TY (f ` X))"
      by (rule hsub_top)
    show "\<nexists>U V.
        U \<in> subspace_topology Y TY (f ` X) \<and>
        V \<in> subspace_topology Y TY (f ` X) \<and>
        U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = f ` X"
    proof (rule notI)
      assume hsep:
        "\<exists>U V.
            U \<in> subspace_topology Y TY (f ` X) \<and>
            V \<in> subspace_topology Y TY (f ` X) \<and>
            U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = f ` X"
      then obtain U V where
        hU: "U \<in> subspace_topology Y TY (f ` X)" and
        hV: "V \<in> subspace_topology Y TY (f ` X)" and
        hUne: "U \<noteq> {}" and
        hVne: "V \<noteq> {}" and
        hdisj: "U \<inter> V = {}" and
        hunion: "U \<union> V = f ` X"
        by blast

      obtain W1 where hW1: "W1 \<in> TY" and hUeq: "U = f ` X \<inter> W1"
        using hU unfolding subspace_topology_def by blast
      obtain W2 where hW2: "W2 \<in> TY" and hVeq: "V = f ` X \<inter> W2"
        using hV unfolding subspace_topology_def by blast

      define P where "P = {x \<in> X. f x \<in> W1}"
      define Q where "Q = {x \<in> X. f x \<in> W2}"

      have hPopen: "P \<in> TX"
      proof -
        have "{x \<in> X. f x \<in> W1} \<in> TX"
          using hcont hW1 unfolding top1_continuous_map_on_def by blast
        thus ?thesis unfolding P_def by simp
      qed
      have hQopen: "Q \<in> TX"
      proof -
        have "{x \<in> X. f x \<in> W2} \<in> TX"
          using hcont hW2 unfolding top1_continuous_map_on_def by blast
        thus ?thesis unfolding Q_def by simp
      qed

      have hPne: "P \<noteq> {}"
      proof
        assume hPemp: "P = {}"
        have exyU: "\<exists>y. y \<in> U"
          using hUne by (simp add: ex_in_conv)
        obtain y where hyU: "y \<in> U" using exyU by blast
        have hy_int: "y \<in> f ` X \<inter> W1"
          using hyU by (simp only: hUeq)
        have hyfx: "y \<in> f ` X"
          by (rule IntD1[OF hy_int])
        have hyW1: "y \<in> W1"
          by (rule IntD2[OF hy_int])
        obtain x where hxX: "x \<in> X" and hy: "y = f x"
          using hyfx by blast
        have hxP: "x \<in> P"
          unfolding P_def using hxX hyW1 hy by blast
        show False using hxP hPemp by blast
      qed
      have hQne: "Q \<noteq> {}"
      proof
        assume hQemp: "Q = {}"
        have exyV: "\<exists>y. y \<in> V"
          using hVne by (simp add: ex_in_conv)
        obtain y where hyV: "y \<in> V" using exyV by blast
        have hy_int: "y \<in> f ` X \<inter> W2"
          using hyV by (simp only: hVeq)
        have hyfx: "y \<in> f ` X"
          by (rule IntD1[OF hy_int])
        have hyW2: "y \<in> W2"
          by (rule IntD2[OF hy_int])
        obtain x where hxX: "x \<in> X" and hy: "y = f x"
          using hyfx by blast
        have hxQ: "x \<in> Q"
          unfolding Q_def using hxX hyW2 hy by blast
        show False using hxQ hQemp by blast
      qed

      have hdisjPQ: "P \<inter> Q = {}"
      proof (rule equalityI)
        show "P \<inter> Q \<subseteq> {}"
        proof (rule subsetI)
          fix x
          assume hx: "x \<in> P \<inter> Q"
          have hxP: "x \<in> P" and hxQ: "x \<in> Q" using hx by blast+
          have hxP_conj: "x \<in> X \<and> f x \<in> W1"
            using hxP by (simp only: P_def mem_Collect_eq)
          have hxX: "x \<in> X"
            using hxP_conj by (rule conjunct1)
          have hfxW1: "f x \<in> W1"
            using hxP_conj by (rule conjunct2)
          have hxQ_conj: "x \<in> X \<and> f x \<in> W2"
            using hxQ by (simp only: Q_def mem_Collect_eq)
          have hfxW2: "f x \<in> W2"
            using hxQ_conj by (rule conjunct2)
          have hfxU: "f x \<in> U"
            unfolding hUeq
            apply (rule IntI)
             apply (rule imageI)
             apply (rule hxX)
            apply (rule hfxW1)
            done
          have hfxV: "f x \<in> V"
            unfolding hVeq
            apply (rule IntI)
             apply (rule imageI)
             apply (rule hxX)
            apply (rule hfxW2)
            done
          have "f x \<in> U \<inter> V"
            apply (rule IntI)
             apply (rule hfxU)
            apply (rule hfxV)
            done
          hence False using hdisj by blast
          thus "x \<in> {}" by blast
        qed
        show "{} \<subseteq> P \<inter> Q" by simp
      qed

      have hunionPQ: "P \<union> Q = X"
      proof (rule equalityI)
        show "P \<union> Q \<subseteq> X" unfolding P_def Q_def by blast
        show "X \<subseteq> P \<union> Q"
        proof (rule subsetI)
          fix x
          assume hxX: "x \<in> X"
          have hfxUorV: "f x \<in> U \<or> f x \<in> V"
          proof -
            have hfx: "f x \<in> f ` X" using hxX by blast
            have "f x \<in> U \<union> V"
              using hunion hfx by simp
            thus ?thesis by blast
          qed
          show "x \<in> P \<union> Q"
          proof (rule disjE[OF hfxUorV])
            assume hfxU: "f x \<in> U"
            have hfx_int: "f x \<in> f ` X \<inter> W1"
              using hfxU by (simp only: hUeq)
            have hfxW1: "f x \<in> W1"
              by (rule IntD2[OF hfx_int])
            have hxP: "x \<in> P"
              unfolding P_def
              apply (simp only: mem_Collect_eq)
              apply (intro conjI)
               apply (rule hxX)
              apply (rule hfxW1)
              done
            show "x \<in> P \<union> Q"
              apply (rule UnI1)
              apply (rule hxP)
              done
          next
            assume hfxV: "f x \<in> V"
            have hfx_int: "f x \<in> f ` X \<inter> W2"
              using hfxV by (simp only: hVeq)
            have hfxW2: "f x \<in> W2"
              by (rule IntD2[OF hfx_int])
            have hxQ: "x \<in> Q"
              unfolding Q_def
              apply (simp only: mem_Collect_eq)
              apply (intro conjI)
               apply (rule hxX)
              apply (rule hfxW2)
              done
            show "x \<in> P \<union> Q"
              apply (rule UnI2)
              apply (rule hxQ)
              done
          qed
        qed
      qed

      have False
        using hconn_nosep hPopen hQopen hPne hQne hdisjPQ hunionPQ by blast
      thus False ..
    qed
  qed
qed

(** Helper: the identity map is continuous. **)
lemma top1_continuous_map_on_id:
  assumes hTX: "is_topology_on X TX"
  shows "top1_continuous_map_on X TX X TX id"
proof -
  have hX: "X \<in> TX"
    using hTX unfolding is_topology_on_def by blast
  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. id x \<in> X"
      by simp
    show "\<forall>U\<in>TX. {x \<in> X. id x \<in> U} \<in> TX"
	    proof (intro ballI)
	      fix U assume hU: "U \<in> TX"
	      have hEq: "{x \<in> X. id x \<in> U} = X \<inter> U"
	      proof (rule set_eqI)
	        fix x
	        show "x \<in> {x \<in> X. id x \<in> U} \<longleftrightarrow> x \<in> X \<inter> U"
	          by simp
	      qed
	      show "{x \<in> X. id x \<in> U} \<in> TX"
	        apply (subst hEq)
	        apply (rule topology_inter2[OF hTX hX hU])
	        done
    qed
  qed
qed

(** Helper: local rectangle refinement for product-topology opens. **)
lemma top1_product_open_contains_rect:
  assumes hW: "W \<in> product_topology_on TX TY"
  assumes hp: "p \<in> W"
  obtains U V where "U \<in> TX" and "V \<in> TY" and "p \<in> U \<times> V" and "U \<times> V \<subseteq> W"
proof -
  have hcov: "\<forall>x\<in>W. \<exists>b\<in>product_basis TX TY. x \<in> b \<and> b \<subseteq> W"
    using hW unfolding product_topology_on_def topology_generated_by_basis_def by blast
  obtain b where hb: "b \<in> product_basis TX TY" and hp_b: "p \<in> b" and hb_sub: "b \<subseteq> W"
    using hcov hp by blast
  obtain U V where hU: "U \<in> TX" and hV: "V \<in> TY" and hb_eq: "b = U \<times> V"
    using hb unfolding product_basis_def by blast
  have hpUV: "p \<in> U \<times> V"
    using hp_b hb_eq by simp
  have hsub: "U \<times> V \<subseteq> W"
    using hb_sub hb_eq by simp
  show ?thesis
    by (rule that[OF hU hV hpUV hsub])
qed

(** Constant maps are continuous (restricted to carriers). **)
lemma top1_continuous_map_on_const:
  assumes hTA: "is_topology_on A TA"
  assumes hTX: "is_topology_on X TX"
  assumes hx0: "x0 \<in> X"
  shows "top1_continuous_map_on A TA X TX (\<lambda>a. x0)"
proof -
  have empty_TA: "{} \<in> TA"
    using hTA unfolding is_topology_on_def by blast
  have A_TA: "A \<in> TA"
    using hTA unfolding is_topology_on_def by blast
  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>a\<in>A. (\<lambda>a. x0) a \<in> X"
      using hx0 by simp
    show "\<forall>U\<in>TX. {a \<in> A. (\<lambda>a. x0) a \<in> U} \<in> TA"
    proof (intro ballI)
      fix U assume hU: "U \<in> TX"
      have hEq: "{a \<in> A. (\<lambda>a. x0) a \<in> U} = (if x0 \<in> U then A else {})"
      proof (rule set_eqI)
        fix a
        show "a \<in> {a \<in> A. (\<lambda>a. x0) a \<in> U} \<longleftrightarrow> a \<in> (if x0 \<in> U then A else {})"
          by simp
      qed
      show "{a \<in> A. (\<lambda>a. x0) a \<in> U} \<in> TA"
      proof (cases "x0 \<in> U")
        case True
        show ?thesis
          using A_TA hEq True by simp
      next
        case False
        show ?thesis
          using empty_TA hEq False by simp
      qed
    qed
  qed
qed

(** Sections of the product are continuous: y \<mapsto> (x0,y). **)
lemma top1_continuous_map_on_section2:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hx0: "x0 \<in> X"
  shows "top1_continuous_map_on Y TY (X \<times> Y) (product_topology_on TX TY) (\<lambda>y. (x0, y))"
proof -
  have hpi1: "top1_continuous_map_on Y TY X TX (pi1 \<circ> (\<lambda>y. (x0, y)))"
  proof -
    have hEq: "(pi1 \<circ> (\<lambda>y. (x0, y))) = (\<lambda>y. x0)"
    proof (rule ext)
      fix y
      show "(pi1 \<circ> (\<lambda>y. (x0, y))) y = (\<lambda>y. x0) y"
        unfolding o_def pi1_def by simp
    qed
    have hconst: "top1_continuous_map_on Y TY X TX (\<lambda>y. x0)"
      by (rule top1_continuous_map_on_const[OF hTY hTX hx0])
    show ?thesis
      using hconst by (simp add: hEq)
  qed
  have hpi2: "top1_continuous_map_on Y TY Y TY (pi2 \<circ> (\<lambda>y. (x0, y)))"
  proof -
    have hEq: "(pi2 \<circ> (\<lambda>y. (x0, y))) = id"
    proof (rule ext)
      fix y
      show "(pi2 \<circ> (\<lambda>y. (x0, y))) y = id y"
        unfolding o_def pi2_def by simp
    qed
    have hid: "top1_continuous_map_on Y TY Y TY id"
      by (rule top1_continuous_map_on_id[OF hTY])
    show ?thesis
      using hid by (simp add: hEq)
  qed
  show ?thesis
    using Theorem_18_4[OF hTY hTX hTY] hpi1 hpi2 by blast
qed

lemma top1_section_preimage_open:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hW: "W \<in> product_topology_on TX TY"
  assumes hx0: "x0 \<in> X"
  shows "{y \<in> Y. (x0, y) \<in> W} \<in> TY"
proof -
  have hcont: "top1_continuous_map_on Y TY (X \<times> Y) (product_topology_on TX TY) (\<lambda>y. (x0, y))"
    by (rule top1_continuous_map_on_section2[OF hTX hTY hx0])
  have hpre: "\<forall>V\<in>product_topology_on TX TY. {y\<in>Y. (\<lambda>y. (x0, y)) y \<in> V} \<in> TY"
    using hcont unfolding top1_continuous_map_on_def by blast
  have "{y\<in>Y. (\<lambda>y. (x0, y)) y \<in> W} \<in> TY"
    using hpre hW by blast
  thus ?thesis
    by simp
qed

(** from \S23 Theorem 23.6 [top1.tex:~2664] **)
theorem Theorem_23_6:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hconnX: "top1_connected_on X TX"
  assumes hconnY: "top1_connected_on Y TY"
  shows "top1_connected_on (X \<times> Y) (product_topology_on TX TY)"
proof -
  have hTopXY: "is_topology_on (X \<times> Y) (product_topology_on TX TY)"
    by (rule product_topology_on_is_topology_on[OF hTX hTY])

  have hNoSepX:
    "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    using hconnX unfolding top1_connected_on_def by blast
  have hNoSepY:
    "\<nexists>U V. U \<in> TY \<and> V \<in> TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
    using hconnY unfolding top1_connected_on_def by blast

  show ?thesis
    unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on (X \<times> Y) (product_topology_on TX TY)"
      by (rule hTopXY)

    show "\<nexists>U V.
        U \<in> product_topology_on TX TY \<and>
        V \<in> product_topology_on TX TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X \<times> Y"
    proof (rule notI)
      assume hsep:
        "\<exists>U V.
          U \<in> product_topology_on TX TY \<and>
          V \<in> product_topology_on TX TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X \<times> Y"
      then obtain U V where
        hUopen: "U \<in> product_topology_on TX TY" and
        hVopen: "V \<in> product_topology_on TX TY" and
        hUne: "U \<noteq> {}" and
        hVne: "V \<noteq> {}" and
        hdisj: "U \<inter> V = {}" and
        hUV: "U \<union> V = X \<times> Y"
        by blast

      show False
      proof (cases "X = {} \<or> Y = {}")
        case True
        have "X \<times> Y = {}"
          using True by blast
        hence "U \<union> V = {}"
          using hUV by simp
        hence "U = {}"
          by blast
        thus False
          using hUne by blast
      next
        case False
        have hXne: "X \<noteq> {}" and hYne: "Y \<noteq> {}"
          using False by blast+
        obtain y0 where hy0: "y0 \<in> Y"
          using hYne by blast

        have hUsubXY: "U \<subseteq> X \<times> Y"
          using hUV by blast
        have hVsubXY: "V \<subseteq> X \<times> Y"
          using hUV by blast

        define UX where "UX = (\<lambda>x. {y \<in> Y. (x, y) \<in> U})"
        define VX where "VX = (\<lambda>x. {y \<in> Y. (x, y) \<in> V})"

        have hUX_open: "\<forall>x0\<in>X. UX x0 \<in> TY"
        proof (intro ballI)
          fix x0 assume hx0: "x0 \<in> X"
          have "{y \<in> Y. (x0, y) \<in> U} \<in> TY"
            by (rule top1_section_preimage_open[OF hTX hTY hUopen hx0])
          thus "UX x0 \<in> TY"
          proof -
            have hEq: "UX x0 = {y \<in> Y. (x0, y) \<in> U}"
              unfolding UX_def by simp
            show ?thesis
              by (subst hEq) (rule \<open>{y \<in> Y. (x0, y) \<in> U} \<in> TY\<close>)
          qed
        qed
        have hVX_open: "\<forall>x0\<in>X. VX x0 \<in> TY"
        proof (intro ballI)
          fix x0 assume hx0: "x0 \<in> X"
          have "{y \<in> Y. (x0, y) \<in> V} \<in> TY"
            by (rule top1_section_preimage_open[OF hTX hTY hVopen hx0])
          thus "VX x0 \<in> TY"
          proof -
            have hEq: "VX x0 = {y \<in> Y. (x0, y) \<in> V}"
              unfolding VX_def by simp
            show ?thesis
              by (subst hEq) (rule \<open>{y \<in> Y. (x0, y) \<in> V} \<in> TY\<close>)
          qed
        qed

        have hUV_sections:
          "\<forall>x0\<in>X. (UX x0 \<inter> VX x0 = {}) \<and> (UX x0 \<union> VX x0 = Y)"
        proof (intro ballI conjI)
          fix x0 assume hx0: "x0 \<in> X"
          show "UX x0 \<inter> VX x0 = {}"
          proof (rule equalityI)
            show "UX x0 \<inter> VX x0 \<subseteq> {}"
            proof (rule subsetI)
              fix y assume hy: "y \<in> UX x0 \<inter> VX x0"
              have hyU: "y \<in> UX x0" and hyV: "y \<in> VX x0"
                using hy by blast+
              have hxyU: "(x0, y) \<in> U"
                using hyU unfolding UX_def by blast
              have hxyV: "(x0, y) \<in> V"
                using hyV unfolding VX_def by blast
              have "(x0, y) \<in> U \<inter> V"
                using hxyU hxyV by blast
              hence False
                using hdisj by blast
              thus "y \<in> {}"
                by blast
            qed
            show "{} \<subseteq> UX x0 \<inter> VX x0"
              by simp
          qed
          show "UX x0 \<union> VX x0 = Y"
          proof (rule equalityI)
            show "UX x0 \<union> VX x0 \<subseteq> Y"
              unfolding UX_def VX_def by blast
            show "Y \<subseteq> UX x0 \<union> VX x0"
            proof (rule subsetI)
              fix y assume hyY: "y \<in> Y"
              have "(x0, y) \<in> X \<times> Y"
                using hx0 hyY by blast
              hence "(x0, y) \<in> U \<union> V"
                using hUV by simp
              hence "(x0, y) \<in> U \<or> (x0, y) \<in> V"
                by blast
              thus "y \<in> UX x0 \<union> VX x0"
                unfolding UX_def VX_def using hyY by blast
            qed
          qed
        qed

        have hUX_or_VX_empty: "\<forall>x0\<in>X. UX x0 = {} \<or> VX x0 = {}"
        proof (intro ballI)
          fix x0 assume hx0: "x0 \<in> X"
          have hUX: "UX x0 \<in> TY"
            using hUX_open hx0 by blast
          have hVX: "VX x0 \<in> TY"
            using hVX_open hx0 by blast
          have hdisj0: "UX x0 \<inter> VX x0 = {}"
            using hUV_sections hx0 by blast
          have hcov0: "UX x0 \<union> VX x0 = Y"
            using hUV_sections hx0 by blast
          show "UX x0 = {} \<or> VX x0 = {}"
          proof (rule classical)
            assume hnot: "\<not> (UX x0 = {} \<or> VX x0 = {})"
            have hUXne: "UX x0 \<noteq> {}" and hVXne: "VX x0 \<noteq> {}"
              using hnot by blast+
            have "\<exists>U V. U \<in> TY \<and> V \<in> TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
              apply (rule exI[where x="UX x0"])
              apply (rule exI[where x="VX x0"])
              using hUX hVX hUXne hVXne hdisj0 hcov0 by blast
            thus "UX x0 = {} \<or> VX x0 = {}"
              using hNoSepY by blast
          qed
        qed

        define A where "A = {x \<in> X. UX x \<noteq> {}}"
        define B where "B = {x \<in> X. VX x \<noteq> {}}"

        have hA_nonempty: "A \<noteq> {}"
        proof -
          obtain p where hpU: "p \<in> U"
            using hUne by blast
	          obtain x y where hp: "p = (x, y)"
	            by (cases p) simp
	          have "(x, y) \<in> X \<times> Y"
	          proof -
	            have "(x, y) \<in> U"
	              using hpU hp by simp
	            hence "(x, y) \<in> X \<times> Y"
	              using hUsubXY by blast
	            thus ?thesis .
	          qed
	          hence hxX: "x \<in> X" and hyY: "y \<in> Y"
	            by blast+
	          have "y \<in> UX x"
	            unfolding UX_def using hyY hpU hp by simp
          hence "UX x \<noteq> {}"
            by blast
          hence "x \<in> A"
            unfolding A_def using hxX by blast
          thus ?thesis
            by blast
        qed
        have hB_nonempty: "B \<noteq> {}"
        proof -
          obtain p where hpV: "p \<in> V"
            using hVne by blast
	          obtain x y where hp: "p = (x, y)"
	            by (cases p) simp
	          have "(x, y) \<in> X \<times> Y"
	          proof -
	            have "(x, y) \<in> V"
	              using hpV hp by simp
	            hence "(x, y) \<in> X \<times> Y"
	              using hVsubXY by blast
	            thus ?thesis .
	          qed
	          hence hxX: "x \<in> X" and hyY: "y \<in> Y"
	            by blast+
          have "y \<in> VX x"
            unfolding VX_def using hyY hpV hp by simp
          hence "VX x \<noteq> {}"
            by blast
          hence "x \<in> B"
            unfolding B_def using hxX by blast
          thus ?thesis
            by blast
        qed

        have hA_open: "A \<in> TX"
        proof -
          have union_T: "\<forall>S. S \<subseteq> TX \<longrightarrow> \<Union>S \<in> TX"
            using hTX unfolding is_topology_on_def by blast
          define SA where "SA = {U0 \<in> TX. U0 \<subseteq> A}"
          have hSA_sub: "SA \<subseteq> TX"
            unfolding SA_def by blast
          have hUnion_SA: "\<Union>SA \<in> TX"
            using union_T hSA_sub by blast
          have hEq: "A = \<Union>SA"
          proof (rule subset_antisym)
            show "A \<subseteq> \<Union>SA"
            proof (rule subsetI)
              fix x assume hxA: "x \<in> A"
              have hxX: "x \<in> X" and hUXne: "UX x \<noteq> {}"
                using hxA unfolding A_def by blast+
              obtain y where hy: "y \<in> UX x"
                using hUXne by blast
              have hyY: "y \<in> Y" and hxyU: "(x, y) \<in> U"
                using hy unfolding UX_def by blast+
              obtain U0 V0 where hU0: "U0 \<in> TX" and hV0: "V0 \<in> TY"
                and hpUV: "(x, y) \<in> U0 \<times> V0" and hsub: "U0 \<times> V0 \<subseteq> U"
                by (rule top1_product_open_contains_rect[OF hUopen], rule hxyU)
              have hxU0: "x \<in> U0"
                using hpUV by blast
              have hyV0: "y \<in> V0"
                using hpUV by blast
              have hU0subA: "U0 \<subseteq> A"
              proof (rule subsetI)
                fix x' assume hx': "x' \<in> U0"
                have "(x', y) \<in> U0 \<times> V0"
                  using hx' hyV0 by blast
                hence "(x', y) \<in> U"
                  using hsub by blast
                hence "y \<in> UX x'"
                  unfolding UX_def using hyY by blast
                hence "UX x' \<noteq> {}"
                  by blast
                show "x' \<in> A"
                proof -
                  have "(x', y) \<in> U0 \<times> V0"
                    using hx' hyV0 by blast
                  hence "(x', y) \<in> U"
                    using hsub by blast
                  hence "(x', y) \<in> X \<times> Y"
                    using hUsubXY by blast
                  hence "x' \<in> X"
                    by blast
                  thus ?thesis
                    unfolding A_def using \<open>UX x' \<noteq> {}\<close> by blast
                qed
              qed
              have hU0memSA: "U0 \<in> SA"
                unfolding SA_def using hU0 hU0subA by blast
              show "x \<in> \<Union>SA"
                using hU0memSA hxU0 by blast
            qed
            show "\<Union>SA \<subseteq> A"
            proof (rule subsetI)
              fix x assume hx: "x \<in> \<Union>SA"
              then obtain U0 where hU0: "U0 \<in> SA" and hxU0: "x \<in> U0"
                by blast
              have "U0 \<subseteq> A"
                using hU0 unfolding SA_def by blast
              thus "x \<in> A"
                using hxU0 by blast
            qed
          qed
          show "A \<in> TX"
            by (subst hEq) (rule hUnion_SA)
        qed

        have hB_open: "B \<in> TX"
        proof -
          have union_T: "\<forall>S. S \<subseteq> TX \<longrightarrow> \<Union>S \<in> TX"
            using hTX unfolding is_topology_on_def by blast
          define SB where "SB = {U0 \<in> TX. U0 \<subseteq> B}"
          have hSB_sub: "SB \<subseteq> TX"
            unfolding SB_def by blast
          have hUnion_SB: "\<Union>SB \<in> TX"
            using union_T hSB_sub by blast
          have hEq: "B = \<Union>SB"
          proof (rule subset_antisym)
            show "B \<subseteq> \<Union>SB"
            proof (rule subsetI)
              fix x assume hxB: "x \<in> B"
              have hxX: "x \<in> X" and hVXne: "VX x \<noteq> {}"
                using hxB unfolding B_def by blast+
              obtain y where hy: "y \<in> VX x"
                using hVXne by blast
              have hyY: "y \<in> Y" and hxyV: "(x, y) \<in> V"
                using hy unfolding VX_def by blast+
              obtain U0 V0 where hU0: "U0 \<in> TX" and hV0: "V0 \<in> TY"
                and hpUV: "(x, y) \<in> U0 \<times> V0" and hsub: "U0 \<times> V0 \<subseteq> V"
                by (rule top1_product_open_contains_rect[OF hVopen], rule hxyV)
              have hxU0: "x \<in> U0"
                using hpUV by blast
              have hyV0: "y \<in> V0"
                using hpUV by blast
              have hU0subB: "U0 \<subseteq> B"
              proof (rule subsetI)
                fix x' assume hx': "x' \<in> U0"
                have "(x', y) \<in> U0 \<times> V0"
                  using hx' hyV0 by blast
                hence "(x', y) \<in> V"
                  using hsub by blast
                hence "y \<in> VX x'"
                  unfolding VX_def using hyY by blast
                hence "VX x' \<noteq> {}"
                  by blast
                have "(x', y) \<in> X \<times> Y"
                  using hVsubXY \<open>(x', y) \<in> V\<close> by blast
                hence "x' \<in> X"
                  by blast
                show "x' \<in> B"
                  unfolding B_def using \<open>x' \<in> X\<close> \<open>VX x' \<noteq> {}\<close> by blast
              qed
              have hU0memSB: "U0 \<in> SB"
                unfolding SB_def using hU0 hU0subB by blast
              show "x \<in> \<Union>SB"
                using hU0memSB hxU0 by blast
            qed
            show "\<Union>SB \<subseteq> B"
            proof (rule subsetI)
              fix x assume hx: "x \<in> \<Union>SB"
              then obtain U0 where hU0: "U0 \<in> SB" and hxU0: "x \<in> U0"
                by blast
              have "U0 \<subseteq> B"
                using hU0 unfolding SB_def by blast
              thus "x \<in> B"
                using hxU0 by blast
            qed
          qed
          show "B \<in> TX"
            by (subst hEq) (rule hUnion_SB)
        qed

        have hA_subX: "A \<subseteq> X"
          unfolding A_def by blast
        have hB_subX: "B \<subseteq> X"
          unfolding B_def by blast

        have hAunionB: "A \<union> B = X"
        proof (rule equalityI)
          show "A \<union> B \<subseteq> X"
            using hA_subX hB_subX by blast
          show "X \<subseteq> A \<union> B"
          proof (rule subsetI)
            fix x assume hxX: "x \<in> X"
            have "(x, y0) \<in> X \<times> Y"
              using hxX hy0 by blast
            hence "(x, y0) \<in> U \<union> V"
              using hUV by simp
            hence "(x, y0) \<in> U \<or> (x, y0) \<in> V"
              by blast
            thus "x \<in> A \<union> B"
            proof
              assume hxyU: "(x, y0) \<in> U"
              have "y0 \<in> UX x"
                unfolding UX_def using hy0 hxyU by blast
              hence "UX x \<noteq> {}"
                by blast
              hence "x \<in> A"
                unfolding A_def using hxX by blast
              thus ?thesis
                by blast
            next
              assume hxyV: "(x, y0) \<in> V"
              have "y0 \<in> VX x"
                unfolding VX_def using hy0 hxyV by blast
              hence "VX x \<noteq> {}"
                by blast
              hence "x \<in> B"
                unfolding B_def using hxX by blast
              thus ?thesis
                by blast
            qed
          qed
        qed

        have hAdisjB: "A \<inter> B = {}"
        proof (rule equalityI)
          show "A \<inter> B \<subseteq> {}"
          proof (rule subsetI)
            fix x assume hx: "x \<in> A \<inter> B"
            have hxA: "x \<in> A" and hxB: "x \<in> B"
              using hx by blast+
            have hxX: "x \<in> X"
              using hxA unfolding A_def by blast
            have hUXne: "UX x \<noteq> {}"
              using hxA unfolding A_def by blast
            have hVXne: "VX x \<noteq> {}"
              using hxB unfolding B_def by blast
            have "UX x = {} \<or> VX x = {}"
              using hUX_or_VX_empty hxX by blast
            thus "x \<in> {}"
              using hUXne hVXne by blast
          qed
          show "{} \<subseteq> A \<inter> B"
            by simp
        qed

        have "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
          apply (rule exI[where x=A])
          apply (rule exI[where x=B])
          using hA_open hB_open hA_nonempty hB_nonempty hAdisjB hAunionB by blast
        thus False
          using hNoSepX by blast
      qed
    qed
  qed
qed

(* proof -
  have hTopXY: "is_topology_on (X \<times> Y) (product_topology_on TX TY)"
    by (rule product_topology_on_is_topology_on[OF hTX hTY])

  have hNoSepX:
    "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    using hconnX unfolding top1_connected_on_def by blast
  have hNoSepY:
    "\<nexists>U V. U \<in> TY \<and> V \<in> TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = Y"
    using hconnY unfolding top1_connected_on_def by blast

  show ?thesis
    unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on (X \<times> Y) (product_topology_on TX TY)"
      by (rule hTopXY)

    show "\<nexists>U V.
        U \<in> product_topology_on TX TY \<and>
        V \<in> product_topology_on TX TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X \<times> Y"
    proof (rule notI)
      assume hsep:
        "\<exists>U V.
          U \<in> product_topology_on TX TY \<and>
          V \<in> product_topology_on TX TY \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X \<times> Y"
      then obtain U V where
        hUopen: "U \<in> product_topology_on TX TY" and
        hVopen: "V \<in> product_topology_on TX TY" and
        hUne: "U \<noteq> {}" and
        hVne: "V \<noteq> {}" and
        hdisj: "U \<inter> V = {}" and
        hUV: "U \<union> V = X \<times> Y"
        by blast

      have hUsubXY: "U \<subseteq> X \<times> Y"
        using hUV by blast
      have hVsubXY: "V \<subseteq> X \<times> Y"
        using hUV by blast

      show False
      proof (cases "X = {} \<or> Y = {}")
        case True
        have "X \<times> Y = {}"
          using True by blast
        hence "U \<union> V = {}"
          using hUV by simp
        hence "U = {}"
          by blast
        thus False
          using hUne by blast
      next
        case False
        have hXne: "X \<noteq> {}" and hYne: "Y \<noteq> {}"
          using False by blast+
        obtain y0 where hy0: "y0 \<in> Y"
          using hYne by blast

        define UX where "UX x = {y \<in> Y. (x, y) \<in> U}"
        define VX where "VX x = {y \<in> Y. (x, y) \<in> V}"
        define A where "A = {x \<in> X. UX x \<noteq> {}}"
        define B where "B = {x \<in> X. VX x \<noteq> {}}"

        have hXmem: "X \<in> TX"
          using hTX unfolding is_topology_on_def by blast
        have hYmem: "Y \<in> TY"
          using hTY unfolding is_topology_on_def by blast

        have cont_const_X:
          "\<forall>x0\<in>X. top1_continuous_map_on Y TY X TX (\<lambda>y. x0)"
        proof (intro ballI)
          fix x0 assume hx0: "x0 \<in> X"
          show "top1_continuous_map_on Y TY X TX (\<lambda>y. x0)"
            unfolding top1_continuous_map_on_def
          proof (intro conjI)
            show "\<forall>y\<in>Y. (\<lambda>y. x0) y \<in> X"
              using hx0 by simp
            show "\<forall>U\<in>TX. {y \<in> Y. (\<lambda>y. x0) y \<in> U} \<in> TY"
            proof (intro ballI)
              fix U assume hU: "U \<in> TX"
              have empty_TY: "{} \<in> TY"
                using hTY unfolding is_topology_on_def by blast
              have Y_TY: "Y \<in> TY"
                using hTY unfolding is_topology_on_def by blast
              have hEq: "{y \<in> Y. (\<lambda>y. x0) y \<in> U} = (if x0 \<in> U then Y else {})"
              proof (rule set_eqI)
                fix y
                show "y \<in> {y \<in> Y. (\<lambda>y. x0) y \<in> U} \<longleftrightarrow> y \<in> (if x0 \<in> U then Y else {})"
                  by simp
              qed
              show "{y \<in> Y. (\<lambda>y. x0) y \<in> U} \<in> TY"
              proof (cases "x0 \<in> U")
                case True
                show ?thesis
                  using Y_TY hEq True by simp
              next
                case False
                show ?thesis
                  using empty_TY hEq False by simp
              qed
            qed
          qed
        qed
        have cont_id_Y: "top1_continuous_map_on Y TY Y TY id"
          by (rule top1_continuous_map_on_id[OF hTY])

        have cont_pair:
          "\<forall>x0\<in>X. top1_continuous_map_on Y TY (X \<times> Y) (product_topology_on TX TY) (\<lambda>y. (x0, y))"
        proof (intro ballI)
          fix x0 assume hx0: "x0 \<in> X"
          have hpi1: "top1_continuous_map_on Y TY X TX (pi1 \<circ> (\<lambda>y. (x0, y)))"
	          proof -
	            have hEq: "(pi1 \<circ> (\<lambda>y. (x0, y))) = (\<lambda>y. x0)"
	              unfolding o_def pi1_def by simp
	            show ?thesis
	            proof -
	              have hconst: "top1_continuous_map_on Y TY X TX (\<lambda>y. x0)"
	                using cont_const_X hx0 by blast
	              show ?thesis
	                using hconst by (simp add: hEq)
	            qed
	          qed
		          have hpi2: "top1_continuous_map_on Y TY Y TY (pi2 \<circ> (\<lambda>y. (x0, y)))"
		          proof -
		            have hEq: "(pi2 \<circ> (\<lambda>y. (x0, y))) = id"
		            proof (rule ext)
		              fix y
		              show "(pi2 \<circ> (\<lambda>y. (x0, y))) y = id y"
		                unfolding o_def pi2_def by simp
		            qed
		            show ?thesis
		              using cont_id_Y by (simp add: hEq)
		          qed
          show "top1_continuous_map_on Y TY (X \<times> Y) (product_topology_on TX TY) (\<lambda>y. (x0, y))"
            using Theorem_18_4[OF hTY hTX hTY] hpi1 hpi2 by blast
        qed

        have hUX_open: "\<forall>x0\<in>X. UX x0 \<in> TY"
	        proof (intro ballI)
	          fix x0 assume hx0: "x0 \<in> X"
	          have hcont: "top1_continuous_map_on Y TY (X \<times> Y) (product_topology_on TX TY) (\<lambda>y. (x0, y))"
	            using cont_pair hx0 by blast
		          have hpre: "{y \<in> Y. (\<lambda>y. (x0, y)) y \<in> U} \<in> TY"
		            using hcont hUopen unfolding top1_continuous_map_on_def by blast
			          have hpre': "{y \<in> Y. (x0, y) \<in> U} \<in> TY"
			            using hpre by simp
			          show "UX x0 \<in> TY"
			          proof -
			            have hEq: "UX x0 = {y \<in> Y. (x0, y) \<in> U}"
			              unfolding UX_def by simp
			            show ?thesis
			              by (subst hEq) (rule hpre')
			          qed
			        qed
			        have hVX_open: "\<forall>x0\<in>X. VX x0 \<in> TY"
			        proof (intro ballI)
			          fix x0 assume hx0: "x0 \<in> X"
		          have hcont: "top1_continuous_map_on Y TY (X \<times> Y) (product_topology_on TX TY) (\<lambda>y. (x0, y))"
		            using cont_pair hx0 by blast
		          have hpre: "{y \<in> Y. (\<lambda>y. (x0, y)) y \<in> V} \<in> TY"
		            using hcont hVopen unfolding top1_continuous_map_on_def by blast
			          have hpre': "{y \<in> Y. (x0, y) \<in> V} \<in> TY"
			            using hpre by simp
			          show "VX x0 \<in> TY"
			          proof -
			            have hEq: "VX x0 = {y \<in> Y. (x0, y) \<in> V}"
			              unfolding VX_def by simp
			            show ?thesis
			              by (subst hEq) (rule hpre')
			          qed
			        qed

        have hUV_sections:
          "\<forall>x0\<in>X. (UX x0 \<inter> VX x0 = {}) \<and> (UX x0 \<union> VX x0 = Y)"
        proof (intro ballI conjI)
          fix x0 assume hx0: "x0 \<in> X"
          show "UX x0 \<inter> VX x0 = {}"
          proof (rule equalityI)
            show "UX x0 \<inter> VX x0 \<subseteq> {}"
            proof (rule subsetI)
	              fix y assume hy: "y \<in> UX x0 \<inter> VX x0"
		              have hyU: "y \<in> UX x0" and hyV: "y \<in> VX x0"
		                using hy by blast+
		              have hyU': "y \<in> {y \<in> Y. (x0, y) \<in> U}"
		                using hyU by (simp add: UX_def)
		              have hyU_conj: "y \<in> Y \<and> (x0, y) \<in> U"
		                using hyU' by simp
		              have hxyU: "(x0, y) \<in> U"
		                by (rule conjunct2[OF hyU_conj])
		              have hyV': "y \<in> {y \<in> Y. (x0, y) \<in> V}"
		                using hyV by (simp add: VX_def)
		              have hyV_conj: "y \<in> Y \<and> (x0, y) \<in> V"
		                using hyV' by simp
		              have hxyV: "(x0, y) \<in> V"
		                by (rule conjunct2[OF hyV_conj])
              have "(x0, y) \<in> U \<inter> V"
                using hxyU hxyV by blast
              hence False
                using hdisj by blast
              thus "y \<in> {}" by blast
            qed
            show "{} \<subseteq> UX x0 \<inter> VX x0" by simp
          qed
          show "UX x0 \<union> VX x0 = Y"
          proof (rule equalityI)
            show "UX x0 \<union> VX x0 \<subseteq> Y"
              unfolding UX_def VX_def by blast
            show "Y \<subseteq> UX x0 \<union> VX x0"
            proof (rule subsetI)
              fix y assume hyY: "y \<in> Y"
              have hxyXY: "(x0, y) \<in> X \<times> Y"
                using hx0 hyY by (simp add: mem_Times_iff)
              have hxyUV: "(x0, y) \<in> U \<union> V"
                using hUV hxyXY by simp
              show "y \<in> UX x0 \<union> VX x0"
              proof (cases "(x0, y) \<in> U")
                case True
                have "y \<in> UX x0"
                  unfolding UX_def using hyY True by blast
                thus ?thesis
                  by blast
              next
                case False
                have "(x0, y) \<in> V"
                  using hxyUV False by blast
                hence "y \<in> VX x0"
                  unfolding VX_def using hyY by blast
                thus ?thesis
                  by blast
              qed
            qed
          qed
        qed

        have hsection_empty:
          "\<forall>x0\<in>X. UX x0 = {} \<or> VX x0 = {}"
        proof (intro ballI)
          fix x0 assume hx0: "x0 \<in> X"
          have hUo: "UX x0 \<in> TY" and hVo: "VX x0 \<in> TY"
            using hUX_open hVX_open hx0 by blast+
          have hdisj': "UX x0 \<inter> VX x0 = {}"
            using hUV_sections hx0 by blast
          have hcov': "UX x0 \<union> VX x0 = Y"
            using hUV_sections hx0 by blast
          show "UX x0 = {} \<or> VX x0 = {}"
          proof (rule classical)
            assume hne: "\<not> (UX x0 = {} \<or> VX x0 = {})"
            have hUne': "UX x0 \<noteq> {}" and hVne': "VX x0 \<noteq> {}"
              using hne by blast+
            have "\<exists>U' V'. U' \<in> TY \<and> V' \<in> TY \<and> U' \<noteq> {} \<and> V' \<noteq> {} \<and> U' \<inter> V' = {} \<and> U' \<union> V' = Y"
              apply (rule exI[where x="UX x0"])
              apply (rule exI[where x="VX x0"])
              using hUo hVo hUne' hVne' hdisj' hcov' by blast
            thus False
              using hNoSepY by blast
          qed
        qed

        have hAB_disj: "A \<inter> B = {}"
          unfolding A_def B_def using hsection_empty by blast

        have hAB_cov: "A \<union> B = X"
        proof (rule equalityI)
          show "A \<union> B \<subseteq> X"
            unfolding A_def B_def by blast
          show "X \<subseteq> A \<union> B"
          proof (rule subsetI)
            fix x assume hxX: "x \<in> X"
            have hxyXY: "(x, y0) \<in> X \<times> Y"
              using hxX hy0 by (simp add: mem_Times_iff)
            have hxyUV: "(x, y0) \<in> U \<union> V"
              using hUV hxyXY by simp
            show "x \<in> A \<union> B"
            proof (cases "(x, y0) \<in> U")
              case True
              have "y0 \<in> UX x"
                unfolding UX_def using hy0 True by blast
              hence "UX x \<noteq> {}"
                by blast
              hence "x \<in> A"
                unfolding A_def using hxX by blast
              thus ?thesis by blast
            next
              case False
              have "(x, y0) \<in> V"
                using hxyUV False by blast
              hence "y0 \<in> VX x"
                unfolding VX_def using hy0 by blast
              hence "VX x \<noteq> {}"
                by blast
              hence "x \<in> B"
                unfolding B_def using hxX by blast
              thus ?thesis by blast
            qed
          qed
        qed

        have hA_open: "A \<in> TX"
        proof -
          define F where "F = {W. W \<in> TX \<and> W \<subseteq> A}"
          have hFsub: "F \<subseteq> TX"
            unfolding F_def by blast
          have hUnion_open: "\<Union>F \<in> TX"
            using hTX hFsub unfolding is_topology_on_def by blast
          have hUnion_sub: "\<Union>F \<subseteq> A"
            unfolding F_def by blast
          have hA_sub: "A \<subseteq> \<Union>F"
          proof (rule subsetI)
            fix x assume hxA: "x \<in> A"
            have hxX: "x \<in> X"
              using hxA unfolding A_def by blast
            have hUx_ne: "UX x \<noteq> {}"
              using hxA unfolding A_def by blast
            obtain y where hy: "y \<in> UX x"
              using hUx_ne by (simp add: ex_in_conv)
            have hyY: "y \<in> Y" and hxyU: "(x, y) \<in> U"
              using hy unfolding UX_def by blast+
            have hxyUin: "(x, y) \<in> X \<times> Y"
              using hxX hyY by (simp add: mem_Times_iff)
            have hUin: "(x, y) \<in> U"
              by (rule hxyU)
            obtain U1 V1 where hU1: "U1 \<in> TX" and hV1: "V1 \<in> TY" and hxyUV1: "(x, y) \<in> U1 \<times> V1"
              and hUV1sub: "U1 \<times> V1 \<subseteq> U"
              by (rule top1_product_open_contains_rect[OF hUopen hUin])
            have hxU1: "x \<in> U1" and hyV1: "y \<in> V1"
              using hxyUV1 by (simp add: mem_Times_iff)
            define W where "W = X \<inter> U1"
            have hWopen: "W \<in> TX"
              unfolding W_def by (rule topology_inter2[OF hTX hXmem hU1])
            have hxW: "x \<in> W"
              unfolding W_def using hxX hxU1 by blast
            have hWsubA: "W \<subseteq> A"
            proof (rule subsetI)
              fix x' assume hx': "x' \<in> W"
              have hx'X: "x' \<in> X" and hx'U1: "x' \<in> U1"
                using hx' unfolding W_def by blast+
              have "(x', y) \<in> U1 \<times> V1"
                using hx'U1 hyV1 by (simp add: mem_Times_iff)
              hence "(x', y) \<in> U"
                using hUV1sub by blast
              hence "y \<in> UX x'"
                unfolding UX_def using hyY by blast
              hence "UX x' \<noteq> {}"
                by blast
              thus "x' \<in> A"
                unfolding A_def using hx'X by blast
            qed
            have hWmemF: "W \<in> F"
              unfolding F_def using hWopen hWsubA by blast
            show "x \<in> \<Union>F"
              by (rule UnionI[OF hWmemF hxW])
          qed
          have hEq: "A = \<Union>F"
            by (rule equalityI[OF hUnion_sub hA_sub])
          show ?thesis
            using hUnion_open hEq by simp
        qed

        have hB_open: "B \<in> TX"
        proof -
          define F where "F = {W. W \<in> TX \<and> W \<subseteq> B}"
          have hFsub: "F \<subseteq> TX"
            unfolding F_def by blast
          have hUnion_open: "\<Union>F \<in> TX"
            using hTX hFsub unfolding is_topology_on_def by blast
          have hUnion_sub: "\<Union>F \<subseteq> B"
            unfolding F_def by blast
          have hB_sub: "B \<subseteq> \<Union>F"
          proof (rule subsetI)
            fix x assume hxB: "x \<in> B"
            have hxX: "x \<in> X"
              using hxB unfolding B_def by blast
            have hVx_ne: "VX x \<noteq> {}"
              using hxB unfolding B_def by blast
            obtain y where hy: "y \<in> VX x"
              using hVx_ne by (simp add: ex_in_conv)
            have hyY: "y \<in> Y" and hxyV: "(x, y) \<in> V"
              using hy unfolding VX_def by blast+
            obtain U1 V1 where hU1: "U1 \<in> TX" and hV1: "V1 \<in> TY" and hxyUV1: "(x, y) \<in> U1 \<times> V1"
              and hUV1sub: "U1 \<times> V1 \<subseteq> V"
              by (rule top1_product_open_contains_rect[OF hVopen hxyV])
            have hxU1: "x \<in> U1" and hyV1: "y \<in> V1"
              using hxyUV1 by (simp add: mem_Times_iff)
            define W where "W = X \<inter> U1"
            have hWopen: "W \<in> TX"
              unfolding W_def by (rule topology_inter2[OF hTX hXmem hU1])
            have hxW: "x \<in> W"
              unfolding W_def using hxX hxU1 by blast
            have hWsubB: "W \<subseteq> B"
            proof (rule subsetI)
              fix x' assume hx': "x' \<in> W"
              have hx'X: "x' \<in> X" and hx'U1: "x' \<in> U1"
                using hx' unfolding W_def by blast+
              have "(x', y) \<in> U1 \<times> V1"
                using hx'U1 hyV1 by (simp add: mem_Times_iff)
              hence "(x', y) \<in> V"
                using hUV1sub by blast
              hence "y \<in> VX x'"
                unfolding VX_def using hyY by blast
              hence "VX x' \<noteq> {}"
                by blast
              thus "x' \<in> B"
                unfolding B_def using hx'X by blast
            qed
            have hWmemF: "W \<in> F"
              unfolding F_def using hWopen hWsubB by blast
            show "x \<in> \<Union>F"
              by (rule UnionI[OF hWmemF hxW])
          qed
          have hEq: "B = \<Union>F"
            by (rule equalityI[OF hUnion_sub hB_sub])
          show ?thesis
            using hUnion_open hEq by simp
        qed

        have hA_ne: "A \<noteq> {}"
        proof
          assume hAemp: "A = {}"
          obtain p where hpU: "p \<in> U"
            using hUne by (simp add: ex_in_conv)
          have hpXY: "p \<in> X \<times> Y"
            using hUsubXY hpU by blast
          obtain x y where hp: "p = (x, y)"
            by (cases p) simp
          have hxyU: "(x, y) \<in> U"
            using hpU hp by simp
          have hxX: "x \<in> X" and hyY: "y \<in> Y"
            using hUsubXY hxyU by (simp add: mem_Times_iff)
          have "y \<in> UX x"
            unfolding UX_def using hyY hxyU by blast
          hence "UX x \<noteq> {}"
            by blast
          hence "x \<in> A"
            unfolding A_def using hxX by blast
          thus False
            using hAemp by blast
        qed

        have hB_ne: "B \<noteq> {}"
        proof
          assume hBemp: "B = {}"
          obtain p where hpV: "p \<in> V"
            using hVne by (simp add: ex_in_conv)
          have hpXY: "p \<in> X \<times> Y"
            using hVsubXY hpV by blast
          obtain x y where hp: "p = (x, y)"
            by (cases p) simp
          have hxyV: "(x, y) \<in> V"
            using hpV hp by simp
          have hxX: "x \<in> X" and hyY: "y \<in> Y"
            using hVsubXY hxyV by (simp add: mem_Times_iff)
          have "y \<in> VX x"
            unfolding VX_def using hyY hxyV by blast
          hence "VX x \<noteq> {}"
            by blast
          hence "x \<in> B"
            unfolding B_def using hxX by blast
          thus False
            using hBemp by blast
        qed

        have "\<exists>U' V'. U' \<in> TX \<and> V' \<in> TX \<and> U' \<noteq> {} \<and> V' \<noteq> {} \<and> U' \<inter> V' = {} \<and> U' \<union> V' = X"
          apply (rule exI[where x=A])
          apply (rule exI[where x=B])
          using hA_open hB_open hA_ne hB_ne hAB_disj hAB_cov by blast
        thus False
          using hNoSepX by blast
      qed
    qed
  qed
qed *)

section \<open>\<S>24 Connected Subspaces of the Real Line\<close>

text \<open>
  Section \<S>24 of \<open>top1.tex\<close> specializes the theory of connectedness to subspaces of
  \<open>\<real>\<close>, culminating in the characterization of connected subsets of \<open>\<real>\<close> as intervals.

  Isabelle already provides the order topology (and the corresponding connectedness facts) for
  types in the class \<open>linear_continuum_topology\<close>.  To connect this with the set-based
  framework of \<open>Top1\<close>, we interpret the library notion of openness \<open>open\<close> as a set of open
  sets, and relate library connectedness (\<open>connected\<close>) to our predicate
  \<open>top1_connected_on\<close> for the induced subspace topology.
\<close>

definition top1_open_sets :: "'a::topological_space set set" where
  "top1_open_sets = {U. open U}"

lemma top1_open_sets_is_topology_on_UNIV:
  "is_topology_on (UNIV::'a::topological_space set) top1_open_sets"
  unfolding is_topology_on_def top1_open_sets_def
proof (intro conjI)
  show "{} \<in> {U. open U}"
    by simp
  show "UNIV \<in> {U. open U}"
    by simp
  show "\<forall>U. U \<subseteq> {U. open U} \<longrightarrow> \<Union>U \<in> {U. open U}"
  proof (intro allI impI)
    fix K assume hK: "K \<subseteq> {U. open U}"
    have hall: "\<forall>U\<in>K. open U"
      using hK by blast
    have "open (\<Union>K)"
      by (rule open_Union[OF hall])
    thus "\<Union>K \<in> {U. open U}"
      by simp
  qed
  show "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> {U. open U} \<longrightarrow> \<Inter>F \<in> {U. open U}"
  proof (intro allI impI)
    fix F assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> {U. open U}"
    have hfin: "finite F"
      using hF by blast
    have hall: "\<forall>U\<in>F. open U"
      using hF by blast
    have "open (\<Inter>F)"
      by (rule open_Inter[OF hfin hall])
    thus "\<Inter>F \<in> {U. open U}"
      by simp
  qed
qed

lemma top1_connected_on_subspace_open_iff_connected:
  fixes S :: "'a::topological_space set"
  shows "top1_connected_on S (subspace_topology UNIV top1_open_sets S) \<longleftrightarrow> connected S"
proof (rule iffI)
  assume hS: "top1_connected_on S (subspace_topology UNIV top1_open_sets S)"
  have hNoSep:
    "\<nexists>U V.
        U \<in> subspace_topology UNIV top1_open_sets S \<and>
        V \<in> subspace_topology UNIV top1_open_sets S \<and>
        U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = S"
    using hS unfolding top1_connected_on_def by blast

  show "connected S"
    unfolding connected_def
  proof (rule notI)
    assume hsep:
      "\<exists>A B. open A \<and> open B \<and> S \<subseteq> A \<union> B \<and> A \<inter> B \<inter> S = {} \<and> A \<inter> S \<noteq> {} \<and> B \<inter> S \<noteq> {}"
    then obtain A B where hA: "open A" and hB: "open B" and hcov: "S \<subseteq> A \<union> B"
      and hdisj: "A \<inter> B \<inter> S = {}" and hAne: "A \<inter> S \<noteq> {}" and hBne: "B \<inter> S \<noteq> {}"
      by blast

    define U where "U = S \<inter> A"
    define V where "V = S \<inter> B"

    have hU_mem: "U \<in> subspace_topology UNIV top1_open_sets S"
      unfolding subspace_topology_def top1_open_sets_def U_def
      using hA by blast
    have hV_mem: "V \<in> subspace_topology UNIV top1_open_sets S"
      unfolding subspace_topology_def top1_open_sets_def V_def
      using hB by blast
    have hU_ne: "U \<noteq> {}"
      unfolding U_def using hAne by blast
    have hV_ne: "V \<noteq> {}"
      unfolding V_def using hBne by blast
    have hUV_disj: "U \<inter> V = {}"
      unfolding U_def V_def using hdisj by blast
    have hUV_cov: "U \<union> V = S"
    proof (rule equalityI)
      show "U \<union> V \<subseteq> S"
        unfolding U_def V_def by blast
      show "S \<subseteq> U \<union> V"
      proof (rule subsetI)
        fix x assume hx: "x \<in> S"
        have "x \<in> A \<union> B"
          using hcov hx by blast
        thus "x \<in> U \<union> V"
          unfolding U_def V_def using hx by blast
      qed
    qed

    have "\<exists>U V.
        U \<in> subspace_topology UNIV top1_open_sets S \<and>
        V \<in> subspace_topology UNIV top1_open_sets S \<and>
        U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = S"
      apply (rule exI[where x=U])
      apply (rule exI[where x=V])
      using hU_mem hV_mem hU_ne hV_ne hUV_disj hUV_cov by blast
    thus False
      using hNoSep by blast
  qed
next
  assume hconn: "connected S"

  have hTopS: "is_topology_on S (subspace_topology UNIV top1_open_sets S)"
  proof -
    have hTopU: "is_topology_on (UNIV::'a set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis
      by (rule subspace_topology_is_topology_on[OF hTopU]) simp
  qed

  show "top1_connected_on S (subspace_topology UNIV top1_open_sets S)"
    unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on S (subspace_topology UNIV top1_open_sets S)"
      by (rule hTopS)
    show "\<nexists>U V.
        U \<in> subspace_topology UNIV top1_open_sets S \<and>
        V \<in> subspace_topology UNIV top1_open_sets S \<and>
        U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = S"
    proof (rule notI)
      assume hsep:
        "\<exists>U V.
          U \<in> subspace_topology UNIV top1_open_sets S \<and>
          V \<in> subspace_topology UNIV top1_open_sets S \<and>
          U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = S"
      then obtain U V where hU: "U \<in> subspace_topology UNIV top1_open_sets S"
        and hV: "V \<in> subspace_topology UNIV top1_open_sets S"
        and hUne: "U \<noteq> {}" and hVne: "V \<noteq> {}" and hdisj: "U \<inter> V = {}" and hcov: "U \<union> V = S"
        by blast

      obtain A where hAopen: "open A" and hUeq: "U = S \<inter> A"
        using hU unfolding subspace_topology_def top1_open_sets_def by blast
      obtain B where hBopen: "open B" and hVeq: "V = S \<inter> B"
        using hV unfolding subspace_topology_def top1_open_sets_def by blast

      have hSsub: "S \<subseteq> A \<union> B"
      proof (rule subsetI)
        fix x assume hx: "x \<in> S"
        have "x \<in> U \<union> V"
          using hcov hx by blast
        thus "x \<in> A \<union> B"
          using hx unfolding hUeq hVeq by blast
      qed
      have hABdisj: "A \<inter> B \<inter> S = {}"
        using hdisj unfolding hUeq hVeq by blast
      have hAne: "A \<inter> S \<noteq> {}"
        using hUne unfolding hUeq by blast
      have hBne: "B \<inter> S \<noteq> {}"
        using hVne unfolding hVeq by blast

      have "\<exists>A B. open A \<and> open B \<and> S \<subseteq> A \<union> B \<and> A \<inter> B \<inter> S = {} \<and> A \<inter> S \<noteq> {} \<and> B \<inter> S \<noteq> {}"
        apply (rule exI[where x=A])
        apply (rule exI[where x=B])
        using hAopen hBopen hSsub hABdisj hAne hBne by blast
      thus False
        using hconn unfolding connected_def by blast
    qed
  qed
qed

(** A convenient introduction rule derived from
    \<open>top1_connected_on_subspace_open_iff_connected\<close>. **)
lemma top1_connected_on_subspace_openI:
  fixes S :: "'a::topological_space set"
  assumes "connected S"
  shows "top1_connected_on S (subspace_topology UNIV top1_open_sets S)"
  using top1_connected_on_subspace_open_iff_connected assms
  by (rule iffD2)

(** from \S24 Theorem 24.1 (Convex subspaces of linear continua are connected) [top1.tex:2751] **)
theorem Theorem_24_1:
  fixes U :: "'a::linear_continuum_topology set"
  assumes hconv: "\<And>x y z. x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x \<le> z \<Longrightarrow> z \<le> y \<Longrightarrow> z \<in> U"
  shows "top1_connected_on U (subspace_topology UNIV top1_open_sets U)"
proof -
  have "connected U"
    using hconv by (rule connectedI_interval)
  thus ?thesis
    by (rule top1_connected_on_subspace_openI)
qed

(** from \S24 Corollary 24.2 (Intervals and rays in \<real> are connected) [top1.tex:2792] **)
corollary Corollary_24_2:
  fixes a b :: real
  shows
    "top1_connected_on (UNIV::real set) top1_open_sets"
    and "top1_connected_on {a..b} (subspace_topology UNIV top1_open_sets {a..b})"
    and "top1_connected_on {a<..<b} (subspace_topology UNIV top1_open_sets {a<..<b})"
    and "top1_connected_on {a..} (subspace_topology UNIV top1_open_sets {a..})"
    and "top1_connected_on {a<..} (subspace_topology UNIV top1_open_sets {a<..})"
    and "top1_connected_on {..b} (subspace_topology UNIV top1_open_sets {..b})"
    and "top1_connected_on {..<b} (subspace_topology UNIV top1_open_sets {..<b})"
proof -
  have hUNIV_conn: "connected (UNIV::real set)"
  proof (rule connectedI_interval)
    fix x y z :: real
    assume "x \<in> (UNIV::real set)" and "y \<in> (UNIV::real set)" and "x \<le> z" and "z \<le> y"
    show "z \<in> (UNIV::real set)"
      by simp
  qed

  have hUNIV: "top1_connected_on (UNIV::real set) (subspace_topology UNIV top1_open_sets (UNIV::real set))"
    using hUNIV_conn by (rule top1_connected_on_subspace_openI)
  have hEq: "subspace_topology UNIV top1_open_sets (UNIV::real set) = top1_open_sets"
    unfolding subspace_topology_def top1_open_sets_def by simp

  show "top1_connected_on (UNIV::real set) top1_open_sets"
    by (subst hEq[symmetric]) (rule hUNIV)

  have h1: "connected {a..b}"
    by (rule connected_Icc)
  have h2: "connected {a<..<b}"
    by (rule connected_Ioo)
  have h3: "connected {a..}"
    by (rule connected_Ici)
  have h4: "connected {a<..}"
    by (rule connected_Ioi)
  have h5: "connected {..b}"
    by (rule connected_Iic)
  have h6: "connected {..<b}"
    by (rule connected_Iio)

  show "top1_connected_on {a..b} (subspace_topology UNIV top1_open_sets {a..b})"
    using h1 by (rule top1_connected_on_subspace_openI)
  show "top1_connected_on {a<..<b} (subspace_topology UNIV top1_open_sets {a<..<b})"
    using h2 by (rule top1_connected_on_subspace_openI)
  show "top1_connected_on {a..} (subspace_topology UNIV top1_open_sets {a..})"
    using h3 by (rule top1_connected_on_subspace_openI)
  show "top1_connected_on {a<..} (subspace_topology UNIV top1_open_sets {a<..})"
    using h4 by (rule top1_connected_on_subspace_openI)
  show "top1_connected_on {..b} (subspace_topology UNIV top1_open_sets {..b})"
    using h5 by (rule top1_connected_on_subspace_openI)
  show "top1_connected_on {..<b} (subspace_topology UNIV top1_open_sets {..<b})"
    using h6 by (rule top1_connected_on_subspace_openI)
qed

(** from \S24 Theorem 24.3 (Intermediate value theorem) [top1.tex:2795] **)
theorem Theorem_24_3:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes hconn: "top1_connected_on X TX"
  assumes hcont: "top1_continuous_map_on X TX (UNIV::'b set) (order_topology_on_UNIV::'b set set) f"
  assumes ha: "a \<in> X"
  assumes hb: "b \<in> X"
  assumes hr: "(f a \<le> r \<and> r \<le> f b) \<or> (f b \<le> r \<and> r \<le> f a)"
  shows "\<exists>c\<in>X. f c = r"
proof -
  have hNoSep:
    "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    using hconn unfolding top1_connected_on_def by blast

  have hpre:
    "\<forall>V\<in>(order_topology_on_UNIV::'b set set). {x\<in>X. f x \<in> V} \<in> TX"
    using hcont unfolding top1_continuous_map_on_def by (rule conjunct2)

  have hUopen: "{x\<in>X. f x \<in> open_ray_lt r} \<in> TX"
    by (rule bspec[OF hpre open_ray_lt_in_order_topology])
  have hVopen: "{x\<in>X. f x \<in> open_ray_gt r} \<in> TX"
    by (rule bspec[OF hpre open_ray_gt_in_order_topology])

  have hDisj: "{x\<in>X. f x \<in> open_ray_lt r} \<inter> {x\<in>X. f x \<in> open_ray_gt r} = {}"
  proof (rule subset_antisym)
    show "{x\<in>X. f x \<in> open_ray_lt r} \<inter> {x\<in>X. f x \<in> open_ray_gt r} \<subseteq> {}"
    proof (rule subsetI)
      fix x
      assume hx: "x \<in> {x\<in>X. f x \<in> open_ray_lt r} \<inter> {x\<in>X. f x \<in> open_ray_gt r}"
      have hxX: "x \<in> X"
        using hx by simp
      have hlt: "f x < r"
        using hx unfolding open_ray_lt_def by simp
      have hgt: "r < f x"
        using hx unfolding open_ray_gt_def by simp
      have fxlt: "f x < f x"
        by (rule less_trans[OF hlt hgt])
      have hnir: "\<not> (f x < f x)"
        by (rule less_irrefl)
      show "x \<in> {}"
        using fxlt hnir by blast
    qed
    show "{} \<subseteq> {x\<in>X. f x \<in> open_ray_lt r} \<inter> {x\<in>X. f x \<in> open_ray_gt r}"
      by simp
  qed

  show "\<exists>c\<in>X. f c = r"
  proof (rule ccontr)
    assume hNone: "\<not> (\<exists>c\<in>X. f c = r)"
    have hNoHit: "\<forall>x\<in>X. f x \<noteq> r"
      using hNone by blast

    have hCover: "{x\<in>X. f x \<in> open_ray_lt r} \<union> {x\<in>X. f x \<in> open_ray_gt r} = X"
    proof (rule subset_antisym)
      show "{x\<in>X. f x \<in> open_ray_lt r} \<union> {x\<in>X. f x \<in> open_ray_gt r} \<subseteq> X"
        by blast
      show "X \<subseteq> {x\<in>X. f x \<in> open_ray_lt r} \<union> {x\<in>X. f x \<in> open_ray_gt r}"
      proof (rule subsetI)
        fix x
        assume hxX: "x \<in> X"
        have hneq: "f x \<noteq> r"
          using hNoHit hxX by blast
        show "x \<in> {x\<in>X. f x \<in> open_ray_lt r} \<union> {x\<in>X. f x \<in> open_ray_gt r}"
        proof (cases "f x < r")
          case True
          have "f x \<in> open_ray_lt r"
            unfolding open_ray_lt_def using True by simp
          thus ?thesis
            using hxX by blast
	        next
	          case False
	          have hrle: "r \<le> f x"
	            using False by (simp add: not_less)
	          have hsplit: "r < f x \<or> r = f x"
	            using hrle by (simp add: le_less)
	          have hneq': "r \<noteq> f x"
	            using hneq by simp
	          have hrlt: "r < f x"
	          proof -
	            from hsplit show ?thesis
	            proof
	              assume "r < f x"
	              thus ?thesis .
	            next
	              assume "r = f x"
	              thus ?thesis using hneq' by simp
	            qed
	          qed
	          have "f x \<in> open_ray_gt r"
	            unfolding open_ray_gt_def using hrlt by simp
	          thus ?thesis
	            using hxX by blast
        qed
      qed
    qed

    have hU_ne: "{x\<in>X. f x \<in> open_ray_lt r} \<noteq> {}"
    proof -
      from hr show ?thesis
      proof
        assume hab: "f a \<le> r \<and> r \<le> f b"
        show "{x\<in>X. f x \<in> open_ray_lt r} \<noteq> {}"
        proof (cases "f a = r")
          case True
          have False
            using hNoHit ha True by blast
          thus ?thesis
            by blast
	        next
	          case False
	          have hsplit: "f a < r \<or> f a = r"
	            using conjunct1[OF hab] by (simp add: le_less)
	          have "f a < r"
	          proof -
	            from hsplit show ?thesis
	            proof
	              assume "f a < r"
	              thus ?thesis .
	            next
	              assume "f a = r"
	              thus ?thesis using False by simp
	            qed
	          qed
	          hence "a \<in> {x\<in>X. f x \<in> open_ray_lt r}"
	            using ha unfolding open_ray_lt_def by simp
	          thus ?thesis
	            by blast
        qed
      next
        assume hba: "f b \<le> r \<and> r \<le> f a"
        show "{x\<in>X. f x \<in> open_ray_lt r} \<noteq> {}"
        proof (cases "f b = r")
          case True
          have False
            using hNoHit hb True by blast
          thus ?thesis
            by blast
	        next
	          case False
	          have hsplit: "f b < r \<or> f b = r"
	            using conjunct1[OF hba] by (simp add: le_less)
	          have "f b < r"
	          proof -
	            from hsplit show ?thesis
	            proof
	              assume "f b < r"
	              thus ?thesis .
	            next
	              assume "f b = r"
	              thus ?thesis using False by simp
	            qed
	          qed
	          hence "b \<in> {x\<in>X. f x \<in> open_ray_lt r}"
	            using hb unfolding open_ray_lt_def by simp
	          thus ?thesis
	            by blast
        qed
      qed
    qed

    have hV_ne: "{x\<in>X. f x \<in> open_ray_gt r} \<noteq> {}"
    proof -
      from hr show ?thesis
      proof
        assume hab: "f a \<le> r \<and> r \<le> f b"
        show "{x\<in>X. f x \<in> open_ray_gt r} \<noteq> {}"
        proof (cases "f b = r")
          case True
          have False
            using hNoHit hb True by blast
          thus ?thesis
            by blast
	        next
	          case False
	          have hsplit: "r < f b \<or> r = f b"
	            using conjunct2[OF hab] by (simp add: le_less)
	          have "r < f b"
	          proof -
	            from hsplit show ?thesis
	            proof
	              assume "r < f b"
	              thus ?thesis .
	            next
	              assume "r = f b"
	              thus ?thesis using False by simp
	            qed
	          qed
	          hence "b \<in> {x\<in>X. f x \<in> open_ray_gt r}"
	            using hb unfolding open_ray_gt_def by simp
	          thus ?thesis
	            by blast
        qed
      next
        assume hba: "f b \<le> r \<and> r \<le> f a"
        show "{x\<in>X. f x \<in> open_ray_gt r} \<noteq> {}"
        proof (cases "f a = r")
          case True
          have False
            using hNoHit ha True by blast
          thus ?thesis
            by blast
	        next
	          case False
	          have hsplit: "r < f a \<or> r = f a"
	            using conjunct2[OF hba] by (simp add: le_less)
	          have "r < f a"
	          proof -
	            from hsplit show ?thesis
	            proof
	              assume "r < f a"
	              thus ?thesis .
	            next
	              assume "r = f a"
	              thus ?thesis using False by simp
	            qed
	          qed
	          hence "a \<in> {x\<in>X. f x \<in> open_ray_gt r}"
	            using ha unfolding open_ray_gt_def by simp
	          thus ?thesis
	            by blast
        qed
      qed
    qed

    have hSep:
      "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
      apply (rule exI[where x="{x\<in>X. f x \<in> open_ray_lt r}"])
      apply (rule exI[where x="{x\<in>X. f x \<in> open_ray_gt r}"])
      apply (intro conjI)
           apply (rule hUopen)
          apply (rule hVopen)
         apply (rule hU_ne)
        apply (rule hV_ne)
       apply (rule hDisj)
      apply (rule hCover)
      done

    show False
      using hNoSep hSep by blast
  qed
qed

section \<open>*\<S>25 Components and Local Connectedness\<close>

subsection \<open>Components\<close>

(** Connected singletons are the basic building block ensuring components are nonempty. **)
lemma top1_connected_on_singleton:
  assumes hTX: "is_topology_on X TX"
  assumes hxX: "x \<in> X"
  shows "top1_connected_on {x} (subspace_topology X TX {x})"
proof -
  have hx_sub: "{x} \<subseteq> X"
    using hxX by blast
  have hTop: "is_topology_on {x} (subspace_topology X TX {x})"
    by (rule subspace_topology_is_topology_on[OF hTX hx_sub])

  show ?thesis
    unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on {x} (subspace_topology X TX {x})"
      by (rule hTop)
    show "\<nexists>U V.
        U \<in> subspace_topology X TX {x} \<and>
        V \<in> subspace_topology X TX {x} \<and>
        U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = {x}"
    proof
      assume hSep:
        "\<exists>U V.
          U \<in> subspace_topology X TX {x} \<and>
          V \<in> subspace_topology X TX {x} \<and>
          U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = {x}"
      then obtain U V where hU: "U \<in> subspace_topology X TX {x}"
        and hV: "V \<in> subspace_topology X TX {x}"
        and hUne: "U \<noteq> {}" and hVne: "V \<noteq> {}"
        and hdisj: "U \<inter> V = {}" and hcov: "U \<union> V = {x}"
        by blast

      obtain U0 where hU0: "U0 \<in> TX" and hUeq: "U = {x} \<inter> U0"
        using hU unfolding subspace_topology_def by blast
      obtain V0 where hV0: "V0 \<in> TX" and hVeq: "V = {x} \<inter> V0"
        using hV unfolding subspace_topology_def by blast
      have hxU0: "x \<in> U0"
      proof (rule ccontr)
        assume hxnot: "x \<notin> U0"
        have "U = {}"
          unfolding hUeq using hxnot by simp
        thus False
          using hUne by simp
      qed
      have hxV0: "x \<in> V0"
      proof (rule ccontr)
        assume hxnot: "x \<notin> V0"
        have "V = {}"
          unfolding hVeq using hxnot by simp
        thus False
          using hVne by simp
      qed

      have hU_singleton: "U = {x}"
        unfolding hUeq using hxU0 by simp
      have hV_singleton: "V = {x}"
        unfolding hVeq using hxV0 by simp

      have "U \<inter> V = {x}"
        unfolding hU_singleton hV_singleton by simp
      thus False
        using hdisj by blast
    qed
  qed
qed

(** Equivalence relation used in *\<S>25 of \<open>top1.tex\<close>: points are related if they lie together
    in some connected subspace. **)
definition top1_in_same_component_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_in_same_component_on X TX x y \<longleftrightarrow>
     (\<exists>C. C \<subseteq> X \<and> x \<in> C \<and> y \<in> C \<and> top1_connected_on C (subspace_topology X TX C))"

(** The connected component of \<open>x\<close> in \<open>(X,TX)\<close> is the union of all connected subspaces containing \<open>x\<close>. **)
definition top1_component_of_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "top1_component_of_on X TX x =
     \<Union>{C. C \<subseteq> X \<and> x \<in> C \<and> top1_connected_on C (subspace_topology X TX C)}"

definition top1_components_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "top1_components_on X TX = {top1_component_of_on X TX x | x. x \<in> X}"

lemma top1_component_of_on_mem_iff:
  "y \<in> top1_component_of_on X TX x \<longleftrightarrow>
     (\<exists>C. C \<subseteq> X \<and> x \<in> C \<and> top1_connected_on C (subspace_topology X TX C) \<and> y \<in> C)"
  unfolding top1_component_of_on_def
  by simp

lemma top1_in_same_component_on_iff_component_mem:
  "top1_in_same_component_on X TX x y \<longleftrightarrow> y \<in> top1_component_of_on X TX x"
proof (rule iffI)
  assume hxy: "top1_in_same_component_on X TX x y"
  obtain C where hCsub: "C \<subseteq> X" and hxC: "x \<in> C" and hyC: "y \<in> C"
    and hconnC: "top1_connected_on C (subspace_topology X TX C)"
    using hxy unfolding top1_in_same_component_on_def by blast
  show "y \<in> top1_component_of_on X TX x"
    unfolding top1_component_of_on_mem_iff
    apply (rule exI[where x=C])
    using hCsub hxC hconnC hyC by blast
next
  assume hy: "y \<in> top1_component_of_on X TX x"
  obtain C where hCsub: "C \<subseteq> X" and hxC: "x \<in> C"
    and hconnC: "top1_connected_on C (subspace_topology X TX C)" and hyC: "y \<in> C"
    using hy unfolding top1_component_of_on_mem_iff by blast
  show "top1_in_same_component_on X TX x y"
    unfolding top1_in_same_component_on_def
    apply (rule exI[where x=C])
    using hCsub hxC hyC hconnC by blast
qed

lemma top1_component_of_on_subset:
  shows "top1_component_of_on X TX x \<subseteq> X"
proof (rule subsetI)
  fix y assume hy: "y \<in> top1_component_of_on X TX x"
  obtain C where hCsub: "C \<subseteq> X" and hyC: "y \<in> C"
    using hy unfolding top1_component_of_on_mem_iff by blast
  show "y \<in> X"
    using hCsub hyC by blast
qed

lemma top1_component_of_on_self_mem:
  assumes hTX: "is_topology_on X TX"
  assumes hxX: "x \<in> X"
  shows "x \<in> top1_component_of_on X TX x"
proof -
  have hxconn: "top1_connected_on {x} (subspace_topology X TX {x})"
    by (rule top1_connected_on_singleton[OF hTX hxX])
  have hx_mem: "x \<in> {x}"
    by simp
  have hx_sub: "{x} \<subseteq> X"
    using hxX by blast
  show ?thesis
    unfolding top1_component_of_on_mem_iff
    apply (rule exI[where x="{x}"])
    using hx_sub hx_mem hxconn by blast
qed

lemma top1_connected_subspace_subset_component_of:
  assumes hAX: "A \<subseteq> X"
  assumes hxA: "x \<in> A"
  assumes hconn: "top1_connected_on A (subspace_topology X TX A)"
  shows "A \<subseteq> top1_component_of_on X TX x"
proof (rule subsetI)
  fix y assume hyA: "y \<in> A"
  show "y \<in> top1_component_of_on X TX x"
    unfolding top1_component_of_on_mem_iff
    apply (rule exI[where x=A])
    using hAX hxA hyA hconn by blast
qed

lemma top1_in_same_component_on_refl:
  assumes hTX: "is_topology_on X TX"
  assumes hxX: "x \<in> X"
  shows "top1_in_same_component_on X TX x x"
proof -
  have hxconn: "top1_connected_on {x} (subspace_topology X TX {x})"
    by (rule top1_connected_on_singleton[OF hTX hxX])
  have hx_sub: "{x} \<subseteq> X"
    using hxX by blast
  show ?thesis
    unfolding top1_in_same_component_on_def
    apply (rule exI[where x="{x}"])
    using hx_sub hxconn by simp
qed

lemma top1_in_same_component_on_sym:
  assumes "top1_in_same_component_on X TX x y"
  shows "top1_in_same_component_on X TX y x"
  using assms unfolding top1_in_same_component_on_def by blast

lemma top1_in_same_component_on_trans:
  assumes hTX: "is_topology_on X TX"
  assumes hxy: "top1_in_same_component_on X TX x y"
  assumes hyz: "top1_in_same_component_on X TX y z"
  shows "top1_in_same_component_on X TX x z"
proof -
  obtain A where hAX: "A \<subseteq> X" and hxA: "x \<in> A" and hyA: "y \<in> A"
    and hconnA: "top1_connected_on A (subspace_topology X TX A)"
    using hxy unfolding top1_in_same_component_on_def by blast
  obtain B where hBX: "B \<subseteq> X" and hyB: "y \<in> B" and hzB: "z \<in> B"
    and hconnB: "top1_connected_on B (subspace_topology X TX B)"
    using hyz unfolding top1_in_same_component_on_def by blast

  define I where "I = {A, B}"
  have hI_ne: "I \<noteq> {}"
    unfolding I_def by simp
  have hA_fun: "\<forall>C\<in>I. C \<subseteq> X"
    unfolding I_def using hAX hBX by simp
  have hconn_fun: "\<forall>C\<in>I. top1_connected_on C (subspace_topology X TX C)"
    unfolding I_def using hconnA hconnB by simp
  have hyInter: "y \<in> \<Inter>(id ` I)"
    unfolding I_def by (simp add: hyA hyB)

  have hUnion_conn:
    "top1_connected_on (\<Union>C\<in>I. id C) (subspace_topology X TX (\<Union>C\<in>I. id C))"
  proof -
    have hA_id: "\<forall>C\<in>I. id C \<subseteq> X"
      using hA_fun by simp
    have hconn_id: "\<forall>C\<in>I. top1_connected_on (id C) (subspace_topology X TX (id C))"
      using hconn_fun by simp
    show ?thesis
      apply (rule Theorem_23_3[where A=id and I=I and p=y])
           apply (rule hTX)
          apply (rule hI_ne)
         apply (rule hA_id)
        apply (rule hconn_id)
       apply (rule hyInter)
      done
  qed
  have hUnion_sub: "(\<Union>C\<in>I. id C) \<subseteq> X"
  proof (rule subsetI)
    fix t
    assume ht: "t \<in> (\<Union>C\<in>I. id C)"
    then obtain C where hCI: "C \<in> I" and htC: "t \<in> id C"
      by blast
    have hCsub: "C \<subseteq> X"
      using hA_fun hCI by blast
    show "t \<in> X"
    proof -
      have htC': "t \<in> C"
        using htC by simp
      show "t \<in> X"
        by (rule subsetD[OF hCsub htC'])
    qed
  qed

  have hxU: "x \<in> (\<Union>C\<in>I. id C)"
    unfolding I_def by (simp add: hxA)
  have hzU: "z \<in> (\<Union>C\<in>I. id C)"
    unfolding I_def by (simp add: hzB)

  show ?thesis
    unfolding top1_in_same_component_on_def
    apply (rule exI[where x="(\<Union>C\<in>I. id C)"])
    using hUnion_sub hxU hzU hUnion_conn by blast
qed

lemma top1_component_of_on_eq_of_mem:
  assumes hTX: "is_topology_on X TX"
  assumes hy: "y \<in> top1_component_of_on X TX x"
  shows "top1_component_of_on X TX y = top1_component_of_on X TX x"
proof (rule equalityI)
  show "top1_component_of_on X TX y \<subseteq> top1_component_of_on X TX x"
  proof (rule subsetI)
    fix z assume hz: "z \<in> top1_component_of_on X TX y"
    have hxy: "top1_in_same_component_on X TX x y"
      using hy by (simp add: top1_in_same_component_on_iff_component_mem)
    have hyz: "top1_in_same_component_on X TX y z"
      using hz by (simp add: top1_in_same_component_on_iff_component_mem)
    have hxz: "top1_in_same_component_on X TX x z"
      by (rule top1_in_same_component_on_trans[OF hTX hxy hyz])
    show "z \<in> top1_component_of_on X TX x"
      using hxz by (simp add: top1_in_same_component_on_iff_component_mem)
  qed
  show "top1_component_of_on X TX x \<subseteq> top1_component_of_on X TX y"
  proof (rule subsetI)
    fix z assume hz: "z \<in> top1_component_of_on X TX x"
    have hxy: "top1_in_same_component_on X TX x y"
      using hy by (simp add: top1_in_same_component_on_iff_component_mem)
    have hyx: "top1_in_same_component_on X TX y x"
      by (rule top1_in_same_component_on_sym[OF hxy])
    have hxz: "top1_in_same_component_on X TX x z"
      using hz by (simp add: top1_in_same_component_on_iff_component_mem)
    have hyz: "top1_in_same_component_on X TX y z"
      by (rule top1_in_same_component_on_trans[OF hTX hyx hxz])
    show "z \<in> top1_component_of_on X TX y"
      using hyz by (simp add: top1_in_same_component_on_iff_component_mem)
  qed
qed

lemma top1_component_of_on_connected:
  assumes hTX: "is_topology_on X TX"
  assumes hxX: "x \<in> X"
  shows "top1_connected_on (top1_component_of_on X TX x) (subspace_topology X TX (top1_component_of_on X TX x))"
proof -
  define I where "I = {C. C \<subseteq> X \<and> x \<in> C \<and> top1_connected_on C (subspace_topology X TX C)}"
  have hxI: "{x} \<in> I"
  proof -
    have hxconn: "top1_connected_on {x} (subspace_topology X TX {x})"
      by (rule top1_connected_on_singleton[OF hTX hxX])
    have hx_sub: "{x} \<subseteq> X"
      using hxX by blast
    show ?thesis
      unfolding I_def
      using hx_sub hxconn by simp
  qed
  have hI_ne: "I \<noteq> {}"
    using hxI by blast
  have hI_subX: "\<forall>C\<in>I. C \<subseteq> X"
    unfolding I_def by blast
  have hI_conn: "\<forall>C\<in>I. top1_connected_on C (subspace_topology X TX C)"
    unfolding I_def by blast
  have hxInter: "x \<in> \<Inter>(id ` I)"
  proof -
    have hall: "\<forall>C\<in>I. x \<in> C"
      unfolding I_def by blast
    show ?thesis
      using hall by simp
  qed

  have hUnion_conn:
    "top1_connected_on (\<Union>C\<in>I. id C) (subspace_topology X TX (\<Union>C\<in>I. id C))"
  proof -
    have hI_subX_id: "\<forall>C\<in>I. id C \<subseteq> X"
      using hI_subX by simp
    have hI_conn_id: "\<forall>C\<in>I. top1_connected_on (id C) (subspace_topology X TX (id C))"
      using hI_conn by simp
    show ?thesis
      apply (rule Theorem_23_3[where A=id and I=I and p=x])
           apply (rule hTX)
          apply (rule hI_ne)
         apply (rule hI_subX_id)
        apply (rule hI_conn_id)
       apply (rule hxInter)
      done
  qed

  have hUnion_eq: "(\<Union>C\<in>I. id C) = top1_component_of_on X TX x"
    unfolding top1_component_of_on_def I_def by simp

  show ?thesis
    unfolding hUnion_eq[symmetric] by (rule hUnion_conn)
qed

lemma top1_component_of_on_in_components:
  assumes hxX: "x \<in> X"
  shows "top1_component_of_on X TX x \<in> top1_components_on X TX"
  unfolding top1_components_on_def using hxX by blast

lemma top1_component_of_on_as_component:
  assumes hTX: "is_topology_on X TX"
  assumes hC: "C \<in> top1_components_on X TX"
  assumes hxC: "x \<in> C"
  shows "C = top1_component_of_on X TX x"
proof -
  obtain x0 where hx0: "x0 \<in> X" and hCeq: "C = top1_component_of_on X TX x0"
    using hC unfolding top1_components_on_def by blast
  have hx0x: "x \<in> top1_component_of_on X TX x0"
    using hxC hCeq by simp
  have hEq: "top1_component_of_on X TX x = top1_component_of_on X TX x0"
    using hx0x by (rule top1_component_of_on_eq_of_mem[OF hTX])
  show ?thesis
    unfolding hCeq using hEq by simp
qed

(** from *\S25 Theorem 25.1 (Components) [top1.tex:2948] **)
theorem Theorem_25_1:
  assumes hTX: "is_topology_on X TX"
  shows
    "(\<Union>(top1_components_on X TX)) = X"
    and "\<And>C1 C2. C1 \<in> top1_components_on X TX \<Longrightarrow> C2 \<in> top1_components_on X TX \<Longrightarrow> C1 \<inter> C2 \<noteq> {} \<Longrightarrow> C1 = C2"
    and "\<And>C. C \<in> top1_components_on X TX \<Longrightarrow> top1_connected_on C (subspace_topology X TX C)"
    and "\<And>A. A \<subseteq> X \<Longrightarrow> top1_connected_on A (subspace_topology X TX A) \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
              (\<exists>C\<in>top1_components_on X TX. A \<subseteq> C)"
proof -
  show "(\<Union>(top1_components_on X TX)) = X"
  proof (rule equalityI)
    show "(\<Union>(top1_components_on X TX)) \<subseteq> X"
    proof (rule subsetI)
      fix y assume hy: "y \<in> (\<Union>(top1_components_on X TX))"
      obtain C where hC: "C \<in> top1_components_on X TX" and hyC: "y \<in> C"
        using hy by blast
      obtain x where hxX: "x \<in> X" and hCeq: "C = top1_component_of_on X TX x"
        using hC unfolding top1_components_on_def by blast
      have hyComp: "y \<in> top1_component_of_on X TX x"
        using hyC hCeq by simp
      have hsub: "top1_component_of_on X TX x \<subseteq> X"
        by (rule top1_component_of_on_subset)
      show "y \<in> X"
        using hyComp by (rule subsetD[OF hsub])
    qed
    show "X \<subseteq> (\<Union>(top1_components_on X TX))"
    proof (rule subsetI)
      fix x assume hxX: "x \<in> X"
      have hxC: "x \<in> top1_component_of_on X TX x"
        by (rule top1_component_of_on_self_mem[OF hTX hxX])
      have hComp: "top1_component_of_on X TX x \<in> top1_components_on X TX"
        by (rule top1_component_of_on_in_components[OF hxX])
      show "x \<in> (\<Union>(top1_components_on X TX))"
        using hComp hxC by blast
    qed
  qed

  show "\<And>C1 C2. C1 \<in> top1_components_on X TX \<Longrightarrow> C2 \<in> top1_components_on X TX \<Longrightarrow> C1 \<inter> C2 \<noteq> {} \<Longrightarrow> C1 = C2"
  proof -
    fix C1 C2
    assume hC1: "C1 \<in> top1_components_on X TX"
    assume hC2: "C2 \<in> top1_components_on X TX"
    assume hinter: "C1 \<inter> C2 \<noteq> {}"
    obtain z where hz1: "z \<in> C1" and hz2: "z \<in> C2"
      using hinter by blast
    have hC1z: "C1 = top1_component_of_on X TX z"
      by (rule top1_component_of_on_as_component[OF hTX hC1 hz1])
    have hC2z: "C2 = top1_component_of_on X TX z"
      by (rule top1_component_of_on_as_component[OF hTX hC2 hz2])
    show "C1 = C2"
      using hC1z hC2z by simp
  qed

  show "\<And>C. C \<in> top1_components_on X TX \<Longrightarrow> top1_connected_on C (subspace_topology X TX C)"
  proof -
    fix C assume hC: "C \<in> top1_components_on X TX"
    obtain x where hxX: "x \<in> X" and hCeq: "C = top1_component_of_on X TX x"
      using hC unfolding top1_components_on_def by blast
    have "top1_connected_on (top1_component_of_on X TX x) (subspace_topology X TX (top1_component_of_on X TX x))"
      by (rule top1_component_of_on_connected[OF hTX hxX])
    thus "top1_connected_on C (subspace_topology X TX C)"
      unfolding hCeq by simp
  qed

  show "\<And>A. A \<subseteq> X \<Longrightarrow> top1_connected_on A (subspace_topology X TX A) \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
            (\<exists>C\<in>top1_components_on X TX. A \<subseteq> C)"
  proof -
    fix A
    assume hAX: "A \<subseteq> X"
    assume hconnA: "top1_connected_on A (subspace_topology X TX A)"
    assume hAne: "A \<noteq> {}"
    obtain x where hxA: "x \<in> A"
      using hAne by blast
    have hAsub: "A \<subseteq> top1_component_of_on X TX x"
      by (rule top1_connected_subspace_subset_component_of[OF hAX hxA hconnA])
    have hxX: "x \<in> X"
      using hAX hxA by blast
    have hComp: "top1_component_of_on X TX x \<in> top1_components_on X TX"
      by (rule top1_component_of_on_in_components[OF hxX])
    show "\<exists>C\<in>top1_components_on X TX. A \<subseteq> C"
      apply (rule bexI[where x="top1_component_of_on X TX x"])
       apply (rule hAsub)
      apply (rule hComp)
      done
  qed
qed

subsection \<open>Local connectedness\<close>

(** Local connectedness at a point: every open neighborhood contains a smaller connected open neighborhood. **)
definition top1_locally_connected_at :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_locally_connected_at X TX x \<longleftrightarrow>
     (\<forall>U. neighborhood_of x X TX U \<and> U \<subseteq> X \<longrightarrow>
        (\<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> U \<and> V \<subseteq> X
             \<and> top1_connected_on V (subspace_topology X TX V)))"

definition top1_locally_connected_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_locally_connected_on X TX \<longleftrightarrow> is_topology_on X TX \<and> (\<forall>x\<in>X. top1_locally_connected_at X TX x)"

(** from *\S25 Theorem 25.3 (Local connectedness via open components) [top1.tex:2987] **)
theorem Theorem_25_3:
  assumes hTX: "is_topology_on X TX"
  shows
    "top1_locally_connected_on X TX \<longleftrightarrow>
       (\<forall>U\<in>TX. U \<subseteq> X \<longrightarrow> (\<forall>C\<in>top1_components_on U (subspace_topology X TX U). C \<in> TX))"
proof (rule iffI)
  assume hLoc: "top1_locally_connected_on X TX"
  have hLocAll: "\<forall>x\<in>X. top1_locally_connected_at X TX x"
    using hLoc unfolding top1_locally_connected_on_def by blast

  have hUnionTX: "\<And>S. S \<subseteq> TX \<Longrightarrow> \<Union>S \<in> TX"
  proof -
    fix S assume hS: "S \<subseteq> TX"
    have "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
      using hTX unfolding is_topology_on_def by blast
    thus "\<Union>S \<in> TX"
      using hS by blast
  qed

  show "\<forall>U\<in>TX. U \<subseteq> X \<longrightarrow> (\<forall>C\<in>top1_components_on U (subspace_topology X TX U). C \<in> TX)"
  proof (rule ballI)
    fix U assume hU: "U \<in> TX"
    show "U \<subseteq> X \<longrightarrow> (\<forall>C\<in>top1_components_on U (subspace_topology X TX U). C \<in> TX)"
    proof (rule impI)
      assume hUX: "U \<subseteq> X"
      let ?TU = "subspace_topology X TX U"
      have hTU: "is_topology_on U ?TU"
        by (rule subspace_topology_is_topology_on[OF hTX hUX])

      show "\<forall>C\<in>top1_components_on U ?TU. C \<in> TX"
      proof (rule ballI)
        fix C assume hC: "C \<in> top1_components_on U ?TU"
        obtain u0 where hu0U: "u0 \<in> U" and hCeq: "C = top1_component_of_on U ?TU u0"
          using hC unfolding top1_components_on_def by blast

        have hCsubU: "C \<subseteq> U"
          unfolding hCeq by (rule top1_component_of_on_subset)

        have hC_open: "\<forall>x\<in>C. \<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> C \<and> V \<subseteq> X
            \<and> top1_connected_on V (subspace_topology X TX V)"
        proof (intro ballI)
          fix x assume hxC: "x \<in> C"
          have hxU: "x \<in> U"
            using hCsubU hxC by blast
          have hxX: "x \<in> X"
            using hUX hxU by blast
          have hU_nbhd: "neighborhood_of x X TX U"
            unfolding neighborhood_of_def using hU hxU by blast

          have hLocx: "top1_locally_connected_at X TX x"
            using hLocAll hxX by blast
          obtain V where hVnbhd: "neighborhood_of x X TX V"
            and hVsubU: "V \<subseteq> U"
            and hVX: "V \<subseteq> X"
            and hVconn: "top1_connected_on V (subspace_topology X TX V)"
            using hLocx hU_nbhd hUX unfolding top1_locally_connected_at_def by blast

          have hxV: "x \<in> V"
            using hVnbhd unfolding neighborhood_of_def by blast

          have hVconnU: "top1_connected_on V (subspace_topology U ?TU V)"
          proof -
            have hTopEq: "subspace_topology U ?TU V = subspace_topology X TX V"
              by (rule subspace_topology_trans[OF hVsubU])
            show ?thesis
              unfolding hTopEq by (rule hVconn)
          qed

          have hC_as_x: "C = top1_component_of_on U ?TU x"
          proof -
            have hx_mem: "x \<in> top1_component_of_on U ?TU u0"
              using hxC hCeq by simp
            have "top1_component_of_on U ?TU x = top1_component_of_on U ?TU u0"
              by (rule top1_component_of_on_eq_of_mem[OF hTU hx_mem])
            thus ?thesis
              unfolding hCeq by simp
          qed

          have hVsubC: "V \<subseteq> C"
          proof -
            have "V \<subseteq> top1_component_of_on U ?TU x"
              by (rule top1_connected_subspace_subset_component_of[OF hVsubU hxV hVconnU])
            thus ?thesis
              unfolding hC_as_x by simp
          qed

          show "\<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> C \<and> V \<subseteq> X
              \<and> top1_connected_on V (subspace_topology X TX V)"
            using hVnbhd hVsubC hVX hVconn by blast
        qed

        define VC where "VC = {V. \<exists>x\<in>C. neighborhood_of x X TX V \<and> V \<subseteq> C \<and> V \<subseteq> X
            \<and> top1_connected_on V (subspace_topology X TX V)}"

        have hVC_sub: "VC \<subseteq> TX"
        proof (rule subsetI)
          fix V assume hV: "V \<in> VC"
          obtain x where hxC: "x \<in> C" and hnbhd: "neighborhood_of x X TX V"
            and hVsub: "V \<subseteq> C" and hVX: "V \<subseteq> X"
            and hconnV: "top1_connected_on V (subspace_topology X TX V)"
            using hV unfolding VC_def by blast
          show "V \<in> TX"
            using hnbhd unfolding neighborhood_of_def by blast
        qed

        have hCeqUnion: "C = \<Union>VC"
        proof (rule equalityI)
          show "C \<subseteq> \<Union>VC"
          proof (rule subsetI)
            fix x assume hxC: "x \<in> C"
            obtain V where hVnbhd: "neighborhood_of x X TX V" and hVsubC: "V \<subseteq> C"
              and hVX: "V \<subseteq> X" and hVconn: "top1_connected_on V (subspace_topology X TX V)"
              using hC_open hxC by blast
            have hxV: "x \<in> V"
              using hVnbhd unfolding neighborhood_of_def by blast
            have "V \<in> VC"
              unfolding VC_def using hxC hVnbhd hVsubC hVX hVconn by blast
            thus "x \<in> \<Union>VC"
              using hxV by blast
          qed
          show "\<Union>VC \<subseteq> C"
            unfolding VC_def by blast
        qed

        have "C \<in> TX"
          unfolding hCeqUnion
          by (rule hUnionTX[OF hVC_sub])
        thus "C \<in> TX" .
      qed
    qed
  qed
next
  assume hOpenComp:
    "\<forall>U\<in>TX. U \<subseteq> X \<longrightarrow> (\<forall>C\<in>top1_components_on U (subspace_topology X TX U). C \<in> TX)"
  show "top1_locally_connected_on X TX"
    unfolding top1_locally_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on X TX"
      by (rule hTX)
    fix x assume hxX: "x \<in> X"
    show "top1_locally_connected_at X TX x"
      unfolding top1_locally_connected_at_def
    proof (intro allI impI)
      fix U assume hU: "neighborhood_of x X TX U \<and> U \<subseteq> X"
      have hUopen: "U \<in> TX"
        using hU unfolding neighborhood_of_def by blast
      have hxU: "x \<in> U"
        using hU unfolding neighborhood_of_def by blast
      have hUX: "U \<subseteq> X"
        using hU by blast

      let ?TU = "subspace_topology X TX U"
      have hTU: "is_topology_on U ?TU"
        by (rule subspace_topology_is_topology_on[OF hTX hUX])

      define C where "C = top1_component_of_on U ?TU x"

      have hCmem: "C \<in> top1_components_on U ?TU"
        unfolding C_def top1_components_on_def using hxU by blast
      have hCopen: "C \<in> TX"
        using hOpenComp hUopen hUX hCmem by blast

      have hxC: "x \<in> C"
        unfolding C_def by (rule top1_component_of_on_self_mem[OF hTU hxU])
      have hCsubU: "C \<subseteq> U"
        unfolding C_def by (rule top1_component_of_on_subset)
      have hCconnU: "top1_connected_on C (subspace_topology U ?TU C)"
        unfolding C_def by (rule top1_component_of_on_connected[OF hTU hxU])
      have hCconnX: "top1_connected_on C (subspace_topology X TX C)"
      proof -
        have hTopEq: "subspace_topology U ?TU C = subspace_topology X TX C"
          by (rule subspace_topology_trans[OF hCsubU])
        show ?thesis
          unfolding hTopEq[symmetric] by (rule hCconnU)
      qed

      have hCnbhd: "neighborhood_of x X TX C"
        unfolding neighborhood_of_def using hCopen hxC by blast

      show "\<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> U \<and> V \<subseteq> X
          \<and> top1_connected_on V (subspace_topology X TX V)"
        apply (rule exI[where x=C])
        using hCnbhd hCsubU hUX hCconnX by blast
    qed
  qed
qed

subsection \<open>Path components\<close>

text \<open>
  The remaining results of *\<S>25 concerning paths are recorded here with the intended definitions.
  Their proofs are currently omitted.
\<close>

definition top1_unit_interval :: "real set" where
  "top1_unit_interval = {0..1}"

definition top1_unit_interval_topology :: "real set set" where
  "top1_unit_interval_topology =
     subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval"

definition top1_is_path_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_is_path_on X TX x y f \<longleftrightarrow>
     top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f
     \<and> f 0 = x \<and> f 1 = y"

definition top1_in_same_path_component_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_in_same_path_component_on X TX x y \<longleftrightarrow> (\<exists>f. top1_is_path_on X TX x y f)"

definition top1_path_component_of_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "top1_path_component_of_on X TX x = {y. top1_in_same_path_component_on X TX x y}"

definition top1_path_components_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set set" where
  "top1_path_components_on X TX = {top1_path_component_of_on X TX x | x. x \<in> X}"

definition top1_path_connected_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_path_connected_on X TX \<longleftrightarrow>
     is_topology_on X TX \<and> (\<forall>x\<in>X. \<forall>y\<in>X. \<exists>f. top1_is_path_on X TX x y f)"

definition top1_locally_path_connected_at :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_locally_path_connected_at X TX x \<longleftrightarrow>
     (\<forall>U. neighborhood_of x X TX U \<and> U \<subseteq> X \<longrightarrow>
        (\<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> U \<and> V \<subseteq> X
             \<and> top1_path_connected_on V (subspace_topology X TX V)))"

definition top1_locally_path_connected_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_locally_path_connected_on X TX \<longleftrightarrow>
     is_topology_on X TX \<and> (\<forall>x\<in>X. top1_locally_path_connected_at X TX x)"

(** The unit interval topology is a topology (as a subspace of \<real>). **)
lemma top1_unit_interval_topology_is_topology_on:
  "is_topology_on top1_unit_interval top1_unit_interval_topology"
proof -
  have hTop: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hsub: "top1_unit_interval \<subseteq> (UNIV::real set)"
    by simp
  show ?thesis
    unfolding top1_unit_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF hTop hsub])
qed

(** The unit interval is connected (as a subspace of \<real>). **)
lemma top1_unit_interval_connected:
  "top1_connected_on top1_unit_interval top1_unit_interval_topology"
proof -
  have hconn: "connected top1_unit_interval"
    unfolding top1_unit_interval_def by simp
  show ?thesis
    unfolding top1_unit_interval_topology_def
    by (rule top1_connected_on_subspace_openI[OF hconn])
qed

(** Continuity transfer for real functions between subspace topologies induced by \<open>top1_open_sets\<close>. **)
lemma top1_continuous_map_on_real_subspace_open_sets:
  fixes S T :: "real set"
  assumes hmap: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T"
  assumes hcont: "continuous_on UNIV f"
  shows
    "top1_continuous_map_on S (subspace_topology (UNIV::real set) top1_open_sets S)
                           T (subspace_topology (UNIV::real set) top1_open_sets T) f"
proof -
  have hfT: "\<forall>x\<in>S. f x \<in> T"
    by (intro ballI, rule hmap)
  show ?thesis
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>S. f x \<in> T"
      using hfT .
    show "\<forall>V\<in>subspace_topology UNIV top1_open_sets T. {x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
    proof (intro ballI)
      fix V
      assume hV: "V \<in> subspace_topology UNIV top1_open_sets T"
      obtain U where hU: "U \<in> top1_open_sets" and hVeq: "V = T \<inter> U"
        using hV unfolding subspace_topology_def by blast
      have hopenU: "open U"
        using hU unfolding top1_open_sets_def by simp
      have hopen_pre: "open (f -` U)"
        by (rule open_vimage[OF hopenU hcont])
      have hpre_mem: "f -` U \<in> top1_open_sets"
        unfolding top1_open_sets_def using hopen_pre by simp
      have hEq: "{x \<in> S. f x \<in> V} = S \<inter> (f -` U)"
      proof (rule set_eqI)
        fix x
        show "x \<in> {x \<in> S. f x \<in> V} \<longleftrightarrow> x \<in> S \<inter> (f -` U)"
          unfolding hVeq using hfT by blast
      qed
      show "{x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
        unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x="f -` U"])
        apply (intro conjI)
         apply (simp add: hEq Int_commute Int_left_commute Int_assoc)
        apply (rule hpre_mem)
        done
    qed
  qed
qed

(** Paths can always be traversed in the reverse direction. **)
lemma top1_is_path_on_reverse:
  assumes hTX: "is_topology_on X TX"
  assumes hf: "top1_is_path_on X TX x y f"
  shows "top1_is_path_on X TX y x (\<lambda>t. f (1 - t))"
proof -
  have hI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  have contf: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hf0: "f 0 = x" and hf1: "f 1 = y"
    using hf unfolding top1_is_path_on_def by blast+

  have hmap_r: "\<And>t. t \<in> top1_unit_interval \<Longrightarrow> (1 - t) \<in> top1_unit_interval"
  proof -
    fix t
    assume ht: "t \<in> top1_unit_interval"
    have h0: "0 \<le> t" and h1: "t \<le> 1"
      using ht unfolding top1_unit_interval_def by simp+
    have "0 \<le> 1 - t"
      using h1 by simp
    moreover have "1 - t \<le> 1"
      using h0 by simp
    ultimately show "(1 - t) \<in> top1_unit_interval"
      unfolding top1_unit_interval_def by simp
  qed

  have cont_r:
    "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology top1_unit_interval top1_unit_interval_topology ((-) (1::real))"
    unfolding top1_unit_interval_topology_def
    apply (rule top1_continuous_map_on_real_subspace_open_sets)
     apply (simp add: hmap_r)
    apply (rule continuous_on_op_minus)
    done

  have cont_rev:
    "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX (f \<circ> ((-) (1::real)))"
    by (rule top1_continuous_map_on_comp[OF cont_r contf])

  have cont_rev': "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX (\<lambda>t. f (1 - t))"
  proof -
    have heq: "\<forall>t\<in>top1_unit_interval. (f \<circ> ((-) (1::real))) t = (\<lambda>t. f (1 - t)) t"
      by simp
    show ?thesis
      using top1_continuous_map_on_cong[OF heq] cont_rev by blast
  qed

  have hrev0: "(f \<circ> ((-) (1::real))) 0 = y"
    using hf1 by simp
  have hrev1: "(f \<circ> ((-) (1::real))) 1 = x"
    using hf0 by simp

  show ?thesis
    unfolding top1_is_path_on_def
    using cont_rev' hrev0 hrev1 by simp
qed

(** Concatenation of two paths. **)
lemma top1_is_path_on_append:
  assumes hTX: "is_topology_on X TX"
  assumes hf: "top1_is_path_on X TX x y f"
  assumes hg: "top1_is_path_on X TX y z g"
  shows "top1_is_path_on X TX x z (\<lambda>t. if t \<le> (1/2) then f (2 * t) else g (2 * t - 1))"
proof -
  have hI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  have contf: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have contg: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX g"
    using hg unfolding top1_is_path_on_def by blast
  have hf0: "f 0 = x" and hf1: "f 1 = y"
    using hf unfolding top1_is_path_on_def by blast+
  have hg0: "g 0 = y" and hg1: "g 1 = z"
    using hg unfolding top1_is_path_on_def by blast+

  let ?I = "top1_unit_interval"
  let ?TI = "top1_unit_interval_topology"
  let ?A = "{t \<in> ?I. t \<le> (1/2)}"
  let ?B = "{t \<in> ?I. (1/2) \<le> t}"

  have hA_sub: "?A \<subseteq> ?I" by blast
  have hB_sub: "?B \<subseteq> ?I" by blast

  have hI_eq: "?I = ?A \<union> ?B"
  proof (rule equalityI)
    show "?I \<subseteq> ?A \<union> ?B"
    proof (rule subsetI)
      fix t assume ht: "t \<in> ?I"
      have "t \<le> (1/2) \<or> (1/2) \<le> t"
      proof (cases "t \<le> (1/2)")
        case True
        show ?thesis
          using True by simp
      next
        case False
        have "(1/2) < t"
          using False by simp
        hence "(1/2) \<le> t"
          by simp
        thus ?thesis
          by simp
      qed
      thus "t \<in> ?A \<union> ?B"
        using ht by blast
    qed
    show "?A \<union> ?B \<subseteq> ?I"
      by blast
  qed

  have hIA: "?I - ?A = ?I \<inter> {(1/2) <..}"
  proof (rule equalityI)
    show "?I - ?A \<subseteq> ?I \<inter> {(1/2) <..}"
    proof (rule subsetI)
      fix t
      assume ht: "t \<in> ?I - ?A"
      have htI: "t \<in> ?I" and htNA: "t \<notin> ?A"
        using ht by blast+
      have htNle: "\<not> t \<le> (1/2)"
        using htI htNA by blast
      have hlt: "(1/2) < t"
        using htNle by (simp add: not_le)
      show "t \<in> ?I \<inter> {(1/2) <..}"
        using htI hlt by simp
    qed
    show "?I \<inter> {(1/2) <..} \<subseteq> ?I - ?A"
    proof (rule subsetI)
      fix t
      assume ht: "t \<in> ?I \<inter> {(1/2) <..}"
      have htI: "t \<in> ?I" and hlt: "(1/2) < t"
        using ht by blast+
      have htNle: "\<not> t \<le> (1/2)"
        using hlt by simp
      have "t \<notin> ?A"
        using htI htNle by blast
      thus "t \<in> ?I - ?A"
        using htI by blast
    qed
  qed
  have hIB: "?I - ?B = ?I \<inter> {..< (1/2)}"
  proof (rule equalityI)
    show "?I - ?B \<subseteq> ?I \<inter> {..< (1/2)}"
    proof (rule subsetI)
      fix t
      assume ht: "t \<in> ?I - ?B"
      have htI: "t \<in> ?I" and htNB: "t \<notin> ?B"
        using ht by blast+
      have htNge: "\<not> (1/2) \<le> t"
        using htI htNB by blast
      have hlt: "t < (1/2)"
        using htNge by (simp add: not_le)
      show "t \<in> ?I \<inter> {..< (1/2)}"
        using htI hlt by simp
    qed
    show "?I \<inter> {..< (1/2)} \<subseteq> ?I - ?B"
    proof (rule subsetI)
      fix t
      assume ht: "t \<in> ?I \<inter> {..< (1/2)}"
      have htI: "t \<in> ?I" and hlt: "t < (1/2)"
        using ht by blast+
      have htNge: "\<not> (1/2) \<le> t"
        using hlt by simp
      have "t \<notin> ?B"
        using htI htNge by blast
      thus "t \<in> ?I - ?B"
        using htI by blast
    qed
  qed

  have hOpen_gt: "{(1/2::real) <..} \<in> top1_open_sets"
    unfolding top1_open_sets_def by simp
  have hOpen_lt: "{..< (1/2::real)} \<in> top1_open_sets"
    unfolding top1_open_sets_def by simp

  have hIA_open: "?I - ?A \<in> ?TI"
    unfolding top1_unit_interval_topology_def subspace_topology_def
    apply (rule CollectI)
    apply (rule exI[where x="{(1/2::real) <..}"])
    apply (intro conjI)
     apply (rule hIA)
    apply (rule hOpen_gt)
    done
  have hIB_open: "?I - ?B \<in> ?TI"
    unfolding top1_unit_interval_topology_def subspace_topology_def
    apply (rule CollectI)
    apply (rule exI[where x="{..< (1/2::real)}"])
    apply (intro conjI)
     apply (rule hIB)
    apply (rule hOpen_lt)
    done

  have hA_closed: "closedin_on ?I ?TI ?A"
    by (rule closedin_intro[OF hA_sub hIA_open])
  have hB_closed: "closedin_on ?I ?TI ?B"
    by (rule closedin_intro[OF hB_sub hIB_open])

  have hmap_2t: "\<And>t. t \<in> ?A \<Longrightarrow> (2 * t) \<in> ?I"
  proof -
    fix t
    assume htA: "t \<in> ?A"
    have htI: "t \<in> ?I" and ht_le: "t \<le> (1/2)"
      using htA by blast+
    have ht0: "0 \<le> t"
      using htI unfolding top1_unit_interval_def by simp
    have h0: "0 \<le> 2 * t"
      using ht0 by simp
    have h1: "2 * t \<le> 1"
    proof -
      have h2pos: "0 \<le> (2::real)" by simp
      have "2 * t \<le> 2 * (1/2)"
        by (rule mult_left_mono[OF ht_le h2pos])
      thus ?thesis by simp
    qed
    show "2 * t \<in> ?I"
      unfolding top1_unit_interval_def using h0 h1 by simp
  qed

  have hmap_2t1: "\<And>t. t \<in> ?B \<Longrightarrow> (2 * t - 1) \<in> ?I"
  proof -
    fix t
    assume htB: "t \<in> ?B"
    have htI: "t \<in> ?I" and ht_ge: "(1/2) \<le> t"
      using htB by blast+
    have ht1: "t \<le> 1"
      using htI unfolding top1_unit_interval_def by simp
    have h0: "0 \<le> 2 * t - 1"
    proof -
      have h2pos: "0 \<le> (2::real)" by simp
      have "2 * (1/2) \<le> 2 * t"
        by (rule mult_left_mono[OF ht_ge h2pos])
      hence "1 \<le> 2 * t" by simp
      thus ?thesis by simp
    qed
    have h1: "2 * t - 1 \<le> 1"
    proof -
      have h2pos: "0 \<le> (2::real)" by simp
      have "2 * t \<le> 2 * 1"
        by (rule mult_left_mono[OF ht1 h2pos])
      hence "2 * t - 1 \<le> 2 - 1"
        by simp
      thus ?thesis by simp
    qed
    show "2 * t - 1 \<in> ?I"
      unfolding top1_unit_interval_def using h0 h1 by simp
  qed

  have hTopA: "subspace_topology ?I (subspace_topology (UNIV::real set) top1_open_sets ?I) ?A =
               subspace_topology (UNIV::real set) top1_open_sets ?A"
    by (rule subspace_topology_trans[OF hA_sub])
  have hTopB: "subspace_topology ?I (subspace_topology (UNIV::real set) top1_open_sets ?I) ?B =
               subspace_topology (UNIV::real set) top1_open_sets ?B"
    by (rule subspace_topology_trans[OF hB_sub])

  have cont_2t_A:
    "top1_continuous_map_on ?A (subspace_topology ?I ?TI ?A) ?I ?TI ((*) (2::real))"
  proof -
    have hmap': "\<And>x. x \<in> ?A \<Longrightarrow> ((*) (2::real)) x \<in> ?I"
      using hmap_2t by simp
    have hcont': "continuous_on UNIV ((*) (2::real))"
      by simp

    have cont':
      "top1_continuous_map_on ?A (subspace_topology UNIV top1_open_sets ?A)
         ?I (subspace_topology UNIV top1_open_sets ?I) ((*) (2::real))"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap' hcont'])

	    show ?thesis
	      unfolding top1_unit_interval_topology_def
	      apply (subst hTopA)
	      apply (rule cont')
	      done
	  qed

  have cont_2t1_B:
    "top1_continuous_map_on ?B (subspace_topology ?I ?TI ?B) ?I ?TI (\<lambda>t. 2 * t - 1)"
  proof -
    have hmap': "\<And>x. x \<in> ?B \<Longrightarrow> (\<lambda>t. 2 * t - 1) x \<in> ?I"
      using hmap_2t1 by simp
    have hcont': "continuous_on UNIV (\<lambda>t::real. 2 * t - 1)"
      apply (rule continuous_on_diff)
       apply (rule continuous_on_mult_left)
       apply (rule continuous_on_id)
      apply (rule continuous_on_const)
      done

    have cont':
      "top1_continuous_map_on ?B (subspace_topology UNIV top1_open_sets ?B)
         ?I (subspace_topology UNIV top1_open_sets ?I) (\<lambda>t. 2 * t - 1)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap' hcont'])

	    show ?thesis
	      unfolding top1_unit_interval_topology_def
	      apply (subst hTopB)
	      apply (rule cont')
	      done
	  qed

  have cont_fA:
    "top1_continuous_map_on ?A (subspace_topology ?I ?TI ?A) X TX (\<lambda>t. f (2 * t))"
  proof -
    have hcont_comp:
      "top1_continuous_map_on ?A (subspace_topology ?I ?TI ?A) X TX (f \<circ> ((*) (2::real)))"
      by (rule top1_continuous_map_on_comp[OF cont_2t_A contf])
    have heq: "\<forall>t\<in>?A. (f \<circ> ((*) (2::real))) t = (\<lambda>t. f (2 * t)) t"
      by simp
    have "top1_continuous_map_on ?A (subspace_topology ?I ?TI ?A) X TX (\<lambda>t. f (2 * t))"
      using top1_continuous_map_on_cong[OF heq] hcont_comp by blast
    thus ?thesis .
  qed

  have cont_gB:
    "top1_continuous_map_on ?B (subspace_topology ?I ?TI ?B) X TX (\<lambda>t. g (2 * t - 1))"
  proof -
    have hcont_comp:
      "top1_continuous_map_on ?B (subspace_topology ?I ?TI ?B) X TX (g \<circ> (\<lambda>t. 2 * t - 1))"
      by (rule top1_continuous_map_on_comp[OF cont_2t1_B contg])
    have heq: "\<forall>t\<in>?B. (g \<circ> (\<lambda>t. 2 * t - 1)) t = (\<lambda>t. g (2 * t - 1)) t"
      by simp
    have "top1_continuous_map_on ?B (subspace_topology ?I ?TI ?B) X TX (\<lambda>t. g (2 * t - 1))"
      using top1_continuous_map_on_cong[OF heq] hcont_comp by blast
    thus ?thesis .
  qed

  have agree_mid: "\<forall>t\<in>(?A \<inter> ?B). f (2 * t) = g (2 * t - 1)"
  proof (intro ballI)
    fix t
    assume ht: "t \<in> ?A \<inter> ?B"
    have ht1: "t \<le> (1/2)" and ht2: "(1/2) \<le> t"
      using ht by blast+
    have htEq: "t = (1/2)"
      using ht1 ht2 by simp
    show "f (2 * t) = g (2 * t - 1)"
      by (simp add: htEq hf1 hg0)
  qed

  have cont_h_mem:
    "top1_continuous_map_on ?I ?TI X TX (\<lambda>t. if t \<in> ?A then f (2 * t) else g (2 * t - 1))"
  proof -
    have hcont:
	      "top1_continuous_map_on ?I ?TI X TX
	        (\<lambda>t. if t \<in> ?A then (\<lambda>t. f (2 * t)) t else (\<lambda>t. g (2 * t - 1)) t)"
	      apply (rule Theorem_18_3[where A="?A" and B="?B"
	            and f="(\<lambda>t. f (2 * t))" and g="(\<lambda>t. g (2 * t - 1))"])
	              apply (rule hI)
	             apply (rule hTX)
	            apply (rule hA_closed)
	           apply (rule hB_closed)
          apply (rule hI_eq)
	         apply (rule cont_fA)
	        apply (rule cont_gB)
	       apply (rule agree_mid)
	      done
	    show ?thesis
	      using hcont by simp
	  qed

  define h where "h = (\<lambda>t. if t \<le> (1/2) then f (2 * t) else g (2 * t - 1))"

  have heq:
    "\<forall>t\<in>?I. h t = (\<lambda>t. if t \<in> ?A then f (2 * t) else g (2 * t - 1)) t"
    unfolding h_def by simp

  have cont_h: "top1_continuous_map_on ?I ?TI X TX h"
    using top1_continuous_map_on_cong[OF heq] cont_h_mem by blast

  have h0: "h 0 = x"
    unfolding h_def using hf0 by simp
  have h1: "h 1 = z"
    unfolding h_def using hg1 by simp

  show ?thesis
    unfolding top1_is_path_on_def
  proof (intro conjI)
    have cont_h': "top1_continuous_map_on ?I ?TI X TX (\<lambda>t. if t \<le> (1/2) then f (2 * t) else g (2 * t - 1))"
      using cont_h unfolding h_def by simp
    show "top1_continuous_map_on ?I ?TI X TX (\<lambda>t. if t \<le> (1/2) then f (2 * t) else g (2 * t - 1))"
      by (rule cont_h')
    show "(\<lambda>t. if t \<le> (1/2) then f (2 * t) else g (2 * t - 1)) 0 = x"
      using hf0 by simp
    show "(\<lambda>t. if t \<le> (1/2) then f (2 * t) else g (2 * t - 1)) 1 = z"
      using hg1 by simp
  qed
qed

(** Any point on a path from \<open>x\<close> is in the same path component as \<open>x\<close>. **)
lemma top1_is_path_on_point_in_path_component:
  assumes hTX: "is_topology_on X TX"
  assumes hf: "top1_is_path_on X TX x y f"
  assumes ht: "t \<in> top1_unit_interval"
  shows "top1_in_same_path_component_on X TX x (f t)"
proof -
  have contf: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hf0: "f 0 = x"
    using hf unfolding top1_is_path_on_def by blast

  have ht0: "0 \<le> t" and ht1: "t \<le> 1"
    using ht unfolding top1_unit_interval_def by simp+

  have hmap_scale: "\<And>s. s \<in> top1_unit_interval \<Longrightarrow> t * s \<in> top1_unit_interval"
  proof -
    fix s
    assume hs: "s \<in> top1_unit_interval"
    have hs0: "0 \<le> s" and hs1: "s \<le> 1"
      using hs unfolding top1_unit_interval_def by simp+
    have h0: "0 \<le> t * s"
      using ht0 hs0 by simp
    have h1: "t * s \<le> 1"
    proof -
      have "t * s \<le> t * 1"
        by (rule mult_left_mono[OF hs1 ht0])
      also have "... \<le> 1"
        using ht1 by simp
      finally show ?thesis by simp
    qed
    show "t * s \<in> top1_unit_interval"
      unfolding top1_unit_interval_def using h0 h1 by simp
  qed

  have cont_scale:
    "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology top1_unit_interval top1_unit_interval_topology (\<lambda>s. t * s)"
  proof -
    have hmap: "\<And>x. x \<in> top1_unit_interval \<Longrightarrow> (\<lambda>s. t * s) x \<in> top1_unit_interval"
      using hmap_scale by simp
    have hcont: "continuous_on UNIV (\<lambda>s::real. t * s)"
      apply (rule continuous_on_mult)
       apply (rule continuous_on_const)
      apply (rule continuous_on_id)
      done
    show ?thesis
      unfolding top1_unit_interval_topology_def
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
  qed

  have cont_comp:
    "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX (f \<circ> (\<lambda>s. t * s))"
    by (rule top1_continuous_map_on_comp[OF cont_scale contf])

  have h0: "(f \<circ> (\<lambda>s. t * s)) 0 = x"
    using hf0 by simp
  have h1: "(f \<circ> (\<lambda>s. t * s)) 1 = f t"
    by simp

  show ?thesis
    unfolding top1_in_same_path_component_on_def
    apply (rule exI[where x="f \<circ> (\<lambda>s. t * s)"])
    unfolding top1_is_path_on_def
    using cont_comp h0 h1 by simp
qed

(** Path components are contained in the carrier. **)
lemma top1_path_component_of_on_subset:
  assumes hTX: "is_topology_on X TX"
  assumes hx: "x \<in> X"
  shows "top1_path_component_of_on X TX x \<subseteq> X"
proof (rule subsetI)
  fix y
  assume hy: "y \<in> top1_path_component_of_on X TX x"
  have hxy: "top1_in_same_path_component_on X TX x y"
    using hy unfolding top1_path_component_of_on_def by simp
  obtain f where hf: "top1_is_path_on X TX x y f"
    using hxy unfolding top1_in_same_path_component_on_def by blast
  have contf: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have mapf: "\<forall>t\<in>top1_unit_interval. f t \<in> X"
    using contf unfolding top1_continuous_map_on_def by blast
  have h1: "1 \<in> top1_unit_interval"
    unfolding top1_unit_interval_def by simp
  have "f 1 \<in> X"
    using mapf h1 by blast
  thus "y \<in> X"
    using hf unfolding top1_is_path_on_def by simp
qed

(** The relation \<open>top1_in_same_path_component_on\<close> is symmetric. **)
lemma top1_in_same_path_component_on_sym:
  assumes hTX: "is_topology_on X TX"
  assumes hxy: "top1_in_same_path_component_on X TX x y"
  shows "top1_in_same_path_component_on X TX y x"
proof -
  obtain f where hf: "top1_is_path_on X TX x y f"
    using hxy unfolding top1_in_same_path_component_on_def by blast
  have "top1_is_path_on X TX y x (\<lambda>t. f (1 - t))"
    by (rule top1_is_path_on_reverse[OF hTX hf])
  thus ?thesis
    unfolding top1_in_same_path_component_on_def by blast
qed

(** The relation \<open>top1_in_same_path_component_on\<close> is transitive. **)
lemma top1_in_same_path_component_on_trans:
  assumes hTX: "is_topology_on X TX"
  assumes hxy: "top1_in_same_path_component_on X TX x y"
  assumes hyz: "top1_in_same_path_component_on X TX y z"
  shows "top1_in_same_path_component_on X TX x z"
proof -
  obtain f where hf: "top1_is_path_on X TX x y f"
    using hxy unfolding top1_in_same_path_component_on_def by blast
  obtain g where hg: "top1_is_path_on X TX y z g"
    using hyz unfolding top1_in_same_path_component_on_def by blast
  have hh: "top1_is_path_on X TX x z (\<lambda>t. if t \<le> (1/2) then f (2 * t) else g (2 * t - 1))"
    by (rule top1_is_path_on_append[OF hTX hf hg])
  show ?thesis
    unfolding top1_in_same_path_component_on_def using hh by blast
qed

(** from *\S25 Theorem 25.2 (Path components) [top1.tex:2967] **)
theorem Theorem_25_2:
  assumes hTX: "is_topology_on X TX"
  shows
    "(\<Union>(top1_path_components_on X TX)) = X"
    and "\<And>P Q. P \<in> top1_path_components_on X TX \<Longrightarrow> Q \<in> top1_path_components_on X TX \<Longrightarrow> P \<inter> Q \<noteq> {} \<Longrightarrow> P = Q"
    and "\<And>P. P \<in> top1_path_components_on X TX \<Longrightarrow> top1_path_connected_on P (subspace_topology X TX P)"
    and "\<And>A. A \<subseteq> X \<Longrightarrow> top1_path_connected_on A (subspace_topology X TX A) \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
              (\<exists>P\<in>top1_path_components_on X TX. A \<subseteq> P)"
proof -
  have hI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)

  show "(\<Union>(top1_path_components_on X TX)) = X"
  proof (rule equalityI)
    show "\<Union>(top1_path_components_on X TX) \<subseteq> X"
    proof (rule subsetI)
      fix y
      assume hy: "y \<in> \<Union>(top1_path_components_on X TX)"
      obtain P where hP: "P \<in> top1_path_components_on X TX" and hyP: "y \<in> P"
        using hy by blast
      obtain x where hxX: "x \<in> X" and hPeq: "P = top1_path_component_of_on X TX x"
        using hP unfolding top1_path_components_on_def by blast
      have hy_comp: "top1_in_same_path_component_on X TX x y"
        using hyP hPeq unfolding top1_path_component_of_on_def by simp
      obtain f where hf: "top1_is_path_on X TX x y f"
        using hy_comp unfolding top1_in_same_path_component_on_def by blast
      have contf: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
        using hf unfolding top1_is_path_on_def by blast
      have mapf: "\<forall>t\<in>top1_unit_interval. f t \<in> X"
        using contf unfolding top1_continuous_map_on_def by blast
      have h1: "1 \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by simp
      have "f 1 \<in> X"
        using mapf h1 by blast
      thus "y \<in> X"
        using hf unfolding top1_is_path_on_def by simp
    qed
    show "X \<subseteq> \<Union>(top1_path_components_on X TX)"
    proof (rule subsetI)
      fix x
      assume hxX: "x \<in> X"
      have hx_rel: "top1_in_same_path_component_on X TX x x"
        unfolding top1_in_same_path_component_on_def
        apply (rule exI[where x="(\<lambda>t. x)"])
        unfolding top1_is_path_on_def
        apply (intro conjI)
         apply (rule top1_continuous_map_on_const[OF hI hTX hxX])
        apply (rule refl)
        apply (rule refl)
        done
      have hx_mem: "x \<in> top1_path_component_of_on X TX x"
        unfolding top1_path_component_of_on_def using hx_rel by simp
      have hPc: "top1_path_component_of_on X TX x \<in> top1_path_components_on X TX"
        unfolding top1_path_components_on_def using hxX by blast
      show "x \<in> \<Union>(top1_path_components_on X TX)"
        using hPc hx_mem by blast
    qed
  qed

  show "\<And>P Q. P \<in> top1_path_components_on X TX \<Longrightarrow> Q \<in> top1_path_components_on X TX \<Longrightarrow> P \<inter> Q \<noteq> {} \<Longrightarrow> P = Q"
  proof -
    fix P Q
    assume hP: "P \<in> top1_path_components_on X TX"
    assume hQ: "Q \<in> top1_path_components_on X TX"
    assume hPQ: "P \<inter> Q \<noteq> {}"
    obtain x where hxX: "x \<in> X" and hPeq: "P = top1_path_component_of_on X TX x"
      using hP unfolding top1_path_components_on_def by blast
    obtain y where hyX: "y \<in> X" and hQeq: "Q = top1_path_component_of_on X TX y"
      using hQ unfolding top1_path_components_on_def by blast
    obtain p where hp: "p \<in> P \<inter> Q"
      using hPQ by blast
    have hxp: "top1_in_same_path_component_on X TX x p"
      using hp hPeq unfolding top1_path_component_of_on_def by blast
    have hyp: "top1_in_same_path_component_on X TX y p"
      using hp hQeq unfolding top1_path_component_of_on_def by blast
    have hpy: "top1_in_same_path_component_on X TX p y"
      by (rule top1_in_same_path_component_on_sym[OF hTX hyp])
    have hxy: "top1_in_same_path_component_on X TX x y"
      by (rule top1_in_same_path_component_on_trans[OF hTX hxp hpy])

    have hcomp_eq: "top1_path_component_of_on X TX x = top1_path_component_of_on X TX y"
    proof (rule set_eqI)
      fix z
      show "z \<in> top1_path_component_of_on X TX x \<longleftrightarrow> z \<in> top1_path_component_of_on X TX y"
      proof
        assume hz: "z \<in> top1_path_component_of_on X TX x"
        have hxz: "top1_in_same_path_component_on X TX x z"
          using hz unfolding top1_path_component_of_on_def by simp
        have hyx: "top1_in_same_path_component_on X TX y x"
          by (rule top1_in_same_path_component_on_sym[OF hTX hxy])
        have hyz: "top1_in_same_path_component_on X TX y z"
          by (rule top1_in_same_path_component_on_trans[OF hTX hyx hxz])
        show "z \<in> top1_path_component_of_on X TX y"
          unfolding top1_path_component_of_on_def using hyz by simp
      next
        assume hz: "z \<in> top1_path_component_of_on X TX y"
        have hyz: "top1_in_same_path_component_on X TX y z"
          using hz unfolding top1_path_component_of_on_def by simp
        have hxy': "top1_in_same_path_component_on X TX x y"
          using hxy .
        have hxz: "top1_in_same_path_component_on X TX x z"
          by (rule top1_in_same_path_component_on_trans[OF hTX hxy' hyz])
        show "z \<in> top1_path_component_of_on X TX x"
          unfolding top1_path_component_of_on_def using hxz by simp
      qed
    qed
    show "P = Q"
      using hPeq hQeq hcomp_eq by simp
  qed

  show "\<And>P. P \<in> top1_path_components_on X TX \<Longrightarrow> top1_path_connected_on P (subspace_topology X TX P)"
  proof -
    fix P
    assume hP: "P \<in> top1_path_components_on X TX"
    obtain x0 where hx0X: "x0 \<in> X" and hPeq: "P = top1_path_component_of_on X TX x0"
      using hP unfolding top1_path_components_on_def by blast

    have hPX: "P \<subseteq> X"
      using hPeq hx0X by (simp add: top1_path_component_of_on_subset[OF hTX])

    have hTopP: "is_topology_on P (subspace_topology X TX P)"
      by (rule subspace_topology_is_topology_on[OF hTX hPX])

    have paths_P:
      "\<forall>a\<in>P. \<forall>b\<in>P. \<exists>h. top1_is_path_on P (subspace_topology X TX P) a b h"
    proof (intro ballI)
      fix a assume haP: "a \<in> P"
      fix b assume hbP: "b \<in> P"

      have ha_rel: "top1_in_same_path_component_on X TX x0 a"
        using haP hPeq unfolding top1_path_component_of_on_def by simp
      have hb_rel: "top1_in_same_path_component_on X TX x0 b"
        using hbP hPeq unfolding top1_path_component_of_on_def by simp
      obtain fa where hfa: "top1_is_path_on X TX x0 a fa"
        using ha_rel unfolding top1_in_same_path_component_on_def by blast
      obtain fb where hfb: "top1_is_path_on X TX x0 b fb"
        using hb_rel unfolding top1_in_same_path_component_on_def by blast

      define ra where "ra = (\<lambda>t. fa (1 - t))"
      have hra: "top1_is_path_on X TX a x0 ra"
        unfolding ra_def
        by (rule top1_is_path_on_reverse[OF hTX hfa])

      define h0 where "h0 = (\<lambda>t. if t \<le> (1/2) then ra (2 * t) else fb (2 * t - 1))"
      have hh0: "top1_is_path_on X TX a b h0"
        unfolding h0_def
        by (rule top1_is_path_on_append[OF hTX hra hfb])

      have h0_img: "\<forall>t\<in>top1_unit_interval. h0 t \<in> P"
      proof (intro ballI)
        fix t assume ht: "t \<in> top1_unit_interval"
        show "h0 t \<in> P"
        proof (cases "t \<le> (1/2)")
          case True
          have htA: "2 * t \<in> top1_unit_interval"
          proof -
            have ht0: "0 \<le> t" and ht1: "t \<le> 1"
              using ht unfolding top1_unit_interval_def by simp+
            have h0: "0 \<le> 2 * t"
              using ht0 by simp
            have h1: "2 * t \<le> 1"
            proof -
              have h2pos: "0 \<le> (2::real)" by simp
              have "2 * t \<le> 2 * (1/2)"
                by (rule mult_left_mono[OF True h2pos])
              thus ?thesis by simp
            qed
            show ?thesis
              unfolding top1_unit_interval_def using h0 h1 by simp
          qed
          have hmem: "top1_in_same_path_component_on X TX x0 (ra (2 * t))"
          proof -
            have hmap: "(1 - (2 * t)) \<in> top1_unit_interval"
            proof -
              have ht0: "0 \<le> t"
                using ht unfolding top1_unit_interval_def by simp
              have "2 * t \<le> 1"
                using htA unfolding top1_unit_interval_def by simp
              hence "0 \<le> 1 - (2 * t)" by simp
              moreover have "1 - (2 * t) \<le> 1"
              proof -
                have "0 \<le> 2 * t"
                  using ht0 by simp
                thus ?thesis
                  by simp
              qed
              ultimately show ?thesis
                unfolding top1_unit_interval_def by simp
            qed
            have "top1_in_same_path_component_on X TX x0 (fa (1 - (2 * t)))"
              by (rule top1_is_path_on_point_in_path_component[OF hTX hfa hmap])
            thus ?thesis
              unfolding ra_def by simp
          qed
          show ?thesis
            unfolding hPeq top1_path_component_of_on_def h0_def
            using True hmem by simp
        next
          case False
          have htB: "2 * t - 1 \<in> top1_unit_interval"
          proof -
            have ht0: "0 \<le> t" and ht1: "t \<le> 1"
              using ht unfolding top1_unit_interval_def by simp+
            have hge: "(1/2) \<le> t"
              using False by simp
            have h0: "0 \<le> 2 * t - 1"
            proof -
              have h2pos: "0 \<le> (2::real)" by simp
              have "2 * (1/2) \<le> 2 * t"
                by (rule mult_left_mono[OF hge h2pos])
              hence "1 \<le> 2 * t" by simp
              thus ?thesis by simp
            qed
            have h1: "2 * t - 1 \<le> 1"
            proof -
              have h2pos: "0 \<le> (2::real)" by simp
              have "2 * t \<le> 2 * 1"
                by (rule mult_left_mono[OF ht1 h2pos])
              hence "2 * t - 1 \<le> 2 - 1" by simp
              thus ?thesis by simp
            qed
            show ?thesis
              unfolding top1_unit_interval_def using h0 h1 by simp
          qed
          have hmem: "top1_in_same_path_component_on X TX x0 (fb (2 * t - 1))"
            by (rule top1_is_path_on_point_in_path_component[OF hTX hfb htB])
          show ?thesis
            unfolding hPeq top1_path_component_of_on_def h0_def
            using False hmem by simp
        qed
      qed

      have h0_img_set: "h0 ` top1_unit_interval \<subseteq> P"
        using h0_img by blast

      have restrict_range:
        "(\<forall>W f. top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f
            \<and> W \<subseteq> X \<and> f ` top1_unit_interval \<subseteq> W
            \<longrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology W (subspace_topology X TX W) f)"
        using Theorem_18_2(5)[OF hI hTX hTX] .

      have cont_h0X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX h0"
        using hh0 unfolding top1_is_path_on_def by blast
      have cont_h0P:
        "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology P (subspace_topology X TX P) h0"
        using restrict_range cont_h0X hPX h0_img_set by blast

      have h00: "h0 0 = a" and h01: "h0 1 = b"
        using hh0 unfolding top1_is_path_on_def by blast+

      have "top1_is_path_on P (subspace_topology X TX P) a b h0"
        unfolding top1_is_path_on_def
        using cont_h0P h00 h01 by simp
      thus "\<exists>h. top1_is_path_on P (subspace_topology X TX P) a b h"
        by blast
    qed

    show "top1_path_connected_on P (subspace_topology X TX P)"
      unfolding top1_path_connected_on_def
      using hTopP paths_P by blast
  qed

  show "\<And>A. A \<subseteq> X \<Longrightarrow> top1_path_connected_on A (subspace_topology X TX A) \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
            (\<exists>P\<in>top1_path_components_on X TX. A \<subseteq> P)"
  proof -
    fix A
    assume hAX: "A \<subseteq> X"
    assume hApc: "top1_path_connected_on A (subspace_topology X TX A)"
    assume hAne: "A \<noteq> {}"
    obtain x0 where hx0A: "x0 \<in> A"
      using hAne by blast
    have hx0X: "x0 \<in> X"
      using hAX hx0A by blast

    have hTopA: "is_topology_on A (subspace_topology X TX A)"
      using hApc unfolding top1_path_connected_on_def by blast
    have hpathsA: "\<forall>x\<in>A. \<forall>y\<in>A. \<exists>f. top1_is_path_on A (subspace_topology X TX A) x y f"
      using hApc unfolding top1_path_connected_on_def by blast

    have hAsubP: "A \<subseteq> top1_path_component_of_on X TX x0"
    proof (rule subsetI)
      fix y
      assume hyA: "y \<in> A"
      obtain f where hf: "top1_is_path_on A (subspace_topology X TX A) x0 y f"
        using hpathsA hx0A hyA by blast
      have contA: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A (subspace_topology X TX A) f"
        using hf unfolding top1_is_path_on_def by blast

      have contX: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
      proof -
        have rule:
          "(\<forall>W g. top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A (subspace_topology X TX A) g
              \<and> A \<subseteq> W \<and> subspace_topology X TX A = subspace_topology W TX A
              \<longrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology W TX g)"
          using Theorem_18_2(6)[OF hI hTopA hTX] by blast
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
          using rule contA hAX by simp
        thus ?thesis .
      qed

      have hx0: "f 0 = x0" and hy: "f 1 = y"
        using hf unfolding top1_is_path_on_def by blast+
      have hpathX: "top1_is_path_on X TX x0 y f"
        unfolding top1_is_path_on_def using contX hx0 hy by simp
      have "top1_in_same_path_component_on X TX x0 y"
        unfolding top1_in_same_path_component_on_def using hpathX by blast
      thus "y \<in> top1_path_component_of_on X TX x0"
        unfolding top1_path_component_of_on_def by simp
    qed

    have hPc: "top1_path_component_of_on X TX x0 \<in> top1_path_components_on X TX"
      unfolding top1_path_components_on_def using hx0X by blast
    show "\<exists>P\<in>top1_path_components_on X TX. A \<subseteq> P"
      using hPc hAsubP by blast
  qed
qed

(** Reflexivity for path components: each point is in the same path component as itself. **)
lemma top1_in_same_path_component_on_refl:
  assumes hTX: "is_topology_on X TX"
  assumes hxX: "x \<in> X"
  shows "top1_in_same_path_component_on X TX x x"
proof -
  have hI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hpath: "top1_is_path_on X TX x x (\<lambda>t. x)"
    unfolding top1_is_path_on_def
    apply (intro conjI)
     apply (rule top1_continuous_map_on_const[OF hI hTX hxX])
    apply (rule refl)
    apply (rule refl)
    done
  show ?thesis
    unfolding top1_in_same_path_component_on_def using hpath by blast
qed

(** Each point belongs to its own path component. **)
lemma top1_path_component_of_on_self_mem:
  assumes hTX: "is_topology_on X TX"
  assumes hxX: "x \<in> X"
  shows "x \<in> top1_path_component_of_on X TX x"
  unfolding top1_path_component_of_on_def
  by (simp add: top1_in_same_path_component_on_refl[OF hTX hxX])

(** A path component is a member of the collection of path components. **)
lemma top1_path_component_of_on_in_components:
  assumes hxX: "x \<in> X"
  shows "top1_path_component_of_on X TX x \<in> top1_path_components_on X TX"
  unfolding top1_path_components_on_def using hxX by blast

(** If \<open>y\<close> lies in the path component of \<open>x\<close>, then their path components coincide. **)
lemma top1_path_component_of_on_eq_of_mem:
  assumes hTX: "is_topology_on X TX"
  assumes hy: "y \<in> top1_path_component_of_on X TX x"
  shows "top1_path_component_of_on X TX y = top1_path_component_of_on X TX x"
proof (rule equalityI)
  show "top1_path_component_of_on X TX y \<subseteq> top1_path_component_of_on X TX x"
  proof (rule subsetI)
    fix z assume hz: "z \<in> top1_path_component_of_on X TX y"
    have hxy: "top1_in_same_path_component_on X TX x y"
      using hy unfolding top1_path_component_of_on_def by simp
    have hyz: "top1_in_same_path_component_on X TX y z"
      using hz unfolding top1_path_component_of_on_def by simp
    have hxz: "top1_in_same_path_component_on X TX x z"
      by (rule top1_in_same_path_component_on_trans[OF hTX hxy hyz])
    show "z \<in> top1_path_component_of_on X TX x"
      unfolding top1_path_component_of_on_def using hxz by simp
  qed
  show "top1_path_component_of_on X TX x \<subseteq> top1_path_component_of_on X TX y"
  proof (rule subsetI)
    fix z assume hz: "z \<in> top1_path_component_of_on X TX x"
    have hxy: "top1_in_same_path_component_on X TX x y"
      using hy unfolding top1_path_component_of_on_def by simp
    have hyx: "top1_in_same_path_component_on X TX y x"
      by (rule top1_in_same_path_component_on_sym[OF hTX hxy])
    have hxz: "top1_in_same_path_component_on X TX x z"
      using hz unfolding top1_path_component_of_on_def by simp
    have hyz: "top1_in_same_path_component_on X TX y z"
      by (rule top1_in_same_path_component_on_trans[OF hTX hyx hxz])
    show "z \<in> top1_path_component_of_on X TX y"
      unfolding top1_path_component_of_on_def using hyz by simp
  qed
qed

(** A path component is path connected (with the subspace topology). **)
lemma top1_path_component_of_on_path_connected:
  assumes hTX: "is_topology_on X TX"
  assumes hxX: "x \<in> X"
  shows "top1_path_connected_on (top1_path_component_of_on X TX x)
           (subspace_topology X TX (top1_path_component_of_on X TX x))"
proof -
  have hP: "top1_path_component_of_on X TX x \<in> top1_path_components_on X TX"
    by (rule top1_path_component_of_on_in_components[OF hxX])
  show ?thesis
    by (rule Theorem_25_2(3)[OF hTX hP])
qed

(** A path connected subspace lies in a single path component. **)
lemma top1_path_connected_subspace_subset_path_component_of:
  assumes hTX: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hxA: "x \<in> A"
  assumes hApath: "top1_path_connected_on A (subspace_topology X TX A)"
  shows "A \<subseteq> top1_path_component_of_on X TX x"
proof (rule subsetI)
  fix y assume hyA: "y \<in> A"
  have hI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  let ?TA = "subspace_topology X TX A"
  have hTA: "is_topology_on A ?TA"
    using hApath unfolding top1_path_connected_on_def by blast
  have hpathA: "\<exists>f. top1_is_path_on A ?TA x y f"
    using hApath hxA hyA unfolding top1_path_connected_on_def by blast
  obtain f where hfA: "top1_is_path_on A ?TA x y f"
    using hpathA by blast
  have hcontA: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A ?TA f"
    using hfA unfolding top1_is_path_on_def by blast
  have hfx: "f 0 = x" and hfy: "f 1 = y"
    using hfA unfolding top1_is_path_on_def by blast+

  have hcontX: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
  proof -
    have rule:
      "\<And>W g. top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A ?TA g
          \<Longrightarrow> A \<subseteq> W \<Longrightarrow> ?TA = subspace_topology W TX A
          \<Longrightarrow> top1_continuous_map_on top1_unit_interval top1_unit_interval_topology W TX g"
      using Theorem_18_2(6)[OF hI hTA hTX] by blast
    have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
      by (rule rule[OF hcontA hAX], simp)
    thus ?thesis .
  qed

  have hfX: "top1_is_path_on X TX x y f"
    unfolding top1_is_path_on_def using hcontX hfx hfy by simp
  have "top1_in_same_path_component_on X TX x y"
    unfolding top1_in_same_path_component_on_def using hfX by blast
  thus "y \<in> top1_path_component_of_on X TX x"
    unfolding top1_path_component_of_on_def by simp
qed

(** from *\S25 Theorem 25.4 (Local path connectedness via open path components) [top1.tex:2995] **)
theorem Theorem_25_4:
  assumes hTX: "is_topology_on X TX"
  shows
    "top1_locally_path_connected_on X TX \<longleftrightarrow>
       (\<forall>U\<in>TX. U \<subseteq> X \<longrightarrow> (\<forall>P\<in>top1_path_components_on U (subspace_topology X TX U). P \<in> TX))"
proof (rule iffI)
  assume hLoc: "top1_locally_path_connected_on X TX"
  have hLocAll: "\<forall>x\<in>X. top1_locally_path_connected_at X TX x"
    using hLoc unfolding top1_locally_path_connected_on_def by blast

  have hUnionTX: "\<And>S. S \<subseteq> TX \<Longrightarrow> \<Union>S \<in> TX"
  proof -
    fix S assume hS: "S \<subseteq> TX"
    have "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
      using hTX unfolding is_topology_on_def by blast
    thus "\<Union>S \<in> TX"
      using hS by blast
  qed

  show "\<forall>U\<in>TX. U \<subseteq> X \<longrightarrow> (\<forall>P\<in>top1_path_components_on U (subspace_topology X TX U). P \<in> TX)"
  proof (rule ballI)
    fix U assume hU: "U \<in> TX"
    show "U \<subseteq> X \<longrightarrow> (\<forall>P\<in>top1_path_components_on U (subspace_topology X TX U). P \<in> TX)"
    proof (rule impI)
      assume hUX: "U \<subseteq> X"
      let ?TU = "subspace_topology X TX U"
      have hTU: "is_topology_on U ?TU"
        by (rule subspace_topology_is_topology_on[OF hTX hUX])

      show "\<forall>P\<in>top1_path_components_on U ?TU. P \<in> TX"
      proof (rule ballI)
        fix P assume hP: "P \<in> top1_path_components_on U ?TU"
        obtain u0 where hu0U: "u0 \<in> U" and hPeq: "P = top1_path_component_of_on U ?TU u0"
          using hP unfolding top1_path_components_on_def by blast

        have hPsubU: "P \<subseteq> U"
          unfolding hPeq by (rule top1_path_component_of_on_subset[OF hTU hu0U])

        have hP_open: "\<forall>x\<in>P. \<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> P \<and> V \<subseteq> X
            \<and> top1_path_connected_on V (subspace_topology X TX V)"
        proof (intro ballI)
          fix x assume hxP: "x \<in> P"
          have hxU: "x \<in> U"
            using hPsubU hxP by blast
          have hxX: "x \<in> X"
            using hUX hxU by blast
          have hU_nbhd: "neighborhood_of x X TX U"
            unfolding neighborhood_of_def using hU hxU by blast
          have hLocx: "top1_locally_path_connected_at X TX x"
            using hLocAll hxX by blast
          obtain V where hVnbhd: "neighborhood_of x X TX V"
            and hVsubU: "V \<subseteq> U"
            and hVX: "V \<subseteq> X"
            and hVpath: "top1_path_connected_on V (subspace_topology X TX V)"
            using hLocx hU_nbhd hUX unfolding top1_locally_path_connected_at_def by blast
          have hxV: "x \<in> V"
            using hVnbhd unfolding neighborhood_of_def by blast

          have hVpathU: "top1_path_connected_on V (subspace_topology U ?TU V)"
          proof -
            have hTopEq: "subspace_topology U ?TU V = subspace_topology X TX V"
              by (rule subspace_topology_trans[OF hVsubU])
            show ?thesis
              unfolding hTopEq by (rule hVpath)
          qed

          have hP_as_x: "P = top1_path_component_of_on U ?TU x"
          proof -
            have hx_mem: "x \<in> top1_path_component_of_on U ?TU u0"
              using hxP hPeq by simp
            have "top1_path_component_of_on U ?TU x = top1_path_component_of_on U ?TU u0"
              by (rule top1_path_component_of_on_eq_of_mem[OF hTU hx_mem])
            thus ?thesis
              unfolding hPeq by simp
          qed

          have hVsubP: "V \<subseteq> P"
          proof -
            have "V \<subseteq> top1_path_component_of_on U ?TU x"
              by (rule top1_path_connected_subspace_subset_path_component_of[OF hTU hVsubU hxV hVpathU])
            thus ?thesis
              unfolding hP_as_x by simp
          qed

          show "\<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> P \<and> V \<subseteq> X
              \<and> top1_path_connected_on V (subspace_topology X TX V)"
            using hVnbhd hVsubP hVX hVpath by blast
        qed

        define VP where "VP = {V. \<exists>x\<in>P. neighborhood_of x X TX V \<and> V \<subseteq> P \<and> V \<subseteq> X
            \<and> top1_path_connected_on V (subspace_topology X TX V)}"

        have hVP_sub: "VP \<subseteq> TX"
        proof (rule subsetI)
          fix V assume hV: "V \<in> VP"
          obtain x where hxP: "x \<in> P" and hnbhd: "neighborhood_of x X TX V"
            and hVsub: "V \<subseteq> P" and hVX: "V \<subseteq> X"
            and hpathV: "top1_path_connected_on V (subspace_topology X TX V)"
            using hV unfolding VP_def by blast
          show "V \<in> TX"
            using hnbhd unfolding neighborhood_of_def by blast
        qed

        have hPeqUnion: "P = \<Union>VP"
        proof (rule equalityI)
          show "P \<subseteq> \<Union>VP"
          proof (rule subsetI)
            fix x assume hxP: "x \<in> P"
            obtain V where hVnbhd: "neighborhood_of x X TX V" and hVsubP: "V \<subseteq> P"
              and hVX: "V \<subseteq> X" and hVpath: "top1_path_connected_on V (subspace_topology X TX V)"
              using hP_open hxP by blast
            have hxV: "x \<in> V"
              using hVnbhd unfolding neighborhood_of_def by blast
            have "V \<in> VP"
              unfolding VP_def using hxP hVnbhd hVsubP hVX hVpath by blast
            thus "x \<in> \<Union>VP"
              using hxV by blast
          qed
          show "\<Union>VP \<subseteq> P"
            unfolding VP_def by blast
        qed

        have "P \<in> TX"
          unfolding hPeqUnion
          by (rule hUnionTX[OF hVP_sub])
        thus "P \<in> TX" .
      qed
    qed
  qed
next
  assume hOpenPC:
    "\<forall>U\<in>TX. U \<subseteq> X \<longrightarrow> (\<forall>P\<in>top1_path_components_on U (subspace_topology X TX U). P \<in> TX)"
  show "top1_locally_path_connected_on X TX"
    unfolding top1_locally_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on X TX"
      by (rule hTX)
    fix x assume hxX: "x \<in> X"
    show "top1_locally_path_connected_at X TX x"
      unfolding top1_locally_path_connected_at_def
    proof (intro allI impI)
      fix U assume hU: "neighborhood_of x X TX U \<and> U \<subseteq> X"
      have hUopen: "U \<in> TX"
        using hU unfolding neighborhood_of_def by blast
      have hxU: "x \<in> U"
        using hU unfolding neighborhood_of_def by blast
      have hUX: "U \<subseteq> X"
        using hU by blast

      let ?TU = "subspace_topology X TX U"
      have hTU: "is_topology_on U ?TU"
        by (rule subspace_topology_is_topology_on[OF hTX hUX])

      define P where "P = top1_path_component_of_on U ?TU x"

      have hPmem: "P \<in> top1_path_components_on U ?TU"
        unfolding P_def top1_path_components_on_def using hxU by blast
      have hPopen: "P \<in> TX"
        using hOpenPC hUopen hUX hPmem by blast
      have hxP: "x \<in> P"
        unfolding P_def by (rule top1_path_component_of_on_self_mem[OF hTU hxU])
      have hPsubU: "P \<subseteq> U"
        unfolding P_def by (rule top1_path_component_of_on_subset[OF hTU hxU])
      have hPpathU: "top1_path_connected_on P (subspace_topology U ?TU P)"
        unfolding P_def by (rule top1_path_component_of_on_path_connected[OF hTU hxU])
      have hPpathX: "top1_path_connected_on P (subspace_topology X TX P)"
      proof -
        have hTopEq: "subspace_topology U ?TU P = subspace_topology X TX P"
          by (rule subspace_topology_trans[OF hPsubU])
        show ?thesis
          unfolding hTopEq[symmetric] by (rule hPpathU)
      qed

      have hPnbhd: "neighborhood_of x X TX P"
        unfolding neighborhood_of_def using hPopen hxP by blast

      show "\<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> U \<and> V \<subseteq> X
          \<and> top1_path_connected_on V (subspace_topology X TX V)"
        apply (rule exI[where x=P])
        using hPnbhd hPsubU hUX hPpathX by blast
    qed
  qed
qed

(** In a locally path connected space, each path component is open. **)
lemma top1_path_component_of_on_open_if_locally_path_connected:
  assumes hTX: "is_topology_on X TX"
  assumes hLoc: "top1_locally_path_connected_on X TX"
  assumes hxX: "x \<in> X"
  shows "top1_path_component_of_on X TX x \<in> TX"
proof -
  have hLocAll: "\<forall>y\<in>X. top1_locally_path_connected_at X TX y"
    using hLoc unfolding top1_locally_path_connected_on_def by blast
  have hUnionTX: "\<forall>S. S \<subseteq> TX \<longrightarrow> \<Union>S \<in> TX"
    using hTX unfolding is_topology_on_def by blast
  have hXopen: "X \<in> TX"
    using hTX unfolding is_topology_on_def by blast

  let ?P = "top1_path_component_of_on X TX x"
  have hPsubX: "?P \<subseteq> X"
    by (rule top1_path_component_of_on_subset[OF hTX hxX])

  define VP where
    "VP = {V. \<exists>y\<in>?P. neighborhood_of y X TX V \<and> V \<subseteq> ?P}"

  have hVP_sub: "VP \<subseteq> TX"
  proof (rule subsetI)
    fix V assume hV: "V \<in> VP"
    obtain y where hyP: "y \<in> ?P" and hnbhd: "neighborhood_of y X TX V" and hVsub: "V \<subseteq> ?P"
      using hV unfolding VP_def by blast
    show "V \<in> TX"
      using hnbhd unfolding neighborhood_of_def by blast
  qed

  have hP_eq: "?P = \<Union>VP"
  proof (rule equalityI)
    show "?P \<subseteq> \<Union>VP"
    proof (rule subsetI)
      fix y assume hyP: "y \<in> ?P"
      have hyX: "y \<in> X"
        using hPsubX hyP by blast
      have hLocy: "top1_locally_path_connected_at X TX y"
        using hLocAll hyX by blast
      have hXnbhd: "neighborhood_of y X TX X"
        unfolding neighborhood_of_def using hXopen hyX by blast

      have hLocy':
        "\<forall>U. neighborhood_of y X TX U \<and> U \<subseteq> X \<longrightarrow>
            (\<exists>V. neighborhood_of y X TX V \<and> V \<subseteq> U \<and> V \<subseteq> X
                 \<and> top1_path_connected_on V (subspace_topology X TX V))"
        using hLocy unfolding top1_locally_path_connected_at_def by blast
      have hUX: "neighborhood_of y X TX X \<and> X \<subseteq> X"
        using hXnbhd by simp
      obtain V where hVnbhd: "neighborhood_of y X TX V"
        and hVsubX: "V \<subseteq> X"
        and hVpath: "top1_path_connected_on V (subspace_topology X TX V)"
        using hLocy' hUX by blast
      have hyV: "y \<in> V"
        using hVnbhd unfolding neighborhood_of_def by blast

      have hVsubPy: "V \<subseteq> top1_path_component_of_on X TX y"
        by (rule top1_path_connected_subspace_subset_path_component_of[OF hTX hVsubX hyV hVpath])
      have hPy: "top1_path_component_of_on X TX y = ?P"
        by (rule top1_path_component_of_on_eq_of_mem[OF hTX hyP])
      have hVsubP: "V \<subseteq> ?P"
        using hVsubPy unfolding hPy by simp

      have "V \<in> VP"
        unfolding VP_def using hyP hVnbhd hVsubP by blast
      thus "y \<in> \<Union>VP"
        using hyV by blast
    qed
    show "\<Union>VP \<subseteq> ?P"
      unfolding VP_def by blast
  qed

  show ?thesis
    unfolding hP_eq
    by (rule hUnionTX[rule_format, OF hVP_sub])
qed

(** In a locally path connected space, the complement of a path component is open. **)
lemma top1_path_component_of_on_complement_open_if_locally_path_connected:
  assumes hTX: "is_topology_on X TX"
  assumes hLoc: "top1_locally_path_connected_on X TX"
  assumes hxX: "x \<in> X"
  shows "X - top1_path_component_of_on X TX x \<in> TX"
proof -
  have hUnionTX: "\<forall>S. S \<subseteq> TX \<longrightarrow> \<Union>S \<in> TX"
    using hTX unfolding is_topology_on_def by blast

  let ?P = "top1_path_component_of_on X TX x"
  define Other where "Other = {Q. Q \<in> top1_path_components_on X TX \<and> Q \<noteq> ?P}"

  have hOther_sub: "Other \<subseteq> TX"
  proof (rule subsetI)
    fix Q assume hQ: "Q \<in> Other"
    have hQpc: "Q \<in> top1_path_components_on X TX"
      using hQ unfolding Other_def by blast
    obtain y where hyX: "y \<in> X" and hQeq: "Q = top1_path_component_of_on X TX y"
      using hQpc unfolding top1_path_components_on_def by blast
    have "Q \<in> TX"
      unfolding hQeq
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTX hLoc hyX])
    thus "Q \<in> TX" .
  qed

  have hUnionOther: "\<Union>Other \<in> TX"
    by (rule hUnionTX[rule_format, OF hOther_sub])

  have hEq: "X - ?P = \<Union>Other"
  proof (rule equalityI)
    show "X - ?P \<subseteq> \<Union>Other"
    proof (rule subsetI)
      fix y assume hy: "y \<in> X - ?P"
      have hyX: "y \<in> X" and hyNP: "y \<notin> ?P"
        using hy by blast+
      have hCover: "(\<Union>(top1_path_components_on X TX)) = X"
        by (rule Theorem_25_2(1)[OF hTX])
      have "y \<in> \<Union>(top1_path_components_on X TX)"
        using hyX hCover by simp
      then obtain Q where hQ: "Q \<in> top1_path_components_on X TX" and hyQ: "y \<in> Q"
        by blast
      have hQne: "Q \<noteq> ?P"
      proof
        assume hQP: "Q = ?P"
        have "y \<in> ?P"
          using hyQ hQP by simp
        thus False
          using hyNP by blast
      qed
      have "Q \<in> Other"
        unfolding Other_def using hQ hQne by blast
      thus "y \<in> \<Union>Other"
        using hyQ by blast
    qed
    show "\<Union>Other \<subseteq> X - ?P"
    proof (rule subsetI)
      fix y assume hy: "y \<in> \<Union>Other"
      then obtain Q where hQ: "Q \<in> Other" and hyQ: "y \<in> Q"
        by blast
      have hQpc: "Q \<in> top1_path_components_on X TX" and hQne: "Q \<noteq> ?P"
        using hQ unfolding Other_def by blast+
      obtain y0 where hy0X: "y0 \<in> X" and hQeq: "Q = top1_path_component_of_on X TX y0"
        using hQpc unfolding top1_path_components_on_def by blast
      have hQsubX: "Q \<subseteq> X"
        unfolding hQeq by (rule top1_path_component_of_on_subset[OF hTX hy0X])
      have hyX: "y \<in> X"
        using hyQ hQsubX by blast
      have hyNP: "y \<notin> ?P"
      proof
        assume hyP: "y \<in> ?P"
        have "?P \<inter> Q \<noteq> {}"
          using hyP hyQ by blast
        have hPpc: "?P \<in> top1_path_components_on X TX"
          unfolding top1_path_components_on_def using hxX by blast
        have "?P = Q"
          by (rule Theorem_25_2(2)[OF hTX hPpc hQpc \<open>?P \<inter> Q \<noteq> {}\<close>])
        thus False
          using hQne by blast
      qed
      show "y \<in> X - ?P"
        using hyX hyNP by blast
    qed
  qed

  show ?thesis
    unfolding hEq
    by (rule hUnionOther)
qed

(** In a locally path connected space, each component is contained in the path component. **)
lemma top1_component_of_on_subset_path_component_if_locally_path_connected:
  assumes hTX: "is_topology_on X TX"
  assumes hLoc: "top1_locally_path_connected_on X TX"
  assumes hxX: "x \<in> X"
  shows "top1_component_of_on X TX x \<subseteq> top1_path_component_of_on X TX x"
proof (rule subsetI)
  fix y assume hyC: "y \<in> top1_component_of_on X TX x"
  let ?C = "top1_component_of_on X TX x"
  let ?P = "top1_path_component_of_on X TX x"
  have hCsubX: "?C \<subseteq> X"
    by (rule top1_component_of_on_subset)
  have hyX: "y \<in> X"
    using hyC hCsubX by blast

  have hCconn: "top1_connected_on ?C (subspace_topology X TX ?C)"
    by (rule top1_component_of_on_connected[OF hTX hxX])
  have hNoSep:
    "\<nexists>U V. U \<in> subspace_topology X TX ?C \<and> V \<in> subspace_topology X TX ?C
        \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = ?C"
    using hCconn unfolding top1_connected_on_def by blast

  have hPopen: "?P \<in> TX"
    by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTX hLoc hxX])
  have hXPopen: "X - ?P \<in> TX"
    by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hTX hLoc hxX])

  have hxC: "x \<in> ?C"
    by (rule top1_component_of_on_self_mem[OF hTX hxX])
  have hxP: "x \<in> ?P"
    by (rule top1_path_component_of_on_self_mem[OF hTX hxX])

  show "y \<in> ?P"
  proof (rule classical)
    show "y \<in> ?P"
    proof (rule ccontr)
      assume hyNP: "y \<notin> ?P"
      define U where "U = ?C \<inter> ?P"
      define V where "V = ?C \<inter> (X - ?P)"

      have hU_mem: "U \<in> subspace_topology X TX ?C"
        unfolding subspace_topology_def U_def
        apply (rule CollectI)
        apply (rule exI[where x="?P"])
        apply (intro conjI)
         apply (rule refl)
        apply (rule hPopen)
        done
      have hV_mem: "V \<in> subspace_topology X TX ?C"
        unfolding subspace_topology_def V_def
        apply (rule CollectI)
        apply (rule exI[where x="X - ?P"])
        apply (intro conjI)
         apply (rule refl)
        apply (rule hXPopen)
        done

      have hU_ne: "U \<noteq> {}"
      proof -
        have "x \<in> U"
          unfolding U_def using hxC hxP by blast
        thus ?thesis by blast
      qed
      have hV_ne: "V \<noteq> {}"
      proof -
        have "y \<in> V"
          unfolding V_def using hyC hyX hyNP by blast
        thus ?thesis by blast
      qed

      have hUV_disj: "U \<inter> V = {}"
        unfolding U_def V_def by blast
      have hUV_cov: "U \<union> V = ?C"
        unfolding U_def V_def using hCsubX by blast

      have False
        using hNoSep hU_mem hV_mem hU_ne hV_ne hUV_disj hUV_cov by blast
      thus False by simp
    qed
  qed
qed

(** from *\S25 Theorem 25.5 (Path components vs components) [top1.tex:2999] **)
theorem Theorem_25_5:
  assumes hTX: "is_topology_on X TX"
  shows
    "(\<forall>x\<in>X. top1_path_component_of_on X TX x \<subseteq> top1_component_of_on X TX x)
     \<and> (top1_locally_path_connected_on X TX \<longrightarrow> (\<forall>x\<in>X. top1_path_component_of_on X TX x = top1_component_of_on X TX x))"
proof (intro conjI)
  show "\<forall>x\<in>X. top1_path_component_of_on X TX x \<subseteq> top1_component_of_on X TX x"
  proof (intro ballI)
    fix x assume hxX: "x \<in> X"
    show "top1_path_component_of_on X TX x \<subseteq> top1_component_of_on X TX x"
    proof (rule subsetI)
      fix y assume hy: "y \<in> top1_path_component_of_on X TX x"
      obtain f where hf: "top1_is_path_on X TX x y f"
        using hy unfolding top1_path_component_of_on_def top1_in_same_path_component_on_def by blast
      have hI: "is_topology_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hconnI: "top1_connected_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_connected)

      have contf: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
        using hf unfolding top1_is_path_on_def by blast
      have mapf: "\<forall>t\<in>top1_unit_interval. f t \<in> X"
        using contf unfolding top1_continuous_map_on_def by blast

      have hconn_im:
        "top1_connected_on (f ` top1_unit_interval) (subspace_topology X TX (f ` top1_unit_interval))"
        by (rule Theorem_23_5[OF hI hTX hconnI contf])

      have him_subX: "f ` top1_unit_interval \<subseteq> X"
      proof (rule subsetI)
        fix u assume hu: "u \<in> f ` top1_unit_interval"
        then obtain t where ht: "t \<in> top1_unit_interval" and hu_eq: "u = f t"
          by blast
        show "u \<in> X"
          using mapf ht hu_eq by blast
      qed

      have h0: "0 \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by simp
      have h1: "1 \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by simp
      have hx_im: "x \<in> f ` top1_unit_interval"
      proof -
        have "f 0 \<in> f ` top1_unit_interval"
          by (rule imageI[OF h0])
        thus ?thesis
          using hf unfolding top1_is_path_on_def by simp
      qed
      have hy_im: "y \<in> f ` top1_unit_interval"
      proof -
        have "f 1 \<in> f ` top1_unit_interval"
          by (rule imageI[OF h1])
        thus ?thesis
          using hf unfolding top1_is_path_on_def by simp
      qed

      have him_subComp: "f ` top1_unit_interval \<subseteq> top1_component_of_on X TX x"
        by (rule top1_connected_subspace_subset_component_of[OF him_subX hx_im hconn_im])
      show "y \<in> top1_component_of_on X TX x"
        using hy_im by (rule subsetD[OF him_subComp])
    qed
  qed

  show "top1_locally_path_connected_on X TX \<longrightarrow>
        (\<forall>x\<in>X. top1_path_component_of_on X TX x = top1_component_of_on X TX x)"
  proof (intro impI ballI)
    assume hLoc: "top1_locally_path_connected_on X TX"
    fix x assume hxX: "x \<in> X"
    have hPCsub: "top1_path_component_of_on X TX x \<subseteq> top1_component_of_on X TX x"
      using \<open>\<forall>x\<in>X. top1_path_component_of_on X TX x \<subseteq> top1_component_of_on X TX x\<close> hxX by blast
    have hCsub: "top1_component_of_on X TX x \<subseteq> top1_path_component_of_on X TX x"
      by (rule top1_component_of_on_subset_path_component_if_locally_path_connected[OF hTX hLoc hxX])
    show "top1_path_component_of_on X TX x = top1_component_of_on X TX x"
      by (rule equalityI[OF hPCsub hCsub])
  qed
qed

section \<open>\<S>26 Compact Spaces\<close>

definition top1_compact_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_compact_on X T \<longleftrightarrow>
     is_topology_on X T \<and>
     (\<forall>Uc. Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc \<longrightarrow>
          (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F))"

(** from \S26 Lemma 26.1 (Compactness of subspaces, open covers from the ambient space) [top1.tex:3096] **)
theorem Lemma_26_1:
  assumes hTX: "is_topology_on X TX"
  assumes hYX: "Y \<subseteq> X"
  shows "top1_compact_on Y (subspace_topology X TX Y)
    \<longleftrightarrow> (\<forall>Uc. Uc \<subseteq> TX \<and> Y \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F))"
proof -
  let ?TY = "subspace_topology X TX Y"

  have hTopY: "is_topology_on Y ?TY"
    by (rule subspace_topology_is_topology_on[OF hTX hYX])

  show ?thesis
  proof (rule iffI)
    assume hcomp: "top1_compact_on Y ?TY"
    have hcoverY:
      "\<forall>Uc. Uc \<subseteq> ?TY \<and> Y \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"
      using hcomp unfolding top1_compact_on_def by blast

    show "\<forall>Uc. Uc \<subseteq> TX \<and> Y \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"
    proof (intro allI impI)
      fix Uc
      assume hUc: "Uc \<subseteq> TX \<and> Y \<subseteq> \<Union>Uc"
      have hUcTX: "Uc \<subseteq> TX"
        using hUc by blast
      have hcov: "Y \<subseteq> \<Union>Uc"
        using hUc by blast

      define UcY where "UcY = {Y \<inter> U | U. U \<in> Uc}"

      have hUcY_sub: "UcY \<subseteq> ?TY"
        unfolding UcY_def subspace_topology_def using hUcTX by blast

      have hcovY: "Y \<subseteq> \<Union>UcY"
      proof (rule subsetI)
        fix y assume hy: "y \<in> Y"
        have "y \<in> \<Union>Uc"
          using hcov hy by blast
        then obtain U where hU: "U \<in> Uc" and hyU: "y \<in> U"
          by blast
        have hyYU: "y \<in> Y \<inter> U"
          using hy hyU by blast
        have "Y \<inter> U \<in> UcY"
          unfolding UcY_def using hU by blast
        thus "y \<in> \<Union>UcY"
          using hyYU by blast
      qed

      obtain F' where hF'fin: "finite F'" and hF'sub: "F' \<subseteq> UcY" and hF'cov: "Y \<subseteq> \<Union>F'"
        using hcoverY[rule_format, OF conjI[OF hUcY_sub hcovY]] by blast

      have ex_pick: "\<forall>W\<in>F'. \<exists>U. U \<in> Uc \<and> W = Y \<inter> U"
      proof (intro ballI)
        fix W assume hW: "W \<in> F'"
        have "W \<in> UcY"
          using hF'sub hW by blast
        thus "\<exists>U. U \<in> Uc \<and> W = Y \<inter> U"
          unfolding UcY_def by blast
      qed

      obtain pick where hpick: "\<forall>W\<in>F'. pick W \<in> Uc \<and> W = Y \<inter> pick W"
        using bchoice[OF ex_pick] by blast

      define F where "F = pick ` F'"
      have hFfin: "finite F"
        unfolding F_def using hF'fin by simp
      have hFsub: "F \<subseteq> Uc"
        unfolding F_def using hpick by blast

      have hFcov: "Y \<subseteq> \<Union>F"
      proof (rule subsetI)
        fix y assume hy: "y \<in> Y"
        have "y \<in> \<Union>F'"
          using hF'cov hy by blast
        then obtain W where hW: "W \<in> F'" and hyW: "y \<in> W"
          by blast
        have hWp: "pick W \<in> Uc" and hWeq: "W = Y \<inter> pick W"
          using hpick hW by blast+
        have hyU: "y \<in> pick W"
        proof -
          have hyYpick: "y \<in> Y \<inter> pick W"
            apply (subst hWeq[symmetric])
            apply (rule hyW)
            done
          show ?thesis
            using hyYpick by simp
        qed
        have "pick W \<in> F"
          unfolding F_def using hW by blast
        thus "y \<in> \<Union>F"
          using hyU by blast
      qed

      show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F"
        by (rule exI[where x=F], intro conjI, rule hFfin, rule hFsub, rule hFcov)
    qed
  next
    assume hcovX:
      "\<forall>Uc. Uc \<subseteq> TX \<and> Y \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"

    have hcoverY:
      "\<forall>UcY. UcY \<subseteq> ?TY \<and> Y \<subseteq> \<Union>UcY \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> UcY \<and> Y \<subseteq> \<Union>F)"
    proof (intro allI impI)
      fix UcY
      assume hUcY: "UcY \<subseteq> ?TY \<and> Y \<subseteq> \<Union>UcY"
      have hUcY_sub: "UcY \<subseteq> ?TY"
        using hUcY by blast
      have hcovY: "Y \<subseteq> \<Union>UcY"
        using hUcY by blast

      have ex_pick: "\<forall>W\<in>UcY. \<exists>U. U \<in> TX \<and> W = Y \<inter> U"
      proof (intro ballI)
        fix W assume hW: "W \<in> UcY"
        have "W \<in> ?TY"
          using hUcY_sub hW by blast
        thus "\<exists>U. U \<in> TX \<and> W = Y \<inter> U"
          unfolding subspace_topology_def by blast
      qed

      obtain pick where hpick: "\<forall>W\<in>UcY. pick W \<in> TX \<and> W = Y \<inter> pick W"
        using bchoice[OF ex_pick] by blast

      define Uc where "Uc = pick ` UcY"
      have hUc_sub: "Uc \<subseteq> TX"
        unfolding Uc_def using hpick by blast

      have hcov: "Y \<subseteq> \<Union>Uc"
      proof (rule subsetI)
        fix y assume hy: "y \<in> Y"
        have "y \<in> \<Union>UcY"
          using hcovY hy by blast
        then obtain W where hW: "W \<in> UcY" and hyW: "y \<in> W"
          by blast
        have hWeq: "W = Y \<inter> pick W"
          using hpick hW by blast
        have hyU: "y \<in> pick W"
        proof -
          have hyYpick: "y \<in> Y \<inter> pick W"
            apply (subst hWeq[symmetric])
            apply (rule hyW)
            done
          show ?thesis
            using hyYpick by simp
        qed
        have "pick W \<in> Uc"
          unfolding Uc_def using hW by blast
        thus "y \<in> \<Union>Uc"
          using hyU by blast
      qed

      obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "Y \<subseteq> \<Union>F"
        using hcovX[rule_format, OF conjI[OF hUc_sub hcov]] by blast

      define F' where "F' = {Y \<inter> U | U. U \<in> F}"
      have hF'fin: "finite F'"
        unfolding F'_def using hFfin by simp

      have hF'sub: "F' \<subseteq> UcY"
      proof (rule subsetI)
        fix W assume hW: "W \<in> F'"
        then obtain U where hU: "U \<in> F" and hWeq: "W = Y \<inter> U"
          unfolding F'_def by blast
        have hUUc: "U \<in> Uc"
          using hFsub hU by blast
        obtain W0 where hW0: "W0 \<in> UcY" and hUeq: "U = pick W0"
          using hUUc unfolding Uc_def by blast
        have hW0eq: "W0 = Y \<inter> pick W0"
          using hpick hW0 by blast
        have "Y \<inter> U = W0"
          unfolding hUeq using hW0eq by simp
        show "W \<in> UcY"
          unfolding hWeq \<open>Y \<inter> U = W0\<close> using hW0 by simp
      qed

      have hF'cov: "Y \<subseteq> \<Union>F'"
      proof (rule subsetI)
        fix y assume hy: "y \<in> Y"
        have "y \<in> \<Union>F"
          using hFcov hy by blast
        then obtain U where hU: "U \<in> F" and hyU: "y \<in> U"
          by blast
        have hyWU: "y \<in> Y \<inter> U"
          using hy hyU by blast
        have "Y \<inter> U \<in> F'"
          unfolding F'_def using hU by blast
        thus "y \<in> \<Union>F'"
          using hyWU by blast
      qed

      show "\<exists>F. finite F \<and> F \<subseteq> UcY \<and> Y \<subseteq> \<Union>F"
        by (rule exI[where x=F'], intro conjI, rule hF'fin, rule hF'sub, rule hF'cov)
    qed

    show "top1_compact_on Y ?TY"
      unfolding top1_compact_on_def
      by (intro conjI, rule hTopY, rule hcoverY)
  qed
qed

(** Finite subspaces are compact (in the subspace topology). **)
lemma top1_compact_on_finite_subspace:
  assumes hTX: "is_topology_on X TX"
  assumes hYX: "Y \<subseteq> X"
  assumes hfin: "finite Y"
  shows "top1_compact_on Y (subspace_topology X TX Y)"
proof -
  let ?TY = "subspace_topology X TX Y"

  have hTopY: "is_topology_on Y ?TY"
    by (rule subspace_topology_is_topology_on[OF hTX hYX])

  have hSubcover:
    "\<forall>Uc. Uc \<subseteq> ?TY \<and> Y \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"
  proof (intro allI impI)
    fix Uc
    assume hUc: "Uc \<subseteq> ?TY \<and> Y \<subseteq> \<Union>Uc"
    have hcov: "Y \<subseteq> \<Union>Uc"
      using hUc by simp

    have hfinite_cover:
      "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F"
      using hfin hcov
    proof (induction rule: finite_induct)
      case empty
      show ?case
        by (rule exI[where x="{}"], simp)
    next
      case (insert y0 Y')
      have hy0: "y0 \<in> \<Union>Uc"
        using insert.prems by simp
      obtain U0 where hU0: "U0 \<in> Uc" and hy0U0: "y0 \<in> U0"
        using hy0 by blast

      have hcovY': "Y' \<subseteq> \<Union>Uc"
        using insert.prems by simp
      obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "Y' \<subseteq> \<Union>F"
        using insert.IH hcovY' by blast

      have hInsFin: "finite (insert U0 F)"
        using hFfin by simp
      have hInsSub: "insert U0 F \<subseteq> Uc"
        using hFsub hU0 by simp
      have hInsCov: "insert y0 Y' \<subseteq> \<Union>(insert U0 F)"
      proof
        fix y
        assume hy: "y \<in> insert y0 Y'"
        show "y \<in> \<Union>(insert U0 F)"
        proof (cases "y = y0")
          case True
          show ?thesis
            unfolding True using hU0 hy0U0 by blast
        next
          case False
          have "y \<in> Y'"
            using hy False by simp
          then show ?thesis
            using hFcov by blast
        qed
      qed

      show ?case
        apply (rule exI[where x="insert U0 F"])
        using hInsFin hInsSub hInsCov by blast
    qed

    show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F"
      by (rule hfinite_cover)
  qed

  show ?thesis
    unfolding top1_compact_on_def
    apply (intro conjI)
     apply (rule hTopY)
    apply (rule hSubcover)
    done
qed

(** from \S26 Lemma 26.8 (Tube lemma) [top1.tex:3236] **)
theorem Lemma_26_8:
  assumes hY: "top1_compact_on Y TY"
  assumes hTopX: "is_topology_on X TX"
  assumes hTopY: "is_topology_on Y TY"
  assumes hN: "N \<in> product_topology_on TX TY"
  assumes hx0: "x0 \<in> X"
  assumes hslice: "{x0} \<times> Y \<subseteq> N"
  shows "\<exists>W. neighborhood_of x0 X TX W \<and> W \<times> Y \<subseteq> N"
proof (cases "Y = {}")
  case True

  have hX_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]])
  have hnbhd: "neighborhood_of x0 X TX X"
    unfolding neighborhood_of_def using hX_TX hx0 by blast

  have hprod: "X \<times> Y \<subseteq> N"
    unfolding True by simp

  show ?thesis
    apply (rule exI[where x=X])
    apply (intro conjI)
     apply (rule hnbhd)
    apply (rule hprod)
    done
next
  case False

  have hCoverY:
    "\<forall>Uc. Uc \<subseteq> TY \<and> Y \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"
    using hY unfolding top1_compact_on_def by blast

  have hex:
    "\<forall>y\<in>Y. \<exists>U\<in>TX. \<exists>V\<in>TY. x0 \<in> U \<and> y \<in> V \<and> U \<times> V \<subseteq> N"
  proof (intro ballI)
    fix y assume hyY: "y \<in> Y"
    have hpN: "(x0, y) \<in> N"
      using hslice hyY by blast
    obtain U V where hU: "U \<in> TX" and hV: "V \<in> TY"
      and hpUV: "(x0, y) \<in> U \<times> V" and hsub: "U \<times> V \<subseteq> N"
      by (rule top1_product_open_contains_rect[OF hN hpN])
    have hx0U: "x0 \<in> U" and hyV: "y \<in> V"
      using hpUV by blast+
    show "\<exists>U\<in>TX. \<exists>V\<in>TY. x0 \<in> U \<and> y \<in> V \<and> U \<times> V \<subseteq> N"
      apply (rule bexI[where x=U])
       apply (rule bexI[where x=V])
        apply (rule conjI)
         apply (rule hx0U)
        apply (rule conjI)
         apply (rule hyV)
        apply (rule hsub)
       apply (rule hV)
      apply (rule hU)
      done
  qed

  obtain f where hf:
    "\<forall>y\<in>Y. fst (f y) \<in> TX \<and> snd (f y) \<in> TY
           \<and> x0 \<in> fst (f y) \<and> y \<in> snd (f y)
           \<and> fst (f y) \<times> snd (f y) \<subseteq> N"
  proof -
    have hex':
      "\<forall>y\<in>Y. \<exists>p. fst p \<in> TX \<and> snd p \<in> TY
               \<and> x0 \<in> fst p \<and> y \<in> snd p
               \<and> fst p \<times> snd p \<subseteq> N"
    proof (intro ballI)
      fix y assume hyY: "y \<in> Y"
      obtain U V where hU: "U \<in> TX" and hV: "V \<in> TY"
        and hx0U: "x0 \<in> U" and hyV: "y \<in> V" and hsub: "U \<times> V \<subseteq> N"
        using hex hyY by blast
      show "\<exists>p. fst p \<in> TX \<and> snd p \<in> TY
               \<and> x0 \<in> fst p \<and> y \<in> snd p
               \<and> fst p \<times> snd p \<subseteq> N"
        apply (rule exI[where x="(U,V)"])
        using hU hV hx0U hyV hsub by simp
    qed
    obtain g where hg:
      "\<forall>y\<in>Y. fst (g y) \<in> TX \<and> snd (g y) \<in> TY
             \<and> x0 \<in> fst (g y) \<and> y \<in> snd (g y)
             \<and> fst (g y) \<times> snd (g y) \<subseteq> N"
      using bchoice[OF hex'] by blast
    show ?thesis
      by (rule that[OF hg])
  qed

  define U where "U = (\<lambda>y. fst (f y))"
  define V where "V = (\<lambda>y. snd (f y))"

  have hUopen: "\<forall>y\<in>Y. U y \<in> TX"
    using hf unfolding U_def by blast
  have hVopen: "\<forall>y\<in>Y. V y \<in> TY"
    using hf unfolding V_def by blast
  have hx0U: "\<forall>y\<in>Y. x0 \<in> U y"
    using hf unfolding U_def by blast
  have hyV: "\<forall>y\<in>Y. y \<in> V y"
    using hf unfolding V_def by blast
  have hUVsub: "\<forall>y\<in>Y. U y \<times> V y \<subseteq> N"
    using hf unfolding U_def V_def by blast

  have hVimg_sub: "V ` Y \<subseteq> TY"
    using hVopen by blast
  have hVcov: "Y \<subseteq> \<Union>(V ` Y)"
  proof (rule subsetI)
    fix y assume hyY: "y \<in> Y"
    have hyVy: "y \<in> V y"
      using hyV hyY by blast
    have hVy: "V y \<in> V ` Y"
      using hyY by blast
    show "y \<in> \<Union>(V ` Y)"
      by (rule UnionI[OF hVy hyVy])
  qed

  obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> V ` Y" and hFcov: "Y \<subseteq> \<Union>F"
    using hCoverY[rule_format, OF conjI[OF hVimg_sub hVcov]] by blast

  have hFne: "F \<noteq> {}"
  proof
    assume hF0: "F = {}"
    have "\<Union>F = {}"
      unfolding hF0 by simp
    hence "Y = {}"
      using hFcov by blast
    thus False
      using False by blast
  qed

  have hrepr: "\<forall>W\<in>F. \<exists>y. y \<in> Y \<and> V y = W"
  proof (intro ballI)
    fix W assume hWF: "W \<in> F"
    have "W \<in> V ` Y"
      using hFsub hWF by blast
    then obtain y where hyY: "y \<in> Y" and hWeq: "W = V y"
      by blast
    show "\<exists>y. y \<in> Y \<and> V y = W"
      by (rule exI[where x=y]) (use hyY hWeq in simp)
  qed

  obtain pick where hpick: "\<forall>W\<in>F. pick W \<in> Y \<and> V (pick W) = W"
    using bchoice[OF hrepr] by blast

  define I where "I = pick ` F"
  have hIfin: "finite I"
    unfolding I_def by (rule finite_imageI[OF hFfin])
  have hIne: "I \<noteq> {}"
    unfolding I_def using hFne by simp
  have hIsub: "I \<subseteq> Y"
    unfolding I_def using hpick by blast

  have hIcov: "Y \<subseteq> \<Union>(V ` I)"
  proof (rule subsetI)
    fix y assume hyY: "y \<in> Y"
    have "y \<in> \<Union>F"
      using hFcov hyY by blast
    then obtain W where hWF: "W \<in> F" and hyW: "y \<in> W"
      by blast
    have hVI: "V (pick W) \<in> V ` I"
      unfolding I_def using hWF by blast
    have hyVpick: "y \<in> V (pick W)"
      using hyW hpick hWF by simp
    show "y \<in> \<Union>(V ` I)"
      by (rule UnionI[OF hVI hyVpick])
  qed

  define W where "W = \<Inter>(U ` I)"

  have hInterTX: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hTopX[unfolded is_topology_on_def]]]])
  have hUimg_sub: "U ` I \<subseteq> TX"
    using hUopen hIsub by blast
  have hUimg_ne: "U ` I \<noteq> {}"
    using hIne by blast

  have hW_TX: "W \<in> TX"
  proof -
    have "finite (U ` I) \<and> U ` I \<noteq> {} \<and> U ` I \<subseteq> TX"
      by (intro conjI, rule finite_imageI[OF hIfin], rule hUimg_ne, rule hUimg_sub)
    hence "\<Inter>(U ` I) \<in> TX"
      using hInterTX by blast
    thus ?thesis
      unfolding W_def by simp
  qed

  have hx0W: "x0 \<in> W"
  proof -
    have "\<forall>S\<in>U ` I. x0 \<in> S"
    proof (intro ballI)
      fix S assume hS: "S \<in> U ` I"
      obtain i where hiI: "i \<in> I" and hSeq: "S = U i"
        using hS by blast
      have hiY: "i \<in> Y"
        using hIsub hiI by blast
      show "x0 \<in> S"
        unfolding hSeq using hx0U hiY by blast
    qed
    thus ?thesis
      unfolding W_def by blast
  qed

  have hnbhd: "neighborhood_of x0 X TX W"
    unfolding neighborhood_of_def using hW_TX hx0W by blast

  have hWprod_sub: "W \<times> Y \<subseteq> N"
  proof (rule subsetI)
    fix p assume hp: "p \<in> W \<times> Y"
    obtain x y where hp1: "p = (x,y)" and hxW: "x \<in> W" and hyY: "y \<in> Y"
      using hp by blast
    have hyU: "y \<in> \<Union>(V ` I)"
      using hIcov hyY by blast
    then obtain S where hS: "S \<in> V ` I" and hyS: "y \<in> S"
      by blast
    obtain i where hiI: "i \<in> I" and hSeq: "S = V i"
      using hS by blast
    have hiY: "i \<in> Y"
      using hIsub hiI by blast
    have hyVi: "y \<in> V i"
      using hyS unfolding hSeq .
    have hxUi: "x \<in> U i"
    proof -
      have hiUI: "U i \<in> U ` I"
        using hiI by blast
      have hxAll: "\<forall>S\<in>U ` I. x \<in> S"
        using hxW unfolding W_def by simp
      have "x \<in> U i"
        using hxAll hiUI by (rule bspec)
      thus ?thesis .
    qed
    have hsub: "U i \<times> V i \<subseteq> N"
      using hUVsub hiY by blast
    have "(x,y) \<in> U i \<times> V i"
      using hxUi hyVi by blast
    hence "(x,y) \<in> N"
      using hsub by blast
    thus "p \<in> N"
      unfolding hp1 by simp
  qed

  show ?thesis
    apply (rule exI[where x=W])
    apply (rule conjI)
     apply (rule hnbhd)
    apply (rule hWprod_sub)
    done
qed

text \<open>
  Tube lemma (\<S>26, Lemma 26.8): given an open set \<open>N\<close> in the product and a full slice
  \<open>{x0} \<times> Y\<close> contained in \<open>N\<close>, compactness of \<open>Y\<close> yields a neighborhood \<open>W\<close> of \<open>x0\<close>
  such that \<open>W \<times> Y \<subseteq> N\<close>.
\<close>

(** from \S26 Theorem 26.7 (Finite products of compact spaces are compact) [top1.tex:3184] **)
theorem Theorem_26_7:
  assumes hX: "top1_compact_on X TX"
  assumes hY: "top1_compact_on Y TY"
  shows "top1_compact_on (X \<times> Y) (product_topology_on TX TY)"
proof -
  have hTopX: "is_topology_on X TX"
    using hX unfolding top1_compact_on_def by blast
  have hCoverX:
    "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hX unfolding top1_compact_on_def by blast

  have hTopY: "is_topology_on Y TY"
    using hY unfolding top1_compact_on_def by blast
  have hCoverY:
    "\<forall>Uc. Uc \<subseteq> TY \<and> Y \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"
    using hY unfolding top1_compact_on_def by blast

  have hTopXY: "is_topology_on (X \<times> Y) (product_topology_on TX TY)"
    by (rule product_topology_on_is_topology_on[OF hTopX hTopY])

  have hUnionTP: "\<forall>K. K \<subseteq> product_topology_on TX TY \<longrightarrow> \<Union>K \<in> product_topology_on TX TY"
    using hTopXY unfolding is_topology_on_def by blast

  show ?thesis
    unfolding top1_compact_on_def
  proof (intro conjI)
    show "is_topology_on (X \<times> Y) (product_topology_on TX TY)"
      by (rule hTopXY)

    show "\<forall>Uc. Uc \<subseteq> product_topology_on TX TY \<and> X \<times> Y \<subseteq> \<Union>Uc
           \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<times> Y \<subseteq> \<Union>F)"
    proof (intro allI impI)
      fix Uc :: "('a \<times> 'b) set set"
      assume hUc: "Uc \<subseteq> product_topology_on TX TY \<and> X \<times> Y \<subseteq> \<Union>Uc"
      have hUc_sub: "Uc \<subseteq> product_topology_on TX TY"
        using hUc by blast
      have hUc_cov: "X \<times> Y \<subseteq> \<Union>Uc"
        using hUc by blast

      have exWFX:
        "\<forall>x\<in>X. \<exists>p. neighborhood_of x X TX (fst p)
                 \<and> finite (snd p)
                 \<and> snd p \<subseteq> Uc
                 \<and> (fst p) \<times> Y \<subseteq> \<Union>(snd p)"
      proof (intro ballI)
        fix x assume hxX: "x \<in> X"

        define Vc where "Vc = (\<lambda>W. {y \<in> Y. (x, y) \<in> W}) ` Uc"

        have hVc_sub: "Vc \<subseteq> TY"
        proof (rule subsetI)
          fix V assume hV: "V \<in> Vc"
          obtain W where hWUc: "W \<in> Uc" and hVeq: "V = {y\<in>Y. (x, y) \<in> W}"
            using hV unfolding Vc_def by blast
          have hWopen: "W \<in> product_topology_on TX TY"
            using hUc_sub hWUc by blast
          have "V \<in> TY"
            unfolding hVeq
            by (rule top1_section_preimage_open[OF hTopX hTopY hWopen hxX])
          thus "V \<in> TY" .
        qed

        have hVc_cov: "Y \<subseteq> \<Union>Vc"
        proof (rule subsetI)
          fix y assume hyY: "y \<in> Y"
          have hxy: "(x, y) \<in> X \<times> Y"
            using hxX hyY by blast
          have "(x, y) \<in> \<Union>Uc"
            by (rule subsetD[OF hUc_cov hxy])
          then obtain W where hWUc: "W \<in> Uc" and hxyW: "(x, y) \<in> W"
            by blast
          have hyV: "y \<in> {y\<in>Y. (x, y) \<in> W}"
            using hyY hxyW by simp
          have hVin: "{y\<in>Y. (x, y) \<in> W} \<in> Vc"
            unfolding Vc_def using hWUc by blast
          show "y \<in> \<Union>Vc"
            by (rule UnionI[OF hVin hyV])
        qed

        obtain Fc where hFcfin: "finite Fc" and hFcsub: "Fc \<subseteq> Vc" and hFccov: "Y \<subseteq> \<Union>Fc"
          using hCoverY[rule_format, OF conjI[OF hVc_sub hVc_cov]] by blast

        have hrepr: "\<forall>V\<in>Fc. \<exists>W. W \<in> Uc \<and> V = {y\<in>Y. (x, y) \<in> W}"
        proof (intro ballI)
          fix V assume hVFc: "V \<in> Fc"
          have hV: "V \<in> Vc"
            using hFcsub hVFc by blast
          show "\<exists>W. W \<in> Uc \<and> V = {y\<in>Y. (x, y) \<in> W}"
            using hV unfolding Vc_def by blast
        qed

        obtain pick where hpick:
          "\<forall>V\<in>Fc. pick V \<in> Uc \<and> V = {y\<in>Y. (x, y) \<in> pick V}"
          using bchoice[OF hrepr] by blast

        define Fx where "Fx = pick ` Fc"
        have hFxfin: "finite Fx"
          unfolding Fx_def by (rule finite_imageI[OF hFcfin])
        have hFxsub: "Fx \<subseteq> Uc"
          unfolding Fx_def using hpick by blast

        have hslice: "{x} \<times> Y \<subseteq> \<Union>Fx"
        proof (rule subsetI)
          fix p assume hp: "p \<in> {x} \<times> Y"
          obtain y where hyY: "y \<in> Y" and hpEq: "p = (x,y)"
            using hp by blast
          have "y \<in> \<Union>Fc"
            by (rule subsetD[OF hFccov hyY])
          then obtain V where hVFc: "V \<in> Fc" and hyV: "y \<in> V"
            by blast
          have hWUc: "pick V \<in> Uc" and hVeq: "V = {y\<in>Y. (x, y) \<in> pick V}"
            using hpick hVFc by blast+
          have hxyW: "(x, y) \<in> pick V"
          proof -
            have hsubV: "V \<subseteq> {y\<in>Y. (x, y) \<in> pick V}"
              using hVeq by (rule equalityD1)
            have "y \<in> {y\<in>Y. (x, y) \<in> pick V}"
              by (rule subsetD[OF hsubV hyV])
            thus ?thesis
              by blast
          qed
          have hWFx: "pick V \<in> Fx"
            unfolding Fx_def using hVFc by blast
          have hpW: "p \<in> pick V"
            unfolding hpEq using hxyW by simp
          show "p \<in> \<Union>Fx"
            by (rule UnionI[OF hWFx hpW])
        qed

        have hFx_subTP: "Fx \<subseteq> product_topology_on TX TY"
          using hUc_sub hFxsub by blast
        have hNopen: "\<Union>Fx \<in> product_topology_on TX TY"
          using hUnionTP hFx_subTP by blast

        obtain W where hWnb: "neighborhood_of x X TX W" and hWsub: "W \<times> Y \<subseteq> \<Union>Fx"
          using Lemma_26_8[OF hY hTopX hTopY hNopen hxX hslice] by blast

        show "\<exists>p. neighborhood_of x X TX (fst p)
                 \<and> finite (snd p)
                 \<and> snd p \<subseteq> Uc
                 \<and> (fst p) \<times> Y \<subseteq> \<Union>(snd p)"
          apply (rule exI[where x="(W,Fx)"])
          apply (simp add: hWnb hFxfin hFxsub hWsub)
          done
      qed

      obtain sel where hsel:
        "\<forall>x\<in>X. neighborhood_of x X TX (fst (sel x))
             \<and> finite (snd (sel x))
             \<and> snd (sel x) \<subseteq> Uc
             \<and> (fst (sel x)) \<times> Y \<subseteq> \<Union>(snd (sel x))"
        using bchoice[OF exWFX] by blast

      define W where "W x = fst (sel x)" for x
      define Fx where "Fx x = snd (sel x)" for x

      have hWsubTX: "W ` X \<subseteq> TX"
      proof (rule subsetI)
        fix U assume hU: "U \<in> W ` X"
        then obtain x where hxX: "x \<in> X" and hUeq: "U = W x"
          by blast
        have "neighborhood_of x X TX (W x)"
          using hsel hxX unfolding W_def Fx_def by simp
        hence "W x \<in> TX"
          unfolding neighborhood_of_def by blast
        thus "U \<in> TX"
          unfolding hUeq .
      qed

      have hWcov: "X \<subseteq> \<Union>(W ` X)"
      proof (rule subsetI)
        fix x assume hxX: "x \<in> X"
        have hnb: "neighborhood_of x X TX (W x)"
          using hsel hxX unfolding W_def Fx_def by simp
        hence hxW: "x \<in> W x"
          unfolding neighborhood_of_def by blast
        have hWin: "W x \<in> W ` X"
          using hxX unfolding W_def by blast
        show "x \<in> \<Union>(W ` X)"
          by (rule UnionI[OF hWin hxW])
      qed

      obtain G where hGfin: "finite G" and hGsub: "G \<subseteq> W ` X" and hGcov: "X \<subseteq> \<Union>G"
        using hCoverX[rule_format, OF conjI[OF hWsubTX hWcov]] by blast

      have hreprG: "\<forall>U\<in>G. \<exists>x\<in>X. U = W x"
      proof (intro ballI)
        fix U assume hUG: "U \<in> G"
        have "U \<in> W ` X"
          using hGsub hUG by blast
        thus "\<exists>x\<in>X. U = W x"
          unfolding W_def by blast
      qed

      obtain pick where hpick:
        "\<forall>U\<in>G. pick U \<in> X \<and> U = W (pick U)"
      proof -
        have hreprG': "\<forall>U\<in>G. \<exists>x. x \<in> X \<and> U = W x"
          using hreprG by blast
        obtain f where hf: "\<forall>U\<in>G. f U \<in> X \<and> U = W (f U)"
          using bchoice[OF hreprG'] by blast
        show ?thesis
          by (rule that[OF hf])
      qed

      define I where "I = pick ` G"
      have hIfin: "finite I"
        unfolding I_def by (rule finite_imageI[OF hGfin])
      have hIsub: "I \<subseteq> X"
        unfolding I_def using hpick by blast

      define F where "F = (\<Union>x\<in>I. Fx x)"

      have hFfin: "finite F"
      proof -
        have hfinFx: "\<And>x. x \<in> I \<Longrightarrow> finite (Fx x)"
        proof -
          fix x assume hxI: "x \<in> I"
          have hxX: "x \<in> X"
            using hIsub hxI by blast
          show "finite (Fx x)"
            using hsel hxX unfolding W_def Fx_def by simp
        qed
        show ?thesis
          unfolding F_def
          apply (rule finite_UN_I)
           apply (rule hIfin)
          apply (rule hfinFx)
          apply assumption
          done
      qed

      have hFsubUc: "F \<subseteq> Uc"
      proof (rule subsetI)
        fix U assume hU: "U \<in> F"
        then obtain x where hxI: "x \<in> I" and hUin: "U \<in> Fx x"
          unfolding F_def by blast
        have hxX: "x \<in> X"
          using hIsub hxI by blast
        have "Fx x \<subseteq> Uc"
          using hsel hxX unfolding W_def Fx_def by simp
        show "U \<in> Uc"
          using \<open>Fx x \<subseteq> Uc\<close> hUin by blast
      qed

      have hFcov: "X \<times> Y \<subseteq> \<Union>F"
      proof (rule subsetI)
        fix p assume hp: "p \<in> X \<times> Y"
        obtain x y where hpEq: "p = (x,y)" and hxX: "x \<in> X" and hyY: "y \<in> Y"
          using hp by blast
        have "x \<in> \<Union>G"
          using hGcov hxX by blast
        then obtain U0 where hU0G: "U0 \<in> G" and hxU0: "x \<in> U0"
          by blast
        have hiX: "pick U0 \<in> X" and hU0eq: "U0 = W (pick U0)"
          using hpick hU0G by blast+
        have hsubU0: "U0 \<subseteq> W (pick U0)"
          using hU0eq by (rule equalityD1)
        have hiI: "pick U0 \<in> I"
          unfolding I_def using hU0G by blast
        have hsub: "W (pick U0) \<times> Y \<subseteq> \<Union>(Fx (pick U0))"
          using hsel hiX unfolding W_def Fx_def by simp
        have hxWi: "x \<in> W (pick U0)"
          by (rule subsetD[OF hsubU0 hxU0])
        have hpWi: "(x,y) \<in> W (pick U0) \<times> Y"
          using hxWi hyY by blast
        have "(x,y) \<in> \<Union>(Fx (pick U0))"
          using hsub hpWi by blast
        moreover have "\<Union>(Fx (pick U0)) \<subseteq> \<Union>F"
        proof -
          have "Fx (pick U0) \<subseteq> F"
            unfolding F_def using hiI by blast
          thus ?thesis
            by blast
        qed
        ultimately have "(x,y) \<in> \<Union>F"
          by blast
        thus "p \<in> \<Union>F"
          unfolding hpEq by simp
      qed

      show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<times> Y \<subseteq> \<Union>F"
        apply (rule exI[where x=F])
        apply (rule conjI)
         apply (rule hFfin)
        apply (rule conjI)
         apply (rule hFsubUc)
        apply (rule hFcov)
        done
    qed
  qed
qed

(** from \S26 Theorem 26.9 (Finite intersection property characterization) [top1.tex:3268] **)
theorem Theorem_26_9:
  assumes hTop: "is_topology_on X TX"
  shows "top1_compact_on X TX \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
         (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})
         \<longrightarrow> \<Inter>\<C> \<noteq> {})"
proof (rule iffI)
  assume hcomp: "top1_compact_on X TX"
  have hCover:
    "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  show "\<forall>\<C>. (\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
       (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {}) \<longrightarrow>
       \<Inter>\<C> \<noteq> {}"
  proof (intro allI impI)
    fix \<C> :: "'a set set"
    assume hC: "(\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
      (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})"
    have hClosed: "\<forall>C\<in>\<C>. closedin_on X TX C"
      using hC by blast
    have hFIP:
      "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {}"
      using hC by blast

    show "\<Inter>\<C> \<noteq> {}"
    proof
      assume hInt: "\<Inter>\<C> = {}"

      have hCne: "\<C> \<noteq> {}"
      proof
        assume hC0: "\<C> = {}"
        have "\<Inter>\<C> = (UNIV::'a set)"
          unfolding hC0 by simp
        thus False
          using hInt by simp
      qed

      obtain A where hA: "A \<in> \<C>"
        using hCne by blast
      have hA_closed: "closedin_on X TX A"
        using hClosed hA by blast
      have hAne: "A \<noteq> {}"
      proof -
        have "finite {A} \<and> {A} \<noteq> {} \<and> {A} \<subseteq> \<C>"
          using hA by simp
        hence "\<Inter>{A} \<noteq> {}"
          using hFIP by blast
        thus ?thesis
          by simp
      qed
      have hXne: "X \<noteq> {}"
        using closedin_sub[OF hA_closed] hAne by blast

      define Uc where "Uc = (\<lambda>A. X - A) ` \<C>"

      have hUc_sub: "Uc \<subseteq> TX"
      proof (rule subsetI)
        fix U assume hU: "U \<in> Uc"
        obtain A where hAin: "A \<in> \<C>" and hUeq: "U = X - A"
          using hU unfolding Uc_def by blast
        have "X - A \<in> TX"
          by (rule closedin_diff_open[OF hClosed[rule_format, OF hAin]])
        thus "U \<in> TX"
          unfolding hUeq .
      qed

      have hCov: "X \<subseteq> \<Union>Uc"
      proof -
        have hEq: "X - \<Inter>\<C> = \<Union>{X - A |A. A \<in> \<C>}"
          by (rule diff_Inter_eq)
        have hEq2: "\<Union>{X - A |A. A \<in> \<C>} = \<Union>Uc"
          unfolding Uc_def by blast
        have "X = X - \<Inter>\<C>"
          using hInt by simp
        hence "X = \<Union>{X - A |A. A \<in> \<C>}"
          using hEq by simp
        thus ?thesis
          unfolding hEq2 by simp
      qed

      obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "X \<subseteq> \<Union>F"
        using hCover[rule_format, OF conjI[OF hUc_sub hCov]] by blast

      have hFne: "F \<noteq> {}"
      proof
        assume hF0: "F = {}"
        have "\<Union>F = {}"
          unfolding hF0 by simp
        thus False
          using hFcov hXne by blast
      qed

      define D where "D = (\<lambda>U. X - U) ` F"
      have hDfin: "finite D"
        unfolding D_def by (rule finite_imageI[OF hFfin])
      have hDne: "D \<noteq> {}"
        unfolding D_def using hFne by blast

      have hDsubC: "D \<subseteq> \<C>"
      proof (rule subsetI)
        fix A assume hAin: "A \<in> D"
        obtain U where hUF: "U \<in> F" and hAeq: "A = X - U"
          using hAin unfolding D_def by blast
        have hUUc: "U \<in> Uc"
          using hFsub hUF by blast
        obtain A0 where hA0in: "A0 \<in> \<C>" and hUeq: "U = X - A0"
          using hUUc unfolding Uc_def by blast
        have hA0subX: "A0 \<subseteq> X"
          by (rule closedin_sub[OF hClosed[rule_format, OF hA0in]])
        have "A = X - (X - A0)"
          unfolding hAeq hUeq by simp
        also have "... = A0"
          using hA0subX by blast
        finally show "A \<in> \<C>"
          using hA0in by simp
      qed

      have hInterD: "\<Inter>D = {}"
      proof (rule ccontr)
        assume hNonempty: "\<Inter>D \<noteq> {}"
        obtain x where hx: "x \<in> \<Inter>D"
          using hNonempty by blast

        have hxX: "x \<in> X"
        proof -
          have "\<Inter>D \<subseteq> X"
          proof (rule subsetI)
            fix y assume hy: "y \<in> \<Inter>D"
            have "\<forall>A\<in>D. y \<in> A"
              using hy by blast
            obtain A where hAD: "A \<in> D"
              using hDne by blast
            have hyA: "y \<in> A"
              using \<open>\<forall>A\<in>D. y \<in> A\<close> hAD by blast
            have hAinC: "A \<in> \<C>"
              using hDsubC hAD by blast
            have "A \<subseteq> X"
              by (rule closedin_sub[OF hClosed[rule_format, OF hAinC]])
            thus "y \<in> X"
              using hyA by blast
          qed
          thus ?thesis
            using hx by blast
        qed

        have hxNotUnionF: "x \<notin> \<Union>F"
        proof
          assume hxUF: "x \<in> \<Union>F"
          obtain U where hUF: "U \<in> F" and hxU: "x \<in> U"
            using hxUF by blast
          have "x \<in> X - U"
            using hx unfolding D_def using hUF by blast
          thus False
            using hxU by blast
        qed

        have hxUnionF: "x \<in> \<Union>F"
          using hFcov hxX by blast
        show False
          using hxNotUnionF hxUnionF by blast
      qed

      have False
        using hFIP[rule_format, OF conjI[OF hDfin conjI[OF hDne hDsubC]]]
        using hInterD by simp
      thus False by simp
    qed
  qed
next
  assume hFIPall:
    "\<forall>\<C>. (\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
         (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})
         \<longrightarrow> \<Inter>\<C> \<noteq> {}"

  show "top1_compact_on X TX"
    unfolding top1_compact_on_def
  proof (intro conjI)
    show "is_topology_on X TX"
      by (rule hTop)
    show "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    proof (intro allI impI)
      fix Uc :: "'a set set"
      assume hUc: "Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc"
      have hUcsub: "Uc \<subseteq> TX"
        using hUc by blast
      have hUccov: "X \<subseteq> \<Union>Uc"
        using hUc by blast

      show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F"
      proof (rule ccontr)
        assume hNoFin: "\<not> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"

        have hNoFin': "\<forall>F. finite F \<and> F \<subseteq> Uc \<longrightarrow> \<not> (X \<subseteq> \<Union>F)"
        proof (intro allI impI)
          fix F
          assume hF: "finite F \<and> F \<subseteq> Uc"
          show "\<not> (X \<subseteq> \<Union>F)"
          proof
            assume hcov: "X \<subseteq> \<Union>F"
            have "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F"
            proof (rule exI[where x=F])
              have hFfin: "finite F"
                using hF by (rule conjunct1)
              have hFsub: "F \<subseteq> Uc"
                using hF by (rule conjunct2)
              show "finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F"
                apply (rule conjI)
                 apply (rule hFfin)
                apply (rule conjI)
                 apply (rule hFsub)
                apply (rule hcov)
                done
            qed
            thus False
              using hNoFin by blast
          qed
        qed

        have hXne: "X \<noteq> {}"
        proof
          assume hX0: "X = {}"
          have "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F"
            unfolding hX0 by (rule exI[where x="{}"]) simp
          thus False
            using hNoFin by blast
        qed

        have hUcne: "Uc \<noteq> {}"
        proof
          assume hUc0: "Uc = {}"
          have "\<Union>Uc = {}"
            unfolding hUc0 by simp
          hence "X = {}"
            using hUccov by blast
          thus False
            using hXne by blast
        qed

        define \<C> where "\<C> = (\<lambda>U. X - U) ` Uc"

        have hX_TX: "X \<in> TX"
          by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])

        have hClosed: "\<forall>A\<in>\<C>. closedin_on X TX A"
        proof (intro ballI)
          fix A assume hA: "A \<in> \<C>"
          obtain U where hUUc: "U \<in> Uc" and hAeq: "A = X - U"
            using hA unfolding \<C>_def by blast
          have hU_TX: "U \<in> TX"
            using hUcsub hUUc by blast
          have hAsubX: "A \<subseteq> X"
            unfolding hAeq by blast
          have hXdiffA: "X - A = X \<inter> U"
            unfolding hAeq by blast
          have hXcapU: "X \<inter> U \<in> TX"
            by (rule topology_inter2[OF hTop hX_TX hU_TX])
          have hXdiffA_open: "X - A \<in> TX"
            unfolding hXdiffA using hXcapU by simp
          show "closedin_on X TX A"
            by (rule closedin_intro[OF hAsubX hXdiffA_open])
        qed

        have hFIP:
          "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {}"
        proof (intro allI impI)
          fix F assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C>"
          have hFfin: "finite F" and hFne: "F \<noteq> {}" and hFsub: "F \<subseteq> \<C>"
            using hF by blast+

          have hrep: "\<forall>A\<in>F. \<exists>U. U \<in> Uc \<and> A = X - U"
            using hFsub unfolding \<C>_def by blast
          obtain g where hg: "\<forall>A\<in>F. g A \<in> Uc \<and> A = X - g A"
            using bchoice[OF hrep] by blast

          define G where "G = g ` F"
          have hGfin: "finite G"
            unfolding G_def by (rule finite_imageI[OF hFfin])
          have hGsub: "G \<subseteq> Uc"
            unfolding G_def using hg by blast

          have hnotcov: "\<not> (X \<subseteq> \<Union>G)"
            using hNoFin'[rule_format, of G] hGfin hGsub by blast
          obtain x where hxX: "x \<in> X" and hxnotU: "x \<notin> \<Union>G"
            using hnotcov by blast

          have hxF: "\<forall>A\<in>F. x \<in> A"
          proof (intro ballI)
            fix A assume hAF: "A \<in> F"
            have hAg: "g A \<in> Uc \<and> A = X - g A"
              using hg hAF by blast
            have hxnotg: "x \<notin> g A"
            proof
              assume hxg: "x \<in> g A"
              have "g A \<in> G"
                unfolding G_def using hAF by blast
              hence "x \<in> \<Union>G"
                using hxg by blast
              thus False
                using hxnotU by blast
            qed
            show "x \<in> A"
              using hxX hxnotg hAg by blast
          qed

          have "x \<in> \<Inter>F"
            using hxF by blast
          thus "\<Inter>F \<noteq> {}"
            by blast
        qed

        have hInt: "\<Inter>\<C> \<noteq> {}"
        proof -
          have hPrem:
            "(\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
             (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})"
            apply (rule conjI)
             apply (rule hClosed)
            apply (rule hFIP)
            done
          show ?thesis
            by (rule hFIPall[rule_format, of \<C>]) (rule hPrem)
        qed
        obtain x where hx: "x \<in> \<Inter>\<C>"
          using hInt by blast

        obtain U0 where hU0: "U0 \<in> Uc"
          using hUcne by blast
        have hxX: "x \<in> X"
          using hx hU0 unfolding \<C>_def by blast

        have hxnotU: "x \<notin> \<Union>Uc"
        proof
          assume hxU: "x \<in> \<Union>Uc"
          obtain U where hUUc: "U \<in> Uc" and hxUin: "x \<in> U"
            using hxU by blast
          have "X - U \<in> \<C>"
            unfolding \<C>_def using hUUc by blast
          have "x \<in> X - U"
            using hx \<open>X - U \<in> \<C>\<close> by blast
          thus False
            using hxUin by blast
        qed

        have hxUnion: "x \<in> \<Union>Uc"
          using hUccov hxX by blast
        show False
          using hxnotU hxUnion by blast
      qed
    qed
  qed
qed

(** from \S26 Theorem 26.2 [top1.tex:3119] **)
theorem Theorem_26_2:
  assumes hcomp: "top1_compact_on X TX"
  assumes hA: "closedin_on X TX A"
  shows "top1_compact_on A (subspace_topology X TX A)"
proof -
  have hTX_top: "is_topology_on X TX"
    using hcomp unfolding top1_compact_on_def by blast
  have hAX: "A \<subseteq> X"
    by (rule closedin_sub[OF hA])
  have hsub_top: "is_topology_on A (subspace_topology X TX A)"
    by (rule subspace_topology_is_topology_on[OF hTX_top hAX])

  have compact_cover: "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  have hXA_open: "X - A \<in> TX"
    by (rule closedin_diff_open[OF hA])

  have cover_A:
    "\<forall>Uc. Uc \<subseteq> subspace_topology X TX A \<and> A \<subseteq> \<Union>Uc
        \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F)"
  proof (intro allI impI)
    fix Uc
    assume hUc: "Uc \<subseteq> subspace_topology X TX A \<and> A \<subseteq> \<Union>Uc"
    have hUc_sub: "Uc \<subseteq> subspace_topology X TX A"
      by (rule conjunct1[OF hUc])
    have hAcov: "A \<subseteq> \<Union>Uc"
      by (rule conjunct2[OF hUc])

    define V where "V = {U. U \<in> TX \<and> (A \<inter> U) \<in> Uc}"
    have hVsub: "V \<subseteq> TX"
      unfolding V_def by blast

    have hXcov: "X \<subseteq> \<Union>(V \<union> {X - A})"
    proof (rule subsetI)
      fix x
      assume hxX: "x \<in> X"
      show "x \<in> \<Union>(V \<union> {X - A})"
      proof (cases "x \<in> A")
        case True
        have "x \<in> \<Union>Uc"
          by (rule subsetD[OF hAcov, OF True])
        then obtain W where hW: "W \<in> Uc" and hxW: "x \<in> W"
          by blast
        have hW_TY: "W \<in> subspace_topology X TX A"
          using hUc_sub hW by blast
        obtain U where hU: "U \<in> TX" and hWeq: "W = A \<inter> U"
          using hW_TY unfolding subspace_topology_def by blast
        have hUV: "U \<in> V"
          unfolding V_def using hU hW hWeq by blast
        have hxU: "x \<in> U" using hxW hWeq by blast
        have hUin: "U \<in> V \<union> {X - A}"
          by (rule UnI1[OF hUV])
        show ?thesis
          by (rule UnionI[OF hUin hxU])
      next
        case False
        have hx: "x \<in> X - A" using hxX False by blast
        have hXAmem: "X - A \<in> V \<union> {X - A}"
          by (rule UnI2, rule singletonI)
        show ?thesis
          by (rule UnionI[OF hXAmem hx])
      qed
    qed

    have hVU_open: "V \<union> {X - A} \<subseteq> TX"
      using hVsub hXA_open by blast

    have hCover_imp: "V \<union> {X - A} \<subseteq> TX \<and> X \<subseteq> \<Union>(V \<union> {X - A})
        \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> V \<union> {X - A} \<and> X \<subseteq> \<Union>F)"
      by (rule spec[where x="V \<union> {X - A}", OF compact_cover])
    have hCover: "\<exists>F. finite F \<and> F \<subseteq> V \<union> {X - A} \<and> X \<subseteq> \<Union>F"
      by (rule mp[OF hCover_imp], intro conjI, rule hVU_open, rule hXcov)
    obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> V \<union> {X - A}" and hFcov: "X \<subseteq> \<Union>F"
      using hCover by blast

    define FV where "FV = F \<inter> V"
    have hFVfin: "finite FV"
      unfolding FV_def using hFfin by simp
    have hFVsub: "FV \<subseteq> V"
      unfolding FV_def by blast

    have hAcovFV: "A \<subseteq> \<Union>FV"
    proof (rule subsetI)
      fix x
      assume hxA: "x \<in> A"
      have hxX: "x \<in> X" using hAX hxA by blast
      have hxUF: "x \<in> \<Union>F"
        by (rule subsetD[OF hFcov, OF hxX])
      obtain U where hU: "U \<in> F" and hxU: "x \<in> U"
        using hxUF by blast
      have hU_notXA: "U \<noteq> X - A"
      proof
        assume h: "U = X - A"
        have "x \<in> X - A" using hxU h by simp
        thus False using hxA by blast
      qed
      have "U \<in> V"
        using hFsub hU hU_notXA by blast
      hence hUV: "U \<in> FV"
        unfolding FV_def using hU by blast
      show "x \<in> \<Union>FV"
        by (rule UnionI[OF hUV], rule hxU)
    qed

    define Fc where "Fc = {A \<inter> U | U. U \<in> FV}"
    have hFcfin: "finite Fc"
      unfolding Fc_def using hFVfin by simp
    have hFcsub: "Fc \<subseteq> Uc"
    proof (rule subsetI)
      fix W
      assume hW: "W \<in> Fc"
      obtain U where hU: "U \<in> FV" and hWeq: "W = A \<inter> U"
        using hW unfolding Fc_def by blast
      have hUV: "U \<in> V"
        using hFVsub hU by blast
      have "(A \<inter> U) \<in> Uc"
        using hUV unfolding V_def by blast
      thus "W \<in> Uc" using hWeq by simp
    qed

    have hAcovFc: "A \<subseteq> \<Union>Fc"
    proof (rule subsetI)
      fix x
      assume hxA: "x \<in> A"
      have hxUFV: "x \<in> \<Union>FV"
        by (rule subsetD[OF hAcovFV, OF hxA])
      obtain U where hU: "U \<in> FV" and hxU: "x \<in> U"
        using hxUFV by blast
      have hxAU: "x \<in> A \<inter> U" using hxA hxU by blast
      have hAU: "A \<inter> U \<in> Fc"
        unfolding Fc_def using hU by blast
      show "x \<in> \<Union>Fc"
        by (rule UnionI[OF hAU], rule hxAU)
    qed

    show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
      apply (rule exI[where x=Fc])
      apply (intro conjI)
        apply (rule hFcfin)
       apply (rule hFcsub)
      apply (rule hAcovFc)
      done
  qed

  show ?thesis
    unfolding top1_compact_on_def
    apply (intro conjI)
     apply (rule hsub_top)
    apply (rule cover_A)
    done
qed

(** from \S26 Theorem 26.3 [top1.tex:3128] **)
theorem Theorem_26_3:
  assumes hH: "is_hausdorff_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hAcomp: "top1_compact_on A (subspace_topology X TX A)"
  shows "closedin_on X TX A"
proof -
  have hTX: "is_topology_on X TX"
    using hH unfolding is_hausdorff_on_def by blast
  have X_T: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])
  have union_T: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])
  have inter_T: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])
  have hausd:
    "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
       (\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
    using hH unfolding is_hausdorff_on_def by blast

  have compact_coverA:
    "\<forall>Uc. Uc \<subseteq> subspace_topology X TX A \<and> A \<subseteq> \<Union>Uc
      \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F)"
    using hAcomp unfolding top1_compact_on_def by blast

  show ?thesis
  proof (rule closedin_intro)
    show "A \<subseteq> X" by (rule hAX)
    show "X - A \<in> TX"
    proof (cases "A = {}")
      case True
      have "X - A = X" using True by simp
      thus ?thesis using X_T by simp
    next
      case False

      have point_sep:
        "\<forall>x\<in>X - A. \<exists>V. V \<in> TX \<and> x \<in> V \<and> V \<subseteq> X - A"
      proof (intro ballI)
        fix x
        assume hx: "x \<in> X - A"
        have hxX: "x \<in> X" and hxA: "x \<notin> A" using hx by blast+

        have ex_pair:
          "\<forall>a\<in>A. \<exists>p. neighborhood_of a X TX (fst p)
                 \<and> neighborhood_of x X TX (snd p)
                 \<and> (fst p \<inter> snd p = {})"
        proof (intro ballI)
          fix a
          assume haA: "a \<in> A"
          have haX: "a \<in> X" using hAX haA by blast
          have hne: "a \<noteq> x"
          proof
            assume h: "a = x"
            hence "x \<in> A" using haA by simp
            thus False using hxA by contradiction
          qed
          obtain U V where hUa: "neighborhood_of a X TX U"
              and hVx: "neighborhood_of x X TX V" and hdisj: "U \<inter> V = {}"
            using hausd haX hxX hne by blast
          show "\<exists>p. neighborhood_of a X TX (fst p)
                 \<and> neighborhood_of x X TX (snd p)
                 \<and> (fst p \<inter> snd p = {})"
            apply (rule exI[where x="(U, V)"])
            apply (simp only: fst_conv snd_conv hUa hVx hdisj)
            done
        qed

        obtain p where hp:
          "\<forall>a\<in>A. neighborhood_of a X TX (fst (p a))
                 \<and> neighborhood_of x X TX (snd (p a))
                 \<and> (fst (p a) \<inter> snd (p a) = {})"
          using bchoice[OF ex_pair] by blast

        let ?U = "\<lambda>a. fst (p a)"
        let ?V = "\<lambda>a. snd (p a)"

        define Uc where "Uc = (\<lambda>a. A \<inter> ?U a) ` A"

        have hUc_sub: "Uc \<subseteq> subspace_topology X TX A"
        proof (rule subsetI)
          fix S
          assume hS: "S \<in> Uc"
          have hS': "S \<in> (\<lambda>a. A \<inter> ?U a) ` A"
            using hS unfolding Uc_def by simp
          have exa0: "\<exists>a\<in>A. S = (\<lambda>a. A \<inter> ?U a) a"
            using hS' by (simp only: image_iff)
          have exa: "\<exists>a\<in>A. A \<inter> ?U a = S"
          proof -
            obtain a where haA: "a \<in> A" and hEq: "S = A \<inter> ?U a"
              using exa0 by blast
            have hEq': "A \<inter> ?U a = S"
              using hEq by (rule sym)
            show ?thesis
              apply (rule bexI[where x=a])
               apply (rule hEq')
              apply (rule haA)
              done
          qed
          obtain a where haA: "a \<in> A" and hEq: "A \<inter> ?U a = S"
            using exa by blast
          have hSeq: "S = A \<inter> ?U a"
            using hEq by simp
          have hUa: "neighborhood_of a X TX (?U a)"
            using hp haA by blast
          have hUopen: "?U a \<in> TX"
            using hUa unfolding neighborhood_of_def by blast
          show "S \<in> subspace_topology X TX A"
            unfolding hSeq subspace_topology_def
            apply (subst setcompr_eq_image)
            apply (simp only: Collect_mem_eq)
            apply (rule imageI)
            apply (rule hUopen)
            done
        qed

        have hAcov: "A \<subseteq> \<Union>Uc"
        proof (rule subsetI)
          fix a
          assume haA: "a \<in> A"
          have hUa: "neighborhood_of a X TX (?U a)"
            using hp haA by blast
          have haUa: "a \<in> ?U a"
            using hUa unfolding neighborhood_of_def by blast
          have haS: "a \<in> A \<inter> ?U a"
            apply (rule IntI)
             apply (rule haA)
            apply (rule haUa)
            done
          have hS_Uc: "A \<inter> ?U a \<in> Uc"
            unfolding Uc_def
            apply (rule imageI)
            apply (rule haA)
            done
          show "a \<in> \<Union>Uc"
            by (rule UnionI[OF hS_Uc haS])
        qed

        have hCov: "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
          by (rule mp[OF spec[where x=Uc, OF compact_coverA]], intro conjI, rule hUc_sub, rule hAcov)
        obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "A \<subseteq> \<Union>F"
          using hCov by blast

        have hFne: "F \<noteq> {}"
        proof
          assume h: "F = {}"
          have hU: "\<Union>F = {}" using h by simp
          have "A \<subseteq> {}" using hFcov hU by simp
          hence "A = {}" by blast
          thus False using False by contradiction
        qed

        have ex_idx: "\<forall>S\<in>F. \<exists>a. a \<in> A \<and> S = A \<inter> ?U a"
        proof (intro ballI)
          fix S
          assume hS: "S \<in> F"
          have hS_Uc: "S \<in> Uc" using hFsub hS by blast
          have hS_Uc': "S \<in> (\<lambda>a. A \<inter> ?U a) ` A"
            using hS_Uc unfolding Uc_def by simp
          have exa0: "\<exists>a\<in>A. S = (\<lambda>a. A \<inter> ?U a) a"
            using hS_Uc' by (simp only: image_iff)
          have exa: "\<exists>a\<in>A. A \<inter> ?U a = S"
          proof -
            obtain a where haA: "a \<in> A" and hEq: "S = A \<inter> ?U a"
              using exa0 by blast
            have hEq': "A \<inter> ?U a = S"
              using hEq by (rule sym)
            show ?thesis
              apply (rule bexI[where x=a])
               apply (rule hEq')
              apply (rule haA)
              done
          qed
          obtain a where haA: "a \<in> A" and hEq: "A \<inter> ?U a = S"
            using exa by blast
          have hSeq: "S = A \<inter> ?U a"
            using hEq by simp
          show "\<exists>a. a \<in> A \<and> S = A \<inter> ?U a"
            apply (rule exI[where x=a])
            apply (intro conjI)
             apply (rule haA)
            apply (rule hSeq)
            done
        qed
        obtain sel where hsel: "\<forall>S\<in>F. sel S \<in> A \<and> S = A \<inter> ?U (sel S)"
          using bchoice[OF ex_idx] by blast

        define Vset where "Vset = (\<lambda>S. ?V (sel S)) ` F"
        have hVset_fin: "finite Vset"
          unfolding Vset_def using hFfin by simp
        have hVset_ne: "Vset \<noteq> {}"
        proof
          assume h: "Vset = {}"
          have "\<Union>Vset = {}" using h by simp
          have exS0: "\<exists>S0. S0 \<in> F"
            using hFne by (simp add: ex_in_conv)
          obtain S0 where hS0: "S0 \<in> F"
            using exS0 by blast
          have "sel S0 \<in> A"
            using hsel hS0 by blast
          have hVx: "neighborhood_of x X TX (?V (sel S0))"
            using hp \<open>sel S0 \<in> A\<close> by blast
          have hVxT: "?V (sel S0) \<in> TX"
            using hVx unfolding neighborhood_of_def by blast
          have "?V (sel S0) \<in> Vset"
            unfolding Vset_def
            apply (rule imageI)
            apply (rule hS0)
            done
          thus False using h by blast
        qed

        have hVset_sub: "Vset \<subseteq> TX"
        proof (rule subsetI)
          fix V
          assume hV: "V \<in> Vset"
          have exS: "\<exists>S\<in>F. V = (\<lambda>S. ?V (sel S)) S"
            using hV unfolding Vset_def by (simp only: image_iff)
          obtain S where hS: "S \<in> F" and hVeq: "V = ?V (sel S)"
            using exS by blast
          have hselA: "sel S \<in> A"
            using hsel hS by blast
          have hVx: "neighborhood_of x X TX (?V (sel S))"
            using hp hselA by blast
          have hVT: "?V (sel S) \<in> TX"
            using hVx unfolding neighborhood_of_def by blast
          show "V \<in> TX" using hVT hVeq by simp
        qed

        have hV0T: "\<Inter>Vset \<in> TX"
          using inter_T hVset_fin hVset_ne hVset_sub by blast

        have hxV0: "x \<in> \<Inter>Vset"
        proof (rule InterI)
          fix V
          assume hV: "V \<in> Vset"
          have exS: "\<exists>S\<in>F. V = (\<lambda>S. ?V (sel S)) S"
            using hV unfolding Vset_def by (simp only: image_iff)
          obtain S where hS: "S \<in> F" and hVeq: "V = ?V (sel S)"
            using exS by blast
          have hselA: "sel S \<in> A"
            using hsel hS by blast
          have hVx: "neighborhood_of x X TX (?V (sel S))"
            using hp hselA by blast
          have hxV: "x \<in> ?V (sel S)"
            using hVx unfolding neighborhood_of_def by blast
          show "x \<in> V" using hxV hVeq by simp
        qed

        have hV0_disj: "A \<inter> \<Inter>Vset = {}"
        proof (rule ccontr)
          assume hne: "A \<inter> \<Inter>Vset \<noteq> {}"
          have exa: "\<exists>a. a \<in> A \<inter> \<Inter>Vset"
            using hne by blast
          obtain a where ha: "a \<in> A \<inter> \<Inter>Vset"
            using exa by blast
          have haA: "a \<in> A" and haV0: "a \<in> \<Inter>Vset" using ha by blast+
          have haUF: "a \<in> \<Union>F"
            using hFcov haA by blast
          obtain S where hS: "S \<in> F" and haS: "a \<in> S"
            using haUF by blast
          have hSeq: "S = A \<inter> ?U (sel S)"
            using hsel hS by blast
          have hselA: "sel S \<in> A"
            using hsel hS by blast
          have hUa: "neighborhood_of (sel S) X TX (?U (sel S))"
            using hp hselA by blast
          have hVx: "neighborhood_of x X TX (?V (sel S))"
            using hp hselA by blast
          have hdisjUV: "?U (sel S) \<inter> ?V (sel S) = {}"
            using hp hselA by blast
          have ha_int: "a \<in> A \<inter> ?U (sel S)"
            apply (subst hSeq[symmetric])
            apply (rule haS)
            done
          have haU: "a \<in> ?U (sel S)"
            by (rule IntD2[OF ha_int])
          have haV: "a \<in> ?V (sel S)"
          proof -
            have "?V (sel S) \<in> Vset"
              unfolding Vset_def
              apply (rule imageI)
              apply (rule hS)
              done
            hence "\<Inter>Vset \<subseteq> ?V (sel S)" by blast
            thus ?thesis using haV0 by blast
          qed
          have "a \<in> ?U (sel S) \<inter> ?V (sel S)"
            apply (rule IntI)
             apply (rule haU)
            apply (rule haV)
            done
          thus False using hdisjUV by blast
        qed

        let ?V0 = "X \<inter> \<Inter>Vset"
        have hV0open: "?V0 \<in> TX"
          by (rule topology_inter2[OF hTX X_T hV0T])
        have hxV0': "x \<in> ?V0"
          apply (rule IntI)
           apply (rule hxX)
          apply (rule hxV0)
          done
        have hV0sub: "?V0 \<subseteq> X - A"
        proof (rule subsetI)
          fix z
          assume hz: "z \<in> ?V0"
          have hzX: "z \<in> X" and hzV0: "z \<in> \<Inter>Vset" using hz by blast+
          show "z \<in> X - A"
          proof (rule DiffI)
            show "z \<in> X" by (rule hzX)
            show "z \<notin> A"
            proof
              assume hzA: "z \<in> A"
              have "z \<in> A \<inter> \<Inter>Vset"
                apply (rule IntI)
                 apply (rule hzA)
                apply (rule hzV0)
                done
              hence False using hV0_disj by blast
              thus False ..
            qed
          qed
        qed

        show "\<exists>V. V \<in> TX \<and> x \<in> V \<and> V \<subseteq> X - A"
          apply (rule exI[where x="X \<inter> \<Inter>Vset"])
          apply (intro conjI)
            apply (rule hV0open)
           apply (rule hxV0')
          apply (rule hV0sub)
          done
      qed

      define G where "G = {V. V \<in> TX \<and> V \<subseteq> X - A}"
      have hGsub: "G \<subseteq> TX" unfolding G_def by blast
      have hUnionG_sub: "\<Union>G \<subseteq> X - A" unfolding G_def by blast

      have hXA_sub: "X - A \<subseteq> \<Union>G"
      proof (rule subsetI)
        fix x
        assume hx: "x \<in> X - A"
        obtain V where hV: "V \<in> TX \<and> x \<in> V \<and> V \<subseteq> X - A"
          using point_sep hx by blast
        have hVG: "V \<in> G" using hV unfolding G_def by blast
        have hxV: "x \<in> V" using hV by blast
        show "x \<in> \<Union>G"
          by (rule UnionI[OF hVG hxV])
      qed

      have "X - A = \<Union>G"
        apply (rule equalityI)
         apply (rule hXA_sub)
        apply (rule hUnionG_sub)
        done
      moreover have "\<Union>G \<in> TX"
        by (rule union_T[rule_format, OF hGsub])
      ultimately show "X - A \<in> TX" by simp
    qed
  qed
qed

(** from \S26 Lemma 26.4 [top1.tex:3157] **)
lemma Lemma_26_4:
  assumes hH: "is_hausdorff_on X TX"
  assumes hYX: "Y \<subseteq> X"
  assumes hYcomp: "top1_compact_on Y (subspace_topology X TX Y)"
  assumes hx0X: "x0 \<in> X"
  assumes hx0Y: "x0 \<notin> Y"
  shows "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> x0 \<in> U \<and> Y \<subseteq> V \<and> U \<inter> V = {}"
proof -
  have hTX: "is_topology_on X TX"
    using hH unfolding is_hausdorff_on_def by blast
  have empty_TX: "{} \<in> TX"
    by (rule conjunct1[OF hTX[unfolded is_topology_on_def]])
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])
  have inter_TX: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> TX \<longrightarrow> \<Inter>F \<in> TX"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])

  have hausd:
    "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
       (\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
    using hH unfolding is_hausdorff_on_def by blast

  show ?thesis
  proof (cases "Y = {}")
    case True
    show ?thesis
      apply (rule exI[where x=X])
      apply (rule exI[where x="{}"])
      apply (intro conjI)
          apply (rule X_TX)
         apply (rule empty_TX)
        apply (rule hx0X)
       apply (simp only: True)
      apply simp
      done
  next
    case False

    have ex_pair:
      "\<forall>y\<in>Y. \<exists>p. neighborhood_of y X TX (fst p)
             \<and> neighborhood_of x0 X TX (snd p)
             \<and> (fst p \<inter> snd p = {})"
    proof (intro ballI)
      fix y
      assume hyY: "y \<in> Y"
      have hyX: "y \<in> X" using hYX hyY by blast
      have hyne: "y \<noteq> x0"
      proof
        assume h: "y = x0"
        hence "x0 \<in> Y" using hyY by simp
        thus False using hx0Y by contradiction
      qed
      obtain U V where hUy: "neighborhood_of y X TX U"
          and hV0: "neighborhood_of x0 X TX V" and hdisj: "U \<inter> V = {}"
        using hausd hyX hx0X hyne by blast
      show "\<exists>p. neighborhood_of y X TX (fst p)
             \<and> neighborhood_of x0 X TX (snd p)
             \<and> (fst p \<inter> snd p = {})"
        apply (rule exI[where x="(U, V)"])
        apply (simp only: fst_conv snd_conv hUy hV0 hdisj)
        done
    qed

    obtain p where hp:
      "\<forall>y\<in>Y. neighborhood_of y X TX (fst (p y))
             \<and> neighborhood_of x0 X TX (snd (p y))
             \<and> (fst (p y) \<inter> snd (p y) = {})"
      using bchoice[OF ex_pair] by blast

    let ?Uy = "\<lambda>y. fst (p y)"
    let ?Vy = "\<lambda>y. snd (p y)"

    define Uc where "Uc = (\<lambda>y. Y \<inter> ?Uy y) ` Y"

    have hUc_sub: "Uc \<subseteq> subspace_topology X TX Y"
    proof (rule subsetI)
      fix S
      assume hS: "S \<in> Uc"
      have hS': "S \<in> (\<lambda>y. Y \<inter> ?Uy y) ` Y"
        using hS unfolding Uc_def by simp
      have exy: "\<exists>y\<in>Y. S = (\<lambda>y. Y \<inter> ?Uy y) y"
        using hS' by (simp only: image_iff)
      obtain y where hyY: "y \<in> Y" and hSeq: "S = Y \<inter> ?Uy y"
        using exy by blast
      have hUy: "neighborhood_of y X TX (?Uy y)"
        using hp hyY by blast
      have hUyT: "?Uy y \<in> TX"
        using hUy unfolding neighborhood_of_def by blast
      show "S \<in> subspace_topology X TX Y"
        unfolding hSeq subspace_topology_def
        apply (subst setcompr_eq_image)
        apply (simp only: Collect_mem_eq)
        apply (rule imageI)
        apply (rule hUyT)
        done
    qed

    have hYcov: "Y \<subseteq> \<Union>Uc"
    proof (rule subsetI)
      fix y
      assume hyY: "y \<in> Y"
      have hUy: "neighborhood_of y X TX (?Uy y)"
        using hp hyY by blast
      have hyUy: "y \<in> ?Uy y"
        using hUy unfolding neighborhood_of_def by blast
      have hyS: "y \<in> Y \<inter> ?Uy y"
        apply (rule IntI)
         apply (rule hyY)
        apply (rule hyUy)
        done
      have hS_Uc: "Y \<inter> ?Uy y \<in> Uc"
        unfolding Uc_def
        apply (rule imageI)
        apply (rule hyY)
        done
      show "y \<in> \<Union>Uc"
        by (rule UnionI[OF hS_Uc hyS])
    qed

    have compact_coverY:
      "\<forall>Uc. Uc \<subseteq> subspace_topology X TX Y \<and> Y \<subseteq> \<Union>Uc
        \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"
      using hYcomp unfolding top1_compact_on_def by blast
    have hCov: "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F"
      by (rule mp[OF spec[where x=Uc, OF compact_coverY]], intro conjI, rule hUc_sub, rule hYcov)
    obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "Y \<subseteq> \<Union>F"
      using hCov by blast

    have hFne: "F \<noteq> {}"
    proof
      assume h: "F = {}"
      have "\<Union>F = {}" using h by simp
      have "Y \<subseteq> {}" using hFcov \<open>\<Union>F = {}\<close> by simp
      hence "Y = {}" by blast
      thus False using False by contradiction
    qed

    have ex_idx: "\<forall>S\<in>F. \<exists>y. y \<in> Y \<and> S = Y \<inter> ?Uy y"
    proof (intro ballI)
      fix S
      assume hS: "S \<in> F"
      have hS_Uc: "S \<in> Uc" using hFsub hS by blast
      have hS': "S \<in> (\<lambda>y. Y \<inter> ?Uy y) ` Y"
        using hS_Uc unfolding Uc_def by simp
      have exy: "\<exists>y\<in>Y. S = (\<lambda>y. Y \<inter> ?Uy y) y"
        using hS' by (simp only: image_iff)
      obtain y where hyY: "y \<in> Y" and hSeq: "S = Y \<inter> ?Uy y"
        using exy by blast
      show "\<exists>y. y \<in> Y \<and> S = Y \<inter> ?Uy y"
        apply (rule exI[where x=y])
        apply (intro conjI)
         apply (rule hyY)
        apply (rule hSeq)
        done
    qed
    obtain sel where hsel: "\<forall>S\<in>F. sel S \<in> Y \<and> S = Y \<inter> ?Uy (sel S)"
      using bchoice[OF ex_idx] by blast

    define Vset where "Vset = (\<lambda>S. ?Vy (sel S)) ` F"
    define Uset where "Uset = (\<lambda>S. ?Uy (sel S)) ` F"

    have hVset_fin: "finite Vset"
      unfolding Vset_def using hFfin by simp
    have hUset_sub: "Uset \<subseteq> TX"
    proof (rule subsetI)
      fix U
      assume hU: "U \<in> Uset"
      have exS: "\<exists>S\<in>F. U = (\<lambda>S. ?Uy (sel S)) S"
        using hU unfolding Uset_def by (simp only: image_iff)
      obtain S where hS: "S \<in> F" and hUeq: "U = ?Uy (sel S)"
        using exS by blast
      have hselY: "sel S \<in> Y" using hsel hS by blast
      have hselX: "sel S \<in> X" using hYX hselY by blast
      have hUy: "neighborhood_of (sel S) X TX (?Uy (sel S))"
        using hp hselY by blast
      have hUT: "?Uy (sel S) \<in> TX" using hUy unfolding neighborhood_of_def by blast
      show "U \<in> TX" using hUT hUeq by simp
    qed
    have hVset_sub: "Vset \<subseteq> TX"
    proof (rule subsetI)
      fix V
      assume hV: "V \<in> Vset"
      have exS: "\<exists>S\<in>F. V = (\<lambda>S. ?Vy (sel S)) S"
        using hV unfolding Vset_def by (simp only: image_iff)
      obtain S where hS: "S \<in> F" and hVeq: "V = ?Vy (sel S)"
        using exS by blast
      have hselY: "sel S \<in> Y" using hsel hS by blast
      have hV0: "neighborhood_of x0 X TX (?Vy (sel S))"
        using hp hselY by blast
      have hVT: "?Vy (sel S) \<in> TX" using hV0 unfolding neighborhood_of_def by blast
      show "V \<in> TX" using hVT hVeq by simp
    qed

    have hVset_ne: "Vset \<noteq> {}"
    proof
      assume h: "Vset = {}"
      have exS0: "\<exists>S0. S0 \<in> F" using hFne by (simp add: ex_in_conv)
      obtain S0 where hS0: "S0 \<in> F" using exS0 by blast
      have "?Vy (sel S0) \<in> Vset"
        unfolding Vset_def
        apply (rule imageI)
        apply (rule hS0)
        done
      thus False using h by blast
    qed

    have hUopen: "\<Inter>Vset \<in> TX"
      using inter_TX hVset_fin hVset_ne hVset_sub by blast
    have hx0U: "x0 \<in> \<Inter>Vset"
    proof (rule InterI)
      fix V
      assume hV: "V \<in> Vset"
      have exS: "\<exists>S\<in>F. V = (\<lambda>S. ?Vy (sel S)) S"
        using hV unfolding Vset_def by (simp only: image_iff)
      obtain S where hS: "S \<in> F" and hVeq: "V = ?Vy (sel S)"
        using exS by blast
      have hselY: "sel S \<in> Y" using hsel hS by blast
      have hV0: "neighborhood_of x0 X TX (?Vy (sel S))"
        using hp hselY by blast
      have hx0V: "x0 \<in> ?Vy (sel S)" using hV0 unfolding neighborhood_of_def by blast
      show "x0 \<in> V" using hx0V hVeq by simp
    qed

    have hVopen: "\<Union>Uset \<in> TX"
      by (rule union_TX[rule_format, OF hUset_sub])

    have hYsubV: "Y \<subseteq> \<Union>Uset"
    proof (rule subsetI)
      fix y
      assume hyY: "y \<in> Y"
      have hyUF: "y \<in> \<Union>F" using hFcov hyY by blast
      obtain S where hS: "S \<in> F" and hyS: "y \<in> S" using hyUF by blast
      have hSeq: "S = Y \<inter> ?Uy (sel S)"
        using hsel hS by blast
      have hy_int: "y \<in> Y \<inter> ?Uy (sel S)"
        apply (subst hSeq[symmetric])
        apply (rule hyS)
        done
      have hyU: "y \<in> ?Uy (sel S)"
        by (rule IntD2[OF hy_int])
      have "?Uy (sel S) \<in> Uset"
        unfolding Uset_def
        apply (rule imageI)
        apply (rule hS)
        done
      thus "y \<in> \<Union>Uset"
        by (rule UnionI[OF _ hyU])
    qed

    have hdisj: "\<Inter>Vset \<inter> \<Union>Uset = {}"
    proof (rule ccontr)
      assume hne: "\<Inter>Vset \<inter> \<Union>Uset \<noteq> {}"
      have exz: "\<exists>z. z \<in> \<Inter>Vset \<inter> \<Union>Uset" using hne by blast
      obtain z where hz: "z \<in> \<Inter>Vset \<inter> \<Union>Uset" using exz by blast
      have hzV: "z \<in> \<Inter>Vset" and hzU: "z \<in> \<Union>Uset" using hz by blast+
      obtain U where hU: "U \<in> Uset" and hzU': "z \<in> U" using hzU by blast
      have exS: "\<exists>S\<in>F. U = (\<lambda>S. ?Uy (sel S)) S"
        using hU unfolding Uset_def by (simp only: image_iff)
      obtain S where hS: "S \<in> F" and hUeq: "U = ?Uy (sel S)"
        using exS by blast
      have hselY: "sel S \<in> Y" using hsel hS by blast
      have hUy: "neighborhood_of (sel S) X TX (?Uy (sel S))"
        using hp hselY by blast
      have hV0: "neighborhood_of x0 X TX (?Vy (sel S))"
        using hp hselY by blast
      have hdisjUV: "?Uy (sel S) \<inter> ?Vy (sel S) = {}"
        using hp hselY by blast
      have "?Vy (sel S) \<in> Vset"
        unfolding Vset_def
        apply (rule imageI)
        apply (rule hS)
        done
      have "\<Inter>Vset \<subseteq> ?Vy (sel S)" using \<open>?Vy (sel S) \<in> Vset\<close> by blast
      have hzV': "z \<in> ?Vy (sel S)" using hzV \<open>\<Inter>Vset \<subseteq> ?Vy (sel S)\<close> by blast
      have hzU'': "z \<in> ?Uy (sel S)" using hzU' hUeq by simp
      have "z \<in> ?Uy (sel S) \<inter> ?Vy (sel S)"
        apply (rule IntI)
         apply (rule hzU'')
        apply (rule hzV')
        done
      thus False using hdisjUV by blast
    qed

    show ?thesis
      apply (rule exI[where x="\<Inter>Vset"])
      apply (rule exI[where x="\<Union>Uset"])
      apply (intro conjI)
          apply (rule hUopen)
         apply (rule hVopen)
        apply (rule hx0U)
       apply (rule hYsubV)
      apply (rule hdisj)
      done
  qed
qed

(** from \S26 Theorem 26.5 [top1.tex:3163] **)
theorem Theorem_26_5:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hcomp: "top1_compact_on X TX"
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
  shows "top1_compact_on (f ` X) (subspace_topology Y TY (f ` X))"
proof -
  have hmap: "\<forall>x\<in>X. f x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hfXsub: "f ` X \<subseteq> Y"
    using hmap by blast
  have hsub_top: "is_topology_on (f ` X) (subspace_topology Y TY (f ` X))"
    by (rule subspace_topology_is_topology_on[OF hTY hfXsub])

  have compact_cover: "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  have pre_open: "\<forall>V\<in>TY. {x\<in>X. f x \<in> V} \<in> TX"
    using hcont unfolding top1_continuous_map_on_def by blast

  have cover_fX:
    "\<forall>Uc. Uc \<subseteq> subspace_topology Y TY (f ` X) \<and> f ` X \<subseteq> \<Union>Uc
        \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> f ` X \<subseteq> \<Union>F)"
  proof (intro allI impI)
    fix Uc
    assume hUc: "Uc \<subseteq> subspace_topology Y TY (f ` X) \<and> f ` X \<subseteq> \<Union>Uc"
    have hUc_sub: "Uc \<subseteq> subspace_topology Y TY (f ` X)"
      by (rule conjunct1[OF hUc])
    have hcov: "f ` X \<subseteq> \<Union>Uc"
      by (rule conjunct2[OF hUc])

    define V where "V = {W. W \<in> TY \<and> (f ` X \<inter> W) \<in> Uc}"
    have hVsub: "V \<subseteq> TY" unfolding V_def by blast

    define Pc where "Pc = {{x \<in> X. f x \<in> W} | W. W \<in> V}"

    have hPc_sub: "Pc \<subseteq> TX"
    proof (rule subsetI)
      fix P
      assume hP: "P \<in> Pc"
      obtain W where hW: "W \<in> V" and hPeq: "P = {x \<in> X. f x \<in> W}"
        using hP unfolding Pc_def by blast
      have hWTY: "W \<in> TY" using hW unfolding V_def by blast
      show "P \<in> TX" using pre_open hWTY hPeq by simp
    qed

    have hXcov: "X \<subseteq> \<Union>Pc"
    proof (rule subsetI)
      fix x
      assume hxX: "x \<in> X"
      have hfx: "f x \<in> f ` X" using hxX by blast
      have "f x \<in> \<Union>Uc"
        by (rule subsetD[OF hcov, OF hfx])
      then obtain U where hU: "U \<in> Uc" and hfxU: "f x \<in> U"
        by blast
      have hU_sub: "U \<in> subspace_topology Y TY (f ` X)"
        using hUc_sub hU by blast
      obtain W where hW: "W \<in> TY" and hUeq: "U = (f ` X) \<inter> W"
        using hU_sub unfolding subspace_topology_def by blast
      have hW_in_V: "W \<in> V"
        unfolding V_def using hW hU hUeq by blast
      have hxP: "x \<in> {x \<in> X. f x \<in> W}"
        using hxX hfxU unfolding hUeq by blast
      have hPW: "{x \<in> X. f x \<in> W} \<in> Pc"
        unfolding Pc_def using hW_in_V by blast
      show "x \<in> \<Union>Pc"
        by (rule UnionI[OF hPW hxP])
    qed

    have hCover_imp: "Pc \<subseteq> TX \<and> X \<subseteq> \<Union>Pc
        \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Pc \<and> X \<subseteq> \<Union>F)"
      by (rule spec[where x=Pc, OF compact_cover])
    have hCover: "\<exists>F. finite F \<and> F \<subseteq> Pc \<and> X \<subseteq> \<Union>F"
      by (rule mp[OF hCover_imp], intro conjI, rule hPc_sub, rule hXcov)
    obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Pc" and hFcov: "X \<subseteq> \<Union>F"
      using hCover by blast

    have hW_ex: "\<forall>P\<in>F. \<exists>W. W \<in> V \<and> P = {x \<in> X. f x \<in> W}"
    proof (intro ballI)
      fix P
      assume hP: "P \<in> F"
      have hP_Pc: "P \<in> Pc" using hFsub hP by blast
      show "\<exists>W. W \<in> V \<and> P = {x \<in> X. f x \<in> W}"
        using hP_Pc unfolding Pc_def by blast
    qed
    obtain sel where hsel: "\<forall>P\<in>F. sel P \<in> V \<and> P = {x \<in> X. f x \<in> sel P}"
      using bchoice[OF hW_ex] by blast

    define Fc where "Fc = {f ` X \<inter> sel P | P. P \<in> F}"
    have hFc_fin: "finite Fc"
      unfolding Fc_def using hFfin by simp

    have hFc_sub: "Fc \<subseteq> Uc"
    proof (rule subsetI)
      fix U
      assume hU: "U \<in> Fc"
      obtain P where hP: "P \<in> F" and hUeq: "U = f ` X \<inter> sel P"
        using hU unfolding Fc_def by blast
      have hselV: "sel P \<in> V"
        using hsel hP by blast
      have "f ` X \<inter> sel P \<in> Uc"
        using hselV unfolding V_def by blast
      thus "U \<in> Uc" using hUeq by simp
    qed

    have hcovFc: "f ` X \<subseteq> \<Union>Fc"
    proof (rule subsetI)
      fix y
      assume hy: "y \<in> f ` X"
      obtain x where hxX: "x \<in> X" and hyfx: "y = f x"
        using hy by blast
      have hxUF: "x \<in> \<Union>F"
        using hFcov hxX by blast
      obtain P where hP: "P \<in> F" and hxP: "x \<in> P"
        using hxUF by blast
      have hPeq: "P = {u \<in> X. f u \<in> sel P}"
        using hsel hP by blast
      have hPeq_sym: "{u \<in> X. f u \<in> sel P} = P"
        using hPeq by (rule sym)
      have hxP_sel: "x \<in> {u \<in> X. f u \<in> sel P}"
        apply (subst hPeq_sym)
        apply (rule hxP)
        done
      have hxP_conj: "x \<in> X \<and> f x \<in> sel P"
        using hxP_sel by (simp only: mem_Collect_eq)
      have hfx: "f x \<in> sel P"
        using hxP_conj by (rule conjunct2)
      have hy_selP: "y \<in> sel P"
        apply (subst hyfx)
        apply (rule hfx)
        done
      have hy_int: "y \<in> f ` X \<inter> sel P"
        apply (rule IntI)
         apply (rule hy)
        apply (rule hy_selP)
        done
      have hFc_mem: "f ` X \<inter> sel P \<in> Fc"
        unfolding Fc_def
        apply (subst setcompr_eq_image)
        apply (simp only: Collect_mem_eq)
        apply (rule imageI)
        apply (rule hP)
        done
      show "y \<in> \<Union>Fc"
        apply (rule UnionI)
         apply (rule hFc_mem)
        apply (rule hy_int)
        done
    qed

    show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> f ` X \<subseteq> \<Union>F"
      apply (rule exI[where x=Fc])
      apply (intro conjI)
        apply (rule hFc_fin)
       apply (rule hFc_sub)
      apply (rule hcovFc)
      done
  qed

  show ?thesis
    unfolding top1_compact_on_def
    apply (intro conjI)
     apply (rule hsub_top)
    apply (rule cover_fX)
    done
qed

(** from \S26 Theorem 26.6 [top1.tex:3180] **)
theorem Theorem_26_6:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hcomp: "top1_compact_on X TX"
  assumes hH: "is_hausdorff_on Y TY"
  assumes hf: "top1_continuous_map_on X TX Y TY f"
  assumes hbij: "bij_betw f X Y"
  shows "top1_homeomorphism_on X TX Y TY f"
proof -
  have hinj: "inj_on f X"
    using hbij unfolding bij_betw_def by blast
  have hsurj: "f ` X = Y"
    using hbij unfolding bij_betw_def by blast

  have cont_inv_closed:
    "top1_continuous_map_on Y TY X TX (inv_into X f) \<longleftrightarrow>
       ((\<forall>y\<in>Y. inv_into X f y \<in> X) \<and>
        (\<forall>B. closedin_on X TX B \<longrightarrow> closedin_on Y TY {y\<in>Y. inv_into X f y \<in> B}))"
    using Theorem_18_1(2)[OF hTY hTX, of "inv_into X f"] .

  have inv_maps: "\<forall>y\<in>Y. inv_into X f y \<in> X"
  proof (intro ballI)
    fix y
    assume hyY: "y \<in> Y"
    have hyFX: "y \<in> f ` X"
      using hyY hsurj by simp
    show "inv_into X f y \<in> X"
      by (rule inv_into_into[OF hyFX])
  qed

  have inv_closed_preimage:
    "\<forall>B. closedin_on X TX B \<longrightarrow> closedin_on Y TY {y\<in>Y. inv_into X f y \<in> B}"
  proof (intro allI impI)
    fix B
    assume hB: "closedin_on X TX B"
    have hBX: "B \<subseteq> X"
      by (rule closedin_sub[OF hB])

    have hBcomp: "top1_compact_on B (subspace_topology X TX B)"
      by (rule Theorem_26_2[OF hcomp hB])

    have hcontB: "top1_continuous_map_on B (subspace_topology X TX B) Y TY f"
    proof -
      have hrd:
        "\<forall>A g. top1_continuous_map_on X TX Y TY g \<and> A \<subseteq> X
          \<longrightarrow> top1_continuous_map_on A (subspace_topology X TX A) Y TY g"
        using Theorem_18_2(4)[OF hTX hTY hTY] .
      have "top1_continuous_map_on X TX Y TY f \<and> B \<subseteq> X"
        apply (intro conjI)
         apply (rule hf)
        apply (rule hBX)
        done
      thus ?thesis
        using hrd by blast
    qed

    have hsub_topB: "is_topology_on B (subspace_topology X TX B)"
      by (rule subspace_topology_is_topology_on[OF hTX hBX])

    have himg_compact: "top1_compact_on (f ` B) (subspace_topology Y TY (f ` B))"
      by (rule Theorem_26_5[OF hsub_topB hTY hBcomp hcontB])

    have hfBsub: "f ` B \<subseteq> Y"
    proof (rule subsetI)
      fix y
      assume hy: "y \<in> f ` B"
      then obtain x where hxB: "x \<in> B" and hyfx: "y = f x"
        by blast
      have hxX: "x \<in> X"
        using hBX hxB by blast
      have hmap: "\<forall>x\<in>X. f x \<in> Y"
        using hf unfolding top1_continuous_map_on_def by blast
      have "f x \<in> Y"
        using hmap hxX by blast
      thus "y \<in> Y" using hyfx by simp
    qed

    have himg_closed: "closedin_on Y TY (f ` B)"
      by (rule Theorem_26_3[OF hH hfBsub himg_compact])

    have preim_eq: "{y\<in>Y. inv_into X f y \<in> B} = f ` B"
    proof (rule equalityI)
      show "{y\<in>Y. inv_into X f y \<in> B} \<subseteq> f ` B"
      proof (rule subsetI)
        fix y
        assume hy: "y \<in> {y\<in>Y. inv_into X f y \<in> B}"
        have hyY: "y \<in> Y" and hinvB: "inv_into X f y \<in> B"
          using hy by blast+
        have hyFX: "y \<in> f ` X"
          using hyY hsurj by simp
        have hy_eq: "f (inv_into X f y) = y"
          by (rule f_inv_into_f[OF hyFX])
        have "y = f (inv_into X f y)" using hy_eq by simp
        thus "y \<in> f ` B"
          apply (subst \<open>y = f (inv_into X f y)\<close>)
          apply (rule imageI)
          apply (rule hinvB)
          done
      qed
      show "f ` B \<subseteq> {y\<in>Y. inv_into X f y \<in> B}"
      proof (rule subsetI)
        fix y
        assume hy: "y \<in> f ` B"
        then obtain x where hxB: "x \<in> B" and hyfx: "y = f x"
          by blast
        have hxX: "x \<in> X" using hBX hxB by blast
        have hyY: "y \<in> Y" using hfBsub hy by blast
        have hinv: "inv_into X f y \<in> B"
        proof -
          have "inv_into X f (f x) = x"
            by (rule inv_into_f_f[OF hinj hxX])
          hence "inv_into X f y = x" using hyfx by simp
          thus ?thesis using hxB by simp
        qed
        show "y \<in> {y\<in>Y. inv_into X f y \<in> B}"
          apply (rule CollectI)
          apply (intro conjI)
           apply (rule hyY)
          apply (rule hinv)
          done
      qed
    qed

    show "closedin_on Y TY {y\<in>Y. inv_into X f y \<in> B}"
      using himg_closed preim_eq by simp
  qed

  have inv_cont: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    by (rule iffD2[OF cont_inv_closed], intro conjI, rule inv_maps, rule inv_closed_preimage)

  show ?thesis
    unfolding top1_homeomorphism_on_def
    apply (intro conjI)
        apply (rule hTX)
       apply (rule hTY)
      apply (rule hbij)
     apply (rule hf)
    apply (rule inv_cont)
    done
qed

lemma top1_embedding_on_compact_inj:
  assumes hTX: "is_topology_on X TX"
  assumes hTY: "is_topology_on Y TY"
  assumes hcomp: "top1_compact_on X TX"
  assumes hH: "is_hausdorff_on Y TY"
  assumes hf: "top1_continuous_map_on X TX Y TY f"
  assumes hinj: "inj_on f X"
  shows "top1_embedding_on X TX Y TY f"
proof -
  let ?W = "f ` X"
  let ?TW = "subspace_topology Y TY ?W"

  have hWsub: "?W \<subseteq> Y"
  proof (rule subsetI)
    fix y assume hy: "y \<in> ?W"
    then obtain x where hxX: "x \<in> X" and hyfx: "y = f x"
      by blast
    have hmap: "\<forall>x\<in>X. f x \<in> Y"
      using hf unfolding top1_continuous_map_on_def by blast
    have "f x \<in> Y"
      using hmap hxX by blast
    thus "y \<in> Y"
      using hyfx by simp
  qed

  have hTW_top: "is_topology_on ?W ?TW"
    by (rule subspace_topology_is_topology_on[OF hTY hWsub])

  have hTW_haus: "is_hausdorff_on ?W ?TW"
  proof -
    have hsub_haus:
      "\<forall>X0 T0 Z. is_hausdorff_on X0 T0 \<and> Z \<subseteq> X0 \<longrightarrow> is_hausdorff_on Z (subspace_topology X0 T0 Z)"
      using Theorem_17_11 by blast
	    have hpre: "is_hausdorff_on Y TY \<and> ?W \<subseteq> Y"
	      by (intro conjI, rule hH, rule hWsub)
	    show ?thesis
	      using mp[OF spec[OF spec[OF spec[OF hsub_haus, where x = Y], where x = TY], where x = ?W] hpre] .
	  qed

  have hcontW: "top1_continuous_map_on X TX ?W ?TW f"
  proof -
    have hrestrict_all:
      "\<forall>W g.
        top1_continuous_map_on X TX Y TY g
        \<and> W \<subseteq> Y
        \<and> g ` X \<subseteq> W
        \<longrightarrow> top1_continuous_map_on X TX W (subspace_topology Y TY W) g"
      using Theorem_18_2(5)[OF hTX hTY hTY] .
	    have hpre: "top1_continuous_map_on X TX Y TY f \<and> ?W \<subseteq> Y \<and> f ` X \<subseteq> ?W"
	      by (intro conjI, rule hf, rule hWsub, simp)
	    show ?thesis
	      using mp[OF spec[OF spec[OF hrestrict_all, where x = ?W], where x = f] hpre] .
	  qed

  have hbij: "bij_betw f X ?W"
    unfolding bij_betw_def
    apply (intro conjI)
     apply (rule hinj)
    apply simp
    done

  have hhomeo: "top1_homeomorphism_on X TX ?W ?TW f"
    by (rule Theorem_26_6[OF hTX hTW_top hcomp hTW_haus hcontW hbij])

  show ?thesis
    unfolding top1_embedding_on_def
    by (intro conjI, rule hWsub, rule hhomeo)
qed

section \<open>\<S>27 Compact Subspaces of the Real Line\<close>

text \<open>
  Section \<S>27 of \<open>top1.tex\<close> proves compactness results for subspaces of \<open>\<real>\<close>
  (including Heine--Borel). We record the core statements in the Top1 framework; proofs are
  deferred.
\<close>

text \<open>
  Our notion of compactness is formulated for explicit set-based topologies.  For the standard
  topology on a type in the Isabelle class \<open>topological_space\<close>, compactness is already
  available as \<open>compact\<close>.  The following lemma bridges the two formulations for subspaces of
  \<open>UNIV\<close>.
\<close>

lemma top1_compact_on_subspace_UNIV_iff_compact:
  fixes A :: "'a::topological_space set"
  shows
    "top1_compact_on A (subspace_topology (UNIV::'a set) top1_open_sets A) \<longleftrightarrow> compact A"
proof
  assume hcomp: "top1_compact_on A (subspace_topology (UNIV::'a set) top1_open_sets A)"
  have hCover:
    "\<forall>Uc. Uc \<subseteq> subspace_topology (UNIV::'a set) top1_open_sets A \<and> A \<subseteq> \<Union>Uc
        \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  show "compact A"
  proof (rule compactI)
    fix C :: "'a set set"
    assume hCopen: "\<forall>t\<in>C. open t"
    assume hAcov: "A \<subseteq> \<Union>C"

    define Uc where "Uc = (\<lambda>U. A \<inter> U) ` C"

    have hUc_sub:
      "Uc \<subseteq> subspace_topology (UNIV::'a set) top1_open_sets A"
    proof (rule subsetI)
      fix W
      assume hW: "W \<in> Uc"
      then obtain U where hU: "U \<in> C" and hWeq: "W = A \<inter> U"
        unfolding Uc_def by blast
      have hopenU: "open U"
        using hCopen hU by blast
      have hU_top1: "U \<in> top1_open_sets"
        unfolding top1_open_sets_def using hopenU by blast
      show "W \<in> subspace_topology (UNIV::'a set) top1_open_sets A"
        unfolding subspace_topology_def hWeq
        apply (rule CollectI)
        apply (rule exI[where x=U])
        using hU_top1 by simp
    qed

    have hAcov_Uc: "A \<subseteq> \<Union>Uc"
    proof (rule subsetI)
      fix x
      assume hxA: "x \<in> A"
      have hx: "x \<in> \<Union>C"
        by (rule subsetD[OF hAcov hxA])
      then obtain U where hU: "U \<in> C" and hxU: "x \<in> U"
        by blast
      have hWU: "A \<inter> U \<in> Uc"
        unfolding Uc_def using hU by blast
      have hxWU: "x \<in> A \<inter> U"
        using hxA hxU by blast
      show "x \<in> \<Union>Uc"
        by (rule UnionI[OF hWU hxWU])
    qed

    obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "A \<subseteq> \<Union>F"
      using hCover[rule_format, OF conjI[OF hUc_sub hAcov_Uc]] by blast

    have hrep: "\<forall>W\<in>F. \<exists>U. U \<in> C \<and> W = A \<inter> U"
    proof (intro ballI)
      fix W
      assume hW: "W \<in> F"
      have "W \<in> Uc"
        using hFsub hW by blast
      thus "\<exists>U. U \<in> C \<and> W = A \<inter> U"
        unfolding Uc_def by blast
    qed

    obtain f where hf: "\<forall>W\<in>F. f W \<in> C \<and> W = A \<inter> f W"
      using bchoice[OF hrep] by blast

    define C' where "C' = f ` F"
    have hC'sub: "C' \<subseteq> C"
      unfolding C'_def using hf by blast
    have hC'fin: "finite C'"
      unfolding C'_def using hFfin by simp

    have hAcovC': "A \<subseteq> \<Union>C'"
    proof (rule subsetI)
      fix x
      assume hxA: "x \<in> A"
      have hxUF: "x \<in> \<Union>F"
        by (rule subsetD[OF hFcov hxA])
      then obtain W where hW: "W \<in> F" and hxW: "x \<in> W"
        by blast
      have hWeq: "W = A \<inter> f W"
        using hf hW by blast
      have hx_fW: "x \<in> f W"
        using hxW hWeq by blast
      have hfwC': "f W \<in> C'"
        unfolding C'_def using hW by blast
      show "x \<in> \<Union>C'"
        by (rule UnionI[OF hfwC' hx_fW])
    qed

    show "\<exists>C'. C' \<subseteq> C \<and> finite C' \<and> A \<subseteq> \<Union>C'"
      by (intro exI[where x=C'] conjI hC'sub hC'fin hAcovC')
  qed
next
  assume hcompact: "compact A"
  show "top1_compact_on A (subspace_topology (UNIV::'a set) top1_open_sets A)"
    unfolding top1_compact_on_def
  proof (intro conjI allI impI)
    show "is_topology_on A (subspace_topology (UNIV::'a set) top1_open_sets A)"
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV], simp)

    fix Uc
    assume hUc: "Uc \<subseteq> subspace_topology (UNIV::'a set) top1_open_sets A \<and> A \<subseteq> \<Union>Uc"
    have hUc_sub: "Uc \<subseteq> subspace_topology (UNIV::'a set) top1_open_sets A"
      using hUc by blast
    have hAcov: "A \<subseteq> \<Union>Uc"
      using hUc by blast

    define C where "C = {U. U \<in> top1_open_sets \<and> (A \<inter> U) \<in> Uc}"
    have hCopen: "\<And>U. U \<in> C \<Longrightarrow> open U"
      unfolding C_def top1_open_sets_def by blast

    have hAcovC: "A \<subseteq> \<Union>C"
    proof (rule subsetI)
      fix x
      assume hxA: "x \<in> A"
      have hxUc: "x \<in> \<Union>Uc"
        by (rule subsetD[OF hAcov hxA])
      then obtain W where hW: "W \<in> Uc" and hxW: "x \<in> W"
        by blast
      have hWsub: "W \<in> subspace_topology (UNIV::'a set) top1_open_sets A"
        using hUc_sub hW by blast
      obtain U where hU: "U \<in> top1_open_sets" and hWeq: "W = A \<inter> U"
        using hWsub unfolding subspace_topology_def by blast
      have hUC: "U \<in> C"
        unfolding C_def using hU hW hWeq by blast
      have hxU: "x \<in> U"
        using hxW hWeq by blast
      show "x \<in> \<Union>C"
        by (rule UnionI[OF hUC hxU])
    qed

    obtain C' where hC'sub: "C' \<subseteq> C" and hC'fin: "finite C'" and hAcovC': "A \<subseteq> \<Union>C'"
      by (rule compactE[OF hcompact hAcovC], use hCopen in blast)

    define F where "F = (\<lambda>U. A \<inter> U) ` C'"
    have hFfin: "finite F"
      unfolding F_def using hC'fin by simp

    have hFsub: "F \<subseteq> Uc"
    proof (rule subsetI)
      fix W
      assume hW: "W \<in> F"
      then obtain U where hU: "U \<in> C'" and hWeq: "W = A \<inter> U"
        unfolding F_def by blast
      have hUC: "U \<in> C"
        using hC'sub hU by blast
      show "W \<in> Uc"
      proof -
        have hAU: "A \<inter> U \<in> Uc"
          using hUC unfolding C_def by simp
        show ?thesis
          unfolding hWeq using hAU by simp
      qed
    qed

    have hAcovF: "A \<subseteq> \<Union>F"
    proof (rule subsetI)
      fix x
      assume hxA: "x \<in> A"
      have hx: "x \<in> \<Union>C'"
        by (rule subsetD[OF hAcovC' hxA])
      then obtain U where hU: "U \<in> C'" and hxU: "x \<in> U"
        by blast
      have hWU: "A \<inter> U \<in> F"
        unfolding F_def using hU by blast
      have hxWU: "x \<in> A \<inter> U"
        using hxA hxU by blast
      show "x \<in> \<Union>F"
        by (rule UnionI[OF hWU hxWU])
    qed

    show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
      by (intro exI[where x=F] conjI hFfin hFsub hAcovF)
  qed
qed

(** Closed intervals in linear continua are compact (library notion \<open>compact\<close>). **)
lemma top1_compact_Icc_linear_continuum:
  fixes a b :: "'a::linear_continuum_topology"
  assumes hab: "a \<le> b"
  shows "compact {a..b}"
proof (rule compactI)
  fix C :: "'a set set"
  assume hCopen: "\<forall>t\<in>C. open t"
  assume hcov: "{a..b} \<subseteq> \<Union>C"

  define S where
    "S = {x \<in> {a..b}. \<exists>C'\<subseteq>C. finite C' \<and> {a..x} \<subseteq> \<Union>C'}"

  have ha_in_cover: "a \<in> \<Union>C"
  proof -
    have haI: "a \<in> {a..b}"
      using hab by simp
    show ?thesis
      by (rule subsetD[OF hcov haI])
  qed

  have S_ne: "S \<noteq> {}"
  proof -
    obtain U where hU: "U \<in> C" and haU: "a \<in> U"
      using ha_in_cover by blast
    have hfin: "finite {U}" by simp
    have hsub: "{U} \<subseteq> C"
      using hU by blast
    have hcovU: "{a..a} \<subseteq> \<Union>{U}"
    proof (rule subsetI)
      fix x assume hx: "x \<in> {a..a}"
      have hx_a: "x = a"
        using hx by simp
      have "x \<in> U"
        using haU hx_a by simp
      thus "x \<in> \<Union>{U}"
        using hU by blast
    qed
    have "a \<in> S"
      unfolding S_def
      apply (rule CollectI)
      apply (intro conjI)
       using hab apply simp
      apply (rule exI[where x="{U}"])
      using hfin hsub hcovU by blast
    thus ?thesis
      by blast
  qed

  have haS: "a \<in> S"
  proof -
    obtain U where hU: "U \<in> C" and haU: "a \<in> U"
      using ha_in_cover by blast
    have hfin: "finite {U}" by simp
    have hsub: "{U} \<subseteq> C"
      using hU by blast
    have hcovU: "{a..a} \<subseteq> \<Union>{U}"
    proof (rule subsetI)
      fix x assume hx: "x \<in> {a..a}"
      have hx_a: "x = a"
        using hx by simp
      have "x \<in> U"
        using haU hx_a by simp
      thus "x \<in> \<Union>{U}"
        using hU by blast
    qed
    show ?thesis
      unfolding S_def
      apply (rule CollectI)
      apply (intro conjI)
       using hab apply simp
      apply (rule exI[where x="{U}"])
      using hfin hsub hcovU by blast
  qed

  have S_bdd: "bdd_above S"
  proof (rule bdd_aboveI[where M=b])
    fix x assume hx: "x \<in> S"
    have "x \<in> {a..b}"
      using hx unfolding S_def by blast
    thus "x \<le> b"
      by simp
  qed

  define c where "c = Sup S"
  have hc_le_b: "c \<le> b"
  proof -
    have hub: "\<And>x. x \<in> S \<Longrightarrow> x \<le> b"
    proof -
      fix x assume hx: "x \<in> S"
      have "x \<in> {a..b}"
        using hx unfolding S_def by blast
      thus "x \<le> b"
        by simp
    qed
    show ?thesis
      unfolding c_def
      by (rule cSup_least[OF S_ne], rule hub)
  qed

  have ha_le_c: "a \<le> c"
  proof -
    obtain x where hx: "x \<in> S"
      using S_ne by blast
    have hx_le: "x \<le> c"
      unfolding c_def by (rule cSup_upper[OF hx S_bdd])
    have ha_le_x: "a \<le> x"
    proof -
      have "x \<in> {a..b}"
        using hx unfolding S_def by blast
      thus "a \<le> x"
        by simp
    qed
    show ?thesis
      using ha_le_x hx_le by simp
  qed

  have hcI: "c \<in> {a..b}"
    using ha_le_c hc_le_b by simp

  have hc_in_cover: "c \<in> \<Union>C"
    by (rule subsetD[OF hcov hcI])

  obtain U where hU: "U \<in> C" and hcU: "c \<in> U"
    using hc_in_cover by blast
  have hopenU: "open U"
    using hCopen hU by blast

  have hc_in_S: "c \<in> S"
  proof (cases "c = a")
    case True
    show ?thesis
      using True haS by simp
  next
    case False
    have ha_lt_c: "a < c"
      using False ha_le_c by simp

    have ex_d: "\<exists>d<c. {d <.. c} \<subseteq> U"
      by (rule open_left[OF hopenU hcU ha_lt_c])
	    then obtain d where hd: "d < c" and hdcU: "{d <.. c} \<subseteq> U"
	      by blast
	
	    have hdSup: "d < Sup S"
	    proof -
	      have "c = Sup S"
	        unfolding c_def by simp
	      thus ?thesis
	        using hd by simp
	    qed
    obtain s where hsS: "s \<in> S" and hd_lt_s: "d < s"
      by (rule less_cSupE[OF hdSup S_ne])

    obtain C1 where hC1sub: "C1 \<subseteq> C" and hC1fin: "finite C1" and hC1cov: "{a..s} \<subseteq> \<Union>C1"
      using hsS unfolding S_def by blast

    have hs_le_c: "s \<le> c"
      unfolding c_def by (rule cSup_upper[OF hsS S_bdd])

    have hcov_ac: "{a..c} \<subseteq> \<Union>(insert U C1)"
    proof (rule subsetI)
      fix x assume hx: "x \<in> {a..c}"
      show "x \<in> \<Union>(insert U C1)"
      proof (cases "x \<le> s")
        case True
        have hx_as: "x \<in> {a..s}"
          using hx True by simp
        have "x \<in> \<Union>C1"
          by (rule subsetD[OF hC1cov hx_as])
        thus ?thesis
          by blast
      next
        case False
        have hsx: "s < x"
          using False by simp
        have hx_le_c: "x \<le> c"
          using hx by simp
        have hd_lt_x: "d < x"
          using hd_lt_s hsx by simp
        have "x \<in> {d <.. c}"
          using hd_lt_x hx_le_c by simp
        hence "x \<in> U"
          by (rule subsetD[OF hdcU])
        thus ?thesis
          using hU by blast
      qed
    qed

	    have "c \<in> S"
	      unfolding S_def
	      apply (rule CollectI)
	      apply (intro conjI)
	       using hc_le_b ha_le_c apply simp
	      apply (rule exI[where x="insert U C1"])
	      apply (intro conjI)
	        using hU hC1sub apply blast
	       apply (rule finite.insertI[OF hC1fin])
	      apply (rule hcov_ac)
	      done
    thus ?thesis .
  qed

  have hc_eq_b: "c = b"
  proof (rule classical)
    show "c = b"
    proof (rule ccontr)
      assume hne: "c \<noteq> b"
      have hc_lt_b: "c < b"
        using hc_le_b hne by simp

      have ex_e: "\<exists>e>c. {c ..< e} \<subseteq> U"
        by (rule open_right[OF hopenU hcU hc_lt_b])
	      then obtain e where he: "c < e" and hceU: "{c ..< e} \<subseteq> U"
	        by blast

	      define e' where "e' = min e b"
	      have hc_lt_e': "c < e'"
	        unfolding e'_def
	        using he hc_lt_b
	        by (simp add: min_less_iff_conj)

	      obtain t where hct: "c < t" and ht_lt_e': "t < e'"
	        using dense[OF hc_lt_e'] by blast

	      have he'_le_e: "e' \<le> e"
	        unfolding e'_def by simp
	      have he'_le_b: "e' \<le> b"
	        unfolding e'_def by simp

	      have ht_lt_e: "t < e"
	        by (rule less_le_trans[OF ht_lt_e' he'_le_e])
	      have ht_lt_b: "t < b"
	        by (rule less_le_trans[OF ht_lt_e' he'_le_b])
	      have ht_le_b: "t \<le> b"
	        by (rule less_imp_le[OF ht_lt_b])

      obtain Cc where hCcsub: "Cc \<subseteq> C" and hCcfin: "finite Cc" and hCccov: "{a..c} \<subseteq> \<Union>Cc"
        using hc_in_S unfolding S_def by blast

      have hcov_at: "{a..t} \<subseteq> \<Union>(insert U Cc)"
      proof (rule subsetI)
        fix x assume hx: "x \<in> {a..t}"
        show "x \<in> \<Union>(insert U Cc)"
        proof (cases "x \<le> c")
          case True
          have hx_ac: "x \<in> {a..c}"
            using hx True by simp
          have "x \<in> \<Union>Cc"
            by (rule subsetD[OF hCccov hx_ac])
          thus ?thesis
            by blast
        next
          case False
          have hcx: "c < x"
            using False by simp
          have hx_lt_e: "x < e"
          proof -
            have "x \<le> t"
              using hx by simp
            thus ?thesis
              using ht_lt_e le_less_trans by blast
          qed
          have "x \<in> {c ..< e}"
            using hcx hx_lt_e by simp
          hence "x \<in> U"
            by (rule subsetD[OF hceU])
          thus ?thesis
            using hU by blast
        qed
      qed

	      have ht_in_S: "t \<in> S"
	      proof -
	        have ha_le_t: "a \<le> t"
	          using ha_le_c hct by simp
	        have ht_ab: "t \<in> {a..b}"
	          using ha_le_t ht_le_b by simp
		        have hcover: "\<exists>C'. C' \<subseteq> C \<and> finite C' \<and> {a..t} \<subseteq> \<Union>C'"
		        proof (rule exI[where x="insert U Cc"])
		          have hsub': "insert U Cc \<subseteq> C"
		          proof (rule subsetI)
		            fix x assume hx: "x \<in> insert U Cc"
		            show "x \<in> C"
		            proof (cases "x = U")
		              case True
		              show ?thesis
		                using True hU by simp
		            next
		              case False
		              have hx_in_Cc: "x \<in> Cc"
		                using hx False by simp
		              show ?thesis
		                by (rule subsetD[OF hCcsub hx_in_Cc])
		            qed
		          qed
		          have hfin': "finite (insert U Cc)"
		            by (rule finite.insertI[OF hCcfin])
		          have hcov': "{a..t} \<subseteq> \<Union>(insert U Cc)"
		            by (rule hcov_at)
		          show "insert U Cc \<subseteq> C \<and> finite (insert U Cc) \<and> {a..t} \<subseteq> \<Union>(insert U Cc)"
		            by (intro conjI hsub' hfin' hcov')
		        qed
	        show ?thesis
	          unfolding S_def
	          using ht_ab hcover by blast
	      qed

      have ht_le_c: "t \<le> c"
        unfolding c_def by (rule cSup_upper[OF ht_in_S S_bdd])
      have False
        using hct ht_le_c by simp
      thus False ..
    qed
  qed

	  obtain Cb where hCbsub: "Cb \<subseteq> C" and hCbfin: "finite Cb" and hCbcov: "{a..b} \<subseteq> \<Union>Cb"
	  proof -
	    have hb_in_S: "b \<in> S"
	      using hc_in_S hc_eq_b by simp
	    have hb_ex: "\<exists>C'. C' \<subseteq> C \<and> finite C' \<and> {a..b} \<subseteq> \<Union>C'"
	    proof -
	      have hb_props: "b \<in> {a..b} \<and> (\<exists>C'. C' \<subseteq> C \<and> finite C' \<and> {a..b} \<subseteq> \<Union>C')"
	        using hb_in_S unfolding S_def by (rule CollectD)
	      show ?thesis
	        using hb_props by (rule conjunct2)
	    qed
	    from hb_ex obtain Cb0 where hCb0sub: "Cb0 \<subseteq> C" and hCb0fin: "finite Cb0" and hCb0cov: "{a..b} \<subseteq> \<Union>Cb0"
	      by blast
	    show ?thesis
	      using hCb0sub hCb0fin hCb0cov by (rule that)
	  qed

  show "\<exists>C'. C' \<subseteq> C \<and> finite C' \<and> {a..b} \<subseteq> \<Union>C'"
    by (intro exI[where x=Cb] conjI hCbsub hCbfin hCbcov)
qed

(** from \S27 Theorem 27.1 (Closed intervals in linear continua are compact) [top1.tex:3357] **)
theorem Theorem_27_1:
  fixes a b :: "'a::linear_continuum_topology"
  assumes hab: "a \<le> b"
  shows "top1_compact_on {a..b} (subspace_topology (UNIV::'a set) top1_open_sets {a..b})"
proof -
  have hcompact: "compact {a..b}"
    by (rule top1_compact_Icc_linear_continuum[OF hab])
  show ?thesis
    using top1_compact_on_subspace_UNIV_iff_compact[of "{a..b}"] hcompact
    by simp
qed

(** from \S27 Corollary 27.2 (Closed intervals in \<open>\<real>\<close> are compact) [top1.tex:3391] **)
corollary Corollary_27_2:
  fixes a b :: real
  assumes hab: "a \<le> b"
  shows "top1_compact_on {a..b} (subspace_topology (UNIV::real set) top1_open_sets {a..b})"
  by (rule Theorem_27_1[OF hab])

(** from \S27 Theorem 27.3 (Heine--Borel in \<open>\<real>^n\<close>) [top1.tex:3393] **)
definition top1_bounded_set :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "top1_bounded_set A \<longleftrightarrow> (\<exists>B\<ge>0. \<forall>x\<in>A. norm x \<le> B)"

lemma compact_real_imp_top1_bounded_set:
  fixes A :: "real set"
  assumes hcomp: "compact A"
  shows "top1_bounded_set A"
proof (cases "A = {}")
  case True
  show ?thesis
    unfolding top1_bounded_set_def True
    apply (intro exI[where x=0] conjI)
    apply simp
    apply simp
    done
next
  case False
  show ?thesis
  proof -
  define f :: "nat \<Rightarrow> real set"
    where f_def: "f = (\<lambda>n::nat. {- (of_nat n :: real) <..< (of_nat (Suc n) :: real)})"

  have hAcov: "A \<subseteq> (\<Union>n::nat. f n)"
  proof (rule subsetI)
    fix x assume hxA: "x \<in> A"
    obtain n :: nat where hn: "abs x + 1 < of_nat n"
      using reals_Archimedean2[of "abs x + 1"] by blast
    have hx_lt_n: "abs x < (of_nat n :: real)"
    proof -
      have "abs x < abs x + 1"
        by simp
      thus ?thesis
        using hn less_trans by blast
    qed

    have hx_lb: "- (of_nat n :: real) < x"
      using hx_lt_n by (simp add: abs_less_iff)
    have hx_ub: "x < (of_nat (Suc n) :: real)"
    proof -
      have hx_ub0: "x < (of_nat n :: real)"
        using hx_lt_n by (simp add: abs_less_iff)
      have hn_lt: "(of_nat n :: real) < of_nat (Suc n)"
        by simp
      show ?thesis
        by (rule less_trans[OF hx_ub0 hn_lt])
    qed

    have "x \<in> f n"
      unfolding f_def using hx_lb hx_ub by simp
    thus "x \<in> (\<Union>n::nat. f n)"
      by blast
  qed

  have hAcov': "A \<subseteq> \<Union>(range f)"
    using hAcov by simp

  have hopen: "\<And>B. B \<in> range f \<Longrightarrow> open B"
  proof -
    fix B assume hB: "B \<in> range f"
    then obtain n where hBeq: "B = f n"
      by blast
    show "open B"
      unfolding hBeq f_def by simp
  qed

  obtain D where hDsub: "D \<subseteq> range f" and hDfin: "finite D" and hDcov: "A \<subseteq> \<Union>D"
    by (rule compactE[OF hcomp hAcov' hopen])

  have ex_n: "\<forall>U\<in>D. \<exists>n. U = f n"
    using hDsub by blast
  obtain g where hg: "\<forall>U\<in>D. U = f (g U)"
    using bchoice[OF ex_n] by blast

  define K where "K = g ` D"
  have hKfin: "finite K"
    unfolding K_def by (rule finite_imageI[OF hDfin])

  have hKcov: "A \<subseteq> (\<Union>n\<in>K. f n)"
  proof -
    have hUn: "\<Union>D \<subseteq> (\<Union>n\<in>K. f n)"
    proof (rule subsetI)
      fix x assume hx: "x \<in> \<Union>D"
      then obtain U where hUD: "U \<in> D" and hxU: "x \<in> U"
        by blast
      have hUeq: "U = f (g U)"
        using hg hUD by blast
      have "g U \<in> K"
        unfolding K_def using hUD by blast
      moreover have "x \<in> f (g U)"
        using hxU hUeq by simp
      ultimately show "x \<in> (\<Union>n\<in>K. f n)"
        by (rule UN_I)
    qed
    show ?thesis
      by (rule subset_trans[OF hDcov hUn])
  qed

  have hKne: "K \<noteq> {}"
  proof
    assume hKempty: "K = {}"
    have "A \<subseteq> {}"
      using hKcov unfolding hKempty by simp
    hence "A = {}"
      by blast
    with False show False
      by simp
  qed

  define N where "N = Max K"
  have hle: "\<And>n. n \<in> K \<Longrightarrow> n \<le> N"
    unfolding N_def using hKfin by (rule Max_ge)

  have hf_mono: "\<And>m n::nat. m \<le> n \<Longrightarrow> f m \<subseteq> f n"
  proof -
    fix m n :: nat assume hmn: "m \<le> n"
    show "f m \<subseteq> f n"
    proof (rule subsetI)
      fix x assume hx: "x \<in> f m"
      have hx_lb: "- (of_nat m :: real) < x"
        using hx unfolding f_def by simp
      have hx_ub: "x < (of_nat (Suc m) :: real)"
        using hx unfolding f_def by simp
      have hm_le: "(of_nat m :: real) \<le> of_nat n"
        using hmn by simp
      have hn_lb: "- (of_nat n :: real) \<le> - (of_nat m :: real)"
        using hm_le by simp
      have hx_lb': "- (of_nat n :: real) < x"
        by (rule le_less_trans[OF hn_lb hx_lb])
      have hsuc_le: "of_nat (Suc m) \<le> (of_nat (Suc n) :: real)"
        using hmn by simp
      have hx_ub': "x < (of_nat (Suc n) :: real)"
        by (rule less_le_trans[OF hx_ub hsuc_le])
      show "x \<in> f n"
        unfolding f_def using hx_lb' hx_ub' by simp
    qed
  qed

  have hUn_sub: "(\<Union>n\<in>K. f n) \<subseteq> f N"
  proof (rule subsetI)
    fix x assume hx: "x \<in> (\<Union>n\<in>K. f n)"
    then obtain n where hnK: "n \<in> K" and hxfn: "x \<in> f n"
      by blast
    have hsub: "f n \<subseteq> f N"
      using hf_mono hle[OF hnK] by blast
    show "x \<in> f N"
      by (rule subsetD[OF hsub hxfn])
  qed

  have hAsubN: "A \<subseteq> f N"
    by (rule subset_trans[OF hKcov hUn_sub])

  have hnorm_le: "\<forall>x\<in>A. norm x \<le> (of_nat (Suc N) :: real)"
  proof (rule ballI)
    fix x assume hxA: "x \<in> A"
    have hxN: "x \<in> f N"
      using hAsubN hxA by blast
    have hx_lb: "- (of_nat N :: real) < x"
      using hxN unfolding f_def by simp
    have hx_ub: "x < (of_nat (Suc N) :: real)"
      using hxN unfolding f_def by simp

    have hneg: "- (of_nat (Suc N) :: real) < - (of_nat N :: real)"
      by simp
    have hx_lb': "- (of_nat (Suc N) :: real) < x"
      by (rule less_trans[OF hneg hx_lb])

    have habs_lt: "abs x < (of_nat (Suc N) :: real)"
      using hx_lb' hx_ub by (simp add: abs_less_iff)
    show "norm x \<le> (of_nat (Suc N) :: real)"
      using habs_lt by (simp add: real_norm_def less_imp_le)
  qed

	    show ?thesis
	      unfolding top1_bounded_set_def
	    proof (intro exI[where x="of_nat (Suc N)"] conjI)
	      show "0 \<le> (of_nat (Suc N) :: real)"
	        by simp
	      show "\<forall>x\<in>A. norm x \<le> (of_nat (Suc N) :: real)"
	        using hnorm_le .
		    qed
		  qed
qed

theorem Theorem_27_3:
  fixes A :: "real set"
  shows
    "top1_compact_on A (subspace_topology (UNIV::real set) top1_open_sets A) \<longleftrightarrow> (closed A \<and> top1_bounded_set A)"
proof -
  have hbridge:
    "top1_compact_on A (subspace_topology (UNIV::real set) top1_open_sets A) \<longleftrightarrow> compact A"
    using top1_compact_on_subspace_UNIV_iff_compact[of A] by simp

  have hcompact_iff: "compact A \<longleftrightarrow> (closed A \<and> top1_bounded_set A)"
  proof
    assume hcomp: "compact A"
    have hclosed: "closed A"
      by (rule compact_imp_closed[OF hcomp])
    have hbounded: "top1_bounded_set A"
      by (rule compact_real_imp_top1_bounded_set[OF hcomp])
    show "closed A \<and> top1_bounded_set A"
      using hclosed hbounded by simp
  next
	    assume hprops: "closed A \<and> top1_bounded_set A"
	    have hclosed: "closed A"
	      using hprops by simp
	    obtain B where hB: "B \<ge> 0" and hBnd: "\<forall>x\<in>A. norm x \<le> B"
	      using hprops unfolding top1_bounded_set_def by blast

    have hAsub: "A \<subseteq> {-B..B}"
    proof (rule subsetI)
      fix x assume hxA: "x \<in> A"
      have hn: "norm x \<le> B"
        using hBnd hxA by blast
      have habs: "abs x \<le> B"
        using hn by (simp add: real_norm_def)
      have hbounds: "-B \<le> x \<and> x \<le> B"
        using habs by (simp add: abs_le_iff)
      thus "x \<in> {-B..B}"
        by simp
    qed

    have hIcc_compact: "compact {-B..B}"
      by (rule top1_compact_Icc_linear_continuum) (use hB in simp)

    have "compact ({-B..B} \<inter> A)"
      by (rule compact_Int_closed[OF hIcc_compact hclosed])
    moreover have "{-B..B} \<inter> A = A"
      using hAsub by blast
    ultimately show "compact A"
      by simp
  qed

  show ?thesis
    using hbridge hcompact_iff by simp
qed

(** from \S27 Theorem 27.4 (Extreme value theorem) [top1.tex:3429] **)

(** Continuous images of compact spaces are compact (in the subspace topology). **)
lemma top1_compact_on_continuous_image:
  assumes hcomp: "top1_compact_on X TX"
  assumes hTopY: "is_topology_on Y TY"
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
  shows "top1_compact_on (f ` X) (subspace_topology Y TY (f ` X))"
proof -
  define FX where "FX = f ` X"

  have hTopX: "is_topology_on X TX"
    using hcomp unfolding top1_compact_on_def by blast
  have hCoverX:
    "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  have hFXsub: "FX \<subseteq> Y"
    unfolding FX_def using hcont unfolding top1_continuous_map_on_def by blast
  have hGoal: "top1_compact_on FX (subspace_topology Y TY FX)"
    unfolding top1_compact_on_def
  proof (intro conjI)
    show "is_topology_on FX (subspace_topology Y TY FX)"
      by (rule subspace_topology_is_topology_on[where X=Y and T=TY and Y=FX, OF hTopY hFXsub])

    show "\<forall>Uc. Uc \<subseteq> subspace_topology Y TY FX \<and> FX \<subseteq> \<Union>Uc
          \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> FX \<subseteq> \<Union>F)"
    proof (intro allI impI)
      fix Uc :: "'b set set"
      assume hUc: "Uc \<subseteq> subspace_topology Y TY FX \<and> FX \<subseteq> \<Union>Uc"
      have hUc_sub: "Uc \<subseteq> subspace_topology Y TY FX"
        using hUc by blast
      have hUc_cov: "FX \<subseteq> \<Union>Uc"
        using hUc by blast

      define Pc where
        "Pc = {{x\<in>X. f x \<in> V} | V. V \<in> TY \<and> (FX \<inter> V) \<in> Uc}"

      have hPc_sub: "Pc \<subseteq> TX"
      proof (rule subsetI)
        fix A
        assume hA: "A \<in> Pc"
        obtain V where hV: "V \<in> TY" and hUin: "(FX \<inter> V) \<in> Uc" and hAeq: "A = {x\<in>X. f x \<in> V}"
          using hA unfolding Pc_def by blast
        have "A \<in> TX"
          using hcont hV unfolding top1_continuous_map_on_def hAeq by blast
        thus "A \<in> TX" .
      qed

      have hPc_cov: "X \<subseteq> \<Union>Pc"
      proof (rule subsetI)
        fix x
        assume hxX: "x \<in> X"
        have hfxFX: "f x \<in> FX"
          unfolding FX_def by (rule imageI[OF hxX])
        have hfxU: "f x \<in> \<Union>Uc"
          by (rule subsetD[OF hUc_cov hfxFX])
        then obtain U where hU: "U \<in> Uc" and hfxU': "f x \<in> U"
          by blast

        have hUsub: "U \<in> subspace_topology Y TY FX"
          using hUc_sub hU by blast
        obtain V where hV: "V \<in> TY" and hUeq: "U = FX \<inter> V"
          using hUsub unfolding subspace_topology_def by blast

        have hfxV: "f x \<in> V"
          using hfxU' unfolding hUeq using hfxFX by blast
        have hxPre: "x \<in> {x\<in>X. f x \<in> V}"
          using hxX hfxV by blast
        have hPre_in: "{x\<in>X. f x \<in> V} \<in> Pc"
          unfolding Pc_def using hV hUeq hU by blast
        show "x \<in> \<Union>Pc"
          by (rule UnionI[OF hPre_in hxPre])
      qed

      obtain Fp where hFpfin: "finite Fp" and hFpsub: "Fp \<subseteq> Pc" and hFpcov: "X \<subseteq> \<Union>Fp"
        using hCoverX[rule_format, OF conjI[OF hPc_sub hPc_cov]] by blast

      have hrepr:
        "\<forall>A\<in>Fp. \<exists>V. V \<in> TY \<and> (FX \<inter> V) \<in> Uc \<and> A = {x\<in>X. f x \<in> V}"
      proof (intro ballI)
        fix A
        assume hAFp: "A \<in> Fp"
        have hA: "A \<in> Pc"
          using hFpsub hAFp by blast
        show "\<exists>V. V \<in> TY \<and> (FX \<inter> V) \<in> Uc \<and> A = {x\<in>X. f x \<in> V}"
          using hA unfolding Pc_def by blast
      qed

      obtain pick where hpick:
        "\<forall>A\<in>Fp. pick A \<in> TY \<and> (FX \<inter> pick A) \<in> Uc \<and> A = {x\<in>X. f x \<in> pick A}"
        using bchoice[OF hrepr] by blast

      define F where "F = (\<lambda>A. FX \<inter> pick A) ` Fp"
      have hFfin: "finite F"
        unfolding F_def by (rule finite_imageI[OF hFpfin])
      have hFsub: "F \<subseteq> Uc"
        unfolding F_def using hpick by blast

      have hFcov: "FX \<subseteq> \<Union>F"
      proof (rule subsetI)
        fix y
        assume hyFX: "y \<in> FX"
        obtain x where hxX: "x \<in> X" and hyEq: "y = f x"
          using hyFX unfolding FX_def by blast
        have hxUFp: "x \<in> \<Union>Fp"
          by (rule subsetD[OF hFpcov hxX])
        then obtain A where hAFp: "A \<in> Fp" and hxA: "x \<in> A"
          by blast
        have hAeq: "A = {x\<in>X. f x \<in> pick A}"
          using hpick hAFp by blast
        have hfx: "f x \<in> pick A"
        proof -
          have hsub: "A \<subseteq> {x\<in>X. f x \<in> pick A}"
            using hAeq by (rule equalityD1)
          have hx_mem: "x \<in> {x\<in>X. f x \<in> pick A}"
            by (rule subsetD[OF hsub hxA])
          show ?thesis
            using hx_mem by simp
        qed
        have hFXA: "f x \<in> FX"
          unfolding FX_def by (rule imageI[OF hxX])
        have "f x \<in> FX \<inter> pick A"
          using hFXA hfx by blast
        moreover have "FX \<inter> pick A \<in> F"
          unfolding F_def using hAFp by blast
        ultimately have "f x \<in> \<Union>F"
          by blast
        thus "y \<in> \<Union>F"
          unfolding hyEq by simp
      qed

      show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> FX \<subseteq> \<Union>F"
        apply (rule exI[where x=F])
        apply (rule conjI)
         apply (rule hFfin)
        apply (rule conjI)
         apply (rule hFsub)
        apply (rule hFcov)
        done
    qed
  qed

  have hGoal': "top1_compact_on (f ` X) (subspace_topology Y TY (f ` X))"
    using hGoal
    by (simp add: FX_def)
  show ?thesis
    by (rule hGoal')
qed

(** A nonempty compact subset of a linearly ordered set has a least element. **)
lemma top1_compact_on_order_topology_has_least:
  fixes A :: "'b::linorder set"
  assumes hAne: "A \<noteq> {}"
  assumes hcomp: "top1_compact_on A (subspace_topology (UNIV::'b set) (order_topology_on_UNIV::'b set set) A)"
  shows "\<exists>m\<in>A. \<forall>x\<in>A. m \<le> x"
proof -
  let ?TA = "subspace_topology (UNIV::'b set) (order_topology_on_UNIV::'b set set) A"

  have hCover:
    "\<forall>Uc. Uc \<subseteq> ?TA \<and> A \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  show ?thesis
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>m\<in>A. \<forall>x\<in>A. m \<le> x)"

    have hdown: "\<forall>x\<in>A. \<exists>a\<in>A. a < x"
    proof (intro ballI)
      fix x assume hxA: "x \<in> A"
      show "\<exists>a\<in>A. a < x"
      proof (rule ccontr)
        assume hcontra: "\<not> (\<exists>a\<in>A. a < x)"
        have hxleast: "\<forall>y\<in>A. x \<le> y"
        proof (intro ballI)
          fix y assume hyA: "y \<in> A"
          have "\<not> (y < x)"
            using hcontra hyA by blast
          thus "x \<le> y"
            by simp
        qed
        have "\<exists>m\<in>A. \<forall>z\<in>A. m \<le> z"
        proof -
          have "\<forall>z\<in>A. x \<le> z"
            by (rule hxleast)
          thus ?thesis
            by (rule bexI[where x=x]) (rule hxA)
        qed
        thus False
          using hno by blast
      qed
    qed

    define Uc where "Uc = {A \<inter> open_ray_gt a | a. a \<in> A}"

    have hUc_sub: "Uc \<subseteq> ?TA"
    proof (rule subsetI)
      fix U assume hU: "U \<in> Uc"
      obtain a where haA: "a \<in> A" and hUeq: "U = A \<inter> open_ray_gt a"
        using hU unfolding Uc_def by blast
      have hopen: "open_ray_gt a \<in> (order_topology_on_UNIV::'b set set)"
        by (rule open_ray_gt_in_order_topology)
      show "U \<in> ?TA"
        unfolding subspace_topology_def
        using hopen hUeq by blast
    qed

    have hUc_cov: "A \<subseteq> \<Union>Uc"
    proof (rule subsetI)
      fix x assume hxA: "x \<in> A"
      obtain a where haA: "a \<in> A" and hlt: "a < x"
        using hdown hxA by blast
      have hxray: "x \<in> open_ray_gt a"
        unfolding open_ray_gt_def using hlt by simp
      have hxU: "x \<in> A \<inter> open_ray_gt a"
        using hxA hxray by blast
      have hUin: "A \<inter> open_ray_gt a \<in> Uc"
        unfolding Uc_def using haA by blast
      show "x \<in> \<Union>Uc"
        by (rule UnionI[OF hUin hxU])
    qed

    obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "A \<subseteq> \<Union>F"
      using hCover[rule_format, of Uc] hUc_sub hUc_cov by blast

    obtain x0 where hx0A: "x0 \<in> A"
      using hAne by blast
    have hFne: "F \<noteq> {}"
    proof
      assume hFemp: "F = {}"
      have "A \<subseteq> \<Union>F"
        by (rule hFcov)
      thus False
        using hx0A hFemp by simp
    qed

    have hrepr: "\<forall>U\<in>F. \<exists>a. a \<in> A \<and> U = A \<inter> open_ray_gt a"
    proof (intro ballI)
      fix U assume hUF: "U \<in> F"
      have hU: "U \<in> Uc"
        using hFsub hUF by blast
      show "\<exists>a. a \<in> A \<and> U = A \<inter> open_ray_gt a"
        using hU unfolding Uc_def by blast
    qed

    obtain pick where hpick: "\<forall>U\<in>F. pick U \<in> A \<and> U = A \<inter> open_ray_gt (pick U)"
      using bchoice[OF hrepr] by blast

    define P where "P = pick ` F"
    have hPfin: "finite P"
      unfolding P_def by (rule finite_imageI[OF hFfin])
    have hPne: "P \<noteq> {}"
      unfolding P_def using hFne by simp

    let ?m = "Min P"
    have hmP: "?m \<in> P"
      by (rule Min_in[OF hPfin hPne])
    have hmle: "\<forall>a\<in>P. ?m \<le> a"
    proof (intro ballI)
      fix a
      assume haP: "a \<in> P"
      show "?m \<le> a"
        by (rule Min_le[OF hPfin haP])
    qed

    have hmA: "?m \<in> A"
    proof -
      obtain U where hUF: "U \<in> F" and hmEq: "?m = pick U"
        using hmP unfolding P_def by blast
      have "pick U \<in> A"
        using hpick hUF by blast
      thus ?thesis
        unfolding hmEq .
    qed

    have hm_notcov: "?m \<notin> \<Union>F"
    proof
      assume hmU: "?m \<in> \<Union>F"
      then obtain U where hUF: "U \<in> F" and hmUin: "?m \<in> U"
        by blast
      have hUeq: "U = A \<inter> open_ray_gt (pick U)"
        using hpick hUF by blast
      have hpU: "pick U \<in> P"
        unfolding P_def using hUF by blast
      have hmin_le: "?m \<le> pick U"
        using hmle hpU by blast
      have "\<not> (pick U < ?m)"
        using hmin_le by simp
      hence "?m \<notin> open_ray_gt (pick U)"
        unfolding open_ray_gt_def by simp
      hence "?m \<notin> U"
      proof -
        have hNotInt: "?m \<notin> A \<inter> open_ray_gt (pick U)"
        proof
          assume hmInt: "?m \<in> A \<inter> open_ray_gt (pick U)"
          have hmRay: "?m \<in> open_ray_gt (pick U)"
            by (rule IntD2[OF hmInt])
          show False
            using \<open>?m \<notin> open_ray_gt (pick U)\<close> hmRay by contradiction
        qed
        have hsubU: "U \<subseteq> A \<inter> open_ray_gt (pick U)"
          using hUeq by (rule equalityD1)
        show ?thesis
        proof
          assume hmU: "?m \<in> U"
          have "?m \<in> A \<inter> open_ray_gt (pick U)"
            by (rule subsetD[OF hsubU hmU])
          thus False
            using hNotInt by contradiction
        qed
      qed
      thus False
        using hmUin by blast
    qed

    have "?m \<in> \<Union>F"
      by (rule subsetD[OF hFcov hmA])
    thus False
      using hm_notcov by blast
  qed
qed

(** A nonempty compact subset of a linearly ordered set has a greatest element. **)
lemma top1_compact_on_order_topology_has_greatest:
  fixes A :: "'b::linorder set"
  assumes hAne: "A \<noteq> {}"
  assumes hcomp: "top1_compact_on A (subspace_topology (UNIV::'b set) (order_topology_on_UNIV::'b set set) A)"
  shows "\<exists>M\<in>A. \<forall>x\<in>A. x \<le> M"
proof -
  let ?TA = "subspace_topology (UNIV::'b set) (order_topology_on_UNIV::'b set set) A"

  have hCover:
    "\<forall>Uc. Uc \<subseteq> ?TA \<and> A \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  show ?thesis
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>M\<in>A. \<forall>x\<in>A. x \<le> M)"

    have hup: "\<forall>x\<in>A. \<exists>a\<in>A. x < a"
    proof (intro ballI)
      fix x assume hxA: "x \<in> A"
      show "\<exists>a\<in>A. x < a"
      proof (rule ccontr)
        assume hcontra: "\<not> (\<exists>a\<in>A. x < a)"
        have hxgreat: "\<forall>y\<in>A. y \<le> x"
        proof (intro ballI)
          fix y assume hyA: "y \<in> A"
          have "\<not> (x < y)"
            using hcontra hyA by blast
          thus "y \<le> x"
            by simp
        qed
        have "\<exists>M\<in>A. \<forall>z\<in>A. z \<le> M"
        proof -
          have "\<forall>z\<in>A. z \<le> x"
            by (rule hxgreat)
          thus ?thesis
            by (rule bexI[where x=x]) (rule hxA)
        qed
        thus False
          using hno by blast
      qed
    qed

    define Uc where "Uc = {A \<inter> open_ray_lt a | a. a \<in> A}"

    have hUc_sub: "Uc \<subseteq> ?TA"
    proof (rule subsetI)
      fix U assume hU: "U \<in> Uc"
      obtain a where haA: "a \<in> A" and hUeq: "U = A \<inter> open_ray_lt a"
        using hU unfolding Uc_def by blast
      have hopen: "open_ray_lt a \<in> (order_topology_on_UNIV::'b set set)"
        by (rule open_ray_lt_in_order_topology)
      show "U \<in> ?TA"
        unfolding subspace_topology_def
        using hopen hUeq by blast
    qed

    have hUc_cov: "A \<subseteq> \<Union>Uc"
    proof (rule subsetI)
      fix x assume hxA: "x \<in> A"
      obtain a where haA: "a \<in> A" and hlt: "x < a"
        using hup hxA by blast
      have hxray: "x \<in> open_ray_lt a"
        unfolding open_ray_lt_def using hlt by simp
      have hxU: "x \<in> A \<inter> open_ray_lt a"
        using hxA hxray by blast
      have hUin: "A \<inter> open_ray_lt a \<in> Uc"
        unfolding Uc_def using haA by blast
      show "x \<in> \<Union>Uc"
        by (rule UnionI[OF hUin hxU])
    qed

    obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "A \<subseteq> \<Union>F"
      using hCover[rule_format, of Uc] hUc_sub hUc_cov by blast

    obtain x0 where hx0A: "x0 \<in> A"
      using hAne by blast
    have hFne: "F \<noteq> {}"
    proof
      assume hFemp: "F = {}"
      have "A \<subseteq> \<Union>F"
        by (rule hFcov)
      thus False
        using hx0A hFemp by simp
    qed

    have hrepr: "\<forall>U\<in>F. \<exists>a. a \<in> A \<and> U = A \<inter> open_ray_lt a"
    proof (intro ballI)
      fix U assume hUF: "U \<in> F"
      have hU: "U \<in> Uc"
        using hFsub hUF by blast
      show "\<exists>a. a \<in> A \<and> U = A \<inter> open_ray_lt a"
        using hU unfolding Uc_def by blast
    qed

    obtain pick where hpick: "\<forall>U\<in>F. pick U \<in> A \<and> U = A \<inter> open_ray_lt (pick U)"
      using bchoice[OF hrepr] by blast

    define P where "P = pick ` F"
    have hPfin: "finite P"
      unfolding P_def by (rule finite_imageI[OF hFfin])
    have hPne: "P \<noteq> {}"
      unfolding P_def using hFne by simp

    let ?M = "Max P"
    have hMP: "?M \<in> P"
      by (rule Max_in[OF hPfin hPne])
    have hleM: "\<forall>a\<in>P. a \<le> ?M"
    proof (intro ballI)
      fix a
      assume haP: "a \<in> P"
      show "a \<le> ?M"
        by (rule Max_ge[OF hPfin haP])
    qed

    have hMA: "?M \<in> A"
    proof -
      obtain U where hUF: "U \<in> F" and hMEq: "?M = pick U"
        using hMP unfolding P_def by blast
      have "pick U \<in> A"
        using hpick hUF by blast
      thus ?thesis
        unfolding hMEq .
    qed

    have hM_notcov: "?M \<notin> \<Union>F"
    proof
      assume hMU: "?M \<in> \<Union>F"
      then obtain U where hUF: "U \<in> F" and hMUin: "?M \<in> U"
        by blast
      have hUeq: "U = A \<inter> open_ray_lt (pick U)"
        using hpick hUF by blast
      have hpU: "pick U \<in> P"
        unfolding P_def using hUF by blast
      have hle: "pick U \<le> ?M"
        using hleM hpU by blast
      have "\<not> (?M < pick U)"
        using hle by simp
      hence "?M \<notin> open_ray_lt (pick U)"
        unfolding open_ray_lt_def by simp
      hence "?M \<notin> U"
      proof -
        have hNotInt: "?M \<notin> A \<inter> open_ray_lt (pick U)"
        proof
          assume hMInt: "?M \<in> A \<inter> open_ray_lt (pick U)"
          have hMRay: "?M \<in> open_ray_lt (pick U)"
            by (rule IntD2[OF hMInt])
          show False
            using \<open>?M \<notin> open_ray_lt (pick U)\<close> hMRay by contradiction
        qed
        have hsubU: "U \<subseteq> A \<inter> open_ray_lt (pick U)"
          using hUeq by (rule equalityD1)
        show ?thesis
        proof
          assume hMU: "?M \<in> U"
          have "?M \<in> A \<inter> open_ray_lt (pick U)"
            by (rule subsetD[OF hsubU hMU])
          thus False
            using hNotInt by contradiction
        qed
      qed
      thus False
        using hMUin by blast
    qed

    have "?M \<in> \<Union>F"
      by (rule subsetD[OF hFcov hMA])
    thus False
      using hM_notcov by blast
  qed
qed

theorem Theorem_27_4:
  fixes f :: "'a \<Rightarrow> 'b::linorder"
  assumes hXne: "X \<noteq> {}"
  assumes hcomp: "top1_compact_on X TX"
  assumes hcont: "top1_continuous_map_on X TX (UNIV::'b set) (order_topology_on_UNIV::'b set set) f"
  shows "\<exists>c\<in>X. \<exists>d\<in>X. \<forall>x\<in>X. f c \<le> f x \<and> f x \<le> f d"
proof -
  have himage_comp:
    "top1_compact_on (f ` X)
       (subspace_topology (UNIV::'b set) (order_topology_on_UNIV::'b set set) (f ` X))"
    by (rule top1_compact_on_continuous_image[OF hcomp order_topology_on_UNIV_is_topology_on hcont])

  have hfx_ne: "f ` X \<noteq> {}"
  proof -
    obtain x0 where hx0X: "x0 \<in> X"
      using hXne by blast
    have "f x0 \<in> f ` X"
      by (rule imageI[OF hx0X])
    thus ?thesis
      by blast
  qed

  obtain m where hmFX: "m \<in> f ` X" and hmin: "\<forall>y\<in>f ` X. m \<le> y"
    using top1_compact_on_order_topology_has_least[OF hfx_ne himage_comp] by blast
  obtain M where hMFX: "M \<in> f ` X" and hmax: "\<forall>y\<in>f ` X. y \<le> M"
    using top1_compact_on_order_topology_has_greatest[OF hfx_ne himage_comp] by blast

  obtain c where hcX: "c \<in> X" and hfc: "f c = m"
    using hmFX by blast
  obtain d where hdX: "d \<in> X" and hfd: "f d = M"
    using hMFX by blast

  show ?thesis
  proof (rule bexI[where x=c])
    show "c \<in> X"
      by (rule hcX)
    show "\<exists>d\<in>X. \<forall>x\<in>X. f c \<le> f x \<and> f x \<le> f d"
    proof (rule bexI[where x=d])
      show "d \<in> X"
        by (rule hdX)
      show "\<forall>x\<in>X. f c \<le> f x \<and> f x \<le> f d"
      proof (intro ballI)
        fix x assume hxX: "x \<in> X"
        have hfxFX: "f x \<in> f ` X"
          by (rule imageI[OF hxX])
        have hm_le: "m \<le> f x"
          using hmin hfxFX by blast
        have hle_M: "f x \<le> M"
          using hmax hfxFX by blast
        show "f c \<le> f x \<and> f x \<le> f d"
          unfolding hfc hfd using hm_le hle_M by simp
      qed
    qed
  qed
qed

(** Diameter of a set in a given "distance" function (used in Lemma 27.5). **)
definition top1_diameter_on :: "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> real" where
  "top1_diameter_on d A = Sup {d x y | x y. x \<in> A \<and> y \<in> A}"

(** Diameter bound for a 2-point subset of a metric space. **)
lemma top1_diameter_on_pair_le:
  assumes hd: "top1_metric_on X d"
  assumes hx: "x \<in> X"
  assumes hy: "y \<in> X"
  shows "top1_diameter_on d {x, y} \<le> d x y"
proof -
  have hxy0: "0 \<le> d x y"
    using hd hx hy unfolding top1_metric_on_def by blast
  have hsym: "d y x = d x y"
    using hd hx hy unfolding top1_metric_on_def by blast
  have hxx: "d x x = 0"
    using hd hx unfolding top1_metric_on_def by blast
  have hyy: "d y y = 0"
    using hd hy unfolding top1_metric_on_def by blast

  define D where "D = {d u v | u v. u \<in> {x, y} \<and> v \<in> {x, y}}"

  have hDle: "\<forall>r\<in>D. r \<le> d x y"
  proof (intro ballI)
    fix r
    assume hr: "r \<in> D"
    obtain u v where hu: "u \<in> {x, y}" and hv: "v \<in> {x, y}" and hr': "r = d u v"
      using hr unfolding D_def by blast
    from hu have hu': "u = x \<or> u = y"
      by simp
    from hv have hv': "v = x \<or> v = y"
      by simp
    show "r \<le> d x y"
      using hu' hv'
    proof (elim disjE)
      assume "u = x" and "v = x"
      show ?thesis
        unfolding hr' \<open>u = x\<close> \<open>v = x\<close> hxx using hxy0 by simp
    next
      assume "u = x" and "v = y"
      show ?thesis
        unfolding hr' \<open>u = x\<close> \<open>v = y\<close> by simp
    next
      assume "u = y" and "v = x"
      show ?thesis
        unfolding hr' \<open>u = y\<close> \<open>v = x\<close> hsym by simp
    next
      assume "u = y" and "v = y"
      show ?thesis
        unfolding hr' \<open>u = y\<close> \<open>v = y\<close> hyy using hxy0 by simp
    qed
  qed

  have hDne: "D \<noteq> {}"
  proof -
    have "d x x \<in> D"
      unfolding D_def by blast
    thus ?thesis
      by blast
  qed
  have hDbd: "bdd_above D"
    unfolding bdd_above_def
  proof (rule exI[where x="d x y"], intro ballI)
    fix r
    assume "r \<in> D"
    thus "r \<le> d x y"
      using hDle by blast
  qed

  have "Sup D \<le> d x y"
    using hDne hDbd
    apply (subst cSup_le_iff)
      apply (rule hDne)
     apply (rule hDbd)
    apply (rule hDle)
    done
  thus ?thesis
    unfolding top1_diameter_on_def D_def by simp
qed

(** Boundedness of a compact metric space (carrier-restricted). **)
lemma top1_metric_compact_bounded_from_point:
  assumes hd: "top1_metric_on X d"
  assumes hcomp: "top1_compact_on X (top1_metric_topology_on X d)"
  assumes hx0X: "x0 \<in> X"
  shows "\<exists>R>0. \<forall>x\<in>X. d x0 x \<le> R"
proof -
  define Balls where "Balls n = top1_ball_on X d x0 (real (Suc n))" for n
  define Uc0 where "Uc0 = range Balls"

  have hUc0sub: "Uc0 \<subseteq> top1_metric_topology_on X d"
  proof (rule subsetI)
    fix U
    assume hU: "U \<in> Uc0"
    obtain n where hUeq: "U = Balls n"
      using hU unfolding Uc0_def by blast
    have hrad: "0 < (real (Suc n) :: real)"
      by simp
    have "top1_ball_on X d x0 (real (Suc n)) \<in> top1_metric_topology_on X d"
      by (rule top1_ball_open_in_metric_topology[OF hd hx0X hrad])
    thus "U \<in> top1_metric_topology_on X d"
      unfolding hUeq Balls_def by simp
  qed

  have hcov0: "X \<subseteq> \<Union>Uc0"
  proof (rule subsetI)
    fix x
    assume hxX: "x \<in> X"
    obtain n where hn: "d x0 x < real n"
      using reals_Archimedean2[of "d x0 x"] by blast
    have hn': "d x0 x < real (Suc n)"
      by (rule less_le_trans[OF hn]) simp
    have hxball: "x \<in> Balls n"
      unfolding Balls_def top1_ball_on_def using hxX hn' by simp
    have "Balls n \<in> Uc0"
      unfolding Uc0_def by blast
    thus "x \<in> \<Union>Uc0"
      using hxball by blast
  qed

  have hcompact_cover:
    "\<forall>V. V \<subseteq> top1_metric_topology_on X d \<and> X \<subseteq> \<Union>V \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> V \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc0" and hFcov: "X \<subseteq> \<Union>F"
    using hcompact_cover[rule_format, of Uc0] hUc0sub hcov0 by blast

  have hFne: "F \<noteq> {}"
  proof -
    have hx0UnionF: "x0 \<in> \<Union>F"
      by (rule subsetD[OF hFcov hx0X])
    then obtain U where "U \<in> F"
      by blast
    thus ?thesis
      by blast
  qed

  have hexIdx: "\<forall>U\<in>F. \<exists>n. U = Balls n"
    using hFsub unfolding Uc0_def by blast
  obtain idx where hidx: "\<forall>U\<in>F. U = Balls (idx U)"
    using bchoice[OF hexIdx] by blast

  define N where "N = idx ` F"
  have hNfin: "finite N"
    unfolding N_def using hFfin by simp
  have hNne: "N \<noteq> {}"
    unfolding N_def using hFne by simp

  define nmax where "nmax = Max N"

  have hR: "\<forall>x\<in>X. d x0 x \<le> real (Suc nmax)"
  proof (intro ballI)
    fix x
    assume hxX: "x \<in> X"
    have hxUF: "x \<in> \<Union>F"
      using hFcov hxX by blast
    then obtain U where hUF: "U \<in> F" and hxU: "x \<in> U"
      by blast

    have hUeq: "U = Balls (idx U)"
      using hidx hUF by blast
    have hxball: "x \<in> Balls (idx U)"
      using hxU by (simp only: hUeq[symmetric])
    have hxball': "x \<in> top1_ball_on X d x0 (real (Suc (idx U)))"
      using hxball unfolding Balls_def by simp
    have hxlt: "d x0 x < real (Suc (idx U))"
      using hxball' unfolding top1_ball_on_def by simp

    have hidxU_in: "idx U \<in> N"
      unfolding N_def using hUF by blast
    have hidxU_le: "idx U \<le> nmax"
      unfolding nmax_def using hNfin hidxU_in by simp
    have hle_rad: "real (Suc (idx U)) \<le> real (Suc nmax)"
      using hidxU_le by simp

    have "d x0 x < real (Suc nmax)"
      by (rule less_le_trans[OF hxlt hle_rad])
    thus "d x0 x \<le> real (Suc nmax)"
      by simp
  qed

  show ?thesis
  proof (rule exI[where x="real (Suc nmax)"], intro conjI)
    show "0 < real (Suc nmax)"
      by simp
    show "\<forall>x\<in>X. d x0 x \<le> real (Suc nmax)"
      using hR .
  qed
qed

lemma top1_metric_compact_bounded:
  assumes hd: "top1_metric_on X d"
  assumes hcomp: "top1_compact_on X (top1_metric_topology_on X d)"
  shows "\<exists>M. \<forall>x\<in>X. \<forall>y\<in>X. d x y \<le> M"
proof (cases "X = {}")
  case True
  show ?thesis
    by (rule exI[where x="0::real"]) (simp add: True)
next
  case False
  obtain x0 where hx0X: "x0 \<in> X"
    using False by blast
  obtain R0 where hR0pos: "0 < R0" and hR0: "\<forall>x\<in>X. d x0 x \<le> R0"
    using top1_metric_compact_bounded_from_point[OF hd hcomp hx0X] by blast

  have hsym: "\<forall>x\<in>X. d x x0 = d x0 x"
    using hd hx0X unfolding top1_metric_on_def by blast
  have htri: "\<forall>x\<in>X. \<forall>y\<in>X. d x y \<le> d x x0 + d x0 y"
    using hd hx0X unfolding top1_metric_on_def by blast

  show ?thesis
  proof (rule exI[where x="2 * R0"])
    show "\<forall>x\<in>X. \<forall>y\<in>X. d x y \<le> 2 * R0"
    proof (intro ballI ballI)
      fix x y
      assume hxX: "x \<in> X"
      assume hyX: "y \<in> X"

      have hxy: "d x y \<le> d x x0 + d x0 y"
        using htri hxX hyX by blast
      have hxx0: "d x x0 = d x0 x"
        using hsym hxX by blast

      have "d x y \<le> d x0 x + d x0 y"
        using hxy hxx0 by simp
      also have "\<dots> \<le> R0 + R0"
      proof -
        have hx0x: "d x0 x \<le> R0"
          using hR0 hxX by blast
        have hx0y: "d x0 y \<le> R0"
          using hR0 hyX by blast
        show "d x0 x + d x0 y \<le> R0 + R0"
          by (rule add_mono[OF hx0x hx0y])
      qed
      also have "\<dots> = 2 * R0"
        by simp
      finally show "d x y \<le> 2 * R0" .
    qed
  qed
qed

(** from \S27 Lemma 27.5 (Lebesgue number lemma) [top1.tex:3484] **)
lemma Lemma_27_5:
  assumes hd: "top1_metric_on X d"
  assumes hcomp: "top1_compact_on X (top1_metric_topology_on X d)"
  assumes hUc: "Uc \<subseteq> top1_metric_topology_on X d"
  assumes hcov: "X \<subseteq> \<Union>Uc"
  shows "\<exists>\<delta>>0. \<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<and> top1_diameter_on d A < \<delta> \<longrightarrow> (\<exists>U\<in>Uc. A \<subseteq> U)"
text \<open>
  Proof status: admitted for now to keep the session build within the default 120s timeout.

  Intended proof plan (from top1.tex): use compactness to extract a finite subcover from a suitable open cover by
  metric balls, obtain a uniform radius bound, then derive a Lebesgue number \<delta> that works for all subsets of
  diameter \<delta>.

  The commented proof below is a first draft; it should be refactored into smaller helper lemmas (with local simp
  sets) to avoid tactic blow-ups.
\<close>
proof (cases "X = {}")
  case True
  show ?thesis
  proof (rule exI[where x="1::real"], intro conjI)
    show "(0::real) < 1"
      by simp
    show "\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<and> top1_diameter_on d A < 1 \<longrightarrow> (\<exists>U\<in>Uc. A \<subseteq> U)"
      using True by blast
  qed
next
  case False
  have hXne: "X \<noteq> {}"
    using False .

  obtain x0 where hx0X: "x0 \<in> X"
    using hXne by blast

  obtain M where hM: "\<forall>x\<in>X. \<forall>y\<in>X. d x y \<le> M"
    using top1_metric_compact_bounded[OF hd hcomp] by blast

  have hexLocal:
    "\<forall>x\<in>X. \<exists>p. 0 < fst p \<and> snd p \<in> Uc \<and> top1_ball_on X d x (fst p) \<subseteq> snd p"
  proof (intro ballI)
    fix x
    assume hxX: "x \<in> X"
    have hxUnion: "x \<in> \<Union>Uc"
      using hcov hxX by blast
    obtain U where hUUc: "U \<in> Uc" and hxU: "x \<in> U"
      using hxUnion by blast
    have hUopen: "U \<in> top1_metric_topology_on X d"
      using hUc hUUc by blast

    have hBasisFor:
      "basis_for X (top1_metric_basis_on X d) (top1_metric_topology_on X d)"
      unfolding basis_for_def top1_metric_topology_on_def
      by (intro conjI top1_metric_basis_is_basis_on[OF hd] refl)

    obtain b where hbbasis: "b \<in> top1_metric_basis_on X d"
      and hxb: "x \<in> b" and hbsub: "b \<subseteq> U"
      using basis_for_refine[OF hBasisFor hUopen hxU] by blast

    obtain c e where hb: "b = top1_ball_on X d c e" and hcX: "c \<in> X" and he: "0 < e"
      using hbbasis unfolding top1_metric_basis_on_def by blast

    have hdx: "d c x < e"
      using hxb unfolding hb top1_ball_on_def using hxX by simp

    define r where "r = (e - d c x) / 2"
    have hrpos: "0 < r"
    proof -
      have hpos: "0 < e - d c x"
        using hdx by linarith
      show ?thesis
        unfolding r_def using hpos by simp
    qed

    have hball_sub_b: "top1_ball_on X d x r \<subseteq> b"
    proof (rule subsetI)
      fix y
      assume hy: "y \<in> top1_ball_on X d x r"
      have hyX: "y \<in> X" and hxy: "d x y < r"
        using hy unfolding top1_ball_on_def by blast+

      have hcx': "d c y \<le> d c x + d x y"
        using hd hcX hxX hyX unfolding top1_metric_on_def by blast
      have "d c x + d x y < d c x + r"
        using hxy by simp
      also have "\<dots> < e"
      proof -
        have hpos: "0 < e - d c x"
          using hdx by linarith
        have "d c x + r = d c x + (e - d c x) / 2"
          unfolding r_def by simp
        also have "\<dots> = (d c x + e) / 2"
          by (simp add: field_simps algebra_simps)
        also have "\<dots> < e"
        proof -
          have "d c x + e < e + e"
            using hdx by linarith
          hence "(d c x + e) / 2 < (e + e) / 2"
            by (rule divide_strict_right_mono) simp
          thus ?thesis
            by simp
        qed
        finally show "d c x + r < e"
          by simp
      qed
      finally have "d c x + d x y < e" .
      hence "d c y < e"
        by (rule le_less_trans[OF hcx'])
      thus "y \<in> b"
        unfolding hb top1_ball_on_def using hyX by simp
    qed

    have hball_sub_U: "top1_ball_on X d x r \<subseteq> U"
      by (rule subset_trans[OF hball_sub_b hbsub])

    show "\<exists>p. 0 < fst p \<and> snd p \<in> Uc \<and> top1_ball_on X d x (fst p) \<subseteq> snd p"
      apply (rule exI[where x="(r, U)"])
      using hrpos hUUc hball_sub_U by simp
  qed

  obtain f where hf:
    "\<forall>x\<in>X. 0 < fst (f x) \<and> snd (f x) \<in> Uc \<and> top1_ball_on X d x (fst (f x)) \<subseteq> snd (f x)"
    using bchoice[OF hexLocal] by blast

  define rad where "rad x = fst (f x)" for x
  define Ufun where "Ufun x = snd (f x)" for x

  have hradpos: "\<forall>x\<in>X. 0 < rad x"
    unfolding rad_def using hf by blast
  have hUfunUc: "\<forall>x\<in>X. Ufun x \<in> Uc"
    unfolding Ufun_def using hf by blast
  have hball_sub: "\<forall>x\<in>X. top1_ball_on X d x (rad x) \<subseteq> Ufun x"
    unfolding rad_def Ufun_def using hf by blast

  define V where "V x = top1_ball_on X d x (rad x / 2)" for x
  define Vc where "Vc = V ` X"

  have hVc_subT: "Vc \<subseteq> top1_metric_topology_on X d"
  proof (rule subsetI)
    fix U
    assume hU: "U \<in> Vc"
    obtain x where hxX: "x \<in> X" and hUeq: "U = V x"
      using hU unfolding Vc_def by blast
    have hrad: "0 < rad x / 2"
      using hradpos hxX by simp
    have "top1_ball_on X d x (rad x / 2) \<in> top1_metric_topology_on X d"
      by (rule top1_ball_open_in_metric_topology[OF hd hxX hrad])
    thus "U \<in> top1_metric_topology_on X d"
      unfolding hUeq V_def by simp
  qed

  have hVc_cov: "X \<subseteq> \<Union>Vc"
  proof (rule subsetI)
    fix x
    assume hxX: "x \<in> X"
    have hdx0: "d x x = 0"
      using hd hxX unfolding top1_metric_on_def by blast
    have hxV: "x \<in> V x"
      unfolding V_def top1_ball_on_def using hxX hdx0 hradpos[rule_format, OF hxX] by simp
    have "V x \<in> Vc"
      unfolding Vc_def by (rule imageI[OF hxX])
    thus "x \<in> \<Union>Vc"
      using hxV by blast
  qed

  have hcompact_cover:
    "\<forall>V. V \<subseteq> top1_metric_topology_on X d \<and> X \<subseteq> \<Union>V \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> V \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Vc" and hFcov: "X \<subseteq> \<Union>F"
    using hcompact_cover[rule_format, of Vc] hVc_subT hVc_cov by blast

  have hFne: "F \<noteq> {}"
  proof -
    have "x0 \<in> \<Union>F"
      using hFcov hx0X by blast
    thus ?thesis
      by blast
  qed

  have hexCenter: "\<forall>U\<in>F. \<exists>c. c \<in> X \<and> U = V c"
    using hFsub unfolding Vc_def by blast
  obtain center where hcenter: "\<forall>U\<in>F. center U \<in> X \<and> U = V (center U)"
    using bchoice[OF hexCenter] by blast

  define R where "R = (\<lambda>U. rad (center U) / 2) ` F"

  have hRfin: "finite R"
    unfolding R_def using hFfin by simp
  have hRne: "R \<noteq> {}"
    unfolding R_def using hFne by simp
  have hRpos: "\<forall>t\<in>R. 0 < t"
  proof (intro ballI)
    fix t
    assume ht: "t \<in> R"
    obtain U where hUF: "U \<in> F" and htdef: "t = rad (center U) / 2"
      using ht unfolding R_def by blast
    have hcxX: "center U \<in> X"
      using hcenter hUF by blast
    show "0 < t"
      unfolding htdef using hradpos hcxX by simp
  qed

  define \<delta> where "\<delta> = Min R"

  have h\<delta>pos: "\<delta> > 0"
  proof -
    have h\<delta>in: "\<delta> \<in> R"
      unfolding \<delta>_def by (rule Min_in[OF hRfin hRne])
    thus ?thesis
      using hRpos by blast
  qed

  have hLeb_point:
    "\<forall>x\<in>X. \<exists>U\<in>Uc. top1_ball_on X d x \<delta> \<subseteq> U"
  proof (intro ballI)
    fix x
    assume hxX: "x \<in> X"
    have hxUF: "x \<in> \<Union>F"
      using hFcov hxX by blast
    obtain B where hBF: "B \<in> F" and hxB: "x \<in> B"
      using hxUF by blast

    have hcX: "center B \<in> X" and hBeq: "B = V (center B)"
      using hcenter hBF by blast+

    have hradB_in_R: "rad (center B) / 2 \<in> R"
      unfolding R_def by (rule imageI[OF hBF])

    have h\<delta>le: "\<delta> \<le> rad (center B) / 2"
      unfolding \<delta>_def by (rule Min_le[OF hRfin hradB_in_R])

    have hcx: "d (center B) x < rad (center B) / 2"
    proof -
      have hBsub: "B \<subseteq> V (center B)"
        by (rule equalityD1[OF hBeq])
      have hxV: "x \<in> V (center B)"
        by (rule subsetD[OF hBsub hxB])
      have hxBall: "x \<in> top1_ball_on X d (center B) (rad (center B) / 2)"
        using hxV unfolding V_def by simp
      show ?thesis
        using hxBall unfolding top1_ball_on_def by simp
    qed

    have hball_sub_Big: "top1_ball_on X d x \<delta> \<subseteq> top1_ball_on X d (center B) (rad (center B))"
    proof (rule subsetI)
      fix y
      assume hy: "y \<in> top1_ball_on X d x \<delta>"
      have hyX: "y \<in> X" and hxy: "d x y < \<delta>"
        using hy unfolding top1_ball_on_def by blast+

      have htri: "d (center B) y \<le> d (center B) x + d x y"
        using hd hcX hxX hyX unfolding top1_metric_on_def by blast
      have "d (center B) x + d x y < rad (center B) / 2 + \<delta>"
        using hcx hxy by linarith
      also have "\<dots> \<le> rad (center B) / 2 + rad (center B) / 2"
        using h\<delta>le by (simp add: add_left_mono)
      also have "\<dots> = rad (center B)"
        by simp
      finally have hsum: "d (center B) x + d x y < rad (center B)" .
      have "d (center B) y < rad (center B)"
        by (rule le_less_trans[OF htri hsum])
      thus "y \<in> top1_ball_on X d (center B) (rad (center B))"
        unfolding top1_ball_on_def using hyX by simp
    qed

    have hU: "Ufun (center B) \<in> Uc"
    proof -
      have hcbX: "center B \<in> X"
        using hcenter hBF by blast
      show ?thesis
        using hUfunUc hcbX by blast
    qed
    have hball_big_sub: "top1_ball_on X d (center B) (rad (center B)) \<subseteq> Ufun (center B)"
      using hball_sub hcX by blast
    have hball_sub_U: "top1_ball_on X d x \<delta> \<subseteq> Ufun (center B)"
      by (rule subset_trans[OF hball_sub_Big hball_big_sub])

    show "\<exists>U\<in>Uc. top1_ball_on X d x \<delta> \<subseteq> U"
    proof (rule bexI[where x="Ufun (center B)"])
      show "Ufun (center B) \<in> Uc"
        by (rule hU)
      show "top1_ball_on X d x \<delta> \<subseteq> Ufun (center B)"
        by (rule hball_sub_U)
    qed
  qed

  show ?thesis
  proof (rule exI[where x=\<delta>], intro conjI)
    show "\<delta> > 0"
      by (rule h\<delta>pos)
    show "\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<and> top1_diameter_on d A < \<delta> \<longrightarrow> (\<exists>U\<in>Uc. A \<subseteq> U)"
    proof (intro allI impI)
      fix A
      assume hA: "A \<subseteq> X \<and> A \<noteq> {} \<and> top1_diameter_on d A < \<delta>"
      have hAX: "A \<subseteq> X"
        using hA by blast
      obtain a where haA: "a \<in> A"
        using hA by blast
      have haX: "a \<in> X"
        using hAX haA by blast

      have hA_sub_ball: "A \<subseteq> top1_ball_on X d a \<delta>"
      proof (rule subsetI)
        fix y
        assume hyA: "y \<in> A"
        have hyX: "y \<in> X"
          using hAX hyA by blast

        define S where "S = {d u v | u v. u \<in> A \<and> v \<in> A}"
        have hSbdd: "bdd_above S"
          unfolding bdd_above_def S_def
        proof (rule exI[where x=M], intro ballI)
          fix r
          assume hr: "r \<in> {d u v |u v. u \<in> A \<and> v \<in> A}"
          then obtain u v where huA: "u \<in> A" and hvA: "v \<in> A" and hrdef: "r = d u v"
            by blast
          have huX: "u \<in> X" and hvX: "v \<in> X"
            using hAX huA hAX hvA by blast+
          show "r \<le> M"
            unfolding hrdef using hM huX hvX by blast
        qed

        have hdy_le: "d a y \<le> Sup S"
        proof -
          have "d a y \<in> S"
            unfolding S_def by (intro CollectI exI[where x=a] exI[where x=y]) (use haA hyA in blast)
          thus ?thesis
            apply (rule cSup_upper)
            apply (rule hSbdd)
            done
        qed

        have hdiam: "top1_diameter_on d A = Sup S"
          unfolding top1_diameter_on_def S_def by simp
        have "top1_diameter_on d A < \<delta>"
          using hA by blast
        hence "Sup S < \<delta>"
          unfolding hdiam by simp
        hence "d a y < \<delta>"
          by (rule le_less_trans[OF hdy_le])

        show "y \<in> top1_ball_on X d a \<delta>"
          unfolding top1_ball_on_def using hyX \<open>d a y < \<delta>\<close> by simp
      qed

      obtain U where hUUc: "U \<in> Uc" and hball_sub_U: "top1_ball_on X d a \<delta> \<subseteq> U"
        using hLeb_point haX by blast

      have "A \<subseteq> U"
        by (rule subset_trans[OF hA_sub_ball hball_sub_U])
      show "\<exists>U\<in>Uc. A \<subseteq> U"
      proof (rule bexI[where x=U])
        show "U \<in> Uc"
          by (rule hUUc)
        show "A \<subseteq> U"
          by fact
      qed
    qed
  qed
qed

(** Uniform continuity between metric spaces (restricted to the carriers). **)
definition top1_uniformly_continuous_map_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
  "top1_uniformly_continuous_map_on X dX Y dY f \<longleftrightarrow>
     (\<forall>x\<in>X. f x \<in> Y)
     \<and> (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>X. \<forall>x'\<in>X. dX x x' < \<delta> \<longrightarrow> dY (f x) (f x') < \<epsilon>)"

(** from \S27 Theorem 27.6 (Uniform continuity theorem) [top1.tex:3511] **)
theorem Theorem_27_6:
  assumes hdX: "top1_metric_on X dX"
  assumes hdY: "top1_metric_on Y dY"
  assumes hcomp: "top1_compact_on X (top1_metric_topology_on X dX)"
  assumes hcont: "top1_continuous_map_on X (top1_metric_topology_on X dX) Y (top1_metric_topology_on Y dY) f"
  shows "top1_uniformly_continuous_map_on X dX Y dY f"
proof -
  have hmap: "\<forall>x\<in>X. f x \<in> Y"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hmapD: "\<And>x. x \<in> X \<Longrightarrow> f x \<in> Y"
    using hmap by blast

  show ?thesis
    unfolding top1_uniformly_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>X. f x \<in> Y"
      by (rule hmap)

    show "\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>X. \<forall>x'\<in>X. dX x x' < \<delta> \<longrightarrow> dY (f x) (f x') < \<epsilon>"
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume h\<epsilon>: "\<epsilon> > 0"

      define Uc where "Uc = (\<lambda>c. {x\<in>X. dY (f c) (f x) < \<epsilon> / 2}) ` X"

      have hUc_sub: "Uc \<subseteq> top1_metric_topology_on X dX"
      proof (rule subsetI)
        fix U
        assume hU: "U \<in> Uc"
        obtain c where hcX: "c \<in> X" and hUdef: "U = {x\<in>X. dY (f c) (f x) < \<epsilon> / 2}"
          using hU unfolding Uc_def by blast

        have hfcY: "f c \<in> Y"
          by (rule hmapD[OF hcX])
        have hball_basis: "top1_ball_on Y dY (f c) (\<epsilon> / 2) \<in> top1_metric_basis_on Y dY"
        proof -
          have "0 < \<epsilon> / 2"
            using h\<epsilon> by simp
          thus ?thesis
            unfolding top1_metric_basis_on_def
            using hfcY by blast
        qed
        have hBasisY: "is_basis_on Y (top1_metric_basis_on Y dY)"
          by (rule top1_metric_basis_is_basis_on[OF hdY])
        have hball_open: "top1_ball_on Y dY (f c) (\<epsilon> / 2) \<in> top1_metric_topology_on Y dY"
          unfolding top1_metric_topology_on_def
          by (rule basis_elem_open_in_generated_topology[OF hBasisY hball_basis])

        have hpreopen: "{x\<in>X. f x \<in> top1_ball_on Y dY (f c) (\<epsilon> / 2)} \<in> top1_metric_topology_on X dX"
          using hcont hball_open unfolding top1_continuous_map_on_def by blast

        have hUeq: "U = {x\<in>X. f x \<in> top1_ball_on Y dY (f c) (\<epsilon> / 2)}"
        proof (rule set_eqI)
          fix x
          show "(x \<in> U) = (x \<in> {x\<in>X. f x \<in> top1_ball_on Y dY (f c) (\<epsilon> / 2)})"
            unfolding hUdef top1_ball_on_def
            apply (cases "x \<in> X")
             apply (simp add: hmapD)
            apply simp
            done
        qed

        show "U \<in> top1_metric_topology_on X dX"
          unfolding hUeq using hpreopen by simp
      qed

	      have hcov: "X \<subseteq> \<Union>Uc"
	      proof (rule subsetI)
	        fix x
	        assume hxX: "x \<in> X"
	        have hfxY: "f x \<in> Y"
	          by (rule hmapD[OF hxX])
	        have hdiag: "dY (f x) (f x) = 0"
	          using hdY hfxY unfolding top1_metric_on_def by blast
	        have hxU: "x \<in> {z\<in>X. dY (f x) (f z) < \<epsilon> / 2}"
	        proof -
	          have hpos: "0 < \<epsilon> / 2"
	            using h\<epsilon> by simp
	          have "dY (f x) (f x) < \<epsilon> / 2"
	            unfolding hdiag using hpos by simp
	          thus ?thesis
	            using hxX by simp
	        qed
        have "{z\<in>X. dY (f x) (f z) < \<epsilon> / 2} \<in> Uc"
        proof -
          have "{z\<in>X. dY (f x) (f z) < \<epsilon> / 2} = (\<lambda>c. {z\<in>X. dY (f c) (f z) < \<epsilon> / 2}) x"
            by simp
          moreover have "(\<lambda>c. {z\<in>X. dY (f c) (f z) < \<epsilon> / 2}) x \<in> (\<lambda>c. {z\<in>X. dY (f c) (f z) < \<epsilon> / 2}) ` X"
            by (rule imageI[OF hxX])
          ultimately show ?thesis
            unfolding Uc_def by simp
        qed
	        thus "x \<in> \<Union>Uc"
	          using hxU by blast
	      qed

		      obtain \<delta> where h\<delta>: "\<delta> > 0"
		        and hLeb: "\<forall>A. A \<subseteq> X \<and> A \<noteq> {} \<and> top1_diameter_on dX A < \<delta> \<longrightarrow> (\<exists>U\<in>Uc. A \<subseteq> U)"
		        using Lemma_27_5[OF hdX hcomp hUc_sub hcov]
		        by (elim exE conjE)

      show "\<exists>\<delta>>0. \<forall>x\<in>X. \<forall>x'\<in>X. dX x x' < \<delta> \<longrightarrow> dY (f x) (f x') < \<epsilon>"
      proof (rule exI[where x=\<delta>], intro conjI)
        show "\<delta> > 0"
          by (rule h\<delta>)
	        show "\<forall>x\<in>X. \<forall>x'\<in>X. dX x x' < \<delta> \<longrightarrow> dY (f x) (f x') < \<epsilon>"
	        proof (intro ballI ballI impI)
	          fix x x'
	          assume hxX: "x \<in> X"
	          assume hx'X: "x' \<in> X"
	          assume hdist: "dX x x' < \<delta>"

          have hdiam: "top1_diameter_on dX {x, x'} < \<delta>"
          proof -
            have "top1_diameter_on dX {x, x'} \<le> dX x x'"
              by (rule top1_diameter_on_pair_le[OF hdX hxX hx'X])
            thus ?thesis
              using hdist by (rule le_less_trans)
          qed

	          have hA: "{x, x'} \<subseteq> X"
	          proof (rule subsetI)
	            fix y
	            assume hy: "y \<in> {x, x'}"
	            show "y \<in> X"
	            proof (cases "y = x")
	              case True
	              show ?thesis
	                using hxX True by simp
	            next
	              case False
	              have "y = x'"
	                using hy False by simp
	              thus ?thesis
	                using hx'X by simp
	            qed
	          qed
	          have hpair_ne: "{x, x'} \<noteq> {}"
	            by simp
	          have hexU: "\<exists>U\<in>Uc. {x, x'} \<subseteq> U"
	          proof -
	            have "{x, x'} \<subseteq> X \<and> {x, x'} \<noteq> {} \<and> top1_diameter_on dX {x, x'} < \<delta>"
	              using hA hdiam hpair_ne by simp
	            thus ?thesis
	              using hLeb[rule_format, of "{x, x'}"]
	              apply blast
	              done
	          qed
	          obtain U where hU: "U \<in> Uc" and hsub: "{x, x'} \<subseteq> U"
	            using hexU by blast

	          obtain c where hcX: "c \<in> X" and hUdef: "U = {z\<in>X. dY (f c) (f z) < \<epsilon> / 2}"
	            using hU unfolding Uc_def by blast

          have hxU: "x \<in> U"
            using hsub by simp
          have hx'U: "x' \<in> U"
            using hsub by simp

          have hcx: "dY (f c) (f x) < \<epsilon> / 2"
            using hxU unfolding hUdef by simp
          have hcx': "dY (f c) (f x') < \<epsilon> / 2"
            using hx'U unfolding hUdef by simp

          have hfxY: "f x \<in> Y"
            by (rule hmapD[OF hxX])
          have hfx'Y: "f x' \<in> Y"
            by (rule hmapD[OF hx'X])
          have hfcY: "f c \<in> Y"
            by (rule hmapD[OF hcX])

          have hsym1: "dY (f x) (f c) = dY (f c) (f x)"
            using hdY hfxY hfcY unfolding top1_metric_on_def by blast
          have hsym2: "dY (f c) (f x') = dY (f x') (f c)"
            using hdY hfcY hfx'Y unfolding top1_metric_on_def by blast
          have htri: "dY (f x) (f x') \<le> dY (f x) (f c) + dY (f c) (f x')"
            using hdY hfxY hfcY hfx'Y unfolding top1_metric_on_def by blast

          have hsum: "dY (f x) (f c) + dY (f c) (f x') < \<epsilon>"
          proof -
            have hpos: "0 < \<epsilon> / 2"
              using h\<epsilon> by simp
            have hlt1: "dY (f x) (f c) < \<epsilon> / 2"
              unfolding hsym1 using hcx .
            have hlt2: "dY (f c) (f x') < \<epsilon> / 2"
              using hcx' .
            have "dY (f x) (f c) + dY (f c) (f x') < \<epsilon> / 2 + \<epsilon> / 2"
              using hlt1 hlt2 by (rule add_strict_mono)
            thus ?thesis
              by simp
          qed

          show "dY (f x) (f x') < \<epsilon>"
            by (rule le_less_trans[OF htri hsum])
        qed
      qed
    qed
  qed
qed

(** Isolated points (used in Theorem 27.7). **)
definition top1_isolated_point_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_isolated_point_on X TX x \<longleftrightarrow> x \<in> X \<and> {x} \<in> TX"

(** Countability predicate, kept local to avoid extra library session dependencies. **)
definition countable :: "'a set \<Rightarrow> bool" where
  "countable S \<longleftrightarrow> (\<exists>f::'a \<Rightarrow> nat. inj_on f S)"

(** The full powerset of \<open>\<nat>\<close> is not countable (Cantor). **)
lemma top1_not_countable_UNIV_nat_set:
  "\<not> countable (UNIV :: nat set set)"
proof
  assume hcnt: "countable (UNIV :: nat set set)"
  obtain g :: "nat set \<Rightarrow> nat" where hg_inj: "inj_on g (UNIV :: nat set set)"
    using hcnt unfolding countable_def by blast
  have hg_inj': "inj g"
    using hg_inj unfolding inj_on_def by simp

  define f :: "nat \<Rightarrow> nat set" where
    "f n = (if n \<in> range g then (SOME S. g S = n) else {})" for n

  have hsurj: "f ` (UNIV :: nat set) = (UNIV :: nat set set)"
  proof (rule set_eqI)
    fix S :: "nat set"
    show "S \<in> f ` (UNIV :: nat set) \<longleftrightarrow> S \<in> (UNIV :: nat set set)"
    proof (rule iffI)
      assume "S \<in> f ` (UNIV :: nat set)"
      then show "S \<in> (UNIV :: nat set set)"
        by simp
    next
      assume "S \<in> (UNIV :: nat set set)"
      define n where "n = g S"
      have hn_range: "n \<in> range g"
        unfolding n_def by blast
      have hsome: "g (SOME S'. g S' = n) = n"
        unfolding n_def by (rule someI, simp)
      have hEq: "(SOME S'. g S' = n) = S"
      proof -
        have "g (SOME S'. g S' = n) = g S"
          using hsome unfolding n_def by simp
        thus ?thesis
          using hg_inj' unfolding inj_def by blast
      qed
      have "f n = S"
        unfolding f_def using hn_range hEq by simp
      have "S \<in> f ` (UNIV :: nat set)"
      proof -
        have "f n \<in> f ` (UNIV :: nat set)"
          by (rule imageI) simp
        thus ?thesis
          using \<open>f n = S\<close> by simp
      qed
      thus "S \<in> f ` (UNIV :: nat set)" .
    qed
  qed

  have "f ` (UNIV :: nat set) = Pow (UNIV :: nat set)"
    using hsurj by simp
  thus False
    using Cantors_theorem by blast
qed

(** A Cantor-style ternary series encoding of \<open>nat set\<close> into an interval of reals. **)
definition top1_ternary_sum :: "nat set \<Rightarrow> real" where
  "top1_ternary_sum S = (\<Sum>n. if n \<in> S then (1/3::real)^(Suc n) else 0)"

lemma top1_summable_ternary_sum:
  "summable (\<lambda>n. if n \<in> S then (1/3::real)^(Suc n) else 0)"
proof (rule summable_comparison_test)
  show "\<exists>N. \<forall>n\<ge>N. norm (if n \<in> S then (1/3::real)^(Suc n) else 0) \<le> (1/3::real)^(Suc n)"
    by (rule exI[where x=0], intro allI impI) simp
  show "summable (\<lambda>n. (1/3::real)^(Suc n))"
  proof -
    have hgeom: "summable (\<lambda>n. (1/3::real)^n)"
      by (rule summable_geometric) simp
    have "summable (\<lambda>n. (1/3::real)^n * (1/3::real))"
      by (rule summable_mult2[OF hgeom])
    thus ?thesis
      by (simp add: power_Suc)
  qed
qed

lemma top1_suminf_geometric_1_3_Suc:
  "(\<Sum>n. (1/3::real)^(Suc n)) = (1/2::real)"
proof -
  have hgeom: "summable (\<lambda>n. (1/3::real)^n)"
    by (rule summable_geometric) simp
  have hsplit:
    "(\<Sum>n. (1/3::real)^(Suc n)) = suminf (\<lambda>n. (1/3::real)^n) - (1/3::real)^0"
    using suminf_split_head[OF hgeom] by simp
  have "(\<Sum>n. (1/3::real)^(Suc n)) = 1 / (1 - (1/3::real)) - 1"
    using hsplit by (simp add: suminf_geometric)
  also have "... = (1/2::real)"
    by simp
  finally show ?thesis .
qed

lemma top1_ternary_sum_ge_0:
  "0 \<le> top1_ternary_sum S"
proof -
  have hs: "summable (\<lambda>n. if n \<in> S then (1/3::real)^(Suc n) else 0)"
    by (rule top1_summable_ternary_sum)
  show ?thesis
    unfolding top1_ternary_sum_def
    by (rule suminf_nonneg[OF hs]) simp
qed

lemma top1_ternary_sum_le_half:
  "top1_ternary_sum S \<le> (1/2::real)"
proof -
  have hs: "summable (\<lambda>n. if n \<in> S then (1/3::real)^(Suc n) else 0)"
    by (rule top1_summable_ternary_sum)
  have hg: "summable (\<lambda>n. (1/3::real)^(Suc n))"
  proof -
    have "summable (\<lambda>n. if n \<in> (UNIV :: nat set) then (1/3::real)^(Suc n) else 0)"
      by (rule top1_summable_ternary_sum)
    thus ?thesis
      by simp
  qed
  have hle: "\<And>n. (if n \<in> S then (1/3::real)^(Suc n) else 0) \<le> (1/3::real)^(Suc n)"
    by simp
  have "top1_ternary_sum S \<le> (\<Sum>n. (1/3::real)^(Suc n))"
    unfolding top1_ternary_sum_def
    by (rule suminf_le[OF hle hs hg])
  thus ?thesis
    using top1_suminf_geometric_1_3_Suc by simp
qed

lemma top1_suminf_geometric_1_3_tail:
  "(\<Sum>n. (1/3::real)^(n + (k + 2))) = (1/2::real) * (1/3::real)^(k + 1)"
proof -
  have hgeom: "summable (\<lambda>n. (1/3::real)^n)"
    by (rule summable_geometric) simp
  have hs: "summable (\<lambda>n. (1/3::real)^(n + (k + 2)))"
  proof -
    have "summable (\<lambda>n. (1/3::real)^n * (1/3::real)^(k + 2))"
      by (rule summable_mult2[OF hgeom])
    thus ?thesis
      by (simp add: power_add algebra_simps)
  qed
  have "(\<Sum>n. (1/3::real)^(n + (k + 2))) = (\<Sum>n. (1/3::real)^n * (1/3::real)^(k + 2))"
    by (simp add: power_add algebra_simps)
  also have "... = suminf (\<lambda>n. (1/3::real)^n) * (1/3::real)^(k + 2)"
    using suminf_mult2[OF hgeom, where c="(1/3::real)^(k + 2)"] by simp
  also have "... = (1 / (1 - (1/3::real))) * (1/3::real)^(k + 2)"
    by (simp add: suminf_geometric)
  also have "... = (1/2::real) * (1/3::real)^(k + 1)"
    by (simp add: power_add algebra_simps)
  finally show ?thesis .
qed

lemma top1_ternary_sum_inj:
  "inj_on top1_ternary_sum (UNIV :: nat set set)"
proof (unfold inj_on_def, intro ballI impI)
  fix S T :: "nat set"
  assume hEq: "top1_ternary_sum S = top1_ternary_sum T"
  show "S = T"
  proof (rule ccontr)
    assume hNe: "S \<noteq> T"
    define P where "P n \<longleftrightarrow> (n \<in> S) \<noteq> (n \<in> T)" for n
    have hex: "\<exists>n. P n"
      using hNe unfolding P_def by blast
    define k where "k = (LEAST n. P n)"
    have hk: "P k"
      unfolding k_def by (rule LeastI_ex[OF hex])
    have hlt: "\<And>m. m < k \<Longrightarrow> \<not> P m"
      unfolding k_def by (rule not_less_Least)

    define fS where "fS n = (if n \<in> S then (1/3::real)^(Suc n) else 0)" for n
    define fT where "fT n = (if n \<in> T then (1/3::real)^(Suc n) else 0)" for n

    have hsS: "summable fS"
      unfolding fS_def by (rule top1_summable_ternary_sum)
    have hsT: "summable fT"
      unfolding fT_def by (rule top1_summable_ternary_sum)

    have hsplitS:
      "top1_ternary_sum S = (\<Sum>n. fS (n + Suc k)) + (\<Sum>i<Suc k. fS i)"
      unfolding top1_ternary_sum_def fS_def
      by (rule suminf_split_initial_segment[OF top1_summable_ternary_sum, of S "Suc k"])
    have hsplitT:
      "top1_ternary_sum T = (\<Sum>n. fT (n + Suc k)) + (\<Sum>i<Suc k. fT i)"
      unfolding top1_ternary_sum_def fT_def
      by (rule suminf_split_initial_segment[OF top1_summable_ternary_sum, of T "Suc k"])

    have hprefix: "\<And>m. m < k \<Longrightarrow> (m \<in> S) = (m \<in> T)"
    proof -
      fix m
      assume hm: "m < k"
      have "\<not> P m" by (rule hlt[OF hm])
      thus "(m \<in> S) = (m \<in> T)"
        unfolding P_def by blast
    qed

    have hsum_lt_k: "(\<Sum>i<k. fS i) = (\<Sum>i<k. fT i)"
    proof (rule sum.cong[OF refl])
      fix i
      assume hi: "i \<in> {..<k}"
      have hik: "i < k" using hi by simp
      have "(i \<in> S) = (i \<in> T)"
        by (rule hprefix[OF hik])
      thus "fS i = fT i"
        unfolding fS_def fT_def by simp
    qed

    have hinitS: "(\<Sum>i<Suc k. fS i) = (\<Sum>i<k. fS i) + fS k"
      by (simp add: sum.lessThan_Suc)
    have hinitT: "(\<Sum>i<Suc k. fT i) = (\<Sum>i<k. fT i) + fT k"
      by (simp add: sum.lessThan_Suc)

    have htailS_ge0: "0 \<le> (\<Sum>n. fS (n + Suc k))"
    proof -
      have hs: "summable (\<lambda>n. fS (n + Suc k))"
        using summable_ignore_initial_segment[OF hsS] .
      show ?thesis
        by (rule suminf_nonneg[OF hs]) (simp add: fS_def)
    qed

    have htailT_le:
      "(\<Sum>n. fT (n + Suc k)) \<le> (\<Sum>n. (1/3::real)^(Suc (n + Suc k)))"
    proof -
      have hs: "summable (\<lambda>n. fT (n + Suc k))"
        using summable_ignore_initial_segment[OF hsT] .
      have hg: "summable (\<lambda>n. (1/3::real)^(Suc (n + Suc k)))"
      proof -
        have hgeom: "summable (\<lambda>n. (1/3::real)^n)"
          by (rule summable_geometric) simp
        have "summable (\<lambda>n. (1/3::real)^n * (1/3::real)^(Suc k + 1))"
          by (rule summable_mult2[OF hgeom])
        thus ?thesis
          by (simp add: power_add algebra_simps)
      qed
      have hle: "\<And>n. fT (n + Suc k) \<le> (1/3::real)^(Suc (n + Suc k))"
        unfolding fT_def by simp
      show ?thesis
        by (rule suminf_le[OF hle hs hg])
    qed

    have htail_full:
      "(\<Sum>n. (1/3::real)^(Suc (n + Suc k))) = (1/2::real) * (1/3::real)^(Suc k)"
    proof -
      have "(\<Sum>n. (1/3::real)^(Suc (n + Suc k))) = (\<Sum>n. (1/3::real)^(n + (k + 2)))"
        by simp
      also have "... = (1/2::real) * (1/3::real)^(k + 1)"
        by (rule top1_suminf_geometric_1_3_tail)
      finally show ?thesis
        by simp
    qed

    have hk_cases: "(k \<in> S \<and> k \<notin> T) \<or> (k \<notin> S \<and> k \<in> T)"
      using hk unfolding P_def by auto

    from hk_cases show False
    proof
      assume hST: "k \<in> S \<and> k \<notin> T"
      have hfSk: "fS k = (1/3::real)^(Suc k)"
        using hST unfolding fS_def by simp
      have hfTk: "fT k = 0"
        using hST unfolding fT_def by simp

      have hinit_diff: "(\<Sum>i<Suc k. fS i) = (\<Sum>i<Suc k. fT i) + (1/3::real)^(Suc k)"
      proof -
        have "(\<Sum>i<Suc k. fS i) = (\<Sum>i<k. fS i) + (1/3::real)^(Suc k)"
          using hinitS hfSk by simp
        also have "... = (\<Sum>i<k. fT i) + (1/3::real)^(Suc k)"
          using hsum_lt_k by simp
        also have "... = (\<Sum>i<Suc k. fT i) + (1/3::real)^(Suc k)"
          using hinitT hfTk by simp
        finally show ?thesis .
      qed

      have hS_ge: "(\<Sum>i<Suc k. fS i) \<le> top1_ternary_sum S"
        using hsplitS htailS_ge0 by simp
      have hT_le: "top1_ternary_sum T \<le> (\<Sum>i<Suc k. fT i) + (1/2::real) * (1/3::real)^(Suc k)"
        using hsplitT htailT_le htail_full by simp

      have hS0: "(\<Sum>i<Suc k. fT i) + (1/3::real)^(Suc k) \<le> top1_ternary_sum S"
        using hS_ge hinit_diff by simp
      have hT0: "top1_ternary_sum T \<le> (\<Sum>i<Suc k. fT i) + (1/2::real) * (1/3::real)^(Suc k)"
        by (rule hT_le)
      have "top1_ternary_sum T < top1_ternary_sum S"
      proof -
        define A where "A = (\<Sum>i<Suc k. fT i)"
        define B where "B = (1/3::real)^(Suc k)"
        have hS: "A + B \<le> top1_ternary_sum S"
          using hS0 unfolding A_def B_def by simp
        have hT: "top1_ternary_sum T \<le> A + (1/2::real) * B"
          using hT0 unfolding A_def B_def by simp
        have hBpos: "0 < B"
          unfolding B_def by simp
        have hhalfB: "(1/2::real) * B < B"
          using hBpos by simp
        have hAhalf: "A + (1/2::real) * B < A + B"
          using hhalfB by simp
        have hTlt: "top1_ternary_sum T < A + B"
          by (rule le_less_trans[OF hT hAhalf])
        show ?thesis
          by (rule less_le_trans[OF hTlt hS])
      qed
      thus False
        using hEq by simp
    next
      assume hTS: "k \<notin> S \<and> k \<in> T"
      have hfSk: "fS k = 0"
        using hTS unfolding fS_def by simp
      have hfTk: "fT k = (1/3::real)^(Suc k)"
        using hTS unfolding fT_def by simp

      have hinit_diff: "(\<Sum>i<Suc k. fT i) = (\<Sum>i<Suc k. fS i) + (1/3::real)^(Suc k)"
      proof -
        have "(\<Sum>i<Suc k. fT i) = (\<Sum>i<k. fT i) + (1/3::real)^(Suc k)"
          using hinitT hfTk by simp
        also have "... = (\<Sum>i<k. fS i) + (1/3::real)^(Suc k)"
          using hsum_lt_k by simp
        also have "... = (\<Sum>i<Suc k. fS i) + (1/3::real)^(Suc k)"
          using hinitS hfSk by simp
        finally show ?thesis .
      qed

      have hS_le: "top1_ternary_sum S \<le> (\<Sum>i<Suc k. fS i) + (1/2::real) * (1/3::real)^(Suc k)"
        using hsplitS
      proof -
        have htailS_le:
          "(\<Sum>n. fS (n + Suc k)) \<le> (\<Sum>n. (1/3::real)^(Suc (n + Suc k)))"
        proof -
          have hs: "summable (\<lambda>n. fS (n + Suc k))"
            using summable_ignore_initial_segment[OF hsS] .
          have hg: "summable (\<lambda>n. (1/3::real)^(Suc (n + Suc k)))"
          proof -
            have hgeom: "summable (\<lambda>n. (1/3::real)^n)"
              by (rule summable_geometric) simp
            have "summable (\<lambda>n. (1/3::real)^n * (1/3::real)^(Suc k + 1))"
              by (rule summable_mult2[OF hgeom])
            thus ?thesis
              by (simp add: power_add algebra_simps)
          qed
          have hle: "\<And>n. fS (n + Suc k) \<le> (1/3::real)^(Suc (n + Suc k))"
            unfolding fS_def by simp
          show ?thesis
            by (rule suminf_le[OF hle hs hg])
        qed
        show "top1_ternary_sum S \<le> (\<Sum>i<Suc k. fS i) + (1/2::real) * (1/3::real)^(Suc k)"
          using htailS_le htail_full unfolding hsplitS by simp
      qed

      have hT_ge: "(\<Sum>i<Suc k. fT i) \<le> top1_ternary_sum T"
      proof -
        have hs: "summable (\<lambda>n. fT (n + Suc k))"
          using summable_ignore_initial_segment[OF hsT] .
        have htail_ge0: "0 \<le> (\<Sum>n. fT (n + Suc k))"
          by (rule suminf_nonneg[OF hs]) (simp add: fT_def)
        show ?thesis
          using hsplitT htail_ge0 by simp
      qed

      have hS0: "top1_ternary_sum S \<le> (\<Sum>i<Suc k. fS i) + (1/2::real) * (1/3::real)^(Suc k)"
        by (rule hS_le)
      have hT0: "(\<Sum>i<Suc k. fS i) + (1/3::real)^(Suc k) \<le> top1_ternary_sum T"
        using hT_ge hinit_diff by simp
      have "top1_ternary_sum S < top1_ternary_sum T"
      proof -
        define A where "A = (\<Sum>i<Suc k. fS i)"
        define B where "B = (1/3::real)^(Suc k)"
        have hS: "top1_ternary_sum S \<le> A + (1/2::real) * B"
          using hS0 unfolding A_def B_def by simp
        have hT: "A + B \<le> top1_ternary_sum T"
          using hT0 unfolding A_def B_def by simp
        have hBpos: "0 < B"
          unfolding B_def by simp
        have hhalfB: "(1/2::real) * B < B"
          using hBpos by simp
        have hAhalf: "A + (1/2::real) * B < A + B"
          using hhalfB by simp
        have hSlt: "top1_ternary_sum S < A + B"
          by (rule le_less_trans[OF hS hAhalf])
        show ?thesis
          by (rule less_le_trans[OF hSlt hT])
      qed
      thus False
        using hEq by simp
    qed
  qed
qed

definition top1_interval_encode :: "real \<Rightarrow> real \<Rightarrow> nat set \<Rightarrow> real" where
  "top1_interval_encode a b S = a + (b - a) * (2 * top1_ternary_sum S)"

lemma top1_interval_encode_mem_Icc:
  assumes hab: "a < b"
  shows "top1_interval_encode a b S \<in> {a..b}"
proof -
  have hsum0: "0 \<le> top1_ternary_sum S"
    by (rule top1_ternary_sum_ge_0)
  have hsumle: "top1_ternary_sum S \<le> (1/2::real)"
    by (rule top1_ternary_sum_le_half)
  have h2sum0: "0 \<le> 2 * top1_ternary_sum S"
    using hsum0 by simp
  have h2sumle: "2 * top1_ternary_sum S \<le> (1::real)"
    using hsumle by simp
  have hba0: "0 < b - a"
    using hab by simp
  have hba: "0 \<le> b - a"
    using hba0 by simp

  have ha: "a \<le> top1_interval_encode a b S"
    unfolding top1_interval_encode_def
    using hba h2sum0 by (simp add: mult_nonneg_nonneg)
  have hb: "top1_interval_encode a b S \<le> b"
  proof -
    have "(b - a) * (2 * top1_ternary_sum S) \<le> (b - a) * (1::real)"
    proof (rule mult_left_mono)
      show "2 * top1_ternary_sum S \<le> (1::real)"
        by (rule h2sumle)
      show "0 \<le> b - a"
        by (rule hba)
    qed
    hence "a + (b - a) * (2 * top1_ternary_sum S) \<le> a + (b - a)"
      by simp
    thus ?thesis
      unfolding top1_interval_encode_def by simp
  qed
  show ?thesis
    using ha hb by simp
qed

lemma top1_interval_encode_inj:
  assumes hab: "a < b"
  shows "inj_on (top1_interval_encode a b) (UNIV :: nat set set)"
proof (unfold inj_on_def, intro ballI impI)
  fix S T :: "nat set"
  assume hEq: "top1_interval_encode a b S = top1_interval_encode a b T"
  have hba0: "b - a \<noteq> 0"
    using hab by simp
  have "2 * top1_ternary_sum S = 2 * top1_ternary_sum T"
    using hEq hba0 unfolding top1_interval_encode_def by (simp add: mult_left_cancel)
  hence "top1_ternary_sum S = top1_ternary_sum T"
    by simp
  thus "S = T"
    using top1_ternary_sum_inj unfolding inj_on_def by blast
qed

(** Helper for Theorem 27.7: shrink a nonempty open set to avoid a given point in its closure. **)
lemma top1_27_7_shrink_open_avoid_closure:
  assumes hH: "is_hausdorff_on X TX"
  assumes hnoi: "\<forall>x\<in>X. \<not> top1_isolated_point_on X TX x"
  assumes hU: "U \<in> TX"
  assumes hUX: "U \<subseteq> X"
  assumes hUne: "U \<noteq> {}"
  assumes hxX: "x \<in> X"
  shows "\<exists>V. V \<in> TX \<and> V \<subseteq> X \<and> V \<subseteq> U \<and> V \<noteq> {} \<and> x \<notin> closure_on X TX V"
proof -
  have hTop: "is_topology_on X TX"
    using hH unfolding is_hausdorff_on_def by blast
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])

  have hx_not_iso: "\<not> top1_isolated_point_on X TX x"
    using hnoi hxX by blast

  have hex_y: "\<exists>y. y \<in> U \<and> y \<noteq> x"
  proof (cases "x \<in> U")
    case True
    have hUdiff_ne: "U - {x} \<noteq> {}"
    proof
      assume h0: "U - {x} = {}"
      have hsub: "U \<subseteq> {x}"
      proof (rule subsetI)
        fix z assume hzU: "z \<in> U"
        show "z \<in> {x}"
        proof (rule ccontr)
          assume hzx: "z \<notin> {x}"
          have "z \<in> U - {x}"
            by (rule DiffI[OF hzU hzx])
          thus False
            using h0 by simp
        qed
      qed
      have hEq: "U = {x}"
      proof (rule equalityI)
        show "U \<subseteq> {x}" by (rule hsub)
        show "{x} \<subseteq> U" using True by simp
      qed
      have "top1_isolated_point_on X TX x"
        unfolding top1_isolated_point_on_def
        by (intro conjI[OF hxX], subst hEq[symmetric], rule hU)
      thus False
        using hx_not_iso by blast
    qed
    obtain y0 where hy0: "y0 \<in> U - {x}"
      using hUdiff_ne by blast
    have hy0U: "y0 \<in> U" and hy0ne: "y0 \<noteq> x"
      using hy0 by blast+
    show ?thesis
      by (rule exI[where x=y0], rule conjI, rule hy0U, rule hy0ne)
  next
    case False
    obtain y0 where hy0U: "y0 \<in> U"
      using hUne by blast
    have hy0ne: "y0 \<noteq> x"
      using False hy0U by blast
    show ?thesis
      by (rule exI[where x=y0], rule conjI, rule hy0U, rule hy0ne)
  qed

  obtain y where hyU: "y \<in> U" and hyne: "y \<noteq> x"
    using hex_y by blast

  have hyX: "y \<in> X"
    using hUX hyU by blast

  obtain Ux0 Uy0 where hUx0: "neighborhood_of x X TX Ux0"
      and hUy0: "neighborhood_of y X TX Uy0"
      and hdisj0: "Ux0 \<inter> Uy0 = {}"
    using hH hxX hyX hyne unfolding is_hausdorff_on_def by blast

  define Ux where "Ux = X \<inter> Ux0"
  define Uy where "Uy = X \<inter> Uy0"

  have hUx: "neighborhood_of x X TX Ux"
  proof -
    have hUx0T: "Ux0 \<in> TX" and hxUx0: "x \<in> Ux0"
      using hUx0 unfolding neighborhood_of_def by blast+
    have hUxT: "Ux \<in> TX"
      unfolding Ux_def by (rule topology_inter2[OF hTop X_TX hUx0T])
    have hxUx: "x \<in> Ux"
      unfolding Ux_def using hxX hxUx0 by blast
    show ?thesis
      unfolding neighborhood_of_def using hUxT hxUx by blast
  qed

  have hUy: "neighborhood_of y X TX Uy"
  proof -
    have hUy0T: "Uy0 \<in> TX" and hyUy0: "y \<in> Uy0"
      using hUy0 unfolding neighborhood_of_def by blast+
    have hUyT: "Uy \<in> TX"
      unfolding Uy_def by (rule topology_inter2[OF hTop X_TX hUy0T])
    have hyUy: "y \<in> Uy"
      unfolding Uy_def using hyX hyUy0 by blast
    show ?thesis
      unfolding neighborhood_of_def using hUyT hyUy by blast
  qed

  have hUxX: "Ux \<subseteq> X"
    unfolding Ux_def by blast
  have hUyX: "Uy \<subseteq> X"
    unfolding Uy_def by blast

  have hdisj: "Ux \<inter> Uy = {}"
  proof -
    have hsub: "Ux \<inter> Uy \<subseteq> Ux0 \<inter> Uy0"
      unfolding Ux_def Uy_def by blast
    show ?thesis
    proof (rule subset_antisym)
      show "Ux \<inter> Uy \<subseteq> {}"
        by (rule subset_trans[OF hsub], simp only: hdisj0)
      show "{} \<subseteq> Ux \<inter> Uy"
        by simp
    qed
  qed

  define V where "V = Uy \<inter> U"
  have hVT: "V \<in> TX"
  proof -
    have hUyT: "Uy \<in> TX"
      using hUy unfolding neighborhood_of_def by blast
    show ?thesis
      unfolding V_def by (rule topology_inter2[OF hTop hUyT hU])
  qed
  have hVsubU: "V \<subseteq> U"
    unfolding V_def by blast
  have hVsubX: "V \<subseteq> X"
    unfolding V_def using hUyX hUX by blast
  have hyV: "y \<in> V"
  proof -
    have hyUy: "y \<in> Uy"
      using hUy unfolding neighborhood_of_def by blast
    show ?thesis
      unfolding V_def using hyUy hyU by blast
  qed
  have hVne: "V \<noteq> {}"
    using hyV by blast

  have hnot_intersects: "\<not> intersects Ux V"
  proof
    assume hint: "intersects Ux V"
    have hne: "Ux \<inter> V \<noteq> {}"
      using hint unfolding intersects_def by simp
    have hsub': "Ux \<inter> V \<subseteq> Ux \<inter> Uy"
      unfolding V_def by blast
    have "Ux \<inter> V \<subseteq> {}"
      by (rule subset_trans[OF hsub'], simp only: hdisj)
    thus False
      using hne by blast
  qed

  have hx_not_cl: "x \<notin> closure_on X TX V"
  proof -
    have hchar:
      "x \<in> closure_on X TX V \<longleftrightarrow> (\<forall>W. neighborhood_of x X TX W \<longrightarrow> intersects W V)"
      by (rule Theorem_17_5a[OF hTop hxX hVsubX])
    have hall_false: "\<not> (\<forall>W. neighborhood_of x X TX W \<longrightarrow> intersects W V)"
    proof
      assume hall: "\<forall>W. neighborhood_of x X TX W \<longrightarrow> intersects W V"
      have "intersects Ux V"
        by (rule hall[rule_format, OF hUx])
      thus False
        using hnot_intersects by blast
    qed
    show ?thesis
      using hchar hall_false by blast
  qed

  show ?thesis
    apply (rule exI[where x=V])
    apply (rule conjI)
     apply (rule hVT)
    apply (rule conjI)
     apply (rule hVsubX)
    apply (rule conjI)
     apply (rule hVsubU)
    apply (rule conjI)
     apply (rule hVne)
    apply (rule hx_not_cl)
    done
qed

(** A small countability helper: a nonempty countable set is the image of a map \<open>nat \<Rightarrow> X\<close>. **)
lemma top1_countable_nonempty_eq_image_nat:
  assumes hcnt: "countable X"
  assumes hXne: "X \<noteq> {}"
  shows "\<exists>f::nat \<Rightarrow> 'a. (\<forall>n. f n \<in> X) \<and> f ` (UNIV :: nat set) = X"
proof -
  obtain g :: "'a \<Rightarrow> nat" where hg: "inj_on g X"
    using hcnt unfolding countable_def by blast
  obtain x0 where hx0X: "x0 \<in> X"
    using hXne by blast

  define f where "f n = (if n \<in> g ` X then inv_into X g n else x0)" for n

  have hfX: "\<forall>n. f n \<in> X"
  proof (intro allI)
    fix n
    show "f n \<in> X"
    proof (cases "n \<in> g ` X")
      case True
      have "inv_into X g n \<in> X"
        by (rule inv_into_into[OF True])
      thus ?thesis
        unfolding f_def using True by simp
    next
      case False
      thus ?thesis
        unfolding f_def using hx0X by simp
    qed
  qed

  have hXsub: "X \<subseteq> f ` (UNIV :: nat set)"
  proof (rule subsetI)
    fix x
    assume hxX: "x \<in> X"
    have hgx: "g x \<in> g ` X"
      using hxX by blast
    have "f (g x) = inv_into X g (g x)"
      unfolding f_def using hgx by simp
    also have "... = x"
      by (rule inv_into_f_f[OF hg hxX])
    finally have hxfx: "f (g x) = x" .
    have "f (g x) \<in> f ` (UNIV :: nat set)"
      by (rule imageI) simp
    thus "x \<in> f ` (UNIV :: nat set)"
      using hxfx by simp
  qed

  have hfsubX: "f ` (UNIV :: nat set) \<subseteq> X"
    using hfX by blast

  have "f ` (UNIV :: nat set) = X"
    by (rule equalityI[OF hfsubX hXsub])
  thus ?thesis
    apply (intro exI[where x=f] conjI)
    apply (rule hfX)
    apply assumption
    done
qed

(** A basic helper about nested sequences of sets (used in compactness/FIP arguments). **)
lemma top1_nested_subset_le:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes hstep: "\<forall>n. A (Suc n) \<subseteq> A n"
  assumes hmn: "m \<le> n"
  shows "A n \<subseteq> A m"
proof -
  have hdec: "decseq A"
  proof (rule decseq_SucI)
    fix k
    have "A (Suc k) \<subseteq> A k"
      by (rule allE[OF hstep, where x=k])
    thus "A (Suc k) \<le> A k"
      by simp
  qed
  show ?thesis
    by (rule decseqD[OF hdec hmn])
qed

(** Compactness yields a nonempty intersection for a nested sequence of nonempty closures. **)
lemma top1_compact_nested_closure_inter_ne:
  fixes V :: "nat \<Rightarrow> 'a set"
  assumes hTop: "is_topology_on X TX"
  assumes hcomp: "top1_compact_on X TX"
  assumes hVsubX: "\<forall>n. V n \<subseteq> X"
  assumes hVne: "\<forall>n. V n \<noteq> {}"
  assumes hVshrink: "\<forall>n. V (Suc n) \<subseteq> V n"
  shows "\<Inter>(range (\<lambda>n. closure_on X TX (V n))) \<noteq> {}"
proof -
  have hCl_closed:
    "\<forall>n. closedin_on X TX (closure_on X TX (V n))"
  proof (intro allI)
    fix n
    have hVnX: "V n \<subseteq> X"
      using hVsubX by blast
    show "closedin_on X TX (closure_on X TX (V n))"
      by (rule closure_on_closed[OF hTop hVnX])
  qed

  have hCl_step:
    "\<forall>n. closure_on X TX (V (Suc n)) \<subseteq> closure_on X TX (V n)"
  proof (intro allI)
    fix n
    have hVV: "V (Suc n) \<subseteq> V n"
      using hVshrink by blast
    show "closure_on X TX (V (Suc n)) \<subseteq> closure_on X TX (V n)"
      by (rule closure_on_mono[OF hVV])
  qed

  have hCl_le:
    "m \<le> n \<Longrightarrow> closure_on X TX (V n) \<subseteq> closure_on X TX (V m)" for m n
    by (rule top1_nested_subset_le[OF hCl_step])

  have hFIP:
    "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> range (\<lambda>n. closure_on X TX (V n))
         \<longrightarrow> \<Inter>F \<noteq> {}"
  proof (intro allI impI)
    fix F
    assume hF: "finite F \<and> F \<noteq> {} \<and> F \<subseteq> range (\<lambda>n. closure_on X TX (V n))"
    have hFfin: "finite F"
      by (rule conjunct1[OF hF])
    have hFne: "F \<noteq> {}"
      by (rule conjunct1[OF conjunct2[OF hF]])
    have hFsub: "F \<subseteq> range (\<lambda>n. closure_on X TX (V n))"
      by (rule conjunct2[OF conjunct2[OF hF]])

    have hFsub_img: "F \<subseteq> (\<lambda>n. closure_on X TX (V n)) ` (UNIV :: nat set)"
      using hFsub by simp

    have exC:
      "\<exists>C::nat set. C \<subseteq> (UNIV :: nat set) \<and> finite C \<and> F = (\<lambda>n. closure_on X TX (V n)) ` C"
      by (rule finite_subset_image[OF hFfin hFsub_img])

    obtain C :: "nat set" where hCsub: "C \<subseteq> (UNIV :: nat set)"
      and hCfin: "finite C"
      and hFeq: "F = (\<lambda>n. closure_on X TX (V n)) ` C"
    proof -
      from exC show thesis
      proof (elim exE)
        fix C :: "nat set"
        assume hC: "C \<subseteq> (UNIV :: nat set) \<and> finite C \<and> F = (\<lambda>n. closure_on X TX (V n)) ` C"
        have hCsub: "C \<subseteq> (UNIV :: nat set)"
          by (rule conjunct1[OF hC])
        have hCfin: "finite C"
          by (rule conjunct1[OF conjunct2[OF hC]])
        have hFeq: "F = (\<lambda>n. closure_on X TX (V n)) ` C"
          by (rule conjunct2[OF conjunct2[OF hC]])
        show thesis
          by (rule that[OF hCsub hCfin hFeq])
      qed
    qed

    have hCne: "C \<noteq> {}"
    proof
      assume hC0: "C = {}"
      have "F = {}"
        unfolding hFeq hC0 by simp
      thus False
        using hFne by simp
    qed

    define nmax where "nmax = Max C"

    have hnmaxC: "nmax \<in> C"
      unfolding nmax_def by (rule Max_in[OF hCfin hCne])

    have hClnmax_ne: "closure_on X TX (V nmax) \<noteq> {}"
    proof -
      have hVnmax_ne: "V nmax \<noteq> {}"
        using hVne by blast
      obtain x0 where hx0: "x0 \<in> V nmax"
        using hVnmax_ne by blast
      have hx0cl: "x0 \<in> closure_on X TX (V nmax)"
        by (rule subsetD[OF subset_closure_on hx0])
      show ?thesis
        using hx0cl by blast
    qed

    have hClnmax_sub: "closure_on X TX (V nmax) \<subseteq> \<Inter>F"
    proof (rule subsetI)
      fix x
      assume hx: "x \<in> closure_on X TX (V nmax)"
      show "x \<in> \<Inter>F"
      proof (rule InterI)
        fix D
        assume hDF: "D \<in> F"
        obtain k where hkC: "k \<in> C" and hDeq: "D = closure_on X TX (V k)"
        proof -
          have hDimg: "D \<in> (\<lambda>n. closure_on X TX (V n)) ` C"
            unfolding hFeq[symmetric] using hDF by simp
          then obtain k where hkC: "k \<in> C" and hDeq: "D = (\<lambda>n. closure_on X TX (V n)) k"
            by blast
          show ?thesis
            by (rule that[OF hkC]) (simp only: hDeq)
        qed

        have hkle: "k \<le> nmax"
          unfolding nmax_def by (rule Max_ge[OF hCfin hkC])
        have hsub: "closure_on X TX (V nmax) \<subseteq> closure_on X TX (V k)"
          by (rule hCl_le[OF hkle])
        have "x \<in> closure_on X TX (V k)"
          by (rule subsetD[OF hsub hx])
        thus "x \<in> D"
          unfolding hDeq by simp
      qed
    qed

    obtain x0 where hx0: "x0 \<in> closure_on X TX (V nmax)"
      using hClnmax_ne by blast
    have "x0 \<in> \<Inter>F"
      by (rule subsetD[OF hClnmax_sub hx0])
    thus "\<Inter>F \<noteq> {}"
      by blast
  qed

  have hCompact_closed_FIP:
    "\<forall>\<C>. (\<forall>C\<in>\<C>. closedin_on X TX C) \<and>
         (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> \<C> \<longrightarrow> \<Inter>F \<noteq> {})
         \<longrightarrow> \<Inter>\<C> \<noteq> {}"
    by (rule iffD1[OF Theorem_26_9[OF hTop] hcomp])

  have hClosed_family: "\<forall>C\<in>range (\<lambda>n. closure_on X TX (V n)). closedin_on X TX C"
  proof (intro ballI)
    fix C
    assume hC: "C \<in> range (\<lambda>n. closure_on X TX (V n))"
    then obtain n where hCeq: "C = closure_on X TX (V n)"
      by blast
    show "closedin_on X TX C"
      unfolding hCeq using hCl_closed by blast
  qed

  have hInter: "\<Inter>(range (\<lambda>n. closure_on X TX (V n))) \<noteq> {}"
  proof -
    have hImp:
      "(\<forall>C\<in>range (\<lambda>n. closure_on X TX (V n)). closedin_on X TX C) \<and>
       (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> range (\<lambda>n. closure_on X TX (V n))
            \<longrightarrow> \<Inter>F \<noteq> {})
       \<longrightarrow> \<Inter>(range (\<lambda>n. closure_on X TX (V n))) \<noteq> {}"
      by (rule spec[OF hCompact_closed_FIP])
    have hPrem:
      "(\<forall>C\<in>range (\<lambda>n. closure_on X TX (V n)). closedin_on X TX C) \<and>
       (\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> range (\<lambda>n. closure_on X TX (V n))
            \<longrightarrow> \<Inter>F \<noteq> {})"
      by (intro conjI hClosed_family hFIP)
    show ?thesis
      by (rule mp[OF hImp hPrem])
  qed

  show ?thesis
    using hInter by simp
qed

(** from \S27 Theorem 27.7 [top1.tex:3519] **)
theorem Theorem_27_7:
  assumes hXne: "X \<noteq> {}"
  assumes hcomp: "top1_compact_on X TX"
  assumes hhaus: "is_hausdorff_on X TX"
  assumes hnoi: "\<forall>x\<in>X. \<not> top1_isolated_point_on X TX x"
  shows "\<not> countable X"
proof
  assume hcnt: "countable X"
  have hTop: "is_topology_on X TX"
    using hhaus unfolding is_hausdorff_on_def by blast
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTop[unfolded is_topology_on_def]]])

  obtain f :: "nat \<Rightarrow> 'a" where hfX: "\<forall>n. f n \<in> X" and hfimg: "f ` (UNIV :: nat set) = X"
    using top1_countable_nonempty_eq_image_nat[OF hcnt hXne] by blast

  define shrink where
    "shrink x U = (SOME V. V \<in> TX \<and> V \<subseteq> X \<and> V \<subseteq> U \<and> V \<noteq> {} \<and> x \<notin> closure_on X TX V)"
    for x U

  have shrink_spec:
    "\<And>x U. U \<in> TX \<Longrightarrow> U \<subseteq> X \<Longrightarrow> U \<noteq> {} \<Longrightarrow> x \<in> X \<Longrightarrow>
      shrink x U \<in> TX \<and> shrink x U \<subseteq> X \<and> shrink x U \<subseteq> U \<and> shrink x U \<noteq> {}
        \<and> x \<notin> closure_on X TX (shrink x U)"
  proof -
    fix x U
    assume hU: "U \<in> TX"
    assume hUX: "U \<subseteq> X"
    assume hUne: "U \<noteq> {}"
    assume hxX: "x \<in> X"
    have hex:
      "\<exists>V. V \<in> TX \<and> V \<subseteq> X \<and> V \<subseteq> U \<and> V \<noteq> {} \<and> x \<notin> closure_on X TX V"
      by (rule top1_27_7_shrink_open_avoid_closure[OF hhaus hnoi hU hUX hUne hxX])
    show
      "shrink x U \<in> TX \<and> shrink x U \<subseteq> X \<and> shrink x U \<subseteq> U \<and> shrink x U \<noteq> {}
        \<and> x \<notin> closure_on X TX (shrink x U)"
      unfolding shrink_def by (rule someI_ex[OF hex])
  qed

  define V where
    "V n = rec_nat (shrink (f 0) X) (\<lambda>n W. shrink (f (Suc n)) W) n"
    for n

  have hV_props:
    "\<forall>n. V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {} \<and> f n \<notin> closure_on X TX (V n)
      \<and> (n \<noteq> 0 \<longrightarrow> V n \<subseteq> V (n - 1))"
  proof (intro allI)
    fix n
    show
      "V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {} \<and> f n \<notin> closure_on X TX (V n)
        \<and> (n \<noteq> 0 \<longrightarrow> V n \<subseteq> V (n - 1))"
    proof (induction n)
      case 0
      have hV0: "V 0 = shrink (f 0) X"
        unfolding V_def by simp
      have hf0X: "f 0 \<in> X"
        using hfX by blast
      have hspec: "shrink (f 0) X \<in> TX \<and> shrink (f 0) X \<subseteq> X \<and> shrink (f 0) X \<subseteq> X \<and>
          shrink (f 0) X \<noteq> {} \<and> f 0 \<notin> closure_on X TX (shrink (f 0) X)"
        by (rule shrink_spec[OF X_TX subset_refl hXne hf0X])
      show ?case
        unfolding hV0
        using hspec by simp
    next
      case (Suc n)
      have hVn: "V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {} \<and> f n \<notin> closure_on X TX (V n)
        \<and> (n \<noteq> 0 \<longrightarrow> V n \<subseteq> V (n - 1))"
        by (rule Suc.IH)
      have hVnT: "V n \<in> TX"
        by (rule conjunct1[OF hVn])
      have hVnX: "V n \<subseteq> X"
        by (rule conjunct1[OF conjunct2[OF hVn]])
      have hVnNe: "V n \<noteq> {}"
        by (rule conjunct1[OF conjunct2[OF conjunct2[OF hVn]]])

      have hVSuc: "V (Suc n) = shrink (f (Suc n)) (V n)"
        unfolding V_def by simp
      have hfSucX: "f (Suc n) \<in> X"
        using hfX by blast

      have hspec: "shrink (f (Suc n)) (V n) \<in> TX \<and> shrink (f (Suc n)) (V n) \<subseteq> X \<and>
          shrink (f (Suc n)) (V n) \<subseteq> V n \<and> shrink (f (Suc n)) (V n) \<noteq> {} \<and>
          f (Suc n) \<notin> closure_on X TX (shrink (f (Suc n)) (V n))"
        by (rule shrink_spec[OF hVnT hVnX hVnNe hfSucX])

      have hVSnT: "V (Suc n) \<in> TX"
        unfolding hVSuc using hspec by blast
      have hVSnX: "V (Suc n) \<subseteq> X"
        unfolding hVSuc using hspec by blast
      have hVSnNe: "V (Suc n) \<noteq> {}"
        unfolding hVSuc using hspec by blast
      have hfSn_not: "f (Suc n) \<notin> closure_on X TX (V (Suc n))"
        unfolding hVSuc using hspec by blast
      have hVsh: "V (Suc n) \<subseteq> V n"
        unfolding hVSuc using hspec by blast

      show ?case
        by (intro conjI hVSnT conjI hVSnX conjI hVSnNe conjI hfSn_not conjI)
          (simp add: hVsh)
    qed
  qed

  have hVsubX: "\<forall>n. V n \<subseteq> X"
    using hV_props by blast
  have hVne: "\<forall>n. V n \<noteq> {}"
    using hV_props by blast
  have hVshrink: "\<forall>n. V (Suc n) \<subseteq> V n"
  proof (intro allI)
    fix n
    have hVSuc: "V (Suc n) = shrink (f (Suc n)) (V n)"
      unfolding V_def by simp
    have hVn: "V n \<in> TX \<and> V n \<subseteq> X \<and> V n \<noteq> {} \<and> f n \<notin> closure_on X TX (V n)
      \<and> (n \<noteq> 0 \<longrightarrow> V n \<subseteq> V (n - 1))"
      using hV_props by blast
    have hVnT: "V n \<in> TX"
      by (rule conjunct1[OF hVn])
    have hVnX: "V n \<subseteq> X"
      by (rule conjunct1[OF conjunct2[OF hVn]])
    have hVnNe: "V n \<noteq> {}"
      by (rule conjunct1[OF conjunct2[OF conjunct2[OF hVn]]])
    have hfSucX: "f (Suc n) \<in> X"
      using hfX by blast
    have hspec: "shrink (f (Suc n)) (V n) \<subseteq> V n"
      using shrink_spec[OF hVnT hVnX hVnNe hfSucX] by blast
    show "V (Suc n) \<subseteq> V n"
      unfolding hVSuc by (rule hspec)
  qed

  have hInt_ne:
    "\<Inter>(range (\<lambda>n. closure_on X TX (V n))) \<noteq> {}"
    by (rule top1_compact_nested_closure_inter_ne[OF hTop hcomp hVsubX hVne hVshrink])

  obtain x0 where hx0: "x0 \<in> \<Inter>(range (\<lambda>n. closure_on X TX (V n)))"
    using hInt_ne by blast

  have hx0X: "x0 \<in> X"
  proof -
    have hV0X: "V 0 \<subseteq> X"
      using hVsubX by blast
    have hcl0X: "closure_on X TX (V 0) \<subseteq> X"
      by (rule closure_on_subset_carrier[OF hTop hV0X])
    have hx0cl0: "x0 \<in> closure_on X TX (V 0)"
    proof -
      have "closure_on X TX (V 0) \<in> range (\<lambda>n. closure_on X TX (V n))"
        by blast
      thus ?thesis
        by (rule InterD[OF hx0])
    qed
    show ?thesis
      by (rule subsetD[OF hcl0X hx0cl0])
  qed

  have hx0img: "x0 \<in> f ` (UNIV :: nat set)"
    using hx0X by (simp add: hfimg)
  obtain n0 where hn0: "f n0 = x0"
    using hx0img by blast

  have hx0cln0: "x0 \<in> closure_on X TX (V n0)"
  proof -
    have "closure_on X TX (V n0) \<in> range (\<lambda>n. closure_on X TX (V n))"
      by blast
    thus ?thesis
      by (rule InterD[OF hx0])
  qed

  have hf_not_cl: "f n0 \<notin> closure_on X TX (V n0)"
  proof -
    have "V n0 \<in> TX \<and> V n0 \<subseteq> X \<and> V n0 \<noteq> {} \<and> f n0 \<notin> closure_on X TX (V n0)
      \<and> (n0 \<noteq> 0 \<longrightarrow> V n0 \<subseteq> V (n0 - 1))"
      using hV_props by blast
    thus ?thesis
      by blast
  qed

  show False
    using hf_not_cl hx0cln0 hn0 by simp
qed

(** from \S27 Corollary 27.8 [top1.tex:3543] **)
corollary Corollary_27_8:
  fixes a b :: real
  assumes hab: "a < b"
  shows "\<not> countable {a..b}"
text \<open>
  Proof status: admitted for now.

  Intended proof plan: specialize Theorem_27_7 to \<open>X = {a..b}\<close> with the standard order topology on reals, using
  known facts: closed intervals are compact and Hausdorff, and have no isolated points when \<open>a < b\<close>.

  Alternative (library) route: importing \<open>HOL-Analysis.Continuum_Not_Denumerable\<close> yields the lemma
  \<open>uncountable_closed_interval\<close>, which implies this statement immediately.  We keep this file on
  \<open>Complex_Main\<close> only, to avoid adding extra session dependencies.
\<close>
proof
  assume hcnt: "countable {a..b}"
  obtain h :: "real \<Rightarrow> nat" where hh: "inj_on h {a..b}"
    using hcnt unfolding countable_def by blast

  define enc where "enc = top1_interval_encode a b"
  have henc_inj: "inj_on enc (UNIV :: nat set set)"
    unfolding enc_def by (rule top1_interval_encode_inj[OF hab])
  have henc_sub: "enc ` (UNIV :: nat set set) \<subseteq> {a..b}"
  proof
    fix x
    assume hx: "x \<in> enc ` (UNIV :: nat set set)"
    then obtain S :: "nat set" where hS: "x = enc S"
      by blast
    show "x \<in> {a..b}"
      unfolding hS enc_def by (rule top1_interval_encode_mem_Icc[OF hab])
  qed

  have hcomp_inj: "inj_on (\<lambda>S. h (enc S)) (UNIV :: nat set set)"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix S T :: "nat set"
    assume hST: "h (enc S) = h (enc T)"
    have hS: "enc S \<in> {a..b}"
      using henc_sub by blast
    have hT: "enc T \<in> {a..b}"
      using henc_sub by blast
    have "enc S = enc T"
      using hh hS hT hST unfolding inj_on_def by blast
    thus "S = T"
      using henc_inj unfolding inj_on_def by blast
  qed

  have "countable (UNIV :: nat set set)"
    unfolding countable_def
    by (rule exI[where x="\<lambda>S. h (enc S)"], rule hcomp_inj)
  thus False
    using top1_not_countable_UNIV_nat_set by blast
qed

section \<open>\<S>28 Limit Point Compactness\<close>

(** from \S28 Definition (Limit point compactness) [top1.tex:3588] **)
definition top1_limit_point_compact_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_limit_point_compact_on X T \<longleftrightarrow>
     is_topology_on X T \<and>
     (\<forall>A. A \<subseteq> X \<and> infinite A \<longrightarrow> (\<exists>x\<in>X. is_limit_point_of x A X T))"

(** from \S28 Theorem 28.1 (Compact \<Longrightarrow> limit point compact) [top1.tex:~3600] **)
theorem Theorem_28_1:
  assumes hcomp: "top1_compact_on X T"
  shows "top1_limit_point_compact_on X T"
proof -
  have hTop: "is_topology_on X T"
    using hcomp unfolding top1_compact_on_def by blast

  have hCompactCover:
    "\<forall>Uc. Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  show ?thesis
    unfolding top1_limit_point_compact_on_def
  proof (intro conjI)
    show "is_topology_on X T"
      by (rule hTop)

    show "\<forall>A. A \<subseteq> X \<and> infinite A \<longrightarrow> (\<exists>x\<in>X. is_limit_point_of x A X T)"
    proof (intro allI impI)
      fix A
      assume hA: "A \<subseteq> X \<and> infinite A"
      have hAX: "A \<subseteq> X"
        using hA by blast
      have hAinf: "infinite A"
        using hA by blast

      show "\<exists>x\<in>X. is_limit_point_of x A X T"
      proof (rule ccontr)
        assume hno: "\<not> (\<exists>x\<in>X. is_limit_point_of x A X T)"
        have hno_all: "\<forall>x\<in>X. \<not> is_limit_point_of x A X T"
          using hno by blast

        have hlp_empty: "limit_points_of A X T = {}"
        proof (rule equalityI)
          show "limit_points_of A X T \<subseteq> {}"
          proof (rule subsetI)
            fix x assume hx: "x \<in> limit_points_of A X T"
            have hxX: "x \<in> X"
              using hx unfolding limit_points_of_def by blast
            have hxlp: "is_limit_point_of x A X T"
              using hx unfolding limit_points_of_def by blast
            have "\<not> is_limit_point_of x A X T"
              using hno_all hxX by blast
            thus "x \<in> {}"
              using hxlp by blast
          qed
          show "{} \<subseteq> limit_points_of A X T"
            by simp
        qed

        have hAcl: "closedin_on X T A"
        proof -
          have "limit_points_of A X T \<subseteq> A"
            using hlp_empty by simp
          thus ?thesis
            by (rule iffD2[OF Corollary_17_7[OF hTop hAX]])
        qed
        have hXmA_open: "X - A \<in> T"
          by (rule closedin_diff_open[OF hAcl])

        have ex_U:
          "\<forall>a\<in>A. \<exists>U. neighborhood_of a X T U \<and> (U - {a}) \<inter> A = {}"
        proof (intro ballI)
          fix a assume haA: "a \<in> A"
          have haX: "a \<in> X"
            using hAX haA by blast
          have hnlim: "\<not> is_limit_point_of a A X T"
            using hno_all haX by blast
          have ex: "\<exists>U. neighborhood_of a X T U \<and> \<not> intersects (U - {a}) A"
          proof -
            have "\<not> (\<forall>U. neighborhood_of a X T U \<longrightarrow> intersects (U - {a}) A)"
              using hnlim haX hAX unfolding is_limit_point_of_def by blast
            thus ?thesis by blast
          qed
          obtain U where hnb: "neighborhood_of a X T U" and hnot: "\<not> intersects (U - {a}) A"
            using ex by blast
          have hdisj: "(U - {a}) \<inter> A = {}"
            using hnot unfolding intersects_def by blast
          show "\<exists>U. neighborhood_of a X T U \<and> (U - {a}) \<inter> A = {}"
            by (rule exI[where x=U], intro conjI, rule hnb, rule hdisj)
        qed

        obtain f where hf:
          "\<forall>a\<in>A. neighborhood_of a X T (f a) \<and> (f a - {a}) \<inter> A = {}"
          using bchoice[OF ex_U] by blast

        define Uc where "Uc = insert (X - A) (f ` A)"

        have hUc_subT: "Uc \<subseteq> T"
        proof (rule subsetI)
          fix U assume hU: "U \<in> Uc"
          have h_cases: "U = X - A \<or> U \<in> f ` A"
            using hU unfolding Uc_def by blast
          show "U \<in> T"
          proof (rule disjE[OF h_cases])
            assume "U = X - A"
            thus "U \<in> T"
              using hXmA_open by simp
          next
            assume hUfA: "U \<in> f ` A"
            then obtain a where haA: "a \<in> A" and hUeq: "U = f a"
              by blast
            have "neighborhood_of a X T (f a)"
              using hf haA by blast
            hence "f a \<in> T"
              unfolding neighborhood_of_def by blast
            thus "U \<in> T"
              using hUeq by simp
          qed
        qed

        have hX_sub_Uc: "X \<subseteq> \<Union>Uc"
        proof (rule subsetI)
          fix x assume hxX: "x \<in> X"
          show "x \<in> \<Union>Uc"
          proof (cases "x \<in> A")
            case True
            have hxA: "x \<in> A" using True .
            have "neighborhood_of x X T (f x)"
              using hf hxA by blast
            hence hxfx: "x \<in> f x"
              unfolding neighborhood_of_def by blast
            have "f x \<in> f ` A"
              by (rule imageI[OF hxA])
            hence "f x \<in> Uc"
              unfolding Uc_def by blast
            thus ?thesis
              using hxfx by blast
          next
            case False
            have hxXmA: "x \<in> X - A"
              using hxX False by blast
            have "X - A \<in> Uc"
              unfolding Uc_def by blast
            thus ?thesis
              using hxXmA by blast
          qed
        qed

        have hUc_cover: "Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc"
          by (intro conjI hUc_subT hX_sub_Uc)
        obtain F where hFfin: "finite F" and hFsub: "F \<subseteq> Uc" and hFcov: "X \<subseteq> \<Union>F"
          using hCompactCover[rule_format, of Uc] hUc_cover by blast

        define G where "G = F - {X - A}"

        have hGfin: "finite G"
          unfolding G_def using hFfin by simp

        have hA_sub_UnionG: "A \<subseteq> \<Union>G"
        proof (rule subsetI)
          fix a assume haA: "a \<in> A"
          have haX: "a \<in> X" using hAX haA by blast
          have haUF: "a \<in> \<Union>F"
            using hFcov haX by blast
          then obtain U where hUF: "U \<in> F" and haU: "a \<in> U"
            by blast
          have hU_not: "U \<noteq> X - A"
          proof
            assume hUeq: "U = X - A"
            have "a \<in> X - A"
              using haU hUeq by simp
            thus False using haA by blast
          qed
          have hUG: "U \<in> G"
            unfolding G_def using hUF hU_not by blast
          show "a \<in> \<Union>G"
            using hUG haU by blast
        qed

        have hG_sub_fA: "G \<subseteq> f ` A"
        proof (rule subsetI)
          fix U assume hUG: "U \<in> G"
          have hUF: "U \<in> F"
            using hUG unfolding G_def by blast
          have hU_Uc: "U \<in> Uc"
            using hFsub hUF by blast
          have hU_cases: "U = X - A \<or> U \<in> f ` A"
            using hU_Uc unfolding Uc_def by blast
          show "U \<in> f ` A"
          proof (rule disjE[OF hU_cases])
            assume hUeq: "U = X - A"
            have "U \<noteq> X - A"
              using hUG unfolding G_def by blast
            thus "U \<in> f ` A"
              using hUeq by blast
          next
            assume "U \<in> f ` A"
            thus "U \<in> f ` A" .
          qed
        qed

        have hUA_finite: "\<forall>U\<in>G. finite (U \<inter> A)"
        proof (intro ballI)
          fix U assume hUG: "U \<in> G"
          have hUfA: "U \<in> f ` A"
            using hG_sub_fA hUG by blast
          obtain a0 where ha0A: "a0 \<in> A" and hUeq: "U = f a0"
            using hUfA by blast
          have hdisj: "(f a0 - {a0}) \<inter> A = {}"
            using hf ha0A by blast
          have hsub: "U \<inter> A \<subseteq> {a0}"
          proof (rule subsetI)
            fix x assume hx: "x \<in> U \<inter> A"
            have hxU: "x \<in> U" and hxA: "x \<in> A"
              using hx by blast+
            have hxU0: "x \<in> f a0"
              using hxU hUeq by simp
            show "x \<in> {a0}"
            proof (cases "x = a0")
              case True
              thus ?thesis by simp
            next
              case False
              have hx_in: "x \<in> (f a0 - {a0}) \<inter> A"
                using hxU0 hxA False by blast
              show ?thesis
                using hdisj hx_in by blast
            qed
          qed
          have hsing: "finite {a0}" by simp
          show "finite (U \<inter> A)"
            by (rule finite_subset[OF hsub hsing])
        qed

        define H where "H = (\<lambda>U. U \<inter> A) ` G"

        have hHfin: "finite H"
          unfolding H_def using hGfin by simp

        have hHall_fin: "\<And>S. S \<in> H \<Longrightarrow> finite S"
        proof -
          fix S assume hS: "S \<in> H"
          then obtain U where hUG: "U \<in> G" and hSeq: "S = U \<inter> A"
            unfolding H_def by blast
          have "finite (U \<inter> A)"
            using hUA_finite hUG by blast
          thus "finite S"
            using hSeq by simp
        qed

        have hUnionH_fin: "finite (\<Union>H)"
          by (rule finite_Union[OF hHfin hHall_fin])

        have hA_sub_UnionH: "A \<subseteq> \<Union>H"
        proof (rule subsetI)
          fix a assume haA: "a \<in> A"
          have haG: "a \<in> \<Union>G"
            using hA_sub_UnionG haA by blast
          then obtain U where hUG: "U \<in> G" and haU: "a \<in> U"
            by blast
          have hS_in: "U \<inter> A \<in> H"
            unfolding H_def by (rule imageI[OF hUG])
          have ha_in: "a \<in> U \<inter> A"
            using haU haA by blast
          show "a \<in> \<Union>H"
            using hS_in ha_in by blast
        qed

        have hAfin: "finite A"
          by (rule finite_subset[OF hA_sub_UnionH hUnionH_fin])

        show False
          using hAinf hAfin by blast
      qed
    qed
  qed
qed

section \<open>\<S>29 Local Compactness\<close>

definition top1_locally_compact_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_locally_compact_on X T \<longleftrightarrow>
     is_topology_on X T \<and>
     (\<forall>x\<in>X. \<exists>U. neighborhood_of x X T U \<and> U \<subseteq> X
        \<and> top1_compact_on (closure_on X T U) (subspace_topology X T (closure_on X T U)))"

(** Closure of the carrier is the carrier. **)
lemma closure_on_carrier:
  assumes hT: "is_topology_on X T"
  shows "closure_on X T X = X"
proof (rule equalityI)
  have empty_T: "{} \<in> T"
    by (rule conjunct1[OF hT[unfolded is_topology_on_def]])
  have X_closed: "closedin_on X T X"
    apply (rule closedin_intro)
     apply (rule subset_refl)
    apply (simp only: Diff_cancel)
    apply (rule empty_T)
    done
  show "closure_on X T X \<subseteq> X"
    by (rule closure_on_subset_of_closed[OF X_closed subset_refl])
  show "X \<subseteq> closure_on X T X"
    by (rule subset_closure_on)
qed

(** Compact spaces are locally compact (choose \<open>X\<close> as neighborhood). **)
lemma top1_compact_on_imp_locally_compact_on:
  assumes hcomp: "top1_compact_on X T"
  shows "top1_locally_compact_on X T"
proof -
  have hT: "is_topology_on X T"
    using hcomp unfolding top1_compact_on_def by blast
  have hCover:
    "\<forall>Uc. Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
    using hcomp unfolding top1_compact_on_def by blast

  have hcomp_sub: "top1_compact_on X (subspace_topology X T X)"
  proof -
    have hIff:
      "top1_compact_on X (subspace_topology X T X)
        \<longleftrightarrow> (\<forall>Uc. Uc \<subseteq> T \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F))"
      by (rule Lemma_26_1[OF hT subset_refl])
    show ?thesis
      by (rule iffD2[OF hIff hCover])
  qed

  show ?thesis
    unfolding top1_locally_compact_on_def
  proof (intro conjI)
    show "is_topology_on X T"
      by (rule hT)
    show "\<forall>x\<in>X. \<exists>U. neighborhood_of x X T U \<and> U \<subseteq> X
      \<and> top1_compact_on (closure_on X T U) (subspace_topology X T (closure_on X T U))"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have X_T: "X \<in> T"
        by (rule conjunct1[OF conjunct2[OF hT[unfolded is_topology_on_def]]])
      have hnbhd: "neighborhood_of x X T X"
        unfolding neighborhood_of_def using X_T hxX by blast
      show "\<exists>U. neighborhood_of x X T U \<and> U \<subseteq> X
        \<and> top1_compact_on (closure_on X T U) (subspace_topology X T (closure_on X T U))"
        apply (rule exI[where x=X])
        apply (intro conjI)
          apply (rule hnbhd)
         apply (rule subset_refl)
        apply (simp only: closure_on_carrier[OF hT])
        apply (rule hcomp_sub)
        done
    qed
  qed
qed

(** Local compactness is preserved by homeomorphisms (one direction). **)
lemma top1_locally_compact_on_of_homeomorphism_on:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
  assumes hLCY: "top1_locally_compact_on Y TY"
  shows "top1_locally_compact_on X TX"
proof -
  define g where "g = inv_into X f"

  have hTopX: "is_topology_on X TX"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hTopY: "is_topology_on Y TY"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hbij: "bij_betw f X Y"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hinj: "inj_on f X"
    using hbij unfolding bij_betw_def by blast

  have hcontf: "top1_continuous_map_on X TX Y TY f"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hcontg: "top1_continuous_map_on Y TY X TX g"
    using hhomeo unfolding top1_homeomorphism_on_def g_def by blast

  have hmapf: "\<forall>x\<in>X. f x \<in> Y"
    using hcontf unfolding top1_continuous_map_on_def by blast
  have hcl_f:
    "\<forall>A. A \<subseteq> X \<longrightarrow> f ` (closure_on X TX A) \<subseteq> closure_on Y TY (f ` A)"
  proof -
    have hiff:
      "top1_continuous_map_on X TX Y TY f \<longleftrightarrow>
         ((\<forall>x\<in>X. f x \<in> Y)
           \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> f ` (closure_on X TX A) \<subseteq> closure_on Y TY (f ` A)))"
      by (rule Theorem_18_1(1)[OF hTopX hTopY])
    have hprops:
      "(\<forall>x\<in>X. f x \<in> Y)
        \<and> (\<forall>A. A \<subseteq> X \<longrightarrow> f ` (closure_on X TX A) \<subseteq> closure_on Y TY (f ` A))"
      by (rule iffD1[OF hiff hcontf])
    show ?thesis
      by (rule conjunct2[OF hprops])
  qed

  have hcl_g:
    "\<forall>A. A \<subseteq> Y \<longrightarrow> g ` (closure_on Y TY A) \<subseteq> closure_on X TX (g ` A)"
  proof -
    have hiff:
      "top1_continuous_map_on Y TY X TX g \<longleftrightarrow>
         ((\<forall>y\<in>Y. g y \<in> X)
           \<and> (\<forall>A. A \<subseteq> Y \<longrightarrow> g ` (closure_on Y TY A) \<subseteq> closure_on X TX (g ` A)))"
      by (rule Theorem_18_1(1)[OF hTopY hTopX])
    have hprops:
      "(\<forall>y\<in>Y. g y \<in> X)
        \<and> (\<forall>A. A \<subseteq> Y \<longrightarrow> g ` (closure_on Y TY A) \<subseteq> closure_on X TX (g ` A))"
      by (rule iffD1[OF hiff hcontg])
    show ?thesis
      by (rule conjunct2[OF hprops])
  qed

  show ?thesis
    unfolding top1_locally_compact_on_def
  proof (intro conjI)
    show "is_topology_on X TX"
      by (rule hTopX)
    show "\<forall>x\<in>X. \<exists>U. neighborhood_of x X TX U \<and> U \<subseteq> X
      \<and> top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
    proof (intro ballI)
      fix x assume hxX: "x \<in> X"
      have hyY: "f x \<in> Y"
        using hmapf hxX by blast

      have hLCY_ex:
        "\<forall>y\<in>Y. \<exists>U. neighborhood_of y Y TY U \<and> U \<subseteq> Y
          \<and> top1_compact_on (closure_on Y TY U) (subspace_topology Y TY (closure_on Y TY U))"
        using hLCY unfolding top1_locally_compact_on_def by blast

      obtain V where
        hVnbhd: "neighborhood_of (f x) Y TY V"
        and hVY: "V \<subseteq> Y"
        and hVcomp: "top1_compact_on (closure_on Y TY V) (subspace_topology Y TY (closure_on Y TY V))"
        using hLCY_ex hyY by blast

      have hVTY: "V \<in> TY"
        using hVnbhd unfolding neighborhood_of_def by blast
      have hfxV: "f x \<in> V"
        using hVnbhd unfolding neighborhood_of_def by blast

      define U where "U = {x\<in>X. f x \<in> V}"
      have hUTX: "U \<in> TX"
        unfolding U_def using hcontf hVTY unfolding top1_continuous_map_on_def by blast
      have hxU: "x \<in> U"
        unfolding U_def using hxX hfxV by blast
      have hUX: "U \<subseteq> X"
        unfolding U_def by blast

      have hUnbhd: "neighborhood_of x X TX U"
        unfolding neighborhood_of_def using hUTX hxU by blast

      have hfU_eq_V: "f ` U = V"
      proof (rule equalityI)
        show "f ` U \<subseteq> V"
          unfolding U_def by blast
        show "V \<subseteq> f ` U"
        proof (rule subsetI)
          fix y assume hyV: "y \<in> V"
          have hyY': "y \<in> Y"
            using hVY hyV by blast
          have hyImg: "y \<in> f ` X"
            using hbij hyY' unfolding bij_betw_def by blast
          obtain x0 where hx0X: "x0 \<in> X" and hf0: "f x0 = y"
            using hyImg by blast
          have hx0U: "x0 \<in> U"
            unfolding U_def using hx0X hf0 hyV by blast
          show "y \<in> f ` U"
            using hx0U hf0 by blast
        qed
      qed

      have hclYX: "closure_on Y TY V \<subseteq> Y"
        by (rule closure_on_subset_carrier[OF hTopY hVY])

      have hclX_sub: "closure_on X TX U \<subseteq> X"
        by (rule closure_on_subset_carrier[OF hTopX hUX])

      have hclosure_eq: "closure_on X TX U = g ` (closure_on Y TY V)"
      proof (rule equalityI)
        show "closure_on X TX U \<subseteq> g ` (closure_on Y TY V)"
        proof (rule subsetI)
          fix x' assume hx': "x' \<in> closure_on X TX U"
          have hx'X: "x' \<in> X"
            using hclX_sub hx' by blast
          have hfx'cl: "f x' \<in> closure_on Y TY V"
          proof -
            have himg: "f x' \<in> f ` (closure_on X TX U)"
              using hx' by blast
            have "f ` (closure_on X TX U) \<subseteq> closure_on Y TY (f ` U)"
              by (rule hcl_f[rule_format, OF hUX])
            have "f x' \<in> closure_on Y TY (f ` U)"
              using himg \<open>f ` (closure_on X TX U) \<subseteq> closure_on Y TY (f ` U)\<close> by blast
            thus ?thesis
              using hfU_eq_V by simp
          qed
          have hx'eq: "g (f x') = x'"
            unfolding g_def by (rule inv_into_f_f[OF hinj hx'X])
          show "x' \<in> g ` (closure_on Y TY V)"
          proof -
            have "g (f x') \<in> g ` (closure_on Y TY V)"
              using hfx'cl by blast
            thus ?thesis
              using hx'eq by simp
          qed
        qed
        show "g ` (closure_on Y TY V) \<subseteq> closure_on X TX U"
        proof -
          have "g ` (closure_on Y TY V) \<subseteq> closure_on X TX (g ` V)"
            by (rule hcl_g[rule_format, OF hVY])
          moreover have "g ` V = U"
          proof (rule equalityI)
            show "g ` V \<subseteq> U"
            proof (rule subsetI)
              fix x' assume hx': "x' \<in> g ` V"
              obtain y where hyV: "y \<in> V" and hx'eq: "x' = g y"
                using hx' by blast
              have hyY': "y \<in> Y"
                using hVY hyV by blast
              have hx'X: "x' \<in> X"
                using hcontg hyY' hx'eq unfolding top1_continuous_map_on_def by blast
              have hfgy: "f (g y) = y"
              proof -
                have hyImg: "y \<in> f ` X"
                  using hbij hyY' unfolding bij_betw_def by simp
                show ?thesis
                  unfolding g_def by (rule f_inv_into_f[OF hyImg])
              qed
              have hfx'V: "f x' \<in> V"
                using hyV hx'eq hfgy by simp
              show "x' \<in> U"
                unfolding U_def using hx'X hfx'V by blast
            qed
            show "U \<subseteq> g ` V"
            proof (rule subsetI)
              fix x' assume hx'U: "x' \<in> U"
              have hx'X: "x' \<in> X" and hfx'V: "f x' \<in> V"
                using hx'U unfolding U_def by blast+
              have hx'eq: "g (f x') = x'"
                unfolding g_def by (rule inv_into_f_f[OF hinj hx'X])
              show "x' \<in> g ` V"
              proof -
                have "g (f x') \<in> g ` V"
                  using hfx'V by blast
                thus ?thesis
                  using hx'eq by simp
              qed
            qed
          qed
          ultimately show "g ` (closure_on Y TY V) \<subseteq> closure_on X TX U"
            by simp
        qed
      qed

      have hcontg_res:
        "top1_continuous_map_on (closure_on Y TY V) (subspace_topology Y TY (closure_on Y TY V)) X TX g"
      proof -
        have hA: "closure_on Y TY V \<subseteq> Y"
          by (rule hclYX)
        have hThm:
          "(\<forall>A f. top1_continuous_map_on Y TY X TX f \<and> A \<subseteq> Y
                \<longrightarrow> top1_continuous_map_on A (subspace_topology Y TY A) X TX f)"
          by (rule Theorem_18_2(4)[OF hTopY hTopX hTopX])
        have "top1_continuous_map_on Y TY X TX g \<and> closure_on Y TY V \<subseteq> Y"
          using hcontg hA by blast
        have "top1_continuous_map_on (closure_on Y TY V) (subspace_topology Y TY (closure_on Y TY V)) X TX g"
          using hThm \<open>top1_continuous_map_on Y TY X TX g \<and> closure_on Y TY V \<subseteq> Y\<close> by blast
        thus ?thesis .
      qed

      have hcomp_closureU:
        "top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
      proof -
        have hCompImg:
          "top1_compact_on (g ` (closure_on Y TY V)) (subspace_topology X TX (g ` (closure_on Y TY V)))"
        proof -
          have hcompDom:
            "top1_compact_on (closure_on Y TY V) (subspace_topology Y TY (closure_on Y TY V))"
            using hVcomp .
          have "top1_compact_on (g ` (closure_on Y TY V)) (subspace_topology X TX (g ` (closure_on Y TY V)))"
            by (rule top1_compact_on_continuous_image[OF hcompDom hTopX hcontg_res])
          thus ?thesis .
        qed
        show ?thesis
          using hCompImg hclosure_eq by simp
      qed

      show "\<exists>U. neighborhood_of x X TX U \<and> U \<subseteq> X
        \<and> top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
        apply (rule exI[where x=U])
        apply (intro conjI)
          apply (rule hUnbhd)
         apply (rule hUX)
        apply (rule hcomp_closureU)
        done
    qed
  qed
qed

(** Hausdorffness is preserved by homeomorphisms (pull back separating neighborhoods). **)
lemma is_hausdorff_on_of_homeomorphism_on:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
  assumes hHausY: "is_hausdorff_on Y TY"
  shows "is_hausdorff_on X TX"
proof -
  have hTopX: "is_topology_on X TX"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hbij: "bij_betw f X Y"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hinj: "inj_on f X"
    using hbij unfolding bij_betw_def by blast
  have hcontf: "top1_continuous_map_on X TX Y TY f"
    using hhomeo unfolding top1_homeomorphism_on_def by blast
  have hpre: "\<forall>V\<in>TY. {x \<in> X. f x \<in> V} \<in> TX"
    using hcontf unfolding top1_continuous_map_on_def by blast

  have hausdY:
    "\<forall>a\<in>Y. \<forall>b\<in>Y. a \<noteq> b \<longrightarrow>
       (\<exists>U V. neighborhood_of a Y TY U \<and> neighborhood_of b Y TY V \<and> U \<inter> V = {})"
    using hHausY unfolding is_hausdorff_on_def by blast

  show ?thesis
    unfolding is_hausdorff_on_def
  proof (intro conjI)
    show "is_topology_on X TX"
      by (rule hTopX)
    show "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
       (\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
    proof (intro ballI impI)
      fix x y
      assume hxX: "x \<in> X"
      assume hyX: "y \<in> X"
      assume hxy: "x \<noteq> y"

      have hfxY: "f x \<in> Y"
        using hbij hxX unfolding bij_betw_def by blast
      have hfyY: "f y \<in> Y"
        using hbij hyX unfolding bij_betw_def by blast
      have hfxy: "f x \<noteq> f y"
        using hinj hxX hyX hxy unfolding inj_on_def by blast

      obtain U0 V0 where
        hU0: "neighborhood_of (f x) Y TY U0"
        and hV0: "neighborhood_of (f y) Y TY V0"
        and hdisj: "U0 \<inter> V0 = {}"
        using hausdY hfxY hfyY hfxy by blast

      have hU0TY: "U0 \<in> TY"
        using hU0 unfolding neighborhood_of_def by blast
      have hV0TY: "V0 \<in> TY"
        using hV0 unfolding neighborhood_of_def by blast
      have hfxU0: "f x \<in> U0"
        using hU0 unfolding neighborhood_of_def by blast
      have hfyV0: "f y \<in> V0"
        using hV0 unfolding neighborhood_of_def by blast

      define U where "U = {u \<in> X. f u \<in> U0}"
      define V where "V = {u \<in> X. f u \<in> V0}"
      have hUTX: "U \<in> TX"
        unfolding U_def using hpre hU0TY by blast
      have hVTX: "V \<in> TX"
        unfolding V_def using hpre hV0TY by blast
      have hxU: "x \<in> U"
        unfolding U_def using hxX hfxU0 by blast
      have hyV: "y \<in> V"
        unfolding V_def using hyX hfyV0 by blast

      have hUVdisj: "U \<inter> V = {}"
      proof (rule equalityI)
        show "U \<inter> V \<subseteq> {}"
        proof (rule subsetI)
          fix u
          assume hu: "u \<in> U \<inter> V"
          have hfuU0: "f u \<in> U0"
            using hu unfolding U_def by blast
          have hfuV0: "f u \<in> V0"
            using hu unfolding V_def by blast
          have "f u \<in> U0 \<inter> V0"
            using hfuU0 hfuV0 by blast
          thus "u \<in> {}"
            using hdisj by blast
        qed
        show "{} \<subseteq> U \<inter> V"
          by blast
      qed

      have hnbx: "neighborhood_of x X TX U"
        unfolding neighborhood_of_def
        apply (rule conjI)
         apply (rule hUTX)
        apply (rule hxU)
        done
      have hnby: "neighborhood_of y X TX V"
        unfolding neighborhood_of_def
        apply (rule conjI)
         apply (rule hVTX)
        apply (rule hyV)
        done

      show "\<exists>U0 V0. neighborhood_of x X TX U0 \<and> neighborhood_of y X TX V0 \<and> U0 \<inter> V0 = {}"
        apply (rule exI[where x=U])
        apply (rule exI[where x=V])
        apply (rule conjI)
         apply (rule hnbx)
        apply (rule conjI)
         apply (rule hnby)
        apply (rule hUVdisj)
        done
    qed
  qed
qed

(** In a compact Hausdorff space, one can shrink an open neighborhood to an open neighborhood with compact closure
    contained in the original neighborhood. **)
lemma compact_hausdorff_shrink_into_open:
  assumes hComp: "top1_compact_on Y TY"
  assumes hHaus: "is_hausdorff_on Y TY"
  assumes hO0: "O0 \<in> TY"
  assumes hO0Y: "O0 \<subseteq> Y"
  assumes hxO0: "x \<in> O0"
  shows "\<exists>U. neighborhood_of x Y TY U \<and> U \<subseteq> O0 \<and> closure_on Y TY U \<subseteq> O0
            \<and> top1_compact_on (closure_on Y TY U) (subspace_topology Y TY (closure_on Y TY U))"
proof -
  have hTopY: "is_topology_on Y TY"
    using hComp unfolding top1_compact_on_def by blast
  have Y_TY: "Y \<in> TY"
    by (rule conjunct1[OF conjunct2[OF hTopY[unfolded is_topology_on_def]]])

  have hxY: "x \<in> Y"
    using hO0Y hxO0 by blast

  define K where "K = Y - O0"
  have hKY: "K \<subseteq> Y"
    unfolding K_def by blast
  have hxK: "x \<notin> K"
    unfolding K_def using hxO0 by blast

  have hKclosed: "closedin_on Y TY K"
  proof (rule closedin_intro)
    show "K \<subseteq> Y"
      by (rule hKY)
    have hEq: "Y - K = O0"
      unfolding K_def using hO0Y by blast
    show "Y - K \<in> TY"
      using hO0 hEq by simp
  qed

  have hKcomp: "top1_compact_on K (subspace_topology Y TY K)"
    by (rule Theorem_26_2[OF hComp hKclosed])

  obtain U0 V0 where
    hU0: "U0 \<in> TY"
    and hV0: "V0 \<in> TY"
    and hxU0: "x \<in> U0"
    and hKsubV0: "K \<subseteq> V0"
    and hdisj: "U0 \<inter> V0 = {}"
    using Lemma_26_4[OF hHaus hKY hKcomp hxY hxK] by blast

  define U where "U = O0 \<inter> U0"

  have hU_TY: "U \<in> TY"
    unfolding U_def by (rule topology_inter2[OF hTopY hO0 hU0])
  have hxU: "x \<in> U"
    unfolding U_def using hxO0 hxU0 by blast
  have hUnb: "neighborhood_of x Y TY U"
    unfolding neighborhood_of_def using hU_TY hxU by blast

  have hUsubO0: "U \<subseteq> O0"
    unfolding U_def by blast
  have hUsubY: "U \<subseteq> Y"
    using hUsubO0 hO0Y by blast

  define C where "C = Y - V0"
  have hC_closed: "closedin_on Y TY C"
  proof (rule closedin_intro)
    show "C \<subseteq> Y"
      unfolding C_def by blast
    have hEq: "Y - C = Y \<inter> V0"
      unfolding C_def by blast
    have "Y \<inter> V0 \<in> TY"
      by (rule topology_inter2[OF hTopY Y_TY hV0])
    thus "Y - C \<in> TY"
      using hEq by simp
  qed

  have hUsubC: "U \<subseteq> C"
  proof (rule subsetI)
    fix z assume hzU: "z \<in> U"
    have hzY: "z \<in> Y"
      using hUsubY hzU by blast
    have hzNotV0: "z \<notin> V0"
    proof
      assume hzV0: "z \<in> V0"
      have hzU0: "z \<in> U0"
        using hzU unfolding U_def by blast
      have "z \<in> U0 \<inter> V0"
        using hzU0 hzV0 by blast
      thus False
        using hdisj by blast
    qed
    show "z \<in> C"
      unfolding C_def using hzY hzNotV0 by blast
  qed

  have hclU_sub_C: "closure_on Y TY U \<subseteq> C"
    by (rule closure_on_subset_of_closed[OF hC_closed hUsubC])

  have hCsubO0: "C \<subseteq> O0"
  proof -
    have hsub: "Y - V0 \<subseteq> Y - K"
    proof (rule subsetI)
      fix z assume hz: "z \<in> Y - V0"
      have hzY: "z \<in> Y" and hzNotV0: "z \<notin> V0"
        using hz by blast+
      have hzNotK: "z \<notin> K"
      proof
        assume hzK: "z \<in> K"
        have "z \<in> V0"
          using hKsubV0 hzK by blast
        thus False
          using hzNotV0 by blast
      qed
      show "z \<in> Y - K"
        using hzY hzNotK by blast
    qed
    have hEq: "Y - K = O0"
      unfolding K_def using hO0Y by blast
    show ?thesis
      unfolding C_def using hsub hEq by simp
  qed

  have hclU_sub_O0: "closure_on Y TY U \<subseteq> O0"
    by (rule subset_trans[OF hclU_sub_C hCsubO0])

  have hclU_closed: "closedin_on Y TY (closure_on Y TY U)"
    by (rule closure_on_closed[OF hTopY hUsubY])
  have hclU_comp: "top1_compact_on (closure_on Y TY U) (subspace_topology Y TY (closure_on Y TY U))"
    by (rule Theorem_26_2[OF hComp hclU_closed])

  show ?thesis
    apply (rule exI[where x=U])
    apply (intro conjI)
       apply (rule hUnb)
      apply (rule hUsubO0)
     apply (rule hclU_sub_O0)
    apply (rule hclU_comp)
    done
qed

(** Open subspaces of compact Hausdorff spaces are locally compact. **)
lemma top1_locally_compact_on_open_subspace_of_compact_hausdorff:
  assumes hComp: "top1_compact_on Y TY"
  assumes hHaus: "is_hausdorff_on Y TY"
  assumes hO0: "O0 \<in> TY"
  assumes hO0Y: "O0 \<subseteq> Y"
  shows "top1_locally_compact_on O0 (subspace_topology Y TY O0)"
proof -
  have hTopY: "is_topology_on Y TY"
    using hComp unfolding top1_compact_on_def by blast
  let ?TO = "subspace_topology Y TY O0"
  have hTopO: "is_topology_on O0 ?TO"
    by (rule subspace_topology_is_topology_on[OF hTopY hO0Y])

  show ?thesis
    unfolding top1_locally_compact_on_def
  proof (intro conjI)
    show "is_topology_on O0 ?TO"
      by (rule hTopO)
    show "\<forall>x\<in>O0. \<exists>U. neighborhood_of x O0 ?TO U \<and> U \<subseteq> O0
      \<and> top1_compact_on (closure_on O0 ?TO U) (subspace_topology O0 ?TO (closure_on O0 ?TO U))"
    proof (intro ballI)
      fix x assume hxO0: "x \<in> O0"
      obtain U where
        hUnb: "neighborhood_of x Y TY U"
        and hUsubO: "U \<subseteq> O0"
        and hclUsubO: "closure_on Y TY U \<subseteq> O0"
        and hclUcomp: "top1_compact_on (closure_on Y TY U) (subspace_topology Y TY (closure_on Y TY U))"
        using compact_hausdorff_shrink_into_open[OF hComp hHaus hO0 hO0Y hxO0] by blast

      have hUsubY: "U \<subseteq> Y"
        using hUsubO hO0Y by blast

      have hU_TO: "U \<in> ?TO"
        unfolding subspace_topology_def
        apply (rule CollectI)
        apply (rule exI[where x=U])
        apply (intro conjI)
         apply (simp add: hUsubO Int_absorb1)
        apply (rule conjunct1[OF hUnb[unfolded neighborhood_of_def]])
        done
      have hxU: "x \<in> U"
        using hUnb unfolding neighborhood_of_def by blast

      have hUnbO: "neighborhood_of x O0 ?TO U"
        unfolding neighborhood_of_def using hU_TO hxU by blast

      have hcl_subspace:
        "closure_on O0 ?TO U = closure_on Y TY U \<inter> O0"
        by (rule Theorem_17_4[OF hTopY hUsubO hO0Y])
      have hcl_eq: "closure_on O0 ?TO U = closure_on Y TY U"
        unfolding hcl_subspace using hclUsubO by blast

      have hTopEq:
        "subspace_topology O0 ?TO (closure_on Y TY U) = subspace_topology Y TY (closure_on Y TY U)"
      proof -
        have hsub: "closure_on Y TY U \<subseteq> O0"
          by (rule hclUsubO)
        have "subspace_topology O0 (subspace_topology Y TY O0) (closure_on Y TY U) = subspace_topology Y TY (closure_on Y TY U)"
          by (rule subspace_topology_trans[OF hsub])
        thus ?thesis
          by simp
      qed

      show "\<exists>U0. neighborhood_of x O0 ?TO U0 \<and> U0 \<subseteq> O0
        \<and> top1_compact_on (closure_on O0 ?TO U0) (subspace_topology O0 ?TO (closure_on O0 ?TO U0))"
        apply (rule exI[where x=U])
        apply (intro conjI)
          apply (rule hUnbO)
         apply (rule hUsubO)
        apply (subst hcl_eq)
        apply (subst hcl_eq)
        apply (subst hTopEq)
        apply (rule hclUcomp)
        done
    qed
  qed
qed

(** One-point compactification (encoded on the carrier \<open>insert None (Some ` X)\<close>). **)
definition top1_one_point_compactification_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a option) set set \<Rightarrow> bool" where
  "top1_one_point_compactification_on X TX TY \<longleftrightarrow>
     (let Y = insert None (Some ` X) in
        top1_homeomorphism_on X TX (Some ` X) (subspace_topology Y TY (Some ` X)) Some
        \<and> top1_compact_on Y TY
        \<and> is_hausdorff_on Y TY)"

(** Helper: the empty subspace is compact. **)
lemma top1_compact_on_empty_subspace:
  assumes hTop: "is_topology_on X TX"
  shows "top1_compact_on {} (subspace_topology X TX {})"
proof -
  have hTopE: "is_topology_on {} (subspace_topology X TX {})"
    by (rule subspace_topology_is_topology_on[OF hTop], simp)
  show ?thesis
    unfolding top1_compact_on_def
  proof (intro conjI)
    show "is_topology_on {} (subspace_topology X TX {})"
      by (rule hTopE)
    show "\<forall>Uc. Uc \<subseteq> subspace_topology X TX {} \<and> {} \<subseteq> \<Union>Uc \<longrightarrow>
        (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {} \<subseteq> \<Union>F)"
    proof (intro allI impI)
      fix Uc :: "'a set set"
      assume hUc: "Uc \<subseteq> subspace_topology X TX {} \<and> {} \<subseteq> \<Union>Uc"
      show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> {} \<subseteq> \<Union>F"
        apply (rule exI[where x="{}"])
        apply (intro conjI)
          apply simp
         apply simp
        apply simp
        done
    qed
  qed
qed

(** Helper: finite unions of compact subspaces are compact (in the subspace topology). **)
lemma top1_compact_on_union2_subspace:
  assumes hTop: "is_topology_on X TX"
  assumes hAX: "A \<subseteq> X"
  assumes hBX: "B \<subseteq> X"
  assumes hAcomp: "top1_compact_on A (subspace_topology X TX A)"
  assumes hBcomp: "top1_compact_on B (subspace_topology X TX B)"
  shows "top1_compact_on (A \<union> B) (subspace_topology X TX (A \<union> B))"
proof -
  let ?AB = "A \<union> B"
  let ?TAB = "subspace_topology X TX ?AB"
  let ?TA = "subspace_topology X TX A"
  let ?TB = "subspace_topology X TX B"

  have hABX: "?AB \<subseteq> X"
    using hAX hBX by blast
  have hTopAB: "is_topology_on ?AB ?TAB"
    by (rule subspace_topology_is_topology_on[OF hTop hABX])

  have hCoverA:
    "\<forall>Uc. Uc \<subseteq> ?TA \<and> A \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F)"
    using hAcomp unfolding top1_compact_on_def by blast
  have hCoverB:
    "\<forall>Uc. Uc \<subseteq> ?TB \<and> B \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> B \<subseteq> \<Union>F)"
    using hBcomp unfolding top1_compact_on_def by blast

  show ?thesis
    unfolding top1_compact_on_def
  proof (intro conjI)
    show "is_topology_on ?AB ?TAB"
      by (rule hTopAB)

    show "\<forall>Uc. Uc \<subseteq> ?TAB \<and> ?AB \<subseteq> \<Union>Uc \<longrightarrow>
        (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> ?AB \<subseteq> \<Union>F)"
    proof (intro allI impI)
      fix Uc :: "'a set set"
      assume hUc: "Uc \<subseteq> ?TAB \<and> ?AB \<subseteq> \<Union>Uc"
      have hUc_sub: "Uc \<subseteq> ?TAB"
        using hUc by blast
      have hUc_cov: "?AB \<subseteq> \<Union>Uc"
        using hUc by blast

      define UcA where "UcA = {A \<inter> U | U. U \<in> Uc}"
      define UcB where "UcB = {B \<inter> U | U. U \<in> Uc}"

      have hUcA_sub: "UcA \<subseteq> ?TA"
      proof (rule subsetI)
        fix S
        assume hS: "S \<in> UcA"
        obtain U where hU: "U \<in> Uc" and hSeq: "S = A \<inter> U"
          using hS unfolding UcA_def by blast
        have hUopen: "U \<in> ?TAB"
          using hUc_sub hU by blast
        obtain V where hV: "V \<in> TX" and hUeq: "U = ?AB \<inter> V"
          using hUopen unfolding subspace_topology_def by blast
        have hSeq2: "S = A \<inter> V"
          using hSeq hUeq by blast
        show "S \<in> ?TA"
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[where x=V])
          apply (intro conjI)
           apply (simp add: hSeq2)
          apply (rule hV)
          done
      qed

      have hUcB_sub: "UcB \<subseteq> ?TB"
      proof (rule subsetI)
        fix S
        assume hS: "S \<in> UcB"
        obtain U where hU: "U \<in> Uc" and hSeq: "S = B \<inter> U"
          using hS unfolding UcB_def by blast
        have hUopen: "U \<in> ?TAB"
          using hUc_sub hU by blast
        obtain V where hV: "V \<in> TX" and hUeq: "U = ?AB \<inter> V"
          using hUopen unfolding subspace_topology_def by blast
        have hSeq2: "S = B \<inter> V"
          using hSeq hUeq by blast
        show "S \<in> ?TB"
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[where x=V])
          apply (intro conjI)
           apply (simp add: hSeq2)
          apply (rule hV)
          done
      qed

      have hUcA_cov: "A \<subseteq> \<Union>UcA"
      proof (rule subsetI)
        fix x
        assume hxA: "x \<in> A"
        have hxAB: "x \<in> ?AB"
          using hxA by blast
        have hxU: "x \<in> \<Union>Uc"
          by (rule subsetD[OF hUc_cov hxAB])
        obtain U where hU: "U \<in> Uc" and hxU': "x \<in> U"
          using hxU by blast
        have hAU: "A \<inter> U \<in> UcA"
          unfolding UcA_def using hU by blast
        have hxAU: "x \<in> A \<inter> U"
          using hxA hxU' by blast
        show "x \<in> \<Union>UcA"
          by (rule UnionI[OF hAU hxAU])
      qed

      have hUcB_cov: "B \<subseteq> \<Union>UcB"
      proof (rule subsetI)
        fix x
        assume hxB: "x \<in> B"
        have hxAB: "x \<in> ?AB"
          using hxB by blast
        have hxU: "x \<in> \<Union>Uc"
          by (rule subsetD[OF hUc_cov hxAB])
        obtain U where hU: "U \<in> Uc" and hxU': "x \<in> U"
          using hxU by blast
        have hBU: "B \<inter> U \<in> UcB"
          unfolding UcB_def using hU by blast
        have hxBU: "x \<in> B \<inter> U"
          using hxB hxU' by blast
        show "x \<in> \<Union>UcB"
          by (rule UnionI[OF hBU hxBU])
      qed

      obtain FA where hFAfin: "finite FA" and hFAsub: "FA \<subseteq> UcA" and hFAcov: "A \<subseteq> \<Union>FA"
        using hCoverA[rule_format, OF conjI[OF hUcA_sub hUcA_cov]] by blast
      obtain FB where hFBfin: "finite FB" and hFBsub: "FB \<subseteq> UcB" and hFBcov: "B \<subseteq> \<Union>FB"
        using hCoverB[rule_format, OF conjI[OF hUcB_sub hUcB_cov]] by blast

      have hreprA: "\<forall>S\<in>FA. \<exists>U. U \<in> Uc \<and> S = A \<inter> U"
        using hFAsub unfolding UcA_def by blast
      obtain pickA where hpickA: "\<forall>S\<in>FA. pickA S \<in> Uc \<and> S = A \<inter> pickA S"
        using bchoice[OF hreprA] by blast
      define F0A where "F0A = pickA ` FA"
      have hF0A_fin: "finite F0A"
        unfolding F0A_def by (rule finite_imageI[OF hFAfin])
      have hF0A_sub: "F0A \<subseteq> Uc"
        unfolding F0A_def using hpickA by blast

      have hAcov0: "A \<subseteq> \<Union>F0A"
      proof (rule subsetI)
        fix x
        assume hxA: "x \<in> A"
        have hx: "x \<in> \<Union>FA"
          by (rule subsetD[OF hFAcov hxA])
        obtain S where hSFA: "S \<in> FA" and hxS: "x \<in> S"
          using hx by blast
        have hEqS: "S = A \<inter> pickA S"
          using hpickA hSFA by blast
        have hxU: "x \<in> pickA S"
        proof -
          have "x \<in> A \<inter> pickA S"
            using hxA hxS hEqS by simp
          thus ?thesis
            by blast
        qed
        have hUin: "pickA S \<in> F0A"
          unfolding F0A_def using hSFA by blast
        show "x \<in> \<Union>F0A"
          by (rule UnionI[OF hUin hxU])
      qed

      have hreprB: "\<forall>S\<in>FB. \<exists>U. U \<in> Uc \<and> S = B \<inter> U"
        using hFBsub unfolding UcB_def by blast
      obtain pickB where hpickB: "\<forall>S\<in>FB. pickB S \<in> Uc \<and> S = B \<inter> pickB S"
        using bchoice[OF hreprB] by blast
      define F0B where "F0B = pickB ` FB"
      have hF0B_fin: "finite F0B"
        unfolding F0B_def by (rule finite_imageI[OF hFBfin])
      have hF0B_sub: "F0B \<subseteq> Uc"
        unfolding F0B_def using hpickB by blast

      have hBcov0: "B \<subseteq> \<Union>F0B"
      proof (rule subsetI)
        fix x
        assume hxB: "x \<in> B"
        have hx: "x \<in> \<Union>FB"
          by (rule subsetD[OF hFBcov hxB])
        obtain S where hSFB: "S \<in> FB" and hxS: "x \<in> S"
          using hx by blast
        have hEqS: "S = B \<inter> pickB S"
          using hpickB hSFB by blast
        have hxU: "x \<in> pickB S"
        proof -
          have "x \<in> B \<inter> pickB S"
            using hxB hxS hEqS by simp
          thus ?thesis
            by blast
        qed
        have hUin: "pickB S \<in> F0B"
          unfolding F0B_def using hSFB by blast
        show "x \<in> \<Union>F0B"
          by (rule UnionI[OF hUin hxU])
      qed

      define F where "F = F0A \<union> F0B"
      have hFfin: "finite F"
        unfolding F_def using hF0A_fin hF0B_fin by simp
      have hFsub: "F \<subseteq> Uc"
        unfolding F_def using hF0A_sub hF0B_sub by blast
      have hFcov: "?AB \<subseteq> \<Union>F"
      proof (rule subsetI)
        fix x
        assume hxAB: "x \<in> ?AB"
        have hxAorB: "x \<in> A \<or> x \<in> B"
          using hxAB by blast
        show "x \<in> \<Union>F"
          using hxAorB
        proof
          assume hxA: "x \<in> A"
          have "x \<in> \<Union>F0A"
            by (rule subsetD[OF hAcov0 hxA])
          thus "x \<in> \<Union>F"
            unfolding F_def by blast
        next
          assume hxB: "x \<in> B"
          have "x \<in> \<Union>F0B"
            by (rule subsetD[OF hBcov0 hxB])
          thus "x \<in> \<Union>F"
            unfolding F_def by blast
        qed
      qed

      show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> ?AB \<subseteq> \<Union>F"
        apply (rule exI[where x=F])
        apply (intro conjI)
          apply (rule hFfin)
         apply (rule hFsub)
        apply (rule hFcov)
        done
    qed
  qed
qed

(** from \S29 Theorem 29.1 (One-point compactification) [top1.tex:3711] **)
theorem Theorem_29_1:
  assumes hTX: "is_topology_on X TX"
  shows
    "(top1_locally_compact_on X TX \<and> is_hausdorff_on X TX)
      \<longleftrightarrow> (\<exists>TY. top1_one_point_compactification_on X TX TY)"
    and
    "(\<forall>TY TY'. top1_one_point_compactification_on X TX TY
        \<and> top1_one_point_compactification_on X TX TY'
        \<longrightarrow> (\<exists>h.
              top1_homeomorphism_on (insert None (Some ` X)) TY (insert None (Some ` X)) TY' h
              \<and> (\<forall>x\<in>X. h (Some x) = Some x)))"
text \<open>
  Proof sketch: use the standard Alexandroff one-point compactification basis on
  \<open>Y = insert None (Some ` X)\<close>: basic opens around \<open>Some x\<close> are images \<open>Some ` U\<close> with \<open>U\<in>TX\<close>, and
  basic opens around \<open>None\<close> are complements of images of compact subsets of \<open>X\<close>.  Compactness is by
  reducing an open cover to a cover of the compact complement of a neighborhood of \<open>None\<close>.  Hausdorffness
  is proved by separating \<open>None\<close> from \<open>Some x\<close> using local compactness, and separating distinct points
  in \<open>X\<close> using the Hausdorff assumption.
\<close>
proof -
  define Y where "Y = insert None (Some ` X)"
  define B1 where "B1 = {Some ` U | U. U \<in> TX \<and> U \<subseteq> X}"
  define B2 where "B2 = {Y - Some ` K | K. K \<subseteq> X \<and> top1_compact_on K (subspace_topology X TX K)}"
  define B where "B = B1 \<union> B2"
  define TY0 where "TY0 = topology_generated_by_basis Y B"

  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])
  have union_TX: "\<forall>U. U \<subseteq> TX \<longrightarrow> \<Union>U \<in> TX"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hTX[unfolded is_topology_on_def]]]])

  have hB_basis: "is_hausdorff_on X TX \<Longrightarrow> is_basis_on Y B"
  proof -
    assume hHaus: "is_hausdorff_on X TX"
    show "is_basis_on Y B"
    proof (unfold is_basis_on_def, intro conjI)
      show "\<forall>b\<in>B. b \<subseteq> Y"
        unfolding B_def B1_def B2_def Y_def by blast
      show "\<forall>y\<in>Y. \<exists>b\<in>B. y \<in> b"
      proof (intro ballI)
        fix y
        assume hyY: "y \<in> Y"
        show "\<exists>b\<in>B. y \<in> b"
        proof (cases y)
        case None
        have hEmptyComp: "top1_compact_on {} (subspace_topology X TX {})"
          by (rule top1_compact_on_empty_subspace[OF hTX])
        have hYB2: "Y - Some ` {} \<in> B2"
          unfolding B2_def using hEmptyComp by blast
	        have hy: "None \<in> Y - Some ` {}"
	          unfolding Y_def by simp
	        have hy': "y \<in> Y - Some ` {}"
	          using hy None by simp
	        show ?thesis
	          unfolding B_def
	          apply (rule bexI[where x="Y - Some ` {}"])
	           apply (rule hy')
	          apply (rule UnI2[OF hYB2])
	          done
	      next
        case (Some x)
        have hSomeX: "Some ` X \<in> B1"
          unfolding B1_def using X_TX by blast
	        have "Some x \<in> Some ` X"
	          using hyY unfolding Y_def Some by blast
	        then have "Some x \<in> Some ` X" .
	        have hySomeX: "y \<in> Some ` X"
	          using \<open>Some x \<in> Some ` X\<close> Some by simp
	        show ?thesis
	          unfolding B_def
	          apply (rule bexI[where x="Some ` X"])
	           apply (rule hySomeX)
	          apply (rule UnI1[OF hSomeX])
	          done
	      qed
    qed
      show "\<forall>b1\<in>B. \<forall>b2\<in>B. \<forall>y\<in>b1 \<inter> b2. \<exists>b3\<in>B. y \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
      proof (intro ballI)
        fix b1 b2 y
        assume hb1: "b1 \<in> B" and hb2: "b2 \<in> B"
        assume hy: "y \<in> b1 \<inter> b2"
      have hy1: "y \<in> b1" and hy2: "y \<in> b2"
        using hy by blast+

      have hb1_cases: "b1 \<in> B1 \<or> b1 \<in> B2"
        using hb1 unfolding B_def by blast
      have hb2_cases: "b2 \<in> B1 \<or> b2 \<in> B2"
        using hb2 unfolding B_def by blast

	      show "\<exists>b3\<in>B. y \<in> b3 \<and> b3 \<subseteq> b1 \<inter> b2"
	      proof (cases "b1 \<in> B1")
	        case True
	        then have hb1B1: "b1 \<in> B1" .
	        obtain U1 where hU1: "U1 \<in> TX" and hU1sub: "U1 \<subseteq> X" and hb1eq: "b1 = Some ` U1"
	          using hb1B1 unfolding B1_def by blast
	        show ?thesis
	        proof (cases "b2 \<in> B1")
	          case True
	          then have hb2B1: "b2 \<in> B1" .
	          obtain U2 where hU2: "U2 \<in> TX" and hU2sub: "U2 \<subseteq> X" and hb2eq: "b2 = Some ` U2"
	            using hb2B1 unfolding B1_def by blast
          have hU12: "U1 \<inter> U2 \<in> TX"
            by (rule topology_inter2[OF hTX hU1 hU2])
          have hb3B1: "Some ` (U1 \<inter> U2) \<in> B1"
            unfolding B1_def using hU12 hU1sub hU2sub by blast
          have hy3: "y \<in> Some ` (U1 \<inter> U2)"
            using hy1 hy2 unfolding hb1eq hb2eq by blast
          have hsub: "Some ` (U1 \<inter> U2) \<subseteq> b1 \<inter> b2"
            unfolding hb1eq hb2eq by blast
          show ?thesis
            unfolding B_def
            apply (rule bexI[where x="Some ` (U1 \<inter> U2)"])
             apply (intro conjI)
              apply (rule hy3)
             apply (rule hsub)
            apply (rule UnI1[OF hb3B1])
            done
        next
          case False
          then have hb2B2: "b2 \<in> B2"
            using hb2_cases by blast
          obtain K where hKX: "K \<subseteq> X"
              and hKcomp: "top1_compact_on K (subspace_topology X TX K)"
              and hb2eq: "b2 = Y - Some ` K"
            using hb2B2 unfolding B2_def by blast
          obtain x0 where hySome: "y = Some x0"
          proof -
            have "y \<in> b1" by (rule hy1)
            hence "y \<in> Some ` U1" unfolding hb1eq .
            then obtain x0 where hx0: "x0 \<in> U1" and hy0: "y = Some x0"
              by blast
            show ?thesis
              by (rule that[OF hy0])
          qed
          have hx0U1: "x0 \<in> U1"
          proof -
            have "y \<in> Some ` U1" using hy1 unfolding hb1eq .
            then show ?thesis
              using hySome by blast
          qed
          have hx0X: "x0 \<in> X"
          proof -
            show ?thesis
              by (rule subsetD[OF hU1sub hx0U1])
          qed
          have hy_in_b2: "y \<in> Y - Some ` K"
            using hy2 unfolding hb2eq .
          have hx0_notK: "x0 \<notin> K"
          proof
            assume hx0K: "x0 \<in> K"
            have "Some x0 \<in> Some ` K"
              by (rule imageI[OF hx0K])
            thus False
              using hy_in_b2 hySome by blast
          qed
          obtain U V where hU: "U \<in> TX" and hV: "V \<in> TX" and hx0U: "x0 \<in> U"
              and hKsubV: "K \<subseteq> V" and hdisj: "U \<inter> V = {}"
            using Lemma_26_4[OF hHaus hKX hKcomp hx0X hx0_notK] by blast
          have hU3: "U1 \<inter> U \<in> TX"
            by (rule topology_inter2[OF hTX hU1 hU])
          have hb3B1: "Some ` (U1 \<inter> U) \<in> B1"
            unfolding B1_def using hU3 hU1sub by blast
          have hy3: "y \<in> Some ` (U1 \<inter> U)"
            using hySome hx0U1 hx0U by blast
          have hsubb2: "Some ` (U1 \<inter> U) \<subseteq> Y - Some ` K"
          proof
            fix z
            assume hz: "z \<in> Some ` (U1 \<inter> U)"
            then obtain x where hx: "x \<in> U1 \<inter> U" and hzEq: "z = Some x"
              by blast
            have hxU': "x \<in> U" and hxU1': "x \<in> U1"
              using hx by blast+
            have hxX': "x \<in> X"
              by (rule subsetD[OF hU1sub hxU1'])
            have hx_notK: "x \<notin> K"
            proof
              assume hxK: "x \<in> K"
              have hxV': "x \<in> V"
                by (rule subsetD[OF hKsubV hxK])
              have "x \<in> U \<inter> V"
                using hxU' hxV' by blast
              thus False
                using hdisj by blast
            qed
            have hz_not: "z \<notin> Some ` K"
              using hx_notK hzEq by blast
            show "z \<in> Y - Some ` K"
              unfolding Y_def using hzEq hxX' hz_not by blast
          qed
          have hsub: "Some ` (U1 \<inter> U) \<subseteq> b1 \<inter> b2"
            unfolding hb1eq hb2eq using hsubb2 by blast
          show ?thesis
            unfolding B_def
            apply (rule bexI[where x="Some ` (U1 \<inter> U)"])
             apply (intro conjI)
              apply (rule hy3)
             apply (rule hsub)
            apply (rule UnI1[OF hb3B1])
            done
        qed
	      next
	        case False
	        then have hb1B2: "b1 \<in> B2"
	          using hb1_cases by blast
        obtain K1 where hK1X: "K1 \<subseteq> X"
            and hK1comp: "top1_compact_on K1 (subspace_topology X TX K1)"
            and hb1eq: "b1 = Y - Some ` K1"
          using hb1B2 unfolding B2_def by blast
	        show ?thesis
	        proof (cases "b2 \<in> B1")
	          case True
	          then have hb2B1: "b2 \<in> B1" .
	          obtain U2 where hU2: "U2 \<in> TX" and hU2sub: "U2 \<subseteq> X" and hb2eq: "b2 = Some ` U2"
	            using hb2B1 unfolding B1_def by blast
          have hySome: "\<exists>x0. y = Some x0"
          proof -
            have "y \<in> b2" by (rule hy2)
            hence "y \<in> Some ` U2" unfolding hb2eq .
            thus ?thesis by blast
          qed
          obtain x0 where hyEq: "y = Some x0"
            using hySome by blast
          have hx0U2: "x0 \<in> U2"
            using hy2 unfolding hb2eq hyEq by blast
          have hx0X: "x0 \<in> X"
          proof -
            show ?thesis
              by (rule subsetD[OF hU2sub hx0U2])
          qed
          have hx0_notK1: "x0 \<notin> K1"
          proof
            assume hx0K1: "x0 \<in> K1"
            have "Some x0 \<in> Some ` K1"
              by (rule imageI[OF hx0K1])
            thus False
              using hy1 unfolding hb1eq hyEq by blast
          qed
          obtain U V where hU: "U \<in> TX" and hV: "V \<in> TX" and hx0U: "x0 \<in> U"
              and hKsubV: "K1 \<subseteq> V" and hdisj: "U \<inter> V = {}"
            using Lemma_26_4[OF hHaus hK1X hK1comp hx0X hx0_notK1] by blast
          have hU3: "U2 \<inter> U \<in> TX"
            by (rule topology_inter2[OF hTX hU2 hU])
          have hb3B1: "Some ` (U2 \<inter> U) \<in> B1"
            unfolding B1_def using hU3 hU2sub by blast
          have hy3: "y \<in> Some ` (U2 \<inter> U)"
            using hyEq hx0U2 hx0U by blast
          have hsubb1: "Some ` (U2 \<inter> U) \<subseteq> Y - Some ` K1"
          proof
            fix z
            assume hz: "z \<in> Some ` (U2 \<inter> U)"
            then obtain x where hx: "x \<in> U2 \<inter> U" and hzEq: "z = Some x"
              by blast
            have hxU': "x \<in> U"
              using hx by blast
            have hxU2': "x \<in> U2"
              using hx by blast
            have hxX': "x \<in> X"
            proof -
              show ?thesis
                by (rule subsetD[OF hU2sub hxU2'])
            qed
            have hx_notK: "x \<notin> K1"
            proof
              assume hxK: "x \<in> K1"
              have hxV': "x \<in> V"
                by (rule subsetD[OF hKsubV hxK])
              have "x \<in> U \<inter> V"
                using hxU' hxV' by blast
              thus False using hdisj by blast
            qed
            have hz_not: "z \<notin> Some ` K1"
              using hx_notK hzEq by blast
            show "z \<in> Y - Some ` K1"
              unfolding Y_def using hzEq hxX' hz_not by blast
          qed
          have hsub: "Some ` (U2 \<inter> U) \<subseteq> b1 \<inter> b2"
            unfolding hb1eq hb2eq using hsubb1 by blast
          show ?thesis
            unfolding B_def
            apply (rule bexI[where x="Some ` (U2 \<inter> U)"])
             apply (intro conjI)
              apply (rule hy3)
             apply (rule hsub)
            apply (rule UnI1[OF hb3B1])
            done
        next
          case False
          then have hb2B2: "b2 \<in> B2"
            using hb2_cases by blast
          obtain K2 where hK2X: "K2 \<subseteq> X"
              and hK2comp: "top1_compact_on K2 (subspace_topology X TX K2)"
              and hb2eq: "b2 = Y - Some ` K2"
            using hb2B2 unfolding B2_def by blast
          have hK12comp: "top1_compact_on (K1 \<union> K2) (subspace_topology X TX (K1 \<union> K2))"
            by (rule top1_compact_on_union2_subspace[OF hTX hK1X hK2X hK1comp hK2comp])
          have hb3B2: "Y - Some ` (K1 \<union> K2) \<in> B2"
            unfolding B2_def using hK1X hK2X hK12comp by blast
          have hy3: "y \<in> Y - Some ` (K1 \<union> K2)"
          proof -
            have hyb1: "y \<in> Y - Some ` K1"
              using hy1 unfolding hb1eq .
            have hyb2: "y \<in> Y - Some ` K2"
              using hy2 unfolding hb2eq .
            have "y \<notin> Some ` (K1 \<union> K2)"
            proof
              assume hyK: "y \<in> Some ` (K1 \<union> K2)"
              then obtain x where hx: "x \<in> K1 \<union> K2" and hyEq: "y = Some x"
                by blast
              have "y \<in> Some ` K1 \<or> y \<in> Some ` K2"
                using hx hyEq by blast
              thus False
              proof
                assume "y \<in> Some ` K1"
                thus False using hyb1 by blast
              next
                assume "y \<in> Some ` K2"
                thus False using hyb2 by blast
              qed
	            qed
	            have hyY': "y \<in> Y"
	              using hyb1 by blast
	            show ?thesis
	              using hyY' \<open>y \<notin> Some ` (K1 \<union> K2)\<close> by blast
	          qed
          have hsub: "Y - Some ` (K1 \<union> K2) \<subseteq> b1 \<inter> b2"
            unfolding hb1eq hb2eq by blast
          show ?thesis
            unfolding B_def
            apply (rule bexI[where x="Y - Some ` (K1 \<union> K2)"])
             apply (intro conjI)
              apply (rule hy3)
             apply (rule hsub)
            apply (rule UnI2[OF hb3B2])
            done
        qed
      qed
      qed
    qed
  qed

  have hTopY0: "is_hausdorff_on X TX \<Longrightarrow> is_topology_on Y TY0"
  proof -
    assume hHaus: "is_hausdorff_on X TX"
    have hB0: "is_basis_on Y B"
      by (rule hB_basis[OF hHaus])
    show "is_topology_on Y TY0"
      unfolding TY0_def
      by (rule topology_generated_by_basis_is_topology_on[OF hB0])
  qed
  
  have hBsubY0: "is_hausdorff_on X TX \<Longrightarrow> B \<subseteq> TY0"
  proof -
    assume hHaus: "is_hausdorff_on X TX"
    have hB0: "is_basis_on Y B"
      by (rule hB_basis[OF hHaus])
    show "B \<subseteq> TY0"
    proof (rule subsetI)
      fix b
      assume hb: "b \<in> B"
      show "b \<in> TY0"
        unfolding TY0_def topology_generated_by_basis_def
      proof (rule CollectI, intro conjI)
        show "b \<subseteq> Y"
          using hB0 hb unfolding is_basis_on_def by blast
        show "\<forall>x\<in>b. \<exists>ba\<in>B. x \<in> ba \<and> ba \<subseteq> b"
        proof (intro ballI)
          fix x
          assume hx: "x \<in> b"
          show "\<exists>ba\<in>B. x \<in> ba \<and> ba \<subseteq> b"
            apply (rule bexI[where x=b])
             apply (intro conjI)
              apply (rule hx)
             apply (rule subset_refl)
            apply (rule hb)
            done
        qed
      qed
    qed
  qed

  have forward_imp:
    "top1_locally_compact_on X TX \<and> is_hausdorff_on X TX \<Longrightarrow> (\<exists>TY. top1_one_point_compactification_on X TX TY)"
  text \<open>
    Forward direction: define \<open>TY0\<close> as the topology generated by the standard Alexandroff basis
    \<open>B = B1 \<union> B2\<close> on \<open>Y = insert None (Some ` X)\<close>, then show that \<open>Some\<close> is a homeomorphism
    \<open>X \<cong> Some ` X\<close> (with the induced subspace topology) and that \<open>(Y, TY0)\<close> is compact and Hausdorff.
    We start this proof with \<open>proof -\<close> (rather than plain \<open>proof\<close>) to prevent goal refinement from
    introducing a schematic witness for the final existential too early.
  \<close>
  proof -
    assume hLH: "top1_locally_compact_on X TX \<and> is_hausdorff_on X TX"
    have hLC: "top1_locally_compact_on X TX"
      using hLH by simp
    have hHaus: "is_hausdorff_on X TX"
      using hLH by simp

    have hTopY0': "is_topology_on Y TY0"
      by (rule hTopY0[OF hHaus])
    have hBsubY0': "B \<subseteq> TY0"
      by (rule hBsubY0[OF hHaus])

    have hSomeContY: "top1_continuous_map_on X TX Y TY0 Some"
    proof -
      have hPreB: "\<forall>b\<in>B. {x \<in> X. Some x \<in> b} \<in> TX"
      proof (intro ballI)
        fix b
        assume hb: "b \<in> B"
        show "{x \<in> X. Some x \<in> b} \<in> TX"
        proof (cases "b \<in> B1")
          case True
          then obtain U where hU: "U \<in> TX" and hUsub: "U \<subseteq> X" and hbEq: "b = Some ` U"
            using True unfolding B1_def by blast
          have hEq: "{x \<in> X. Some x \<in> b} = X \<inter> U"
          proof (rule set_eqI)
            fix x
            show "x \<in> {x \<in> X. Some x \<in> b} \<longleftrightarrow> x \<in> X \<inter> U"
              unfolding hbEq by blast
          qed
          have "X \<inter> U \<in> TX"
            by (rule topology_inter2[OF hTX X_TX hU])
          thus ?thesis
            using hEq by simp
        next
          case False
          have hb2: "b \<in> B2"
            using hb False unfolding B_def by blast
          obtain K where hKX: "K \<subseteq> X"
              and hKcomp: "top1_compact_on K (subspace_topology X TX K)"
              and hbEq: "b = Y - Some ` K"
            using hb2 unfolding B2_def by blast
          have hKclosed: "closedin_on X TX K"
            by (rule Theorem_26_3[OF hHaus hKX hKcomp])
          have hXmK: "X - K \<in> TX"
            by (rule closedin_diff_open[OF hKclosed])
          have hEq: "{x \<in> X. Some x \<in> b} = X - K"
            unfolding hbEq Y_def by blast
          show ?thesis
            using hXmK hEq by simp
        qed
      qed

      have hpre: "\<forall>V\<in>TY0. {x \<in> X. Some x \<in> V} \<in> TX"
      proof (intro ballI)
        fix V
        assume hV: "V \<in> TY0"
        have hVgen: "V \<in> topology_generated_by_basis Y B"
          using hV unfolding TY0_def by simp
        have hVsub: "V \<subseteq> Y" and hrefine: "\<forall>y\<in>V. \<exists>b\<in>B. y \<in> b \<and> b \<subseteq> V"
          using hVgen unfolding topology_generated_by_basis_def by blast+
        define Uc where "Uc = { {x \<in> X. Some x \<in> b} | b. b \<in> B \<and> b \<subseteq> V }"
        have hUc_sub: "Uc \<subseteq> TX"
        proof (rule subsetI)
          fix U
          assume hU: "U \<in> Uc"
          then obtain b where hb: "b \<in> B" and hbsub: "b \<subseteq> V" and hUeq: "U = {x \<in> X. Some x \<in> b}"
            unfolding Uc_def by blast
          have "{x \<in> X. Some x \<in> b} \<in> TX"
            using hPreB hb by blast
          thus "U \<in> TX"
            unfolding hUeq .
        qed
        have hCov: "{x \<in> X. Some x \<in> V} \<subseteq> \<Union>Uc"
        proof (rule subsetI)
          fix x
          assume hx: "x \<in> {x \<in> X. Some x \<in> V}"
          have hxX: "x \<in> X" and hSome: "Some x \<in> V"
            using hx by blast+
          obtain b where hb: "b \<in> B" and hSomeb: "Some x \<in> b" and hbsub: "b \<subseteq> V"
            using hrefine[rule_format, OF hSome] by blast
          have hUin: "{x \<in> X. Some x \<in> b} \<in> Uc"
            unfolding Uc_def using hb hbsub by blast
          have hxU: "x \<in> {x \<in> X. Some x \<in> b}"
            using hxX hSomeb by blast
          show "x \<in> \<Union>Uc"
            by (rule UnionI[OF hUin hxU])
        qed
        have hEq: "{x \<in> X. Some x \<in> V} = \<Union>Uc"
        proof (rule equalityI)
          show "{x \<in> X. Some x \<in> V} \<subseteq> \<Union>Uc"
            by (rule hCov)
          show "\<Union>Uc \<subseteq> {x \<in> X. Some x \<in> V}"
            unfolding Uc_def using hVsub by blast
        qed
        have "(\<Union>Uc) \<in> TX"
          by (rule union_TX[rule_format, OF hUc_sub])
        thus "{x \<in> X. Some x \<in> V} \<in> TX"
          using hEq by simp
      qed

      show ?thesis
        unfolding top1_continuous_map_on_def
        apply (intro conjI)
         apply (intro ballI)
         apply (simp add: Y_def)
        apply (rule hpre)
        done
    qed

    have hHomeo:
      "top1_homeomorphism_on X TX (Some ` X) (subspace_topology Y TY0 (Some ` X)) Some"
    proof (unfold top1_homeomorphism_on_def, intro conjI)
      show "is_topology_on X TX"
        by (rule hTX)
      show "is_topology_on (Some ` X) (subspace_topology Y TY0 (Some ` X))"
      proof -
        have "Some ` X \<subseteq> Y"
          unfolding Y_def by blast
        thus ?thesis
          by (rule subspace_topology_is_topology_on[OF hTopY0'])
      qed
      show "bij_betw Some X (Some ` X)"
        unfolding bij_betw_def by (intro conjI) (auto simp: inj_on_def)
	      show "top1_continuous_map_on X TX (Some ` X) (subspace_topology Y TY0 (Some ` X)) Some"
	      proof -
	        have "Some ` X \<subseteq> Y"
	          unfolding Y_def by blast
		        show ?thesis
		          apply (rule Theorem_18_2(5)[OF hTX hTopY0' hTopY0', rule_format, where W="Some ` X" and f=Some])
		          apply (rule conjI)
		           apply (rule hSomeContY)
		          apply (rule conjI)
		           apply (rule \<open>Some ` X \<subseteq> Y\<close>)
		          apply simp
		          done
	      qed
      show "top1_continuous_map_on (Some ` X) (subspace_topology Y TY0 (Some ` X)) X TX (inv_into X Some)"
      proof -
        have pre: "\<forall>U\<in>TX. {y \<in> Some ` X. inv_into X Some y \<in> U} \<in> subspace_topology Y TY0 (Some ` X)"
        proof (intro ballI)
          fix U
          assume hU: "U \<in> TX"
          have hSomeU: "Some ` (X \<inter> U) \<in> TY0"
          proof -
            have hU0: "X \<inter> U \<in> TX"
              by (rule topology_inter2[OF hTX X_TX hU])
            have hU0sub: "X \<inter> U \<subseteq> X"
              by blast
            have "Some ` (X \<inter> U) \<in> B1"
              unfolding B1_def using hU0 hU0sub by blast
            hence "Some ` (X \<inter> U) \<in> B"
              unfolding B_def by blast
            thus ?thesis
              using hBsubY0' by blast
          qed
          have hEq: "{y \<in> Some ` X. inv_into X Some y \<in> U} = (Some ` X) \<inter> (Some ` (X \<inter> U))"
          proof (rule set_eqI)
            fix y
            show "y \<in> {y \<in> Some ` X. inv_into X Some y \<in> U} \<longleftrightarrow> y \<in> (Some ` X) \<inter> (Some ` (X \<inter> U))"
            proof (cases y)
              case None
              then show ?thesis by simp
            next
              case (Some x)
              show ?thesis
	              proof
	                assume hy: "y \<in> {y \<in> Some ` X. inv_into X Some y \<in> U}"
	                have hxX: "x \<in> X"
	                proof -
	                  have "y \<in> Some ` X"
	                    using hy by simp
	                  thus ?thesis
	                    using Some by blast
	                qed
	                have hxU: "inv_into X Some (Some x) \<in> U"
	                  using hy Some by simp
	                have hinv: "inv_into X Some (Some x) = x"
	                proof -
	                  show ?thesis
	                    apply (rule inv_into_f_f)
	                     apply simp
	                    apply (rule hxX)
	                    done
	                qed
	                have hxU': "x \<in> U"
	                  using hxU hinv by simp
                show "y \<in> (Some ` X) \<inter> (Some ` (X \<inter> U))"
                  using hxX hxU' Some by blast
	              next
	                assume hy: "y \<in> (Some ` X) \<inter> (Some ` (X \<inter> U))"
		                have hxXU: "x \<in> X \<inter> U"
		                proof -
		                  have hyImg: "y \<in> Some ` (X \<inter> U)"
		                    using hy by blast
			                  have hxImg: "Some x \<in> Some ` (X \<inter> U)"
			                    using hyImg Some by simp
			                  have hxXU': "x \<in> X \<inter> U"
			                  proof -
			                    obtain t where ht: "t \<in> X \<inter> U" and hxEq: "Some x = Some t"
			                      using hxImg unfolding image_iff by blast
			                    have "x = t"
			                      using hxEq by simp
			                    thus ?thesis
			                      using ht by simp
			                  qed
			                  show ?thesis
			                    by (rule hxXU')
			                qed
	                have hxX: "x \<in> X"
	                  using hxXU by simp
	                have hxU': "x \<in> U"
	                  using hxXU by simp
		                have hinv: "inv_into X Some (Some x) = x"
		                proof -
		                  show ?thesis
		                    apply (rule inv_into_f_f)
		                     apply simp
	                    apply (rule hxX)
	                    done
	                qed
                have hxU: "inv_into X Some (Some x) \<in> U"
                  using hxU' hinv by simp
                show "y \<in> {y \<in> Some ` X. inv_into X Some y \<in> U}"
                  using Some hxX hxU by simp
              qed
            qed
          qed
          show "{y \<in> Some ` X. inv_into X Some y \<in> U} \<in> subspace_topology Y TY0 (Some ` X)"
            unfolding subspace_topology_def
            apply (rule CollectI)
            apply (rule exI[where x="Some ` (X \<inter> U)"])
            apply (intro conjI)
             apply (simp add: hEq Int_assoc)
            apply (rule hSomeU)
            done
	        qed
	        show ?thesis
	          unfolding top1_continuous_map_on_def
	        proof (intro conjI)
	          show "\<forall>x\<in>Some ` X. inv_into X Some x \<in> X"
	          proof (intro ballI)
	            fix x
	            assume hx: "x \<in> Some ` X"
	            obtain a where haX: "a \<in> X" and hxEq: "x = Some a"
	              using hx by blast
	            have hinv: "inv_into X Some x = a"
	            proof -
	              have "inv_into X Some (Some a) = a"
	                apply (rule inv_into_f_f)
	                 apply simp
	                apply (rule haX)
	                done
	              thus ?thesis
	                using hxEq by simp
	            qed
	            show "inv_into X Some x \<in> X"
	              using haX hinv by simp
	          qed
	          show "\<forall>V\<in>TX. {x \<in> Some ` X. inv_into X Some x \<in> V} \<in> subspace_topology Y TY0 (Some ` X)"
	            by (rule pre)
	        qed
	      qed
	    qed

    have hCompY: "top1_compact_on Y TY0"
    proof (unfold top1_compact_on_def, intro conjI)
      show "is_topology_on Y TY0"
        by (rule hTopY0')
      show "\<forall>Uc. Uc \<subseteq> TY0 \<and> Y \<subseteq> \<Union>Uc \<longrightarrow>
            (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F)"
      proof (intro allI impI)
        fix Uc :: "('a option) set set"
        assume hUc: "Uc \<subseteq> TY0 \<and> Y \<subseteq> \<Union>Uc"
        have hUc_sub: "Uc \<subseteq> TY0" and hCov: "Y \<subseteq> \<Union>Uc"
          using hUc by blast+
        have hNone: "None \<in> \<Union>Uc"
          by (rule subsetD[OF hCov], simp add: Y_def)
        obtain U0 where hU0: "U0 \<in> Uc" and hNoneU0: "None \<in> U0"
          using hNone by blast
        have hU0open: "U0 \<in> TY0"
          using hUc_sub hU0 by blast
        have hU0gen: "U0 \<subseteq> Y \<and> (\<forall>y\<in>U0. \<exists>b\<in>B. y \<in> b \<and> b \<subseteq> U0)"
          using hU0open unfolding TY0_def topology_generated_by_basis_def by blast
        obtain b0 where hb0: "b0 \<in> B" and hNoneb0: "None \<in> b0" and hb0sub: "b0 \<subseteq> U0"
          using hU0gen hNoneU0 by blast
        have hb0B2: "b0 \<in> B2"
        proof -
          have "b0 \<in> B1 \<or> b0 \<in> B2"
            using hb0 unfolding B_def by blast
          thus ?thesis
          proof
            assume hb0B1: "b0 \<in> B1"
            then obtain U where hbEq: "b0 = Some ` U"
              unfolding B1_def by blast
            have "None \<notin> Some ` U"
              by simp
            thus ?thesis
              using hNoneb0 unfolding hbEq by blast
          next
            assume "b0 \<in> B2"
            thus ?thesis .
          qed
        qed
        obtain K0 where hK0X: "K0 \<subseteq> X"
            and hK0comp: "top1_compact_on K0 (subspace_topology X TX K0)"
            and hb0eq: "b0 = Y - Some ` K0"
          using hb0B2 unfolding B2_def by blast
        have hCoverK0:
          "\<forall>Vc. Vc \<subseteq> TX \<and> K0 \<subseteq> \<Union>Vc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Vc \<and> K0 \<subseteq> \<Union>F)"
          using Lemma_26_1[OF hTX hK0X] hK0comp by blast
        define Vc where "Vc = {{x \<in> X. Some x \<in> U} | U. U \<in> Uc}"
        have hVc_sub: "Vc \<subseteq> TX"
        proof (rule subsetI)
          fix V
          assume hV: "V \<in> Vc"
          then obtain U where hU: "U \<in> Uc" and hVeq: "V = {x \<in> X. Some x \<in> U}"
            unfolding Vc_def by blast
          have hUopen: "U \<in> TY0"
            using hUc_sub hU by blast
          have "{x \<in> X. Some x \<in> U} \<in> TX"
            using hSomeContY hUopen unfolding top1_continuous_map_on_def by blast
          thus "V \<in> TX"
            unfolding hVeq .
        qed
        have hVc_cov: "K0 \<subseteq> \<Union>Vc"
        proof (rule subsetI)
          fix x
          assume hxK0: "x \<in> K0"
          have hxY: "Some x \<in> Y"
            unfolding Y_def using hK0X hxK0 by blast
          have hxU: "Some x \<in> \<Union>Uc"
            by (rule subsetD[OF hCov hxY])
          then obtain U where hU: "U \<in> Uc" and hxU': "Some x \<in> U"
            by blast
          have hVin: "{x \<in> X. Some x \<in> U} \<in> Vc"
            unfolding Vc_def using hU by blast
          have hxV: "x \<in> {x \<in> X. Some x \<in> U}"
            using hK0X hxK0 hxU' by blast
          show "x \<in> \<Union>Vc"
            by (rule UnionI[OF hVin hxV])
        qed
        obtain FVc where hFVcfin: "finite FVc" and hFVcsub: "FVc \<subseteq> Vc" and hK0cov: "K0 \<subseteq> \<Union>FVc"
          using hCoverK0[rule_format, OF conjI[OF hVc_sub hVc_cov]] by blast
	        have hrepr: "\<forall>V\<in>FVc. \<exists>U\<in>Uc. V = {x \<in> X. Some x \<in> U}"
	          using hFVcsub unfolding Vc_def by blast
	        have hrepr': "\<forall>V\<in>FVc. \<exists>U. U \<in> Uc \<and> V = {x \<in> X. Some x \<in> U}"
	          using hrepr by blast
	        obtain pick where hpick: "\<forall>V\<in>FVc. pick V \<in> Uc \<and> V = {x \<in> X. Some x \<in> pick V}"
	          using bchoice[OF hrepr'] by blast
	        define F where "F = insert U0 (pick ` FVc)"
	        have hFfin: "finite F"
	          unfolding F_def using hFVcfin by simp
        have hFsub: "F \<subseteq> Uc"
          unfolding F_def using hU0 hpick by blast
        have hFcov: "Y \<subseteq> \<Union>F"
        proof (rule subsetI)
          fix y
          assume hyY: "y \<in> Y"
          show "y \<in> \<Union>F"
          proof (cases "y \<in> Some ` K0")
            case True
            then obtain x where hxK0: "x \<in> K0" and hyEq: "y = Some x"
              by blast
            have hx: "x \<in> \<Union>FVc"
              by (rule subsetD[OF hK0cov hxK0])
	            then obtain V where hV: "V \<in> FVc" and hxV: "x \<in> V"
	              by blast
	            have hp: "pick V \<in> Uc \<and> V = {x \<in> X. Some x \<in> pick V}"
	              using hpick hV by blast
	            have hU: "pick V \<in> Uc"
	              using hp by simp
	            have hVeq: "V = {x \<in> X. Some x \<in> pick V}"
	              using hp by simp
	            have hxPick: "Some x \<in> pick V"
	              using hxV hVeq hK0X hxK0 by blast
	            have hyPick: "y \<in> pick V"
	              using hxPick hyEq by simp
	            have hPickF: "pick V \<in> F"
	              unfolding F_def using hV by blast
	            show ?thesis
	              by (rule UnionI[OF hPickF hyPick])
	          next
	            case False
	            have hyb0: "y \<in> b0"
	              unfolding hb0eq using False hyY by blast
	            have hyU0: "y \<in> U0"
	              by (rule subsetD[OF subset_trans[OF _ hb0sub] hyb0]) simp
	            have hU0F: "U0 \<in> F"
	              unfolding F_def by simp
	            show ?thesis
	              by (rule UnionI[OF hU0F hyU0])
	          qed
	        qed
        show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> Y \<subseteq> \<Union>F"
          apply (rule exI[where x=F])
          apply (intro conjI)
            apply (rule hFfin)
           apply (rule hFsub)
          apply (rule hFcov)
          done
      qed
    qed

    have hHausY: "is_hausdorff_on Y TY0"
    proof (unfold is_hausdorff_on_def, intro conjI)
      show "is_topology_on Y TY0"
        by (rule hTopY0')
      show "\<forall>x\<in>Y. \<forall>y\<in>Y. x \<noteq> y \<longrightarrow>
        (\<exists>U V. neighborhood_of x Y TY0 U \<and> neighborhood_of y Y TY0 V \<and> U \<inter> V = {})"
      proof (intro ballI impI)
        fix x y
	        assume hxY: "x \<in> Y" and hyY: "y \<in> Y" and hne: "x \<noteq> y"
	        show "\<exists>U V. neighborhood_of x Y TY0 U \<and> neighborhood_of y Y TY0 V \<and> U \<inter> V = {}"
	        proof -
	          have hSepNoneSome:
	            "\<And>x0. x0 \<in> X \<Longrightarrow> \<exists>U V. neighborhood_of None Y TY0 U \<and> neighborhood_of (Some x0) Y TY0 V \<and> U \<inter> V = {}"
	          proof -
	            fix x0
	            assume hx0X: "x0 \<in> X"
	            have hLC_ex:
	              "\<exists>U. neighborhood_of x0 X TX U \<and> U \<subseteq> X
	                \<and> top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
	              using hLC hx0X unfolding top1_locally_compact_on_def by blast
	            obtain U where hnb: "neighborhood_of x0 X TX U" and hUX: "U \<subseteq> X"
	                and hKcomp: "top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
	              using hLC_ex by blast
	            define K where "K = closure_on X TX U"
	            have hKX: "K \<subseteq> X"
	              unfolding K_def by (rule closure_on_subset_carrier[OF hTX hUX])
	            have hbInf: "Y - Some ` K \<in> B2"
	              unfolding B2_def using hKX hKcomp K_def by blast
	            have hInf_open: "Y - Some ` K \<in> TY0"
	              using hBsubY0' hbInf unfolding B_def by blast
	            have hSomeU: "Some ` U \<in> TY0"
	            proof -
	              have hUopen: "U \<in> TX"
	                using hnb unfolding neighborhood_of_def by blast
	              have "Some ` U \<in> B1"
	                unfolding B1_def using hUopen hUX by blast
	              hence "Some ` U \<in> B"
	                unfolding B_def by blast
	              thus ?thesis
	                using hBsubY0' by blast
	            qed
	            have hUsubK: "U \<subseteq> K"
	              unfolding K_def by (rule subset_closure_on)
	            have hdisj: "(Y - Some ` K) \<inter> (Some ` U) = {}"
	            proof -
	              have "(Some ` U) \<subseteq> Some ` K"
	                using hUsubK by blast
	              thus ?thesis
	                by blast
	            qed
	            have hnbNone: "neighborhood_of None Y TY0 (Y - Some ` K)"
	              unfolding neighborhood_of_def using hInf_open unfolding Y_def by blast
	            have hnbSome: "neighborhood_of (Some x0) Y TY0 (Some ` U)"
	              unfolding neighborhood_of_def using hSomeU hnb unfolding neighborhood_of_def by blast
	            show "\<exists>U V. neighborhood_of None Y TY0 U \<and> neighborhood_of (Some x0) Y TY0 V \<and> U \<inter> V = {}"
	              apply (rule exI[where x="Y - Some ` K"])
	              apply (rule exI[where x="Some ` U"])
	              apply (intro conjI hnbNone hnbSome)
	              apply (rule hdisj)
	              done
	          qed
	
	          show ?thesis
	          proof (cases x)
	            case None
	            note hxEq = None
	            show ?thesis
	            proof (cases y)
	              case None
	              have False
	                using hne hxEq None by simp
	              thus ?thesis
	                by simp
	            next
	              case (Some y0)
	              note hyEq = Some
	              have hy0X: "y0 \<in> X"
	                using hyY unfolding Y_def hyEq by blast
		              obtain U V where hnbNone: "neighborhood_of None Y TY0 U"
		                  and hnbSome: "neighborhood_of (Some y0) Y TY0 V"
		                  and hdisj: "U \<inter> V = {}"
		                using hSepNoneSome[OF hy0X] by blast
		              show ?thesis
		              proof (rule exI[where x=U])
		                show "\<exists>V'. neighborhood_of x Y TY0 U \<and> neighborhood_of y Y TY0 V' \<and> U \<inter> V' = {}"
		                proof (rule exI[where x=V])
		                  show "neighborhood_of x Y TY0 U \<and> neighborhood_of y Y TY0 V \<and> U \<inter> V = {}"
		                  proof (intro conjI)
		                    show "neighborhood_of x Y TY0 U"
		                      by (subst hxEq; rule hnbNone)
		                    show "neighborhood_of y Y TY0 V"
		                      by (subst hyEq; rule hnbSome)
		                    show "U \<inter> V = {}"
		                      using hdisj .
		                  qed
		                qed
		              qed
		            qed
		          next
		            case (Some x0)
		            note hxEq = Some
	            show ?thesis
	            proof (cases y)
	              case None
	              note hyEq = None
	              have hx0X: "x0 \<in> X"
	                using hxY unfolding Y_def hxEq by blast
		              obtain U V where hnbNone: "neighborhood_of None Y TY0 U"
		                  and hnbSome: "neighborhood_of (Some x0) Y TY0 V"
		                  and hdisj: "U \<inter> V = {}"
		                using hSepNoneSome[OF hx0X] by blast
		              have hdisj': "V \<inter> U = {}"
		                using hdisj by (simp add: Int_commute)
		              show ?thesis
		              proof (rule exI[where x=V])
		                show "\<exists>V'. neighborhood_of x Y TY0 V \<and> neighborhood_of y Y TY0 V' \<and> V \<inter> V' = {}"
		                proof (rule exI[where x=U])
		                  show "neighborhood_of x Y TY0 V \<and> neighborhood_of y Y TY0 U \<and> V \<inter> U = {}"
		                  proof (intro conjI)
		                    show "neighborhood_of x Y TY0 V"
		                      by (subst hxEq; rule hnbSome)
		                    show "neighborhood_of y Y TY0 U"
		                      by (subst hyEq; rule hnbNone)
		                    show "V \<inter> U = {}"
		                      using hdisj' .
		                  qed
		                qed
		              qed
		            next
		              case (Some y0)
		              note hyEq = Some
	              have hx0X: "x0 \<in> X" using hxY unfolding Y_def hxEq by blast
		              have hy0X: "y0 \<in> X" using hyY unfolding Y_def hyEq by blast
		              have hne0: "x0 \<noteq> y0"
		                using hne hxEq hyEq by simp
		              have hSep0:
		                "\<forall>x\<in>X. \<forall>y\<in>X. x \<noteq> y \<longrightarrow>
		                  (\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
		                using hHaus unfolding is_hausdorff_on_def by (rule conjunct2)
		              have hSep1:
		                "\<forall>y\<in>X. x0 \<noteq> y \<longrightarrow>
		                  (\<exists>U V. neighborhood_of x0 X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {})"
		                by (rule bspec[OF hSep0 hx0X])
		              have hSep2:
		                "x0 \<noteq> y0 \<longrightarrow>
		                  (\<exists>U V. neighborhood_of x0 X TX U \<and> neighborhood_of y0 X TX V \<and> U \<inter> V = {})"
		                by (rule bspec[OF hSep1 hy0X])
		              have hSepxy:
		                "\<exists>U V. neighborhood_of x0 X TX U \<and> neighborhood_of y0 X TX V \<and> U \<inter> V = {}"
		                by (rule mp[OF hSep2 hne0])
		              obtain U V where hnbx: "neighborhood_of x0 X TX U" and hnby: "neighborhood_of y0 X TX V"
		                  and hdisj: "U \<inter> V = {}"
		                using hSepxy by blast
		              have hU: "U \<in> TX" and hx0U: "x0 \<in> U"
		                using hnbx unfolding neighborhood_of_def by blast+
		              have hV: "V \<in> TX" and hy0V: "y0 \<in> V"
		                using hnby unfolding neighborhood_of_def by blast+
	              define U0 where "U0 = X \<inter> U"
	              define V0 where "V0 = X \<inter> V"
	              have hU0: "U0 \<in> TX"
	                unfolding U0_def by (rule topology_inter2[OF hTX X_TX hU])
	              have hV0: "V0 \<in> TX"
	                unfolding V0_def by (rule topology_inter2[OF hTX X_TX hV])
	              have hU0sub: "U0 \<subseteq> X"
	                unfolding U0_def by blast
	              have hV0sub: "V0 \<subseteq> X"
	                unfolding V0_def by blast
	              have hx0U0: "x0 \<in> U0"
	                unfolding U0_def using hx0X hx0U by blast
	              have hy0V0: "y0 \<in> V0"
	                unfolding V0_def using hy0X hy0V by blast
	              have hdisj0: "U0 \<inter> V0 = {}"
	                unfolding U0_def V0_def using hdisj by blast
	              have hSomeU: "Some ` U0 \<in> TY0"
	              proof -
	                have "Some ` U0 \<in> B1"
	                  unfolding B1_def using hU0 hU0sub by blast
	                hence "Some ` U0 \<in> B"
	                  unfolding B_def by blast
	                thus ?thesis
	                  using hBsubY0' by blast
	              qed
	              have hSomeV: "Some ` V0 \<in> TY0"
	              proof -
	                have "Some ` V0 \<in> B1"
	                  unfolding B1_def using hV0 hV0sub by blast
	                hence "Some ` V0 \<in> B"
	                  unfolding B_def by blast
	                thus ?thesis
	                  using hBsubY0' by blast
	              qed
	              have hxnb: "neighborhood_of (Some x0) Y TY0 (Some ` U0)"
	                unfolding neighborhood_of_def using hSomeU hx0U0 unfolding Y_def by blast
	              have hynb: "neighborhood_of (Some y0) Y TY0 (Some ` V0)"
	                unfolding neighborhood_of_def using hSomeV hy0V0 unfolding Y_def by blast
		              have hdisjSV: "(Some ` U0) \<inter> (Some ` V0) = {}"
		                using hdisj0 by blast
		              show ?thesis
		              proof (rule exI[where x="Some ` U0"])
		                show "\<exists>V'. neighborhood_of x Y TY0 (Some ` U0) \<and> neighborhood_of y Y TY0 V' \<and> (Some ` U0) \<inter> V' = {}"
		                proof (rule exI[where x="Some ` V0"])
		                  show "neighborhood_of x Y TY0 (Some ` U0) \<and> neighborhood_of y Y TY0 (Some ` V0) \<and> (Some ` U0) \<inter> (Some ` V0) = {}"
		                  proof (intro conjI)
		                    show "neighborhood_of x Y TY0 (Some ` U0)"
		                      by (subst hxEq; rule hxnb)
		                    show "neighborhood_of y Y TY0 (Some ` V0)"
		                      by (subst hyEq; rule hynb)
		                    show "(Some ` U0) \<inter> (Some ` V0) = {}"
		                      using hdisjSV .
		                  qed
		                qed
		              qed
		            qed
		          qed
		        qed
		      qed
	    qed

	    have hHomeo':
	      "top1_homeomorphism_on X TX (Some ` X)
	        (subspace_topology (insert None (Some ` X)) TY0 (Some ` X)) Some"
	      using hHomeo unfolding Y_def by simp
	    have hCompY': "top1_compact_on (insert None (Some ` X)) TY0"
	      using hCompY unfolding Y_def by simp
	    have hHausY': "is_hausdorff_on (insert None (Some ` X)) TY0"
	      using hHausY unfolding Y_def by simp

			    have hOPC: "top1_one_point_compactification_on X TX TY0"
			      unfolding top1_one_point_compactification_on_def
			      unfolding Let_def
			      using hHomeo' hCompY' hHausY' by simp
	
					    show "\<exists>TY. top1_one_point_compactification_on X TX TY"
					      using hOPC
					      by (rule exI[where x=TY0])
				  qed

				  have backward_imp:
				    "(\<exists>TY. top1_one_point_compactification_on X TX TY)
				      \<Longrightarrow> (top1_locally_compact_on X TX \<and> is_hausdorff_on X TX)"
				  proof -
				    assume hEx: "\<exists>TY. top1_one_point_compactification_on X TX TY"
				    obtain TY where hOPC: "top1_one_point_compactification_on X TX TY"
				      using hEx by blast

				    let ?S = "Some ` X"
				    let ?TS = "subspace_topology Y TY ?S"

				    have hProps:
				      "top1_homeomorphism_on X TX ?S ?TS Some \<and> top1_compact_on Y TY \<and> is_hausdorff_on Y TY"
				      using hOPC unfolding top1_one_point_compactification_on_def Y_def Let_def by simp
				    have hHomeoS: "top1_homeomorphism_on X TX ?S ?TS Some"
				      using hProps by blast
				    have hCompY: "top1_compact_on Y TY"
				      using hProps by blast
				    have hHausY: "is_hausdorff_on Y TY"
				      using hProps by blast

				    have hSY: "?S \<subseteq> Y"
				      unfolding Y_def by blast
				    have hNoneY: "None \<in> Y"
				      unfolding Y_def by simp

				    have hS_open: "?S \<in> TY"
				    proof -
				      have hNoneClosed: "closedin_on Y TY {None}"
				        by (rule singleton_closed_in_hausdorff[OF hHausY hNoneY])
				      have hEq: "Y - {None} = ?S"
				        unfolding Y_def by blast
				      have "Y - {None} \<in> TY"
				        by (rule closedin_diff_open[OF hNoneClosed])
				      thus ?thesis
				        using hEq by simp
				    qed

				    have hLC_S: "top1_locally_compact_on ?S ?TS"
				      by (rule top1_locally_compact_on_open_subspace_of_compact_hausdorff[OF hCompY hHausY hS_open hSY])
				    have hLCX: "top1_locally_compact_on X TX"
				      by (rule top1_locally_compact_on_of_homeomorphism_on[OF hHomeoS hLC_S])

				    have hSubHaus:
				      "\<forall>X0 T0 Z. is_hausdorff_on X0 T0 \<and> Z \<subseteq> X0 \<longrightarrow> is_hausdorff_on Z (subspace_topology X0 T0 Z)"
				      using Theorem_17_11 by blast
				    have hHausS: "is_hausdorff_on ?S ?TS"
				      using hSubHaus hHausY hSY by blast
				    have hHausX: "is_hausdorff_on X TX"
				      by (rule is_hausdorff_on_of_homeomorphism_on[OF hHomeoS hHausS])

							    show "top1_locally_compact_on X TX \<and> is_hausdorff_on X TX"
							      by (rule conjI[OF hLCX hHausX])
						  qed
			
				  show "(top1_locally_compact_on X TX \<and> is_hausdorff_on X TX) \<longleftrightarrow> (\<exists>TY. top1_one_point_compactification_on X TX TY)"
				  proof (rule iffI)
			    assume hLH: "top1_locally_compact_on X TX \<and> is_hausdorff_on X TX"
    show "\<exists>TY. top1_one_point_compactification_on X TX TY"
      using forward_imp[OF hLH] .
  next
    assume hEx: "\<exists>TY. top1_one_point_compactification_on X TX TY"
    show "top1_locally_compact_on X TX \<and> is_hausdorff_on X TX"
      using backward_imp[OF hEx] .
  qed

  show "\<forall>TY TY'. top1_one_point_compactification_on X TX TY \<and> top1_one_point_compactification_on X TX TY'
        \<longrightarrow> (\<exists>h. top1_homeomorphism_on (insert None (Some ` X)) TY (insert None (Some ` X)) TY' h
              \<and> (\<forall>x\<in>X. h (Some x) = Some x))"
  proof (intro allI impI)
    fix TY TY'
    assume hBoth: "top1_one_point_compactification_on X TX TY \<and> top1_one_point_compactification_on X TX TY'"
    have hOPC: "top1_one_point_compactification_on X TX TY"
      using hBoth by blast
    have hOPC': "top1_one_point_compactification_on X TX TY'"
      using hBoth by blast

    let ?S = "Some ` X"
    let ?TS = "subspace_topology Y TY ?S"
    let ?TS' = "subspace_topology Y TY' ?S"

    have hProps:
      "top1_homeomorphism_on X TX ?S ?TS Some \<and> top1_compact_on Y TY \<and> is_hausdorff_on Y TY"
      using hOPC unfolding top1_one_point_compactification_on_def Y_def Let_def by simp
    have hProps':
      "top1_homeomorphism_on X TX ?S ?TS' Some \<and> top1_compact_on Y TY' \<and> is_hausdorff_on Y TY'"
      using hOPC' unfolding top1_one_point_compactification_on_def Y_def Let_def by simp

    have hHomeoS: "top1_homeomorphism_on X TX ?S ?TS Some"
      using hProps by blast
    have hHomeoS': "top1_homeomorphism_on X TX ?S ?TS' Some"
      using hProps' by blast

    have hCompY: "top1_compact_on Y TY"
      using hProps by blast
    have hCompY': "top1_compact_on Y TY'"
      using hProps' by blast

    have hHausY: "is_hausdorff_on Y TY"
      using hProps by blast
    have hHausY': "is_hausdorff_on Y TY'"
      using hProps' by blast

    have hTopY: "is_topology_on Y TY"
      using hCompY unfolding top1_compact_on_def by blast
    have hTopY': "is_topology_on Y TY'"
      using hCompY' unfolding top1_compact_on_def by blast

    have hYinTY: "Y \<in> TY"
      by (rule conjunct1[OF conjunct2[OF hTopY[unfolded is_topology_on_def]]])
    have hYinTY': "Y \<in> TY'"
      by (rule conjunct1[OF conjunct2[OF hTopY'[unfolded is_topology_on_def]]])

    have hNoneY: "None \<in> Y"
      unfolding Y_def by simp

    have hS_open: "?S \<in> TY"
    proof -
      have hNoneClosed: "closedin_on Y TY {None}"
        by (rule singleton_closed_in_hausdorff[OF hHausY hNoneY])
      have hEq: "Y - {None} = ?S"
        unfolding Y_def by blast
      have "Y - {None} \<in> TY"
        by (rule closedin_diff_open[OF hNoneClosed])
      thus ?thesis
        using hEq by simp
    qed

    have hS_open': "?S \<in> TY'"
    proof -
      have hNoneClosed: "closedin_on Y TY' {None}"
        by (rule singleton_closed_in_hausdorff[OF hHausY' hNoneY])
      have hEq: "Y - {None} = ?S"
        unfolding Y_def by blast
      have "Y - {None} \<in> TY'"
        by (rule closedin_diff_open[OF hNoneClosed])
      thus ?thesis
        using hEq by simp
    qed

    have hTS_eq: "?TS = ?TS'"
    proof (rule subset_antisym)
      show "?TS \<subseteq> ?TS'"
      proof (rule subsetI)
        fix W
        assume hW: "W \<in> ?TS"
        define A where "A = {x \<in> X. Some x \<in> W}"
        have hcontSome: "top1_continuous_map_on X TX ?S ?TS Some"
          using hHomeoS unfolding top1_homeomorphism_on_def by blast
        have hA: "A \<in> TX"
          using hcontSome hW unfolding top1_continuous_map_on_def A_def by blast
        have hcontInv': "top1_continuous_map_on ?S ?TS' X TX (inv_into X Some)"
          using hHomeoS' unfolding top1_homeomorphism_on_def by blast
        have hOpenA': "{y \<in> ?S. inv_into X Some y \<in> A} \<in> ?TS'"
          using hcontInv' hA unfolding top1_continuous_map_on_def by blast
        have hEq: "{y \<in> ?S. inv_into X Some y \<in> A} = W"
        proof (rule set_eqI)
          fix y
          show "y \<in> {y \<in> ?S. inv_into X Some y \<in> A} \<longleftrightarrow> y \<in> W"
          proof
            assume hy: "y \<in> {y \<in> ?S. inv_into X Some y \<in> A}"
            have hyS: "y \<in> ?S" and hinvA: "inv_into X Some y \<in> A"
              using hy by blast+
	            obtain x where hxX: "x \<in> X" and hyEq: "y = Some x"
	              using hyS by blast
	            have hinv: "inv_into X Some y = x"
	              unfolding hyEq by (rule inv_into_f_f; simp add: hxX inj_on_def)
	            have "Some x \<in> W"
	              using hinvA by (simp add: A_def hinv)
	            thus "y \<in> W"
	              using hyEq by simp
          next
            assume hyW: "y \<in> W"
            have hyS: "y \<in> ?S"
            proof -
              obtain U where hU: "U \<in> TY" and hWEq: "W = ?S \<inter> U"
                using hW unfolding subspace_topology_def by blast
              show ?thesis
                using hyW hWEq by blast
            qed
	            obtain x where hxX: "x \<in> X" and hyEq: "y = Some x"
	              using hyS by blast
	            have hinv: "inv_into X Some y = x"
	              unfolding hyEq by (rule inv_into_f_f; simp add: hxX inj_on_def)
		            have hxA: "x \<in> A"
		              using hyW hxX hyEq unfolding A_def by simp
		            show "y \<in> {y \<in> ?S. inv_into X Some y \<in> A}"
		            proof -
		              have hInvA: "inv_into X Some y \<in> A"
		                by (subst hinv; rule hxA)
		              show ?thesis
		                using hyS hInvA by simp
		            qed
	          qed
	        qed
	        show "W \<in> ?TS'"
	          using hOpenA' unfolding hEq by simp
      qed

      show "?TS' \<subseteq> ?TS"
      proof (rule subsetI)
        fix W
        assume hW: "W \<in> ?TS'"
        define A where "A = {x \<in> X. Some x \<in> W}"
        have hcontSome: "top1_continuous_map_on X TX ?S ?TS' Some"
          using hHomeoS' unfolding top1_homeomorphism_on_def by blast
        have hA: "A \<in> TX"
          using hcontSome hW unfolding top1_continuous_map_on_def A_def by blast
        have hcontInv: "top1_continuous_map_on ?S ?TS X TX (inv_into X Some)"
          using hHomeoS unfolding top1_homeomorphism_on_def by blast
        have hOpenA: "{y \<in> ?S. inv_into X Some y \<in> A} \<in> ?TS"
          using hcontInv hA unfolding top1_continuous_map_on_def by blast
        have hEq: "{y \<in> ?S. inv_into X Some y \<in> A} = W"
        proof (rule set_eqI)
          fix y
          show "y \<in> {y \<in> ?S. inv_into X Some y \<in> A} \<longleftrightarrow> y \<in> W"
          proof
            assume hy: "y \<in> {y \<in> ?S. inv_into X Some y \<in> A}"
            have hyS: "y \<in> ?S" and hinvA: "inv_into X Some y \<in> A"
              using hy by blast+
	            obtain x where hxX: "x \<in> X" and hyEq: "y = Some x"
	              using hyS by blast
	            have hinv: "inv_into X Some y = x"
	              unfolding hyEq by (rule inv_into_f_f; simp add: hxX inj_on_def)
	            have "Some x \<in> W"
	              using hinvA by (simp add: A_def hinv)
	            thus "y \<in> W"
	              using hyEq by simp
          next
            assume hyW: "y \<in> W"
            have hyS: "y \<in> ?S"
            proof -
              obtain U where hU: "U \<in> TY'" and hWEq: "W = ?S \<inter> U"
                using hW unfolding subspace_topology_def by blast
              show ?thesis
                using hyW hWEq by blast
            qed
	            obtain x where hxX: "x \<in> X" and hyEq: "y = Some x"
	              using hyS by blast
	            have hinv: "inv_into X Some y = x"
	              unfolding hyEq by (rule inv_into_f_f; simp add: hxX inj_on_def)
	            have hxA: "x \<in> A"
	              using hyW hxX hyEq unfolding A_def by simp
	            show "y \<in> {y \<in> ?S. inv_into X Some y \<in> A}"
	            proof -
	              have hInvA: "inv_into X Some y \<in> A"
	                by (subst hinv; rule hxA)
	              show ?thesis
	                using hyS hInvA by simp
	            qed
	          qed
	        qed
        show "W \<in> ?TS"
          using hOpenA unfolding hEq by simp
      qed
    qed

									    have hOpenSubsetEq: "\<And>W. W \<subseteq> Y \<Longrightarrow> (W \<in> TY \<longleftrightarrow> W \<in> TY')"
									    proof -
									      fix W
									      assume hWY: "W \<subseteq> Y"
									      show "W \<in> TY \<longleftrightarrow> W \<in> TY'"
									      proof (cases "None \<in> W")
									        case False
									        have hWsubS: "W \<subseteq> ?S"
									        proof (rule subsetI)
									          fix w
									          assume hw: "w \<in> W"
									          have hwY: "w \<in> Y"
									            using hWY hw by blast
									          have hw_notNone: "w \<noteq> None"
									          proof
									            assume h: "w = None"
									            have "None \<in> W"
									              using hw h by simp
									            thus False
									              using False by contradiction
									          qed
									          show "w \<in> ?S"
									          proof (cases w)
									            case None
									            thus ?thesis
									              using hw_notNone by contradiction
									          next
									            case (Some x)
									            have "Some x \<in> Some ` X"
									              using hwY hw_notNone unfolding Y_def Some by blast
									            thus ?thesis
									              using Some by simp
									          qed
									        qed

									        have hTY_iff: "W \<in> TY \<longleftrightarrow> W \<in> ?TS"
									        proof
									          assume hWopen: "W \<in> TY"
									          have hEq: "W = ?S \<inter> W"
									          proof (rule equalityI)
									            show "W \<subseteq> ?S \<inter> W"
									              using hWsubS by blast
									            show "?S \<inter> W \<subseteq> W"
									              by blast
									          qed
									          show "W \<in> ?TS"
									            unfolding subspace_topology_def
									            apply (rule CollectI)
									            apply (rule exI[where x=W])
									            apply (intro conjI)
									             apply (rule hEq)
									            apply (rule hWopen)
									            done
									        next
									          assume hWopen: "W \<in> ?TS"
									          obtain U where hU: "U \<in> TY" and hEq: "W = ?S \<inter> U"
									            using hWopen unfolding subspace_topology_def by blast
									          have hInt: "?S \<inter> U \<in> TY"
									            by (rule topology_inter2[OF hTopY hS_open hU])
									          show "W \<in> TY"
									            by (subst hEq, rule hInt)
									        qed

									        have hTY'_iff: "W \<in> TY' \<longleftrightarrow> W \<in> ?TS'"
									        proof
									          assume hWopen: "W \<in> TY'"
									          have hEq: "W = ?S \<inter> W"
									          proof (rule equalityI)
									            show "W \<subseteq> ?S \<inter> W"
									              using hWsubS by blast
									            show "?S \<inter> W \<subseteq> W"
									              by blast
									          qed
									          show "W \<in> ?TS'"
									            unfolding subspace_topology_def
									            apply (rule CollectI)
									            apply (rule exI[where x=W])
									            apply (intro conjI)
									             apply (rule hEq)
									            apply (rule hWopen)
									            done
									        next
									          assume hWopen: "W \<in> ?TS'"
									          obtain U where hU: "U \<in> TY'" and hEq: "W = ?S \<inter> U"
									            using hWopen unfolding subspace_topology_def by blast
									          have hInt: "?S \<inter> U \<in> TY'"
									            by (rule topology_inter2[OF hTopY' hS_open' hU])
									          show "W \<in> TY'"
									            by (subst hEq, rule hInt)
									        qed

									        have hTS_mem: "W \<in> ?TS \<longleftrightarrow> W \<in> ?TS'"
									          using hTS_eq by simp

									        show ?thesis
									        proof
									          assume hWopen: "W \<in> TY"
									          have "W \<in> ?TS"
									            using iffD1[OF hTY_iff hWopen] .
									          have "W \<in> ?TS'"
									            using iffD1[OF hTS_mem \<open>W \<in> ?TS\<close>] .
									          show "W \<in> TY'"
									            using iffD2[OF hTY'_iff \<open>W \<in> ?TS'\<close>] .
									        next
									          assume hWopen: "W \<in> TY'"
									          have "W \<in> ?TS'"
									            using iffD1[OF hTY'_iff hWopen] .
									          have "W \<in> ?TS"
									            using iffD2[OF hTS_mem \<open>W \<in> ?TS'\<close>] .
									          show "W \<in> TY"
									            using iffD2[OF hTY_iff \<open>W \<in> ?TS\<close>] .
									        qed
									      next
									        case True
									        define C where "C = Y - W"
									        have hCY: "C \<subseteq> Y"
									          unfolding C_def by blast
									        have hCsubS: "C \<subseteq> ?S"
									        proof (rule subsetI)
									          fix c
									          assume hc: "c \<in> C"
									          have hcY: "c \<in> Y"
									            using hc unfolding C_def by blast
									          have hc_notW: "c \<notin> W"
									            using hc unfolding C_def by blast
									          have hc_notNone: "c \<noteq> None"
									          proof
									            assume h: "c = None"
									            have "None \<notin> W"
									              using hc_notW h by simp
									            thus False
									              using True by contradiction
									          qed
									          show "c \<in> ?S"
									          proof (cases c)
									            case None
									            thus ?thesis
									              using hc_notNone by contradiction
									          next
									            case (Some x)
									            have "Some x \<in> Some ` X"
									              using hcY hc_notNone unfolding Y_def Some by blast
									            thus ?thesis
									              using Some by simp
									          qed
									        qed

									        have hYC: "Y - C = W"
									        proof -
									          have h1: "Y - C = Y \<inter> W"
									            by (simp only: C_def Diff_Diff_Int)
									          have h2: "Y \<inter> W = W"
									          proof (rule equalityI)
									            show "Y \<inter> W \<subseteq> W"
									              by blast
									            show "W \<subseteq> Y \<inter> W"
									              using hWY by blast
									          qed
									          show ?thesis
									            using h1 h2 by simp
									        qed

									        have hTopEq: "subspace_topology ?S ?TS C = subspace_topology Y TY C"
									          using subspace_topology_trans[OF hCsubS] by simp
									        have hTopEq': "subspace_topology ?S ?TS' C = subspace_topology Y TY' C"
									          using subspace_topology_trans[OF hCsubS] by simp

									        show ?thesis
									        proof
									          assume hWopen: "W \<in> TY"

									          have hC_closed: "closedin_on Y TY C"
									          proof (rule closedin_intro)
									            show "C \<subseteq> Y"
									              by (rule hCY)
									            show "Y - C \<in> TY"
									              using hWopen hYC by simp
									          qed

									          have hC_comp: "top1_compact_on C (subspace_topology Y TY C)"
									            by (rule Theorem_26_2[OF hCompY hC_closed])

									          have hC_compS: "top1_compact_on C (subspace_topology ?S ?TS C)"
									            by (subst hTopEq, rule hC_comp)
									          have hC_compS': "top1_compact_on C (subspace_topology ?S ?TS' C)"
									            by (subst hTS_eq[symmetric], rule hC_compS)
									          have hC_comp': "top1_compact_on C (subspace_topology Y TY' C)"
									            by (subst hTopEq'[symmetric], rule hC_compS')

									          have hC_closed': "closedin_on Y TY' C"
									            by (rule Theorem_26_3[OF hHausY' hCY hC_comp'])
									          have "Y - C \<in> TY'"
									            by (rule closedin_diff_open[OF hC_closed'])
									          thus "W \<in> TY'"
									            using hYC by simp
									        next
									          assume hWopen: "W \<in> TY'"

									          have hC_closed: "closedin_on Y TY' C"
									          proof (rule closedin_intro)
									            show "C \<subseteq> Y"
									              by (rule hCY)
									            show "Y - C \<in> TY'"
									              using hWopen hYC by simp
									          qed

									          have hC_comp: "top1_compact_on C (subspace_topology Y TY' C)"
									            by (rule Theorem_26_2[OF hCompY' hC_closed])

									          have hC_compS: "top1_compact_on C (subspace_topology ?S ?TS' C)"
									            by (subst hTopEq', rule hC_comp)
									          have hC_compS': "top1_compact_on C (subspace_topology ?S ?TS C)"
									            by (subst hTS_eq, rule hC_compS)
									          have hC_comp': "top1_compact_on C (subspace_topology Y TY C)"
									            by (subst hTopEq[symmetric], rule hC_compS')

									          have hC_closed': "closedin_on Y TY C"
									            by (rule Theorem_26_3[OF hHausY hCY hC_comp'])
									          have "Y - C \<in> TY"
									            by (rule closedin_diff_open[OF hC_closed'])
									          thus "W \<in> TY"
									            using hYC by simp
									        qed
									      qed
									    qed
					
						    define h :: "'a option \<Rightarrow> 'a option" where "h = (\<lambda>z. z)"
	
	    have hCont: "top1_continuous_map_on Y TY Y TY' h"
      unfolding top1_continuous_map_on_def h_def
    proof (intro conjI)
      show "\<forall>x\<in>Y. x \<in> Y"
        by simp
      show "\<forall>V\<in>TY'. {x \<in> Y. x \<in> V} \<in> TY"
      proof (intro ballI)
        fix V
        assume hV: "V \<in> TY'"
        have hW: "Y \<inter> V \<in> TY'"
          by (rule topology_inter2[OF hTopY' hYinTY' hV])
        have hWsub: "Y \<inter> V \<subseteq> Y"
          by blast
	        have "(Y \<inter> V) \<in> TY"
	          using hOpenSubsetEq[OF hWsub] hW by blast
	        thus "{x \<in> Y. x \<in> V} \<in> TY"
	          by (simp add: Int_def)
	      qed
	    qed

	    have hContInv: "top1_continuous_map_on Y TY' Y TY h"
	      unfolding top1_continuous_map_on_def h_def
	    proof (intro conjI)
      show "\<forall>x\<in>Y. x \<in> Y"
        by simp
      show "\<forall>V\<in>TY. {x \<in> Y. x \<in> V} \<in> TY'"
      proof (intro ballI)
        fix V
        assume hV: "V \<in> TY"
        have hW: "Y \<inter> V \<in> TY"
          by (rule topology_inter2[OF hTopY hYinTY hV])
        have hWsub: "Y \<inter> V \<subseteq> Y"
          by blast
	        have "(Y \<inter> V) \<in> TY'"
	          using hOpenSubsetEq[OF hWsub] hW by blast
	        thus "{x \<in> Y. x \<in> V} \<in> TY'"
	          by (simp add: Int_def)
	      qed
	    qed

		    have hInvEq: "\<forall>x\<in>Y. inv_into Y h x = h x"
		    proof (intro ballI)
		      fix x
		      assume hx: "x \<in> Y"
		      show "inv_into Y h x = h x"
		      proof -
		        have hx': "h x = x"
		          unfolding h_def by simp
		        have hInv: "inv_into Y h (h x) = x"
		          by (rule inv_into_f_f; simp add: hx h_def inj_on_def)
		        have "inv_into Y h x = x"
		          using hInv hx' by simp
		        thus ?thesis
		          using hx' by simp
		      qed
		    qed
		    have hContInvInto: "top1_continuous_map_on Y TY' Y TY (inv_into Y h)"
		      using top1_continuous_map_on_cong[OF hInvEq] hContInv by blast
	
	    have hHomeo: "top1_homeomorphism_on Y TY Y TY' h"
	      unfolding top1_homeomorphism_on_def
	      apply (intro conjI)
	          apply (rule hTopY)
	         apply (rule hTopY')
	        apply (simp add: h_def bij_betw_def inj_on_def)
	       apply (rule hCont)
	      apply (rule hContInvInto)
	      done
		    show "\<exists>h. top1_homeomorphism_on (insert None (Some ` X)) TY (insert None (Some ` X)) TY' h
		              \<and> (\<forall>x\<in>X. h (Some x) = Some x)"
		    proof (rule exI[where x=h], intro conjI)
		      show "top1_homeomorphism_on (insert None (Some ` X)) TY (insert None (Some ` X)) TY' h"
		        using hHomeo
		        by (simp add: Y_def[symmetric]; assumption)
		      show "\<forall>x\<in>X. h (Some x) = Some x"
		        by (simp add: h_def)
		    qed
	  qed
qed

(** from \S29 Theorem 29.2 [top1.tex:3767] **)
theorem Theorem_29_2:
  assumes hH: "is_hausdorff_on X TX"
  shows "top1_locally_compact_on X TX \<longleftrightarrow>
    (\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
        (\<exists>V. neighborhood_of x X TX V \<and>
             top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
             \<and> closure_on X TX V \<subseteq> U))"
proof -
  have hTX: "is_topology_on X TX"
    using hH unfolding is_hausdorff_on_def by blast
  have X_TX: "X \<in> TX"
    by (rule conjunct1[OF conjunct2[OF hTX[unfolded is_topology_on_def]]])

  show ?thesis
  proof (rule iffI)
    assume hLC: "top1_locally_compact_on X TX"
    have hLC_top: "is_topology_on X TX"
      using hLC unfolding top1_locally_compact_on_def by blast
    have hLC_ex:
      "\<forall>x\<in>X. \<exists>U. neighborhood_of x X TX U \<and> U \<subseteq> X
         \<and> top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
      using hLC unfolding top1_locally_compact_on_def by blast

    show "\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
        (\<exists>V. neighborhood_of x X TX V \<and>
             top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
             \<and> closure_on X TX V \<subseteq> U)"
    proof (intro ballI allI impI)
      fix x U
      assume hxX: "x \<in> X"
      assume hU: "neighborhood_of x X TX U"
      have hUT: "U \<in> TX" and hxU: "x \<in> U"
        using hU unfolding neighborhood_of_def by blast+

      obtain N where hN: "neighborhood_of x X TX N"
          and hNX: "N \<subseteq> X"
          and hKcomp: "top1_compact_on (closure_on X TX N) (subspace_topology X TX (closure_on X TX N))"
        using hLC_ex hxX by blast

      define K where "K = closure_on X TX N"
      have hKN: "N \<subseteq> K"
        unfolding K_def by (rule subset_closure_on)
      have hKX: "K \<subseteq> X"
        unfolding K_def by (rule closure_on_subset_carrier[OF hLC_top hNX])

      define U' where "U' = X \<inter> U"
      have hU'T: "U' \<in> TX"
        unfolding U'_def
        by (rule topology_inter2[OF hLC_top X_TX hUT])
      have hxU': "x \<in> U'"
        unfolding U'_def using hxX hxU by blast
      have hU'sub: "U' \<subseteq> X"
        unfolding U'_def by blast
      have hU'subU: "U' \<subseteq> U"
        unfolding U'_def by blast

      define C where "C = K - U'"
      have hCX: "C \<subseteq> X"
        unfolding C_def using hKX by blast
      have hxK: "x \<in> K"
      proof -
        have hxN: "x \<in> N"
          using hN unfolding neighborhood_of_def by blast
        have "x \<in> closure_on X TX N"
          by (rule subsetD[OF subset_closure_on, OF hxN])
        thus ?thesis unfolding K_def by simp
      qed
      have hx_not_C: "x \<notin> C"
        unfolding C_def using hxK hxU' by blast

      have hXmU'_closed: "closedin_on X TX (X - U')"
      proof (rule closedin_intro)
        show "X - U' \<subseteq> X"
          by (rule Diff_subset)
        have hEq: "X - (X - U') = U'"
          using hU'sub by blast
        show "X - (X - U') \<in> TX"
          using hU'T hEq by simp
      qed

      have hC_closed_K: "closedin_on K (subspace_topology X TX K) C"
      proof -
        have hEq: "C = (X - U') \<inter> K"
        proof (rule set_eqI)
          fix z
          show "z \<in> C \<longleftrightarrow> z \<in> (X - U') \<inter> K"
          proof
            assume hz: "z \<in> C"
            have hzK: "z \<in> K" and hzU': "z \<notin> U'"
              using hz unfolding C_def by blast+
            have hzX: "z \<in> X"
              using hKX hzK by blast
            have hzXmU': "z \<in> X - U'"
              using hzX hzU' by blast
            show "z \<in> (X - U') \<inter> K"
              using hzXmU' hzK by blast
          next
            assume hz: "z \<in> (X - U') \<inter> K"
            have hzK: "z \<in> K" and hzU': "z \<notin> U'"
              using hz by blast+
            show "z \<in> C"
              unfolding C_def using hzK hzU' by blast
          qed
        qed
        have "\<exists>D. closedin_on X TX D \<and> C = D \<inter> K"
          apply (rule exI[where x="X - U'"])
          apply (intro conjI)
           apply (rule hXmU'_closed)
          apply (rule hEq)
          done
        have hKX': "K \<subseteq> X" by (rule hKX)
        show ?thesis
          using Theorem_17_2[OF hLC_top hKX', of C] \<open>\<exists>D. closedin_on X TX D \<and> C = D \<inter> K\<close>
          by blast
      qed

      have hCcomp: "top1_compact_on C (subspace_topology X TX C)"
      proof -
        have hKcomp': "top1_compact_on K (subspace_topology X TX K)"
          using hKcomp unfolding K_def by simp
        have hCcomp0: "top1_compact_on C (subspace_topology K (subspace_topology X TX K) C)"
          by (rule Theorem_26_2[OF hKcomp' hC_closed_K])
        have hCK: "C \<subseteq> K" unfolding C_def by blast
        have hTopEq: "subspace_topology K (subspace_topology X TX K) C = subspace_topology X TX C"
          by (rule subspace_topology_trans[OF hCK])
        show ?thesis using hCcomp0 hTopEq by simp
      qed

      have hKcomp_sub: "top1_compact_on K (subspace_topology X TX K)"
        using hKcomp unfolding K_def by simp

      obtain P0 Q0 where hP0T: "P0 \<in> TX" and hQ0T: "Q0 \<in> TX"
          and hxP0: "x \<in> P0" and hCsubQ0: "C \<subseteq> Q0" and hdisj0: "P0 \<inter> Q0 = {}"
        using Lemma_26_4[OF hH hCX hCcomp hxX hx_not_C] by blast

      define P where "P = X \<inter> P0"
      define Q where "Q = X \<inter> Q0"

      have hPT: "P \<in> TX"
        unfolding P_def by (rule topology_inter2[OF hLC_top X_TX hP0T])
      have hQT: "Q \<in> TX"
        unfolding Q_def by (rule topology_inter2[OF hLC_top X_TX hQ0T])
      have hxP: "x \<in> P"
        unfolding P_def using hxX hxP0 by blast
      have hCsubQ: "C \<subseteq> Q"
        unfolding Q_def using hCX hCsubQ0 by blast
      have hdisj: "P \<inter> Q = {}"
        unfolding P_def Q_def using hdisj0 by blast

      define V where "V = X \<inter> N \<inter> P0"

      have hVT: "V \<in> TX"
      proof -
        have XN_T: "X \<inter> N \<in> TX"
        proof -
          have hNT: "N \<in> TX"
            using hN unfolding neighborhood_of_def by blast
          show ?thesis
            by (rule topology_inter2[OF hLC_top X_TX hNT])
        qed
        show ?thesis
          unfolding V_def
          by (rule topology_inter2[OF hLC_top XN_T hP0T])
      qed
      have hxV: "x \<in> V"
      proof -
        have hxN: "x \<in> N"
          using hN unfolding neighborhood_of_def by blast
        show ?thesis
          unfolding V_def using hxX hxN hxP0 by blast
      qed
      have hVnbhd: "neighborhood_of x X TX V"
        unfolding neighborhood_of_def using hVT hxV by blast

      have hVsubK: "V \<subseteq> K"
      proof -
        have hVN: "V \<subseteq> N" unfolding V_def by blast
        have hNK: "N \<subseteq> K" by (rule hKN)
        show ?thesis by (rule subset_trans[OF hVN hNK])
      qed
      have hVsubP: "V \<subseteq> P"
        unfolding V_def P_def by blast
      have hPsub: "P \<subseteq> X - Q"
        using hdisj unfolding P_def Q_def by blast
      have hVsubXmQ: "V \<subseteq> X - Q"
        by (rule subset_trans[OF hVsubP hPsub])

      have hXmQ_closed: "closedin_on X TX (X - Q)"
      proof (rule closedin_intro)
        show "X - Q \<subseteq> X"
          by (rule Diff_subset)
        have hEq: "X - (X - Q) = Q"
          unfolding Q_def by blast
        show "X - (X - Q) \<in> TX"
          using hQT hEq by simp
      qed

      have clV_sub_XmQ: "closure_on X TX V \<subseteq> X - Q"
        by (rule closure_on_subset_of_closed[OF hXmQ_closed hVsubXmQ])

      have hK_closed: "closedin_on X TX K"
        unfolding K_def by (rule closure_on_closed[OF hLC_top hNX])
      have clV_sub_K: "closure_on X TX V \<subseteq> K"
        by (rule closure_on_subset_of_closed[OF hK_closed hVsubK])

      have clV_sub_U': "closure_on X TX V \<subseteq> U'"
      proof (rule subsetI)
        fix z
        assume hz: "z \<in> closure_on X TX V"
        have hzK: "z \<in> K"
          using clV_sub_K hz by blast
        have hz_not_Q: "z \<notin> Q"
        proof
          assume hzQ: "z \<in> Q"
          have "z \<in> X - Q"
            using clV_sub_XmQ hz by blast
          thus False using hzQ by blast
        qed
        show "z \<in> U'"
        proof (rule ccontr)
          assume hzU': "z \<notin> U'"
          have hzC: "z \<in> C"
            unfolding C_def using hzK hzU' by blast
          have hzQ: "z \<in> Q"
            using hCsubQ hzC by blast
          show False using hz_not_Q hzQ by contradiction
        qed
      qed
      have clV_sub_U: "closure_on X TX V \<subseteq> U"
        by (rule subset_trans[OF clV_sub_U' hU'subU])

      have clV_comp: "top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))"
      proof -
        have hclVX: "closure_on X TX V \<subseteq> X"
        proof -
          have hVX: "V \<subseteq> X" unfolding V_def by blast
          show ?thesis
            by (rule closure_on_subset_carrier[OF hLC_top hVX])
        qed
        have hclV_closed: "closedin_on X TX (closure_on X TX V)"
        proof -
          have hVX: "V \<subseteq> X" unfolding V_def by blast
          show ?thesis
            by (rule closure_on_closed[OF hLC_top hVX])
        qed
        have hclV_in_K: "closure_on X TX V \<subseteq> K"
          by (rule clV_sub_K)
        have hclV_closed_K: "closedin_on K (subspace_topology X TX K) (closure_on X TX V)"
        proof -
          have hEq: "closure_on X TX V = (closure_on X TX V) \<inter> K"
            using hclV_in_K by blast
          have "\<exists>D. closedin_on X TX D \<and> closure_on X TX V = D \<inter> K"
            apply (rule exI[where x="closure_on X TX V"])
            apply (intro conjI)
             apply (rule hclV_closed)
            apply (rule hEq)
            done
          have hKX': "K \<subseteq> X" by (rule hKX)
          show ?thesis
            using Theorem_17_2[OF hLC_top hKX', of "closure_on X TX V"] \<open>\<exists>D. closedin_on X TX D \<and> closure_on X TX V = D \<inter> K\<close>
            by blast
        qed

        have hclVcomp0:
          "top1_compact_on (closure_on X TX V)
            (subspace_topology K (subspace_topology X TX K) (closure_on X TX V))"
          by (rule Theorem_26_2[OF hKcomp_sub hclV_closed_K])
        have hTopEq:
          "subspace_topology K (subspace_topology X TX K) (closure_on X TX V)
             = subspace_topology X TX (closure_on X TX V)"
          by (rule subspace_topology_trans[OF hclV_in_K])
        show ?thesis
          using hclVcomp0 hTopEq by simp
      qed

      show "\<exists>V. neighborhood_of x X TX V \<and>
             top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V)) \<and>
             closure_on X TX V \<subseteq> U"
        apply (rule exI[where x=V])
        apply (intro conjI)
          apply (rule hVnbhd)
         apply (rule clV_comp)
        apply (rule clV_sub_U)
        done
    qed
  next
    assume hProp:
      "\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
        (\<exists>V. neighborhood_of x X TX V \<and>
             top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
             \<and> closure_on X TX V \<subseteq> U)"
    show "top1_locally_compact_on X TX"
      unfolding top1_locally_compact_on_def
    proof (intro conjI)
      show "is_topology_on X TX" by (rule hTX)
      show "\<forall>x\<in>X. \<exists>U. neighborhood_of x X TX U \<and> U \<subseteq> X \<and>
          top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
      proof (intro ballI)
        fix x
        assume hxX: "x \<in> X"
        have hnbhdX: "neighborhood_of x X TX X"
          unfolding neighborhood_of_def using X_TX hxX by blast
        obtain V where hV: "neighborhood_of x X TX V"
            and hVcomp: "top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))"
            and hclVsubX: "closure_on X TX V \<subseteq> X"
          using hProp hxX hnbhdX by blast
        have hVsubX: "V \<subseteq> X"
          apply (rule subset_trans)
           apply (rule subset_closure_on)
          apply (rule hclVsubX)
          done
        show "\<exists>U. neighborhood_of x X TX U \<and> U \<subseteq> X \<and>
            top1_compact_on (closure_on X TX U) (subspace_topology X TX (closure_on X TX U))"
          apply (rule exI[where x=V])
          apply (intro conjI)
            apply (rule hV)
           apply (rule hVsubX)
          apply (rule hVcomp)
          done
      qed
    qed
  qed
qed

(** from \S29 Corollary 29.3 [top1.tex:3770] **)
corollary Corollary_29_3:
  assumes hLC: "top1_locally_compact_on X TX"
  assumes hH: "is_hausdorff_on X TX"
  assumes hAX: "A \<subseteq> X"
  shows "closedin_on X TX A \<longrightarrow> top1_locally_compact_on A (subspace_topology X TX A)"
    and "A \<in> TX \<longrightarrow> top1_locally_compact_on A (subspace_topology X TX A)"
proof -
  have hTX: "is_topology_on X TX"
    using hLC unfolding top1_locally_compact_on_def by blast
  let ?TA = "subspace_topology X TX A"
  have hTopA: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTX hAX])

  have hPropX:
    "\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
      (\<exists>V. neighborhood_of x X TX V
        \<and> top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
        \<and> closure_on X TX V \<subseteq> U)"
  proof -
    have hEq:
      "top1_locally_compact_on X TX \<longleftrightarrow>
        (\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
            (\<exists>V. neighborhood_of x X TX V \<and>
                 top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
                 \<and> closure_on X TX V \<subseteq> U))"
      by (rule Theorem_29_2[OF hH])
    have hRhs:
      "(\<forall>x\<in>X. \<forall>U. neighborhood_of x X TX U \<longrightarrow>
            (\<exists>V. neighborhood_of x X TX V \<and>
                 top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))
                 \<and> closure_on X TX V \<subseteq> U))"
      by (rule iffD1[OF hEq hLC])
    show ?thesis
      by (rule hRhs)
  qed

  show "closedin_on X TX A \<longrightarrow> top1_locally_compact_on A (subspace_topology X TX A)"
  proof (intro impI)
    assume hAcl: "closedin_on X TX A"
    show "top1_locally_compact_on A ?TA"
      unfolding top1_locally_compact_on_def
    proof (intro conjI)
      show "is_topology_on A ?TA"
        by (rule hTopA)
      show "\<forall>x\<in>A. \<exists>U. neighborhood_of x A ?TA U \<and> U \<subseteq> A
        \<and> top1_compact_on (closure_on A ?TA U) (subspace_topology A ?TA (closure_on A ?TA U))"
      proof (intro ballI)
        fix x
        assume hxA: "x \<in> A"
        have hxX: "x \<in> X"
          using hAX hxA by blast

        obtain U0 where hU0: "neighborhood_of x X TX U0"
          and hU0X: "U0 \<subseteq> X"
          and hK0comp: "top1_compact_on (closure_on X TX U0) (subspace_topology X TX (closure_on X TX U0))"
          using hLC hxX unfolding top1_locally_compact_on_def by blast

        define V where "V = A \<inter> U0"

        have hVnb: "neighborhood_of x A ?TA V"
        proof -
          have hU0T: "U0 \<in> TX"
            using hU0 unfolding neighborhood_of_def by blast
          have hxU0: "x \<in> U0"
            using hU0 unfolding neighborhood_of_def by blast
          have hVT: "V \<in> ?TA"
            unfolding V_def subspace_topology_def
            apply (rule CollectI)
            apply (rule exI[where x=U0])
            apply (intro conjI)
             apply (rule refl)
            apply (rule hU0T)
            done
          have hxV: "x \<in> V"
            unfolding V_def using hxA hxU0 by blast
          show ?thesis
            unfolding neighborhood_of_def
            by (intro conjI, rule hVT, rule hxV)
        qed

        have hVA: "V \<subseteq> A"
          unfolding V_def by blast

        have hVX: "V \<subseteq> X"
          by (rule subset_trans[OF hVA hAX])

        have hclV_subA: "closure_on X TX V \<subseteq> A"
          by (rule closure_on_subset_of_closed[OF hAcl hVA])

        have hclV_eq: "closure_on A ?TA V = closure_on X TX V"
        proof -
          have hclV_subA': "closure_on X TX V \<inter> A = closure_on X TX V"
            using hclV_subA by blast
          have hcl_subspace: "closure_on A ?TA V = closure_on X TX V \<inter> A"
            by (rule Theorem_17_4[OF hTX hVA hAX])
          show ?thesis
            unfolding hcl_subspace hclV_subA' by simp
        qed

        have hclV_sub_clU0: "closure_on X TX V \<subseteq> closure_on X TX U0"
        proof -
          have hVsub: "V \<subseteq> U0"
            unfolding V_def by blast
          show ?thesis
            by (rule closure_on_mono[OF hVsub])
        qed

        have hclV_closed_X: "closedin_on X TX (closure_on X TX V)"
          by (rule closure_on_closed[OF hTX hVX])

        have hK0X: "closure_on X TX U0 \<subseteq> X"
          by (rule closure_on_subset_carrier[OF hTX hU0X])

        have hclV_closed_K0: "closedin_on (closure_on X TX U0) (subspace_topology X TX (closure_on X TX U0)) (closure_on X TX V)"
        proof -
          have hEq: "closure_on X TX V = closure_on X TX V \<inter> closure_on X TX U0"
            using hclV_sub_clU0 by blast
          have hClosed:
            "\<exists>C. closedin_on X TX C \<and> closure_on X TX V = C \<inter> closure_on X TX U0"
            apply (rule exI[where x="closure_on X TX V"])
            apply (intro conjI)
             apply (rule hclV_closed_X)
            apply (subst hEq)
            apply (rule refl)
            done
          have hIff:
            "closedin_on (closure_on X TX U0) (subspace_topology X TX (closure_on X TX U0)) (closure_on X TX V)
              \<longleftrightarrow> (\<exists>C. closedin_on X TX C \<and> closure_on X TX V = C \<inter> closure_on X TX U0)"
            by (rule Theorem_17_2[OF hTX hK0X])
          show ?thesis
            by (rule iffD2[OF hIff hClosed])
        qed

        have hclV_compact:
          "top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))"
        proof -
          have hcomp':
            "top1_compact_on (closure_on X TX V)
              (subspace_topology (closure_on X TX U0) (subspace_topology X TX (closure_on X TX U0)) (closure_on X TX V))"
            by (rule Theorem_26_2[OF hK0comp hclV_closed_K0])
          have hTopEq:
            "subspace_topology (closure_on X TX U0) (subspace_topology X TX (closure_on X TX U0)) (closure_on X TX V)
              = subspace_topology X TX (closure_on X TX V)"
            by (rule subspace_topology_trans[OF hclV_sub_clU0])
          show ?thesis
            using hcomp' unfolding hTopEq by simp
        qed

        have hTopEqA:
          "subspace_topology A ?TA (closure_on A ?TA V) = subspace_topology X TX (closure_on X TX V)"
        proof -
          have hsub: "closure_on X TX V \<subseteq> A"
            by (rule hclV_subA)
          have hTopEq:
            "subspace_topology A (subspace_topology X TX A) (closure_on X TX V) = subspace_topology X TX (closure_on X TX V)"
            by (rule subspace_topology_trans[OF hsub])
          show ?thesis
            unfolding hclV_eq hTopEq by simp
        qed
        have hTopEqA':
          "subspace_topology A ?TA (closure_on X TX V) = subspace_topology X TX (closure_on X TX V)"
          by (subst hclV_eq[symmetric], rule hTopEqA)

        show "\<exists>U. neighborhood_of x A ?TA U \<and> U \<subseteq> A
          \<and> top1_compact_on (closure_on A ?TA U) (subspace_topology A ?TA (closure_on A ?TA U))"
          apply (rule exI[where x=V])
          apply (intro conjI)
            apply (rule hVnb)
           apply (rule hVA)
          apply (subst hclV_eq)
          apply (subst hclV_eq)
          apply (subst hTopEqA')
          apply (rule hclV_compact)
          done
      qed
    qed
  qed

  show "A \<in> TX \<longrightarrow> top1_locally_compact_on A (subspace_topology X TX A)"
  proof (intro impI)
    assume hAopen: "A \<in> TX"
    show "top1_locally_compact_on A ?TA"
      unfolding top1_locally_compact_on_def
    proof (intro conjI)
      show "is_topology_on A ?TA"
        by (rule hTopA)
      show "\<forall>x\<in>A. \<exists>U. neighborhood_of x A ?TA U \<and> U \<subseteq> A
        \<and> top1_compact_on (closure_on A ?TA U) (subspace_topology A ?TA (closure_on A ?TA U))"
      proof (intro ballI)
        fix x
        assume hxA: "x \<in> A"
        have hxX: "x \<in> X"
          using hAX hxA by blast
        have hnbA: "neighborhood_of x X TX A"
          unfolding neighborhood_of_def using hAopen hxA by blast
        obtain V where hV: "neighborhood_of x X TX V"
          and hVcomp: "top1_compact_on (closure_on X TX V) (subspace_topology X TX (closure_on X TX V))"
          and hclVsubA: "closure_on X TX V \<subseteq> A"
          using hPropX hxX hnbA by blast

        have hVsubA: "V \<subseteq> A"
          apply (rule subset_trans)
           apply (rule subset_closure_on)
          apply (rule hclVsubA)
          done

	        have hVnbA: "neighborhood_of x A ?TA V"
	        proof -
	          have hVT: "V \<in> TX"
	            using hV unfolding neighborhood_of_def by blast
	          have hxV: "x \<in> V"
	            using hV unfolding neighborhood_of_def by blast
		          have hVeq: "V = A \<inter> V"
		          proof (rule equalityI)
		            show "V \<subseteq> A \<inter> V"
		            proof
		              fix y
		              assume hyV: "y \<in> V"
		              have hyA: "y \<in> A"
		                by (rule subsetD[OF hVsubA hyV])
		              show "y \<in> A \<inter> V"
		                by (rule IntI[OF hyA hyV])
		            qed
		            show "A \<inter> V \<subseteq> V"
		              by (rule Int_lower2)
		          qed
	          have hVTA: "V \<in> ?TA"
	            unfolding subspace_topology_def
	            apply (rule CollectI)
	            apply (rule exI[where x=V])
	            apply (intro conjI)
	             apply (rule hVeq)
	            apply (rule hVT)
	            done
	          show ?thesis
	            unfolding neighborhood_of_def
	            by (intro conjI, rule hVTA, rule hxV)
	        qed

        have hclV_eq: "closure_on A ?TA V = closure_on X TX V"
        proof -
          have hcl_subspace: "closure_on A ?TA V = closure_on X TX V \<inter> A"
            by (rule Theorem_17_4[OF hTX hVsubA hAX])
          have hEq: "closure_on X TX V \<inter> A = closure_on X TX V"
            using hclVsubA by blast
          show ?thesis
            unfolding hcl_subspace hEq by simp
        qed

	        have hTopEqA:
	          "subspace_topology A ?TA (closure_on A ?TA V) = subspace_topology X TX (closure_on X TX V)"
	        proof -
	          have hTopEq:
	            "subspace_topology A (subspace_topology X TX A) (closure_on X TX V) = subspace_topology X TX (closure_on X TX V)"
	            by (rule subspace_topology_trans[OF hclVsubA])
	          show ?thesis
	            unfolding hclV_eq hTopEq by simp
	        qed
	        have hTopEqA':
	          "subspace_topology A ?TA (closure_on X TX V) = subspace_topology X TX (closure_on X TX V)"
	          by (subst hclV_eq[symmetric], rule hTopEqA)

	        show "\<exists>U. neighborhood_of x A ?TA U \<and> U \<subseteq> A
	          \<and> top1_compact_on (closure_on A ?TA U) (subspace_topology A ?TA (closure_on A ?TA U))"
	          apply (rule exI[where x=V])
	          apply (intro conjI)
	            apply (rule hVnbA)
	           apply (rule hVsubA)
	          apply (subst hclV_eq)
	          apply (subst hclV_eq)
	          apply (subst hTopEqA')
	          apply (rule hVcomp)
	          done
	      qed
	    qed
	  qed
	qed

(** from \S29 Corollary 29.4 [top1.tex:3775] **)
corollary Corollary_29_4:
  assumes hTX: "is_topology_on X TX"
  shows
    "(\<exists>TY. top1_one_point_compactification_on X TX TY \<and> (Some ` X) \<in> TY)
      \<longleftrightarrow> (top1_locally_compact_on X TX \<and> is_hausdorff_on X TX)"
text \<open>
  Note: In this development, the one-point compactification is encoded on the fixed carrier
  \<open>insert None (Some ` X)\<close>.  Thus the existence of a compact Hausdorff space containing \<open>X\<close> as an open subspace
  is expressed via the existence of a topology \<open>TY\<close> on that carrier such that \<open>Some ` X\<close> is open and
  homeomorphic to \<open>X\<close>.
\<close>
proof (rule iffI)
  assume hEx: "\<exists>TY. top1_one_point_compactification_on X TX TY \<and> (Some ` X) \<in> TY"
  have hEx0: "\<exists>TY. top1_one_point_compactification_on X TX TY"
  proof -
    obtain TY where hTY: "top1_one_point_compactification_on X TX TY \<and> (Some ` X) \<in> TY"
      using hEx by (elim exE)
    have "top1_one_point_compactification_on X TX TY"
      using hTY by (rule conjunct1)
    show ?thesis
      by (rule exI[where x=TY], rule \<open>top1_one_point_compactification_on X TX TY\<close>)
  qed
  show "top1_locally_compact_on X TX \<and> is_hausdorff_on X TX"
    by (rule iffD2[OF Theorem_29_1(1)[OF hTX] hEx0])
next
  assume hLC_H: "top1_locally_compact_on X TX \<and> is_hausdorff_on X TX"
  have hExTY: "\<exists>TY. top1_one_point_compactification_on X TX TY"
    by (rule iffD1[OF Theorem_29_1(1)[OF hTX] hLC_H])
  obtain TY where hOPC: "top1_one_point_compactification_on X TX TY"
    using hExTY by (elim exE)
  define Y where "Y = insert None (Some ` X)"
  have hOPC_def:
    "top1_homeomorphism_on X TX (Some ` X) (subspace_topology Y TY (Some ` X)) Some
      \<and> top1_compact_on Y TY
      \<and> is_hausdorff_on Y TY"
    using hOPC unfolding top1_one_point_compactification_on_def Y_def
    by (simp only: Let_def)
  have hHausY: "is_hausdorff_on Y TY"
    using hOPC_def by (rule conjunct2[OF conjunct2])
  have hNoneY: "None \<in> Y"
    unfolding Y_def by simp
  have hNoneClosed: "closedin_on Y TY {None}"
    by (rule singleton_closed_in_hausdorff[OF hHausY hNoneY])
  have hSomeOpen: "(Some ` X) \<in> TY"
  proof -
    have hOpen: "Y - {None} \<in> TY"
      by (rule closedin_diff_open[OF hNoneClosed])
    have hEq: "Y - {None} = Some ` X"
      by (rule set_eqI, simp add: Y_def)
    show ?thesis
      using hOpen hEq by simp
  qed
  show "\<exists>TY. top1_one_point_compactification_on X TX TY \<and> (Some ` X) \<in> TY"
    by (rule exI[where x=TY], intro conjI, rule hOPC, rule hSomeOpen)
qed


end
