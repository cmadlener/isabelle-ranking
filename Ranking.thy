theory Ranking
  imports 
    "AGF.Berge"
    "AGF.Bipartite"
    "List-Index.List_Index"
begin

sledgehammer_params [provers = e z3 spass cvc4 vampire]

lemma vs_empty[simp]: "Vs {} = {}"
  by (simp add: Vs_def)

lemma vs_union: "Vs (A \<union> B) = Vs A \<union> Vs B"
  unfolding Vs_def by simp

lemma graph_abs_empty[simp]: "graph_abs {}"
  by (simp add: graph_abs_def)

lemma graph_abs_insert[simp]: "graph_abs M \<Longrightarrow> u \<noteq> v \<Longrightarrow> graph_abs (insert {u,v} M)"
  by (auto simp: graph_abs_def Vs_def)

lemma graph_abs_union: "graph_abs G \<Longrightarrow> graph_abs H \<Longrightarrow> graph_abs (G \<union> H)"
  by (auto simp: graph_abs_def Vs_def)

lemma graph_abs_compr: "u \<notin> ns \<Longrightarrow> finite ns \<Longrightarrow> graph_abs {{u, v} |v. v \<in> ns}"
  unfolding graph_abs_def by (auto simp: Vs_def)

lemma matching_empty[simp]: "matching {}"
  unfolding matching_def by simp

lemma partitioned_bipartite_empty[simp]: "partitioned_bipartite {} X"
  unfolding partitioned_bipartite_def by simp

lemma partitioned_bipartiteI:
  assumes "graph_abs E"
  assumes "\<And>e. e \<in> E \<Longrightarrow> \<exists>u v. e = {u,v} \<and> u \<in> X \<and> v \<in> Vs E - X"
  shows "partitioned_bipartite E X"
  using assms
  unfolding partitioned_bipartite_def
  by (auto simp: graph_abs_def)

lemma partitioned_bipartite_graph_absD:
  assumes "partitioned_bipartite E X"
  shows "graph_abs E"
  using assms
  unfolding partitioned_bipartite_def
  by (auto intro: graph_abs.intro)

lemma partitioned_bipartiteE:
  assumes "partitioned_bipartite E X"
  assumes "e \<in> E"
  obtains u v where "e = {u,v}" "u \<in> X" "v \<in> Vs E - X"
  using assms
  unfolding partitioned_bipartite_def
  by fast

type_synonym 'a graph = "'a set set"

text \<open>For now we don't care about distinctness of the "ranking" list, as we only need the order
  induced by the list.\<close>
abbreviation "rank \<sigma> v \<equiv> index \<sigma> v"

lemma index_Cons_mono: "x \<noteq> y \<Longrightarrow> index xs y \<le> index (x#xs) y"
  by simp

lemma index_filter_mono: "P x \<Longrightarrow> index (filter P xs) x \<le> index xs x"
  by (induction xs) auto

lemma index_append_mono: "index xs x \<le> index (xs @ ys) x"
  by (induction xs) auto

abbreviation "arriving_U us \<equiv> fst ` set us"
abbreviation "arriving_V us \<equiv> \<Union> (snd ` set us)"

definition wf_input :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> bool" where
  "wf_input \<sigma> us \<equiv> 
    set \<sigma> \<inter> arriving_U us = {} \<and> 
    arriving_V us \<subseteq> set \<sigma> \<and>
    distinct \<sigma> \<and> 
    distinct (map fst us)"

fun neighbors_of :: "'a \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a set" where
  "neighbors_of _ [] = {}"
| "neighbors_of u ((v,ns)#vs) = (if u = v then ns else neighbors_of u vs)"

fun step :: "'a list \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a graph" where
  "step [] M _ _ = M"
| "step (v#vs) M u neighbors = (
    if v \<in> neighbors - Vs M
    then insert {u,v} M
    else step vs M u neighbors
  )"

lemma step_ConsI:
  assumes "v \<in> ns \<Longrightarrow> v \<notin> Vs M \<Longrightarrow> P (insert {u,v} M)"
  assumes "v \<notin> ns \<or> v \<in> Vs M \<Longrightarrow> P (step vs M u ns)"
  shows "P (step (v#vs) M u ns)"
  using assms
  by auto

\<comment> \<open>"Unfold" fold definition to generalize over accumulator.\<close>
fun ranking_aux :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "ranking_aux _ [] M = M"
| "ranking_aux \<sigma> ((u,ns)#us) M = ranking_aux \<sigma> us (step \<sigma> M u ns)"

definition ranking :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a graph" where
  "ranking \<sigma> us = ranking_aux \<sigma> us {}"

lemma ranking_PI: "P (ranking_aux \<sigma> us {}) \<Longrightarrow> P (ranking \<sigma> us)"
  unfolding ranking_def .

text \<open>The following invariant is maintained by the (steps of the) ranking algorithm.\<close>
\<comment> \<open>TODO: reconsider the wellformedness of the input in the invariant. It was put there, since the
  the invariant is only preserved under (some conditions of) wellformedness.\<close>
definition ranking_inv :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "ranking_inv \<sigma> us M \<equiv> wf_input \<sigma> us \<and> matching M \<and> partitioned_bipartite M (set \<sigma>) \<and> 
    Vs M - set \<sigma> \<subseteq> arriving_U us"

lemma ranking_invI:
  assumes "wf_input \<sigma> us"
  assumes "matching M"
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "Vs M - set \<sigma> \<subseteq> arriving_U us"
  shows "ranking_inv \<sigma> us M"
  using assms
  unfolding ranking_inv_def
  by auto

lemma ranking_invD:
  assumes "ranking_inv \<sigma> us M"
  shows "wf_input \<sigma> us" "matching M" "partitioned_bipartite M (set \<sigma>)" "Vs M - set \<sigma> \<subseteq> arriving_U us"
  using assms
  unfolding ranking_inv_def
  by auto

lemma ranking_inv_subset_\<sigma>: "ranking_inv \<sigma> us M \<Longrightarrow> Vs M - arriving_U us \<subseteq> set \<sigma>"
  unfolding ranking_inv_def
  by blast


fun offline_graph :: "('a \<times> 'a set) list \<Rightarrow> 'a graph" where
  "offline_graph [] = {}"
| "offline_graph ((u, ns) # us) =  {{u,v} | v.  v \<in> ns} \<union> (offline_graph us)"

lemma step_mono: "e \<in> M \<Longrightarrow> e \<in> step \<sigma> M u ns"
  by (induction \<sigma>) auto

lemma ranking_aux_mono: "e \<in> M \<Longrightarrow> e \<in> ranking_aux \<sigma> us M"
  by (induction \<sigma> us M rule: ranking_aux.induct) (auto simp: step_mono)

lemma step_empty_if_no_neighbor: "set \<sigma> \<inter> ns = {} \<longleftrightarrow> step \<sigma> {} u ns = {}"
  by (induction \<sigma>) (auto simp: vs_member)

lemma wf_input_arriving_disjoint: "wf_input \<sigma> us \<Longrightarrow> arriving_V us \<inter> arriving_U us = {}"
  unfolding wf_input_def by auto

lemma wf_input_tl: "wf_input \<sigma> (u # us) \<Longrightarrow> wf_input \<sigma> us"
  unfolding wf_input_def by auto

lemma wf_input_hd: "wf_input \<sigma> ((u,ns) # us) \<Longrightarrow> u \<notin> ns \<and> finite ns \<and> u \<notin> set \<sigma> \<and> ns \<subseteq> set \<sigma>"
  unfolding wf_input_def by (auto intro: finite_subset)

lemma wf_input_hd': "wf_input \<sigma> (u#us) \<Longrightarrow> fst u \<notin> snd u \<and> finite (snd u) \<and> fst u \<notin> set \<sigma>"
  unfolding wf_input_def by (auto intro: finite_subset)


lemma edge_in_step:
  assumes "e \<in> step \<sigma> M u ns"
  shows "e \<in> M \<or> (\<exists>v.  e = {u,v} \<and> (v \<in> ns \<inter> set \<sigma> - Vs M))"
  using assms
  by (induction \<sigma> M u ns rule: step.induct) (auto split: if_splits)

lemma edge_in_ranking_aux:
  assumes "e \<in> ranking_aux \<sigma> us M"
  shows "e \<in> M \<or> (\<exists>u ns v. (u,ns) \<in> set us \<and> v \<in> ns \<and> e = {u,v} \<and> v \<notin> Vs M)"
  using assms
  apply (induction \<sigma> us M rule: ranking_aux.induct)
   apply simp_all
  apply (erule disjE)
   apply (drule edge_in_step, blast)
  by (metis step_mono vs_member)

lemma vs_step: "v \<in> Vs (step \<sigma> M u ns) \<Longrightarrow> v = u \<or> v \<in> set \<sigma> \<or> v \<in> Vs M"
  by (induction \<sigma> M u ns rule: step.induct) (auto split: if_splits simp: Vs_def)

lemma vs_step': "v \<in> Vs (step \<sigma> M u ns) \<Longrightarrow> v \<in> Vs M \<or> v \<in> Vs {{u,v}| v. v \<in> ns}"
  by (induction \<sigma> M u ns rule: step.induct) (auto split: if_splits simp: Vs_def)

lemma vs_ranking_aux: "v \<in> Vs (ranking_aux \<sigma> us M) \<Longrightarrow> v \<in> Vs M \<or> v \<in> Vs (offline_graph us)"
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u ns us M)
  then show ?case
    by (auto dest: vs_step' simp: vs_union)
qed simp

lemma vs_offline_graph: "v \<in> Vs (offline_graph us) \<Longrightarrow> v \<in> arriving_U us \<or> v \<in> arriving_V us"
  by (induction us rule: offline_graph.induct) (auto simp: Vs_def)

lemma vs_compr: "Vs {{u, v} |v. v \<in> ns} = (if ns = {} then {} else {u} \<union> ns)"
  unfolding Vs_def by auto

lemma graph_abs_step:
  assumes "graph_abs M"
  assumes "u \<notin> set \<sigma>"
  shows "graph_abs (step \<sigma> M u ns)"
  using assms
  by (induction \<sigma>) auto

lemma matching_step:
  assumes "matching M"
  assumes "u \<notin> set \<sigma>"
  assumes "u \<notin> Vs M"
  shows "matching (step \<sigma> M u ns)"
  using assms
  by (induction \<sigma>) (auto simp: matching_def)

lemma partitioned_bipartite_step:
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "u \<notin> set \<sigma>"
  shows "partitioned_bipartite (step \<sigma> M u ns) (set \<sigma>)"
  using assms
proof (induction \<sigma>)
  case (Cons a \<sigma>)
  then have graph_abs: "graph_abs (step \<sigma> M u ns)"
    by (auto dest: partitioned_bipartite_graph_absD intro: graph_abs_step)
  show ?case
    apply (rule step_ConsI)
    apply (rule partitioned_bipartiteI)
      apply (metis Cons.prems(2) assms(1) graph_abs_insert list.set_intros(1) partitioned_bipartite_graph_absD)
     apply (smt (verit, del_insts) Cons.prems(1) Cons.prems(2) Diff_iff edges_are_Vs insert_commute insert_iff list.set(2) partitioned_bipartiteE)
    apply (rule partitioned_bipartiteI)
     apply (rule graph_abs)
    by (smt (verit, del_insts) Cons.prems(1) Cons.prems(2) Diff_iff IntE edge_in_step edges_are_Vs insertCI insert_commute list.set(2) partitioned_bipartiteE)
qed simp

lemma ranking_inv_step:
  assumes "wf_input \<sigma> ((u,ns)#us)"
  assumes "ranking_inv \<sigma> us M"
  shows "ranking_inv \<sigma> ((u,ns)#us) (step \<sigma> M u ns)"
  using assms
  unfolding ranking_inv_def
  apply (auto intro!: matching_step partitioned_bipartite_step dest: wf_input_hd)
  apply (metis (no_types, hide_lams) DiffI assms(1) distinct.simps(2) fst_conv list.simps(9) set_map subset_iff wf_input_def wf_input_hd)
  by (metis (no_types, lifting) DiffI UnE insert_absorb singleton_insert_inj_eq subset_iff vs_step)


lemma wf_input_graph_abs_ranking_aux:
  assumes "graph_abs M"
  assumes "wf_input \<sigma> us"
  shows "graph_abs (ranking_aux \<sigma> us M)"
  using assms
  by (induction us arbitrary: M) (auto simp: wf_input_def graph_abs_step)


lemma wf_input_matching_ranking_aux:
  assumes "graph_abs M"
  assumes "matching M"
  assumes "wf_input \<sigma> us"
  assumes "arriving_U us \<inter> Vs M = {}"
  shows "matching (ranking_aux \<sigma> us M)"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u ns us M)
  then have 1: "graph_abs (step \<sigma> M u ns)" "matching (step \<sigma> M u ns)" "wf_input \<sigma> us"
    by (auto intro: graph_abs_step matching_step dest: wf_input_hd wf_input_tl)
  have disjoint': "arriving_U us \<inter> ({u} \<union> set \<sigma> \<union> Vs M) = {}"
    using "2.prems"
    unfolding wf_input_def
    by (simp add: Int_Un_distrib Int_commute)

  then have "arriving_U us \<inter> Vs (step \<sigma> M u ns) = {}"
    by (smt (z3) Int_Un_distrib disjoint_iff insertCI sup_bot.neutr_eq_iff vs_step)

  then show ?case
    using "2.IH" 1
    by simp
qed auto

lemma wf_input_partitioned_bipartite_ranking_aux:
  assumes "wf_input \<sigma> us"
  assumes "partitioned_bipartite M (set \<sigma>)"
  shows "partitioned_bipartite (ranking_aux \<sigma> us M) (set \<sigma>)"
  using assms
  by (induction \<sigma> us M rule: ranking_aux.induct)
     (auto dest: partitioned_bipartite_step wf_input_hd wf_input_tl)


lemma wf_input_ranking_inv_ranking_aux:
  assumes "wf_input \<sigma> us"
  assumes "ranking_inv \<sigma> [] M"
  shows "ranking_inv \<sigma> us (ranking_aux \<sigma> us M)"
  using assms
  apply (auto intro!: ranking_invI wf_input_matching_ranking_aux wf_input_partitioned_bipartite_ranking_aux 
        dest: ranking_invD partitioned_bipartite_graph_absD wf_input_tl)
  apply (metis empty_iff empty_set image_empty partitioned_bipartiteE ranking_inv_def subsetD vs_member)
  apply (drule vs_ranking_aux)
  apply auto
  using ranking_inv_subset_\<sigma> apply fastforce
  by (meson in_mono vs_offline_graph wf_input_def)


lemma wf_input_graph_abs_ranking:
  assumes "wf_input \<sigma> us"
  shows "graph_abs (ranking \<sigma> us)"
  by (simp add: assms ranking_PI wf_input_graph_abs_ranking_aux)

lemma wf_input_matching_ranking:
  assumes "wf_input \<sigma> us"
  shows "matching (ranking \<sigma> us)"
  using assms
  by (simp add: ranking_def wf_input_matching_ranking_aux)


lemma wf_input_graph_abs_offline_graph:
  assumes "wf_input \<sigma> us"
  shows "graph_abs (offline_graph us)"
  using assms
  by (induction us rule: offline_graph.induct) 
     (auto dest: wf_input_tl wf_input_hd intro: graph_abs_union graph_abs_compr)

lemma wf_input_partitioned_bipartite_offline_graph:
  assumes "wf_input \<sigma> us"
  shows "partitioned_bipartite (offline_graph us) (set \<sigma>)"
  using assms
proof (induction us rule: offline_graph.induct)
  case (2 u ns us)
  show ?case 
  proof (intro partitioned_bipartiteI)
    show "graph_abs (offline_graph ((u, ns) # us))"
      using 2 wf_input_graph_abs_offline_graph by blast
    show "\<And>e. e \<in> offline_graph ((u, ns) # us) \<Longrightarrow> \<exists>u' v. e = {u', v} \<and> u' \<in> set \<sigma> \<and> v \<in> Vs (offline_graph ((u, ns) # us)) - set \<sigma>"
    proof -
      fix e
      assume "e \<in> offline_graph ((u, ns) # us)"
      then have "e \<in> offline_graph us \<or> e \<in> {{u, v}| v. v \<in> ns}" by auto
      then consider (ind) "e \<in> offline_graph us" | (new) "e \<in> {{u, v}| v. v \<in> ns}" by blast
      then show "\<exists>u' v. e = {u', v} \<and> u' \<in> set \<sigma> \<and> v \<in> Vs (offline_graph ((u, ns) # us)) - set \<sigma>" 
      proof cases
        case ind
        then show ?thesis
          by (smt (verit) "2.IH" "2.prems" DiffD2 DiffI \<open>e \<in> offline_graph ((u, ns) # us)\<close> edges_are_Vs insert_commute partitioned_bipartiteE wf_input_tl)
      next
        case new
        then obtain v where "v \<in> ns" "e = {u,v}" by blast
        then have "v \<in> set \<sigma>" "u \<notin> set \<sigma>"
          using 2
          by (auto dest: wf_input_hd)
        have "u \<in> Vs (offline_graph ((u, ns) # us))"
          by (metis \<open>e = {u, v}\<close> \<open>e \<in> offline_graph ((u, ns) # us)\<close> edges_are_Vs)
        then show ?thesis
          using \<open>e = {u, v}\<close> \<open>u \<notin> set \<sigma>\<close> \<open>v \<in> set \<sigma>\<close> by blast
      qed
    qed
  qed
qed auto

  

lemma in_step_elim:
  assumes "e \<in> step \<sigma> M u ns"
  assumes "e \<notin> M"
  obtains v where "e = {u,v}" "v \<in> ns" "v \<in> set \<sigma>" "v \<notin> Vs M"
  using assms edge_in_step
  by force


lemma ranking_aux_subset_offline_graph:
  assumes "x \<in> ranking_aux \<sigma> us M"
  shows "x \<in> offline_graph us \<union> M"
  using assms
  by (induction \<sigma> us M rule: ranking_aux.induct) (auto dest: edge_in_step)

lemma "x \<in> ranking \<sigma> us \<Longrightarrow> x \<in> offline_graph us"
  unfolding ranking_def
  by (auto dest: ranking_aux_subset_offline_graph)


lemma step_lowest_rank:
  assumes "u \<notin> set \<sigma>"
  assumes "u \<notin> Vs M"
  assumes "w \<in> set \<sigma>" "w \<in> ns" "w \<notin> Vs M" "w \<noteq> v"
  assumes "{u,v} \<in> step \<sigma> M u ns"
  shows "rank \<sigma> v < rank \<sigma> w"
  using assms
  apply (induction \<sigma>)
   apply simp_all
  by (metis doubleton_eq_iff insert_iff vs_member)

lemma neighbors_of_Cons:
  assumes "u \<noteq> u'"
  assumes "w \<in> neighbors_of u ((u', ns) # us)"
  shows "w \<in> neighbors_of u us"
  using assms
  by (induction us) auto

lemma ranking_aux_hd_ineq:
  assumes "wf_input \<sigma> ((u', ns) # us)"
  assumes "v \<in> set \<sigma>"
  assumes "u \<notin> Vs (step \<sigma> M u' ns)"
  assumes "{u, v} \<in> ranking_aux \<sigma> ((u', ns) # us) M"
  shows "u \<noteq> u'"
proof (rule ccontr, simp)
  assume "u = u'"
  have "u \<notin> Vs M" using assms
    by (meson step_mono vs_transport)
  have "u \<notin> arriving_U us"
    by (metis (no_types, hide_lams) \<open>u = u'\<close> assms(1) distinct.simps(2) fst_conv list.simps(9) set_map wf_input_def)
  show False
    by (metis (no_types, lifting) \<open>u = u'\<close> \<open>u \<notin> arriving_U us\<close> assms(1) assms(3) assms(4) edges_are_Vs ranking_aux.simps(2) subset_eq vs_offline_graph vs_ranking_aux wf_input_def wf_input_hd wf_input_tl)
qed


lemma u_in_ranking_aux:
  assumes "wf_input \<sigma> us"
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "v \<in> set \<sigma>"
  assumes "u \<notin> Vs M"
  assumes "{u,v} \<in> ranking_aux \<sigma> us M"
  shows "u \<notin> set \<sigma>"
  by (metis DiffD2 assms(1) assms(2) assms(3) assms(5) doubleton_eq_iff partitioned_bipartiteE wf_input_partitioned_bipartite_ranking_aux)

lemma u_in_stepE:
  assumes "u \<in> Vs (step \<sigma> M u ns)"
  assumes "u \<notin> Vs M"
  assumes "u \<notin> set \<sigma>"
  obtains v where "u \<noteq> v" "{u,v} \<in> step \<sigma> M u ns" "v \<in> ns" "v \<in> set \<sigma>"
  using assms
  by (induction \<sigma> M u ns rule: step.induct) (auto split: if_splits)

lemma vertex_in_step_edge_in_step:
  assumes "wf_input \<sigma> ((u,ns)#us)"
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "matching M"
  assumes "arriving_U ((u,ns)#us) \<inter> Vs M = {}"
  assumes "u \<notin> Vs M"
  assumes "v \<in> set \<sigma>"
  assumes "u \<in> Vs (step \<sigma> M u ns)"
  assumes "{u,v} \<in> ranking_aux \<sigma> ((u,ns)#us) M"
  shows "{u,v} \<in> step \<sigma> M u ns"
proof -
  have "u \<notin> set \<sigma>"
    by (meson assms(1) wf_input_hd)
  with assms obtain v' where "u \<noteq> v'" "{u,v'} \<in> step \<sigma> M u ns" "v' \<in> ns" "v' \<in> set \<sigma>"
    by (auto elim: u_in_stepE)
  have "v' = v" 
  proof (rule ccontr)
    assume "v' \<noteq> v"
    then have "{u,v'} \<in> ranking_aux \<sigma> ((u,ns)#us) M"
      by (simp add: \<open>{u, v'} \<in> step \<sigma> M u ns\<close> ranking_aux_mono)
    have "matching (ranking_aux \<sigma> ((u,ns)#us) M)"
      by (meson assms(1) assms(2) assms(3) assms(4) partitioned_bipartite_graph_absD wf_input_matching_ranking_aux)
    then show False 
      by (metis \<open>v' \<noteq> v\<close> \<open>{u, v'} \<in> ranking_aux \<sigma> ((u, ns) # us) M\<close> assms(8) doubleton_eq_iff insertI1 matching_unique_match)
  qed
  then show ?thesis
    using \<open>{u, v'} \<in> step \<sigma> M u ns\<close> by auto
qed


lemma wf_input_arriving_U_disjoint_Cons:
  assumes "wf_input \<sigma> ((u,ns)#us)"
  assumes "arriving_U ((u,ns)#us) \<inter> Vs M = {}"
  shows "arriving_U us \<inter> Vs (step \<sigma> M u ns) = {}"
proof (rule ccontr)
  assume "arriving_U us \<inter> Vs (step \<sigma> M u ns) \<noteq> {}"
  then obtain u' where "u' \<in> arriving_U us" "u' \<in> Vs (step \<sigma> M u ns)"
    by blast
  then consider "u' = u" | "u' \<in> Vs M"
    by (metis assms(1) disjoint_iff vs_step wf_input_def wf_input_tl)
  then show False
  proof cases
    case 1
    then show ?thesis
      by (metis (no_types, hide_lams) \<open>u' \<in> arriving_U us\<close> assms(1) distinct.simps(2) fst_conv list.map(2) set_map wf_input_def)
  next
    case 2
    then show ?thesis
      using \<open>u' \<in> arriving_U us\<close> assms(2) by fastforce
  qed
qed

lemma ranking_aux_lowest_rank:
  assumes "wf_input \<sigma> us"
  assumes "u \<notin> Vs M"
  assumes "v \<in> set \<sigma>" \<comment> \<open>hence, u is the node that arrives\<close>
  assumes "w \<in> set \<sigma>" "w \<in> neighbors_of u us" "w \<notin> Vs M" "w \<notin> Vs (ranking_aux \<sigma> us M)"
  assumes "{u,v} \<in> ranking_aux \<sigma> us M"
  assumes "partitioned_bipartite M (set \<sigma>)"
  assumes "matching M"
  assumes "arriving_U us \<inter> Vs M = {}"
  shows "rank \<sigma> v < rank \<sigma> w"
  using assms
proof (induction \<sigma> us M rule: ranking_aux.induct)
  case (2 \<sigma> u' ns us M)

  have "u \<notin> set \<sigma>"
    by (meson "2.prems"(1) "2.prems"(2) "2.prems"(3) "2.prems"(8) "2.prems"(9) u_in_ranking_aux)

  have "w \<noteq> v"
    using assms(7) assms(8) insert_commute by auto

  consider (ind) "u \<notin> Vs (step \<sigma> M u' ns)" | (new) "u \<in> Vs (step \<sigma> M u' ns)" by blast
  then show ?case
  proof cases
    case ind
    have "w \<in> set \<sigma>" 
      using "2.prems"(4) by blast
    have "w \<in> neighbors_of u us"
      apply (rule neighbors_of_Cons[where u' = u'])
       apply (metis "2.prems"(1) "2.prems"(3) "2.prems"(8) ind ranking_aux_hd_ineq wf_input_hd)
      using "2.prems"(5) by blast
    have "w \<notin> Vs (step \<sigma> M u' ns)"
      by (metis "2.prems"(7) ranking_aux.simps(2) ranking_aux_mono vs_member_elim vs_member_intro)
    have "arriving_U us \<inter> Vs (step \<sigma> M u' ns) = {}"
      by (meson "2.prems"(1) "2.prems"(11) wf_input_arriving_U_disjoint_Cons)
    show ?thesis
      apply (rule "2.IH")
      using "2.prems"(1) wf_input_tl apply blast
      apply (simp_all add: "2.prems" ind \<open>w \<in> neighbors_of u us\<close> \<open>w \<notin> Vs (step \<sigma> M u' ns)\<close> \<open>arriving_U us \<inter> Vs (step \<sigma> M u' ns) = {}\<close>)
      using "2.prems"(7) apply force
      using "2.prems"(8) apply force
        apply (meson "2.prems"(1) "2.prems"(9) partitioned_bipartite_step wf_input_hd)
       apply (metis "2.prems"(1) "2.prems"(10) "2.prems"(11) disjoint_iff fst_conv image_eqI list.set_intros(1) matching_step wf_input_hd)
      done
  next
    case new
    have "u' = u"
      by (metis "2.prems"(2) \<open>u \<notin> set \<sigma>\<close> new vs_step)
    then have "{u,v} \<in> step \<sigma> M u ns"
      by (metis "2.prems"(1) "2.prems"(10) "2.prems"(11) "2.prems"(2) "2.prems"(3) "2.prems"(8) "2.prems"(9) new vertex_in_step_edge_in_step)
    have "w \<in> ns"
      using "2.prems"(5) \<open>u' = u\<close> by auto
    show ?thesis
      by (meson "2.prems"(2) "2.prems"(4) "2.prems"(6) \<open>u \<notin> set \<sigma>\<close> \<open>w \<in> ns\<close> \<open>w \<noteq> v\<close> \<open>{u, v} \<in> step \<sigma> M u ns\<close> step_lowest_rank)
  qed
qed simp


lemma ranking_lowest_rank:
  assumes "wf_input \<sigma> us"
  assumes "v \<in> set \<sigma>"
  assumes "w \<in> set \<sigma>" "w \<in> neighbors_of u us" "w \<notin> Vs (ranking \<sigma> us)"
  assumes "{u,v} \<in> ranking \<sigma> us"
  shows "rank \<sigma> v < rank \<sigma> w"
  using assms
  by (intro ranking_aux_lowest_rank[where u = u and M = "{}"]) (simp_all add: ranking_def)


definition move_to :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_ \<mapsto>\<index> _" [100,100] 40) where 
  "move_to xs v i \<equiv> (take i [x <- xs. x \<noteq> v]) @ v # (drop i [x <- xs. x \<noteq> v])"

lemma append_cong: "xs = xs' \<Longrightarrow> ys = ys' \<Longrightarrow> xs @ ys = xs' @ ys'"
  by simp

lemma move_to_gt_length:
  "length xs \<le> i \<Longrightarrow> (v \<mapsto>\<^bsub>xs\<^esub> i) = (v \<mapsto>\<^bsub>xs\<^esub> length xs)"
  unfolding move_to_def
  by (auto intro!: append_cong dest: le_trans[OF length_filter_le])

lemma move_to_Cons_Suc:
  assumes "x \<noteq> v"
  assumes "Suc n = i"
  shows "(v \<mapsto>\<^bsub>x#xs\<^esub> i) = x # (v \<mapsto>\<^bsub>xs\<^esub> n)"
  using assms
  unfolding move_to_def
  by auto

lemma move_to_neq_0_Cons:
  assumes "x \<noteq> v"
  assumes "i \<noteq> 0"
  shows "(v \<mapsto>\<^bsub>x#xs\<^esub> i) = x # (v \<mapsto>\<^bsub>xs\<^esub> (i - 1))"
  using assms
  unfolding move_to_def
  by (auto simp: drop_Cons' take_Cons')

lemma move_to_0:
  shows "(v \<mapsto>\<^bsub>xs\<^esub> 0) = v # [x <- xs. x \<noteq> v]"
  unfolding move_to_def
  by simp

lemma move_to_last:
  shows "(v \<mapsto>\<^bsub>xs\<^esub> (length xs)) = [x <- xs. x \<noteq> v] @ [v]"
  unfolding move_to_def
  by simp

lemma move_to_Cons_eq:
  "(v \<mapsto>\<^bsub>v#xs\<^esub> i) = (v \<mapsto>\<^bsub>xs\<^esub> i)"
  unfolding move_to_def
  by simp

lemma move_to_distinct:
  "distinct xs \<Longrightarrow> distinct (x \<mapsto>\<^bsub>xs\<^esub> i)"
  unfolding move_to_def
  by (auto dest: in_set_dropD in_set_takeD distinct_filter set_take_disj_set_drop_if_distinct)


lemma induct_list_nat[case_names nil_zero nil_suc cons_zero cons_suc]:
  assumes "P [] 0"
  assumes "\<And>n. P [] n \<Longrightarrow> P [] (Suc n)"
  assumes "\<And>x xs. P xs 0 \<Longrightarrow> P (x#xs) 0" 
  assumes "\<And>x xs n. P xs n \<Longrightarrow> P (x#xs) (Suc n)"
  shows "P xs n"
  using assms
  by (induction_schema) (pat_completeness, lexicographic_order)

lemma move_to_insert_before: "i \<le> rank \<sigma> w \<Longrightarrow> v \<noteq> w \<Longrightarrow> v \<notin> set \<sigma> \<Longrightarrow> rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w = Suc (rank \<sigma> w)"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto simp: move_to_0 move_to_Cons_Suc)

lemma move_to_insert_after: "rank \<sigma> w < i \<Longrightarrow> i \<le> length \<sigma> \<Longrightarrow> v \<noteq> w \<Longrightarrow> v \<notin> set \<sigma> \<Longrightarrow> rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w = rank \<sigma> w"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto simp: move_to_Cons_Suc)


lemma rank_less_filter: "rank xs w < rank xs v \<Longrightarrow> rank [x <- xs. x \<noteq> v] w = rank xs w"
  by (induction xs) (auto)

lemma not_in_take: "x \<notin> set xs \<Longrightarrow> x \<notin> set (take i xs)"
  by (auto dest: in_set_takeD)

lemma not_in_set_filter_length_eq: "v \<notin> set xs \<Longrightarrow> length [x <- xs. x \<noteq> v] = length xs"
  by (induction xs) auto

lemma in_set_distinct_filter_length_eq: "v \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> length [x <- xs. x \<noteq> v] = length xs - 1"
  by (induction xs) (auto simp: not_in_set_filter_length_eq intro!: Suc_pred)

lemma distinct_filter_length: "distinct xs \<Longrightarrow> (length [x <- xs. x \<noteq> v] = length xs \<and> v \<notin> set xs) \<or> (length [x <- xs. x \<noteq> v] = length xs - 1 \<and> v \<in> set xs)"
  by (metis in_set_distinct_filter_length_eq not_in_set_filter_length_eq)


lemma filter_removeAll: "[x <- xs. x \<noteq> v] = removeAll v xs"
  by (induction xs) auto

lemma not_in_set_filter_id: "v \<notin> set xs \<Longrightarrow> [x <- xs. x \<noteq> v] = xs"
  by (simp add: filter_removeAll)

lemma count_zero: "count_list xs v = 0 \<Longrightarrow>  v \<notin> set xs"
  by (induction xs) (auto split: if_splits)

lemma count_in: "v \<in> set xs \<Longrightarrow> count_list xs v \<noteq> 0"
  by (induction xs) auto

lemma Suc_rank_filter: "rank xs v < rank xs w \<Longrightarrow> v \<in> set xs \<Longrightarrow> count_list xs v = 1 \<Longrightarrow> Suc (rank [x <- xs. x \<noteq> v] w) = rank xs w"
  by (induction xs) (auto simp: not_in_set_filter_id[OF count_zero])

lemma not_Nil_length_SucE: "xs \<noteq> [] \<Longrightarrow> (\<And>n. length xs = Suc n \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction xs) auto


lemma move_to_id:
  "count_list \<sigma> v = 1 \<Longrightarrow> (v \<mapsto>\<^bsub>\<sigma>\<^esub> (rank \<sigma> v)) = \<sigma>"
  by (induction \<sigma>) (auto simp: move_to_0 filter_id_conv move_to_Cons_Suc count_zero)

lemma move_to_front_less:
  assumes "i < rank \<sigma> v"
  assumes "rank \<sigma> w < i"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w = rank \<sigma> w"
  using assms
  by (induction \<sigma> arbitrary: i)
     (auto split: if_splits elim: less_natE simp: move_to_Cons_Suc)



lemma move_to_front_between:
  assumes "count_list \<sigma> v \<le> 1"
  assumes "i < rank \<sigma> v"
  assumes "i \<le> rank \<sigma> w" "rank \<sigma> w < rank \<sigma> v"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w = Suc (rank \<sigma> w)"
  using assms
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits simp: move_to_0 move_to_Cons_Suc)

lemma move_to_front_gr:
  assumes "count_list \<sigma> v = 1"
  assumes "i < rank \<sigma> v" 
  assumes "rank \<sigma> v < rank \<sigma> w"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w = rank \<sigma> w"
proof -
  have "v \<in> set \<sigma>"
    using assms count_notin by fastforce
  then have "count_list \<sigma> v = 1"
    using assms count_zero by blast

  with assms \<open>v \<in> set \<sigma>\<close> show ?thesis
    by (induction \<sigma> i rule: induct_list_nat)
       (auto split: if_splits simp: move_to_0 move_to_Cons_Suc Suc_rank_filter)
qed

lemma move_to_back_less:
  assumes "rank \<sigma> v < i"
  assumes "rank \<sigma> w < rank \<sigma> v"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w = rank \<sigma> w"
  using assms
  by (induction \<sigma> arbitrary: i) (auto split: if_splits simp: move_to_neq_0_Cons)


lemma move_to_back_between:
  assumes "count_list \<sigma> v = 1"
  assumes "rank \<sigma> v < i"  
  assumes "i < length \<sigma>"
  assumes "rank \<sigma> v < rank \<sigma> w" "rank \<sigma> w \<le> i"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w + 1 = rank \<sigma> w"
proof -
  have "v \<in> set \<sigma>"
    using assms count_notin by fastforce
  then have "count_list \<sigma> v = 1"
    using assms count_zero by blast
  with \<open>v \<in> set \<sigma>\<close> assms show ?thesis
    by (induction \<sigma> arbitrary: i)
       (auto simp: move_to_Cons_eq move_to_neq_0_Cons move_to_insert_after split: if_splits dest!: count_zero)
qed

lemma move_to_back_gr:
  assumes "count_list \<sigma> v = 1"
  assumes "rank \<sigma> v < i" "i < length \<sigma>"
  assumes "i < rank \<sigma> w"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w = rank \<sigma> w"
  using assms
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits dest: count_zero
           simp: move_to_Cons_eq move_to_Cons_Suc move_to_insert_before)



lemma distinct_count_list_le: "distinct xs \<Longrightarrow> count_list xs x \<le> 1"
  by (induction xs) auto


lemma move_to_rank_v:
  assumes "distinct \<sigma>"
  assumes "i < length \<sigma>"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) v = i"
  using assms
proof (induction \<sigma> i rule: induct_list_nat)
  case (cons_suc x xs n)
  then show ?case 
    by (cases "x = v")
       (auto simp: move_to_Cons_Suc move_to_Cons_eq move_to_def index_append not_in_set_filter_id 
             dest: in_set_takeD split: if_splits)
qed (auto simp add: move_to_0)

lemma move_to_rank_less:
  assumes "distinct \<sigma>"
  assumes "i < length \<sigma>"
  assumes "v \<noteq> w"
  assumes "rank \<sigma> w < i"
  shows "rank (v \<mapsto>\<^bsub>\<sigma>\<^esub> i) w \<le> rank \<sigma> w"
  using assms
proof (induction \<sigma> i rule: induct_list_nat)
  case (cons_suc x xs n)
  then show ?case 
    by (auto simp: move_to_Cons_Suc move_to_def index_append not_in_set_filter_id set_take_if_index
             dest: in_set_takeD index_take_if_set  split: if_splits)
qed auto



end
