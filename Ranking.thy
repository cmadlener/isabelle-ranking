theory Ranking
  imports 
    "AGF.Berge"
    "AGF.Bipartite"
    "List-Index.List_Index"
begin

lemma vs_empty[simp]: "Vs {} = {}"
  by (simp add: Vs_def)

lemma graph_abs_empty[simp]: "graph_abs {}"
  by (simp add: graph_abs_def)

lemma graph_abs_insert[simp]: "graph_abs M \<Longrightarrow> u \<noteq> v \<Longrightarrow> graph_abs (insert {u,v} M)"
  by (auto simp: graph_abs_def Vs_def)

lemma graph_abs_union[intro]: "graph_abs G \<Longrightarrow> graph_abs H \<Longrightarrow> graph_abs (G \<union> H)"
  by (auto simp: graph_abs_def Vs_def)

lemma graph_abs_compr[intro]: "u \<notin> ns \<Longrightarrow> finite ns \<Longrightarrow> graph_abs {{u, v} |v. v \<in> ns}"
  unfolding graph_abs_def by (auto simp: Vs_def)

lemma matching_empty[simp]: "matching {}"
  unfolding matching_def by simp

type_synonym 'a graph = "'a set set"

text \<open>For now we don't care about distinctness of the "ranking" list, as we only need the order
  induced by the list.\<close>
abbreviation "rank \<sigma> v \<equiv> index \<sigma> v"

abbreviation "arriving_U us \<equiv> set (map fst us)"
abbreviation "arriving_V us \<equiv> \<Union>(set (map snd us))"

definition wf_input :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> bool" where
  "wf_input \<sigma> us \<equiv> 
    set \<sigma> \<inter> arriving_U us = {} \<and> 
    arriving_V us \<subseteq> set \<sigma> \<and>
    distinct \<sigma> \<and> 
    distinct (map fst us)"

fun step :: "'a list \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a graph" where
  "step [] M _ _ = M"
| "step (v#vs) M u neighbors = (
    if v \<in> neighbors - Vs M
    then insert {u,v} M
    else step vs M u neighbors
  )"

\<comment> \<open>"Unfold" fold definition to generalize over accumulator.\<close>
fun ranking_aux :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a graph \<Rightarrow> 'a graph" where
  "ranking_aux _ [] M = M"
| "ranking_aux \<sigma> ((u,ns)#us) M = ranking_aux \<sigma> us (step \<sigma> M u ns)"

definition ranking :: "'a list \<Rightarrow> ('a \<times> 'a set) list \<Rightarrow> 'a graph" where
  "ranking \<sigma> us = ranking_aux \<sigma> us {}"

lemma ranking_PI: "P (ranking_aux \<sigma> us {}) \<Longrightarrow> P (ranking \<sigma> us)"
  unfolding ranking_def .

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

lemma wf_input_hd: "wf_input \<sigma> ((u,ns) # us) \<Longrightarrow> u \<notin> ns \<and> finite ns \<and> u \<notin> set \<sigma>"
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

lemma vs_step: "Vs (step \<sigma> M u ns) \<subseteq> {u} \<union> set \<sigma> \<union> Vs M"
  by (induction \<sigma> M u ns rule: step.induct) (auto simp: Vs_def)

lemma graph_abs_step:
  assumes "graph_abs M"
  assumes "u \<notin> set \<sigma>"
  shows "graph_abs (step \<sigma> M u ns)"
  using assms
  by (induction \<sigma>) auto

lemma matching_step:
  assumes "graph_abs M"
  assumes "matching M"
  assumes "u \<notin> set \<sigma>"
  assumes "u \<notin> Vs M"
  shows "matching (step \<sigma> M u ns)"
  using assms
  by (induction \<sigma>) (auto simp: matching_def)

lemma wf_input_graph_abs_ranking_aux:
  assumes "graph_abs M"
  assumes "wf_input \<sigma> us"
  shows "graph_abs (ranking_aux \<sigma> us M)"
  using assms
  by (induction us arbitrary: M) (auto simp: wf_input_def graph_abs_step)

lemma Int_empty_rev_mono: "A \<inter> C = {} \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<inter> B = {}"
  by blast

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
    by (simp add:  Int_Un_distrib Int_commute)

  then have "arriving_U us \<inter> Vs (step \<sigma> M u ns) = {}"
    by (rule Int_empty_rev_mono[OF _ vs_step])

  then show ?case
    using "2.IH" 1
    by simp
qed auto

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
  by (induction us rule: offline_graph.induct) (auto dest: wf_input_tl wf_input_hd)


lemma in_step_elim:
  assumes "e \<in> step \<sigma> M u ns"
  assumes "e \<notin> M"
  obtains v where "e = {u,v}" "v \<in> ns" "v \<in> set \<sigma>" "v \<notin> Vs M"
  using assms edge_in_step
  by force

lemma step_lowest_rank: "set \<sigma> \<inter> ns \<noteq> {} \<Longrightarrow> step \<sigma> {} u ns = {{u, \<sigma> ! Min (rank \<sigma> ` ns)}}"
  sorry


lemma ranking_aux_subset_offline_graph:
  assumes "x \<in> ranking_aux \<sigma> us M"
  shows "x \<in> offline_graph us \<union> M"
  using assms
  by (induction \<sigma> us M rule: ranking_aux.induct) (auto dest: edge_in_step)

lemma "x \<in> ranking \<sigma> us \<Longrightarrow> x \<in> offline_graph us"
  unfolding ranking_def
  by (auto dest: ranking_aux_subset_offline_graph)


end